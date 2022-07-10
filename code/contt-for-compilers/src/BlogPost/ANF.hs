{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}

module BlogPost.ANF where

import BlogPost.Renaming (Renamable (rename), addRenaming, emptyRenaming, removeBdr, renaming)
import qualified BlogPost.Source as S
import BlogPost.Var (Bdr (B), Var (V))
import Control.Lens (Field1 (..), Identity, makeLenses, over, view, (<<+=))
import Control.Monad (foldM, forM, forM_, (<=<))
import Control.Monad.RWS (MonadState (get), MonadWriter (tell), RWST (RWST, runRWST))
import Control.Monad.Reader (ReaderT (ReaderT, runReaderT))
import Control.Monad.State (StateT (StateT, runStateT), evalStateT, runState)
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.Cont (ContT (runContT))
import Control.Monad.Writer (WriterT (WriterT, runWriterT), runWriter)
import Data.Functor.Identity (Identity (Identity, runIdentity))
import Data.String (IsString (fromString))
import Debug.Trace (trace)
import Prettyprinter (Pretty (pretty), hsep)

data Const
  = Int Int
  | Var Var
  deriving (Show)

instance IsString Const where
  fromString = Var . fromString

instance Pretty Const where
  pretty (Int i) = pretty i
  pretty (Var v) = pretty v

instance Renamable Const where
  rename r (Int i) = Int i
  rename r (Var v) = Var (rename r v)

data Atom
  = App Const Const
  | Const Const
  | Lam Bdr Exp
  deriving (Show)

instance IsString Atom where
  fromString = Const . fromString

instance Renamable Atom where
  rename r (App c1 c2) = App (rename r c1) (rename r c2)
  rename r (Const c) = Const (rename r c)
  rename r (Lam b e) = Lam b (rename (removeBdr b r) e)

gatherLamsAtom :: Atom -> ([Bdr], Exp)
gatherLamsAtom (Lam b a) = over _1 (b :) (gatherLamsExp a)
gatherLamsAtom a = ([], Halt a)

gatherLamsExp :: Exp -> ([Bdr], Exp)
gatherLamsExp (Halt a) = gatherLamsAtom a
gatherLamsExp e = ([], e)

instance Pretty Atom where
  pretty (App v1 v2) = S.prettyApp (pretty v1) (pretty v2)
  pretty (Const c) = pretty c
  pretty a@(Lam {}) =
    let (bs, a') = gatherLamsAtom a
     in S.prettyLam (hsep (fmap pretty bs)) (pretty a')

data Exp
  = Halt Atom
  | Let Bdr Atom Exp
  deriving (Show)

instance IsString Exp where
  fromString = Halt . fromString

instance Pretty Exp where
  pretty (Halt a) = pretty a
  pretty (Let b e1 e2) = S.prettyLet (pretty b) (pretty e1) (pretty e2)

instance Renamable Exp where
  rename r (Halt a) = Halt (rename r a)
  rename r (Let b a e) = Let b (rename r a) (rename (removeBdr b r) e)

type LetBinding = (Bdr, Atom)

newtype ANFState = ANFState {_freshCounter :: Int}

makeLenses ''ANFState

newtype ANFM a = ANFM
  { getANFM :: WriterT [LetBinding] (StateT ANFState Identity) a
  }
  deriving
    ( Applicative,
      Functor,
      Monad,
      MonadWriter [LetBinding],
      MonadState ANFState
    )

fresh :: ANFM (Bdr, Var)
fresh = do
  sId <- freshCounter <<+= 1
  let s = "anf#" <> show sId
  return (B s, V s)

freshFrom :: Bdr -> ANFM (Bdr, Var)
freshFrom (B b) = do
  sId <- freshCounter <<+= 1
  let s = b <> "#" <> show sId
  return (B s, V s)

-- Runs `ma` but capture its local writer output, returning it, and replacing it
-- with an empty writer for the caller.
intercept :: ANFM a -> ANFM (a, [LetBinding])
intercept ma = ANFM $
  WriterT $ do
    (a, w) <- runWriterT . getANFM $ ma
    StateT (Identity . (((a, w), mempty),))

bindAll :: [(Bdr, Atom)] -> Exp -> Exp
bindAll = flip (foldr (uncurry Let))

anf :: S.Exp -> Exp
anf e =
  let (a, bs) =
        runIdentity
          . flip evalStateT (ANFState 0)
          . runWriterT
          . getANFM
          $ anfExp e
   in bindAll bs (Halt a)

anfConst :: S.Exp -> ANFM Const
anfConst (S.Int i) = return (Int i)
anfConst (S.Var v) = return (Var v)
anfConst e = do
  (b, v) <- fresh
  e' <- anfExp e
  tell [(b, e')]
  return (Var v)

anfExp :: S.Exp -> ANFM Atom
anfExp (S.App e1 e2) = App <$> anfConst e1 <*> anfConst e2
anfExp (S.Int i) = return $ Const (Int i)
anfExp (S.Lam b e) = do
  (a, bs) <- intercept (anfExp e)
  return $ Lam b (bindAll bs (Halt a))
anfExp (S.Let b e1 e2) = do
  (a1, bs) <- intercept (anfExp e1)
  r <- foldM sanitize emptyRenaming bs
  tell [(b, rename r a1)]
  anfExp (rename r e2)
  where
    sanitize r (b, a) = do
      (b', _) <- freshFrom b
      tell [(b', rename r a)]
      return $ addRenaming (b, b') r
anfExp (S.Var v) = return $ Const (Var v)
