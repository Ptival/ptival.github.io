{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}

module BlogPost.ANF where

import qualified BlogPost.Source as S
import BlogPost.Var (Bdr (B), Var (V))
import Control.Lens (Field1 (..), Identity, makeLenses, over, view, (<<+=))
import Control.Monad ((<=<))
import Control.Monad.RWS (MonadState (get), MonadWriter (tell), RWST (RWST, runRWST))
import Control.Monad.Reader (ReaderT (runReaderT))
import Control.Monad.State (StateT (StateT, runStateT), evalStateT, runState)
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.Cont (ContT (runContT))
import Control.Monad.Writer (WriterT (WriterT, runWriterT), runWriter)
import Data.Functor.Identity (Identity (Identity, runIdentity))
import Data.String (IsString (fromString))
import Prettyprinter (Pretty (pretty), hsep)

data Const
  = Int Int
  | Var Var
  deriving (Show)

instance IsString Const where
  fromString = Var . fromString

instance Pretty Const where
  pretty (Int n) = pretty n
  pretty (Var v) = pretty v

data Atom
  = App Const Const
  | Const Const
  | Lam Bdr Exp
  deriving (Show)

instance IsString Atom where
  fromString = Const . fromString

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
  | Let Bdr Exp Exp
  deriving (Show)

instance IsString Exp where
  fromString = Halt . fromString

instance Pretty Exp where
  pretty (Halt a) = pretty a
  pretty (Let b e1 e2) = S.prettyLet (pretty b) (pretty e1) (pretty e2)

newtype ANFWriter = ANFWriter {_bindings :: [(Bdr, Exp)]}
  deriving (Monoid, Semigroup)

newtype ANFState = ANFState {_freshCounter :: Int}

makeLenses ''ANFState

newtype ANFM a = ANFM
  { getANFM :: WriterT ANFWriter (StateT ANFState Identity) a
  }
  deriving
    ( Applicative,
      Functor,
      Monad,
      MonadWriter ANFWriter,
      MonadState ANFState
    )

fresh :: ANFM (Bdr, Var)
fresh = do
  sId <- freshCounter <<+= 1
  let s = "anf#" <> show sId
  return (B s, V s)

-- | Runs `ma` but capture its local writer output, returning it, and replacing
-- it with an empty writer for the caller.
intercept :: ANFM a -> ANFM (a, ANFWriter)
intercept ma = do
  (a, w) <- ANFM . lift . runWriterT . getANFM $ ma
  ANFM $ WriterT (StateT (Identity . (((a, w), mempty),)))

anfToConst :: S.Exp -> ANFM Const
anfToConst (S.Int i) = return (Int i)
anfToConst (S.Var v) = return (Var v)
anfToConst e = do
  (b, v) <- fresh
  a <- anfToAtom e
  tell $ ANFWriter [(b, Halt a)]
  return (Var v)

bind :: (Bdr, Exp) -> Exp -> Exp
bind (b, eb) = Let b eb

bindAll :: [(Bdr, Exp)] -> Exp -> Exp
bindAll = flip (foldr bind)

anfToAtom :: S.Exp -> ANFM Atom
anfToAtom (S.App e1 e2) = App <$> anfToConst e1 <*> anfToConst e2
anfToAtom (S.Int i) = return $ Const (Int i)
anfToAtom (S.Lam b e) = do
  (e', ANFWriter bindings) <- intercept (anfToExp e)
  return $ Lam b (bindAll bindings e')
anfToAtom (S.Let b e1 e2) = do
  (a1, ANFWriter bs) <- intercept (anfToAtom e1)
  tell $ ANFWriter [(b, bindAll bs (Halt a1))]
  anfToAtom e2
anfToAtom (S.Var v) = return $ Const (Var v)

anfToExp :: S.Exp -> ANFM Exp
anfToExp e = (Halt <$>) $ anfToAtom e

anf :: S.Exp -> Exp
anf e =
  let (e', ANFWriter bindings) =
        runIdentity
          . flip evalStateT (ANFState 0)
          . runWriterT
          . getANFM
          $ anfToExp e
   in bindAll bindings e'

e1 :: S.Exp
e1 =
  S.lets
    [ ("a", S.Int 2),
      ("b", S.Int 3)
    ]
    $ S.apps ["plus", "a", "b"]

{- >>> pretty e1
let a = 2 in
let b = 3 in
plus a b
-}

{- >>> pretty $ anf e1
let a = 2 in
let b = 3 in
let anf#0 = plus a in
anf#0 b
-}

e2 :: S.Exp
e2 =
  S.lets
    [ ("a", S.Int 5),
      ("sum", e1)
    ]
    $ S.apps ["plus", "a", "sum"]

{- >>> pretty e2
let a = 5 in
let sum = let a = 2 in
          let b = 3 in
          plus a b in
plus a sum
-}

{- >>> pretty $ anf e2
let a = 5 in
let sum = let a = 2 in
          let b = 3 in
          let anf#0 = plus a in
          anf#0 b in
let anf#1 = plus a in
anf#1 sum
-}

e3 :: S.Exp
e3 =
  S.lets
    [("flip", S.lams ["f", "a", "b"] (S.apps ["f", "b", "a"]))]
    $ S.apps ["flip", "minus", S.Int 1, S.Int 5]

{- >>> pretty e3
let flip = \ f a b ->
           f b a in
flip minus 1 5
-}

{- >>> pretty $ anf e3
let flip = \ f a b ->
           let anf#0 = f b in
           anf#0 a in
let anf#2 = flip minus in
let anf#1 = anf#2 1 in
anf#1 5
-}
