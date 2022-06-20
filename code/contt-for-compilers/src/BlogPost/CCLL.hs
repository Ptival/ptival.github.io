{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}

module BlogPost.CCLL where

import qualified BlogPost.ANF as A
import qualified BlogPost.Source as S
import BlogPost.Var (Bdr (B), Var (V), varOfBdr)
import Control.Lens (Field1 (..), Identity, makeLenses, over, view, (<<+=))
import Control.Monad ((<=<))
import Control.Monad.RWS (MonadState (get), MonadWriter (tell), RWST (RWST, runRWST))
import Control.Monad.Reader (ReaderT (runReaderT))
import Control.Monad.State (StateT (StateT, runStateT), evalStateT, runState)
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.Cont (ContT (runContT), callCC, evalContT, mapContT, withContT)
import Control.Monad.Writer (WriterT (WriterT, runWriterT), runWriter)
import Data.Functor.Identity (Identity (Identity, runIdentity))
import Data.Set (Set)
import qualified Data.Set as Set
import Foreign (free)
import Prettyprinter (Pretty (pretty), encloseSep, hsep, sep, (<+>))
import Text.ParserCombinators.ReadP (sepBy)

data Atom
  = App A.Const A.Const
  | Const A.Const
  | Pack [Var]
  deriving (Show)

instance Pretty Atom where
  pretty (App v1 v2) = S.prettyApp (pretty v1) (pretty v2)
  pretty (Const c) = pretty c
  pretty (Pack cs) = encloseSep "<" ">" ", " (pretty <$> cs)

data Fun
  = Atom Atom
  | Lam Bdr (Exp Fun)

instance Pretty Fun where
  pretty (Atom a) = pretty a
  pretty e@Lam {} =
    let (bs, e') = gatherLamsFun e
     in S.prettyLam (hsep $ pretty <$> bs) (pretty e')
    where
      gatherLamsFun :: Fun -> ([Bdr], Exp Fun)
      gatherLamsFun (Lam b e) = over _1 (b :) $ gatherLamsExp e
      gatherLamsFun e = ([], Halt e)
      gatherLamsExp :: Exp Fun -> ([Bdr], Exp Fun)
      gatherLamsExp (Halt f) = gatherLamsFun f
      gatherLamsExp e = ([], e)

data Exp f
  = Halt f
  | Let Bdr (Exp f) (Exp f)
  deriving (Show)

instance Pretty f => Pretty (Exp f) where
  pretty (Halt a) = pretty a
  pretty (Let b e1 e2) = S.prettyLet (pretty b) (pretty e1) (pretty e2)

data Lambda = Lambda
  { _name :: Bdr,
    _params :: [Bdr],
    _body :: Exp Atom
  }

makeLenses ''Lambda

newtype CCLLWriter = CCLLWriter {_lambdas :: [Lambda]}
  deriving (Monoid, Semigroup)

newtype CCLLState = CCLLState {_freshCounter :: Int}

makeLenses ''CCLLState

newtype CCLLM a = CCLLM
  { getCCLLM :: WriterT CCLLWriter (StateT CCLLState Identity) a
  }
  deriving
    ( Applicative,
      Functor,
      Monad,
      MonadWriter CCLLWriter,
      MonadState CCLLState
    )

fresh :: CCLLM (Bdr, Var)
fresh = do
  sId <- freshCounter <<+= 1
  let s = "ccll#" <> show sId
  return (B s, V s)

class FreeVars a where
  freeVars :: a -> Set Var

instance FreeVars Var where
  freeVars = Set.singleton

instance FreeVars A.Const where
  freeVars (A.Var v) = freeVars v
  freeVars (A.Int _) = Set.empty

instance FreeVars A.Atom where
  freeVars (A.App e1 e2) = freeVars e1 `Set.union` freeVars e2
  freeVars (A.Const c) = freeVars c
  freeVars (A.Lam b e) = freeVars e `Set.difference` Set.singleton (varOfBdr b)

instance FreeVars A.Exp where
  freeVars (A.Halt a) = freeVars a
  -- Here we're going to consider lets as non-recursive by default
  freeVars (A.Let b e1 e2) =
    freeVars e1
      `Set.union` (freeVars e2 `Set.difference` Set.singleton (varOfBdr b))

ccllAtom :: A.Atom -> ContT (Exp Atom) CCLLM Atom
ccllAtom (A.App e1 e2) = return $ App e1 e2
ccllAtom (A.Const c) = return $ Const c
ccllAtom (A.Lam p e) = do
  (b, v) <- lift fresh
  e' <- lift $ ccllExp e
  let fvs = freeVars e
  lift $ tell $ CCLLWriter [Lambda b ["env", p] e']
  mapContT (fmap (Let "env" (Halt $ Pack (Set.toList fvs)))) $
    return (App (A.Var v) (A.Var "env"))

ccllExp :: A.Exp -> CCLLM (Exp Atom)
ccllExp (A.Halt a) = evalContT $ Halt <$> ccllAtom a
ccllExp (A.Let b e1 e2) = Let b <$> ccllExp e1 <*> ccllExp e2

nestLambdas :: [Bdr] -> Exp Fun -> Exp Fun
nestLambdas = flip $ foldr lam
  where
    lam :: Bdr -> Exp Fun -> Exp Fun
    lam b e = Halt (Lam b e)

liftedLambda :: Lambda -> Exp Fun -> Exp Fun
liftedLambda l =
  Let
    (view name l)
    (nestLambdas (view params l) (asExpFun (view body l)))

asExpFun :: Exp Atom -> Exp Fun
asExpFun (Halt a) = Halt (Atom a)
asExpFun (Let b e1 e2) = Let b (asExpFun e1) (asExpFun e2)

ccll :: A.Exp -> Exp Fun
ccll e =
  let (e', CCLLWriter ls) =
        runIdentity
          . flip evalStateT (CCLLState 0)
          . runWriterT
          . getCCLLM
          $ ccllExp e
   in foldr liftedLambda (asExpFun e') ls

e1 :: S.Exp
e1 =
  S.Let
    "flip"
    (S.lams ["f", "a", "b"] (S.apps [S.Var "f", S.Var "b", S.Var "a"]))
    $ S.apps [S.Var "flip", S.Var "minus", S.Int 1, S.Int 5]

{- >>> pretty e1
let flip = \ f a b ->
           f b a in
flip minus 1 5
-}

{- >>> pretty (ccll (A.anf e1))
let ccll#2 = \ env b ->
             let anf#0 = f b in
             anf#0 a in
let ccll#1 = \ env a ->
             let env = <a, b, f> in
             ccll#2 env in
let ccll#0 = \ env f ->
             let env = <a, f> in
             ccll#1 env in
let flip = let env = <f> in
           ccll#0 env in
let anf#2 = flip minus in
let anf#1 = anf#2 1 in
anf#1 5
-}
