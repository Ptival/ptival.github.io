{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}

module ANF where

import Control.Lens (Field1 (..), Identity, makeLenses, view, (<<+=))
import Control.Monad.RWS (MonadState (get), MonadWriter (tell), RWST (RWST, runRWST))
import Control.Monad.Reader (ReaderT (runReaderT))
import Control.Monad.State (StateT (StateT, runStateT), evalStateT, runState)
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.Cont (ContT (runContT))
import Control.Monad.Writer (WriterT (WriterT, runWriterT), runWriter)
import Data.Functor.Identity (Identity (Identity, runIdentity))
import Prettyprinter (Pretty (pretty))
import qualified Source as S
import Var (Bdr (B), Var (V))

data Atom
  = App Var Var
  | Int Int
  | Var Var
  deriving (Show)

-- I know, I'm not parenthesizing appropriately
instance Pretty Atom where
  pretty (App v1 v2) = S.prettyApp v1 v2
  pretty (Int n) = pretty n
  pretty (Var v) = pretty v

data Exp
  = Halt Atom
  | Let Bdr Exp Exp
  deriving (Show)

instance Pretty Exp where
  pretty (Halt a) = pretty a
  pretty (Let b e1 e2) = S.prettyLet b e1 e2

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
  let s = "x#" <> show sId
  return (B s, V s)

-- | Runs `ma` but capture its local writer output, returning it, and replacing
-- it with an empty writer for the caller.
intercept :: ANFM a -> ANFM (a, ANFWriter)
intercept ma = do
  (a, w) <- ANFM $ lift $ runWriterT . getANFM $ ma
  ANFM $ WriterT (StateT (Identity . (((a, w), mempty),)))

anfToVar :: S.Exp -> ContT Exp ANFM Var
anfToVar (S.Var v) = return v
anfToVar e = do
  (b, v) <- lift fresh
  a <- anfToAtom e
  lift $ tell $ ANFWriter [(b, Halt a)]
  return v

bind :: (Bdr, Exp) -> Exp -> Exp
bind (b, eb) = Let b eb

bindAll :: [(Bdr, Exp)] -> Exp -> Exp
bindAll = flip (foldr bind)

anfToAtom :: S.Exp -> ContT Exp ANFM Atom
anfToAtom (S.App e1 e2) = App <$> anfToVar e1 <*> anfToVar e2
anfToAtom (S.Int i) = return $ Int i
anfToAtom (S.Let b e1 e2) = do
  -- Wihtout `intercept`, the local let bindings introduced by `e1` are hoisted
  -- all the way to the top.
  (e1, ANFWriter bs) <- lift $ intercept $ runContT (anfToAtom e1) (pure . Halt)
  lift $ tell $ ANFWriter [(b, bindAll bs e1)]
  anfToAtom e2
anfToAtom (S.Var v) = return (Var v)

anfToExp :: S.Exp -> ANFM Exp
anfToExp = flip runContT (pure . Halt) . anfToAtom

anf :: S.Exp -> Exp
anf e =
  let (e', ANFWriter bindings) =
        runIdentity $
          flip evalStateT (ANFState 0) $
            runWriterT (getANFM (anfToExp e))
   in bindAll bindings e'

e1 :: S.Exp
e1 =
  S.Let "a" (S.Int 2) $
    S.Let "b" (S.Int 3) $
      S.App (S.App (S.Var "plus") (S.Var "a")) (S.Var "b")

{- >>> pretty e1
let a = 2 in
let b = 3 in
plus a b
-}

{- >>> pretty $ anf e1
let a = 2 in
let b = 3 in
let x#0 = plus a in
x#0 b
-}

e2 :: S.Exp
e2 =
  S.Let "a" (S.Int 5) $
    S.Let "sum" e1 $
      S.App (S.App (S.Var "plus") (S.Var "a")) (S.Var "sum")

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
          let x#0 = plus a in
          x#0 b in
let x#1 = plus a in
x#1 sum
-}
