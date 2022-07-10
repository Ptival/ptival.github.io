{-# LANGUAGE OverloadedStrings #-}

module BlogPost.Examples where

import qualified BlogPost.ANF as ANF
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
((plus a) b)
-}

{- >>> pretty $ ANF.anf e1
let a = 2 in
let b = 3 in
let anf#0 = (plus a) in
(anf#0 b)
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
          ((plus a) b) in
((plus a) sum)
-}

{- >>> pretty $ ANF.anf e2
let a = 5 in
let a#1 = 2 in
let b#2 = 3 in
let anf#0#3 = (plus a#1) in
let sum = (anf#0#3 b#2) in
let anf#4 = (plus a#1) in
(anf#4 sum)
-}

e3 :: S.Exp
e3 =
  S.lets
    [("flip", S.lams ["f", "a", "b"] (S.apps ["f", "b", "a"]))]
    $ S.apps ["flip", "minus", S.Int 1, S.Int 5]

{- >>> pretty e3
let flip = \ f a b ->
           ((f b) a) in
(((flip minus) 1) 5)
-}

{- >>> pretty $ ANF.anf e4
let f#0 = \ x ->
          x in
let main = (f#0 1) in
main
-}

e4 :: S.Exp
e4 =
  S.Let
    "main"
    ( S.Let
        "f"
        (S.lams ["x"] "x")
        (S.apps ["f", "1"])
    )
    "main"

{- >>> pretty e4
let main = let f = \ x ->
                   x in
           (f 1) in
main
-}

{- >>> pretty $ ANF.anf e4
let f#0 = \ x ->
          x in
let main = (f#0 1) in
main
-}

e5 :: S.Exp
e5 = S.apps ["f", S.apps ["f", "1", "2"], "3"]

{- >>> pretty e5
((f ((f 1) 2)) 3)
-}

{- >>> pretty $ ANF.anf e5
let anf#2 = (f 1) in
let anf#1 = (anf#2 2) in
let anf#0 = (f anf#1) in
(anf#0 3)
-}

e6 :: S.Exp
e6 =
  S.Let
    "main"
    ( S.lams
        ["arg"]
        ( S.Let
            "sum"
            ( S.lams
                ["n"]
                ( S.Let
                    "f"
                    (S.lams ["x"] (S.apps ["+", "n", "x"]))
                    ( S.apps
                        [ "cond",
                          S.apps ["==", "n", "1"],
                          "1",
                          S.apps ["f", S.apps ["sum", S.apps ["-", "n", "1"]]]
                        ]
                    )
                )
            )
            (S.apps ["sum", "arg"])
        )
    )
    (S.apps ["main", "42"])

e7 :: S.Exp
e7 =
  S.Let "main" "boop" (S.apps ["+", "1", S.Let "bop" "zoop" "schmoop"])

{- >>> pretty e6
let main = \ arg ->
           let sum = \ n ->
                     let f = \ x ->
                             ((+ n) x) in
                     (((cond ((== n) 1)) 1) (f (sum ((- n) 1)))) in
           (sum arg) in
(main 42)
-}

{- >>> pretty $ ANF.anf e6
let main = \ arg ->
           let sum = \ n ->
                     let f = \ x ->
                             let anf#0 = (+ n) in
                             (anf#0 x) in
                     let anf#4 = (== n) in
                     let anf#3 = (anf#4 1) in
                     let anf#2 = (cond anf#3) in
                     let anf#1 = (anf#2 1) in
                     let anf#8 = (- n) in
                     let anf#7 = (anf#8 1) in
                     let anf#6 = (sum anf#7) in
                     let anf#5 = (f anf#6) in
                     (anf#1 anf#5) in
           (sum arg) in
(main 42)
-}
