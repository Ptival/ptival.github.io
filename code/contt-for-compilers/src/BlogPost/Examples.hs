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
let a#0 = 2 in
let b#1 = 3 in
let anf#2 = (plus a#0) in
(anf#2 b#1)
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
let a#0 = 5 in
let a#1 = 2 in
let b#2 = 3 in
let anf#3 = (plus a#1) in
let sum#4 = (anf#3 b#2) in
let anf#5 = (plus a#0) in
(anf#5 sum#4)
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

{- >>> pretty $ ANF.anf e3
let flip#1 = \ f a b ->
             let anf#0 = (f b) in
             (anf#0 a) in
let anf#3 = (flip#1 minus) in
let anf#2 = (anf#3 1) in
(anf#2 5)
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
let main#1 = (f#0 1) in
main#1
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
                    (S.lams ["x"] (S.apps ["plus", "n", "x"]))
                    ( S.apps
                        [ "cond",
                          S.apps ["eq", "n", "1"],
                          "1",
                          S.apps ["f", S.apps ["sum", S.apps ["minus", "n", "1"]]]
                        ]
                    )
                )
            )
            (S.apps ["sum", "arg"])
        )
    )
    (S.apps ["main", "42"])

{- >>> pretty e6
let main = \ arg ->
           let sum = \ n ->
                     let f = \ x ->
                             ((plus n) x) in
                     (((cond ((eq n) 1)) 1) (f (sum ((minus n) 1)))) in
           (sum arg) in
(main 42)
-}

{- >>> pretty $ ANF.anf e6
let main#11 = \ arg ->
              let sum#10 = \ n ->
                           let f#1 = \ x ->
                                     let anf#0 = (plus n) in
                                     (anf#0 x) in
                           let anf#5 = (eq n) in
                           let anf#4 = (anf#5 1) in
                           let anf#3 = (cond anf#4) in
                           let anf#2 = (anf#3 1) in
                           let anf#9 = (minus n) in
                           let anf#8 = (anf#9 1) in
                           let anf#7 = (sum anf#8) in
                           let anf#6 = (f#1 anf#7) in
                           (anf#2 anf#6) in
              (sum#10 arg) in
(main#11 42)
-}
