module Snake.Text.Parser.Base where

open import Data.Product         using (_×_; _,_)
open import Data.Nat.Base        using (ℕ)
open import Data.List            using (List; []; _∷_)
open import Data.String.Base     using (String)

open import Text.Parser.Monad    using (module Agdarsec)
open import Text.Parser.Types    using (runParser)
open import Text.Parser.Position using (Position)

open import Relation.Unary

--------------------------------------------------------------------------------

data Error : Set where
  syntax-error : Position          → Error
  expected     : Position → String → Error

private
  toError : Position × List String → Error
  toError (pos , [])      = syntax-error pos
  toError (pos , ann ∷ _) = expected pos ann

module Monad = Agdarsec Error String (record { into = toError })
open Monad public using (monad; commit)

Parser = Text.Parser.Types.Parser Monad.chars

instance
  open import Category.Monad using (RawMonadPlus)
  monadPlus : RawMonadPlus _
  monadPlus = Monad.monadPlus

annot : ∀ {A} → String → ∀[ Parser A ⇒ Parser A ]
runParser (annot ann p) n≤m s = Monad.withAnnotation ann (runParser p n≤m s)
