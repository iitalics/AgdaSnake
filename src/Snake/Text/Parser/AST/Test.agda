module Snake.Text.Parser.AST.Test where

open import Function
open import Data.Product               using (_×_; _,_; proj₁)
open import Data.List.Base             using (List; []; _∷_)
open import Data.List.NonEmpty         using (List⁺; _∷_)
open import Data.Vec            as Vec using (Vec)
open import Data.String.Base as String using (String)
open import Data.Unit

open import Relation.Unary
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Nat.Properties        using (≤-refl)

open import Text.Parser.Position       using (Position; start)
open import Text.Parser.Types          using (Success; _^_,_; runParser)
open import Text.Parser.Monad

open import Snake.Text.Parser.Base
open import Snake.Data.AST.Raw Position
import Snake.Text.Parser.AST as P
-- import Data.Snake.AST as AST

--------------------------------------------------------------------------------

[_]_=>_ : ∀ {A} → ∀[ Parser A ] → String → A → Set
[ parser ] str => expr
  = Value expr ≡ (Success.value ∘ proj₁ <$> run (start , []))
  where
  import Category.Monad
  open Category.Monad.RawMonad (Text.Parser.Monad.Result-monad _)
  run = runParser parser ≤-refl $ Vec.fromList $ String.toList str

[_]_=error>_ : ∀ {A} → ∀[ Parser A ] → String → Error → Set
[ parser ] str =error> err
  = HardFail err ≡ (Success.value ∘ proj₁ <$> run (start , []))
  where
  import Category.Monad
  open Category.Monad.RawMonad (Text.Parser.Monad.Result-monad _)
  run = runParser (commit parser) ≤-refl $ Vec.fromList $ String.toList str

----

module KWs-Idents where
  t1 : [ P.ident  ]   "foo"    => "foo"
  t2 : [ P.kw "fun" ] "fun"    => tt
  t3 : [ P.kw "fun" ] "fune"   =error> expected _ "keyword `fun'"
  t4 : [ P.ident ]    "fun"    =error> expected _ "non-keyword identifier"
  t1 = refl
  t2 = refl
  t3 = refl
  t4 = refl

module Pats-Exprs where
  t1 : [ P.patn ] "x" => ident _ "x"
  t2 : [ P.patn ] "_" => wildcard _
  t3 : [ P.expr ] "x" => ident _ "x"
  t4 : [ P.expr ] "_" =error> _
  t5 : [ P.expr ] "f x y" => app (ident _ "f") (ident _ "x" ∷ ident _ "y" ∷ [])
  t6 : [ P.expr ] "(x)" => ident _ "x"
  t7 : [ P.expr ] "f (x ( y ))" => app (ident _ "f") (app (ident _ "x") (ident _ "y" ∷ []) ∷ [])
  t1 = refl
  t2 = refl
  t3 = refl
  t4 = refl
  t5 = refl
  t6 = refl
  t7 = refl
