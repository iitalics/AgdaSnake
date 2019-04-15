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
  t1 : [ P.ident  ]   "foo_bar123"    => "foo_bar123"
  t2 : [ P.kw "fun" ] "fun"    => tt
  t3 : [ P.kw "fun" ] "fune"   =error> expected _ "keyword `fun'"
  t4 : [ P.ident ]    "fun"    =error> expected _ "non-keyword identifier"
  t5 : [ P.ident ]    "1foo"   =error> _
  t1 = refl
  t2 = refl
  t3 = refl
  t4 = refl
  t5 = refl

module Numbers where
  t1 : [ P.nat ] "013" => 13
  t2 : [ P.nat ] "10"  => 10
  -- t3 : [ P.nat ] "1a"  =error> _ -- TODO
  t1 = refl
  t2 = refl
  -- t3 = refl

module Pats where
  t1 : [ P.patn ] "x" => ident _ "x"
  t2 : [ P.patn ] "_" => wildcard _
  t3 : [ P.patn ] "45" => litl _ 45
  t1 = refl
  t2 = refl
  t3 = refl

module Exprs where
  t1 : [ P.expr ] "_" =error> _
  t2 : [ P.expr ] "x" => ident _ "x"
  t3 : [ P.expr ] "4" => litl _ 4
  t4 : [ P.expr ] "f 2 x" => app (ident _ "f") (litl _ 2 ∷ ident _ "x" ∷ [])
  t5 : [ P.expr ] "(x)"  => ident _ "x"
  t6 : [ P.expr ] "f (x ( 3 ))" => app (ident _ "f") (app (ident _ "x") (litl _ 3 ∷ []) ∷ [])
  t1 = refl
  t2 = refl
  t3 = refl
  t4 = refl
  t5 = refl
  t6 = refl

module Decls where
  t1 : [ P.decl ] "x = y" => fun _ "x" [] (ident _ "y")
  t2 : [ P.decl ] "id x = x" => fun _ "id" (ident _ "x" ∷ []) (ident _ "x")
  t3 : [ P.decl ] "k x _ = x" => fun _ "k" (ident _ "x" ∷ wildcard _ ∷ []) (ident _ "x")
  t1 = refl
  t2 = refl
  t3 = refl
