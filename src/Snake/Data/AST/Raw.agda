module Snake.Data.AST.Raw (T : Set) where

open import Size               using (Size; Size<_; ∞)

open import Data.String.Base   using (String)
open import Data.Nat.Base      using (ℕ)
open import Data.List.Base     using (List)

--------------------------------------------------------------------------------

data Litl : Set where
  num : ℕ → Litl

data Patn (i : Size) : Set where
  wildcard : (t : T) → Patn i
  ident    : (t : T) (name : String) → Patn i
  tuple    : (t : T) {j : Size< i} (ps : List (Patn j)) → Patn i

data Expr (i : Size) : Set where
  ident : (t : T) (name : String) → Expr i
  app   : (t : T) (f : Expr i) {j : Size< i} (es : List (Expr j)) → Expr i
  tuple : (t : T) {j : Size< i} (es : List (Expr j)) → Expr i

data Decl (i : Size) : Set where
  fun : (t : T) (name : String)
        (params : List (Patn i))
        (body : Expr i) → Decl i
