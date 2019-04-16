open import Snake.Data.AST.HO.Base

module Snake.Data.AST.HO
  (S : SHAPE)
  where

open import Size using (Size; Size<_; ∞)
open import Data.String.Base using (String)
open import Data.Product using (_×_)
open import Data.List.NonEmpty using (List⁺)

--------------------------------------------------------------------------------

data Patn (V : Set) (R : Set) : Set where
  wild : S wild-p → R → Patn V R
  name : S name-p → (V → R) → Patn V R
  litl : S litl-p → R → Patn V R

data Expr (V : Set) : Set where
  var  : S var-e  → V → Expr V
  litl : S litl-e → Expr V
  app1 : S app1-e → (f : Expr V) (e : Expr V) → Expr V
  app  : S app-e  → (f : Expr V) (es : List⁺ (Expr V)) → Expr V

data Fun (V : Set) (i : Size) : Set where
  body : (e : Expr V) → Fun V i
  arg  : S arg → {j : Size< i} (p : Patn V (Fun V j)) → Fun V i

data Decl (V : Set) (R : Set) : Set where
  fun : S fun → (V → Fun V ∞ × R) → Decl V R

data Prog (V : Set) (i : Size) : Set where
  empty : Prog V i
  more  : {j : Size< i} → Decl V (Prog V j) → Prog V i

ClosedOverProgram : Set₁
ClosedOverProgram = ∀ V → Prog V ∞
