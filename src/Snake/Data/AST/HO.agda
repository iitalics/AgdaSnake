open import Snake.Data.AST.HO.Base

module Snake.Data.AST.HO
  (S : SHAPE)
  where

open import Size using (Size; Size<_)
open import Data.String.Base using (String)
open import Data.Product using (_×_)

--------------------------------------------------------------------------------

data Patn (V : Set) (R : Set) : Set where
  wild : S wild-p → R → Patn V R
  name : S name-p → (V → R) → Patn V R
  litl : S litl-p → R → Patn V R

data Expr (V : Set) : Set where
  var  : S var-e  → V → Expr V
  app1 : S app1-e → (f : Expr V) (e : Expr V) → Expr V
  litl : S litl-e → Expr V

data Fun (V : Set) : Set where
  body : (e : Expr V) → Fun V
  arg  : S arg → (p : Patn V (Fun V)) → Fun V

data Decl (V : Set) (R : Set) : Set where
  fun : S fun → (V → Fun V × R) → Decl V R

data Prog (V : Set) : Set where
  empty : Prog V
  more  : Decl V (Prog V) → Prog V

ClosedOverProgram : Set₁
ClosedOverProgram = ∀ V → Prog V
