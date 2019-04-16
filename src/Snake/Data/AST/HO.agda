module Snake.Data.AST.HO where

open import Size using (Size; Size<_)
open import Data.String.Base using (String)
open import Data.Product using (_×_)

open import Snake.Data.AST.Base

--------------------------------------------------------------------------------

data Patn (V : Set) (R : Set) : Set where
  wild : R → Patn V R
  name : (name : String) → (V → R) → Patn V R
  litl : (l : Litl) → R → Patn V R

data Expr (V : Set) : Set where
  var : V → Expr V
  app1 : (f : Expr V) (e : Expr V) → Expr V
  litl : (l : Litl) → Expr V

data Fun (V : Set) : Set where
  body : (e : Expr V) → Fun V
  arg : (p : Patn V (Fun V)) → Fun V

data Decl (V : Set) (R : Set) : Set where
  fun : (name : String) → (V → Fun V × R) → Decl V R

data Prog (V : Set) : Set where
  empty : Prog V
  more  : Decl V (Prog V) → Prog V

ClosedOverProgram : Set₁
ClosedOverProgram = ∀ V → Prog V
