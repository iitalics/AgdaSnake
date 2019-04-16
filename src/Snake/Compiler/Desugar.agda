open import Snake.Compiler.Desugar.Base

module Snake.Compiler.Desugar
  {PrevShape : _}
  (desugarable : DesugarableShape PrevShape)
  where

open import Function
open import Relation.Unary

open import Data.Unit                  using (⊤)
open import Data.Empty                 using (⊥)
open import Data.Product       as Prod using (_×_; _,_)
open import Data.String.Base           using (String)
open import Data.List.Base             using (List; []; _∷_)
open import Data.List.NonEmpty         using (_∷_)
open import Text.Parser.Position       using (Position)

open import Snake.Data.AST.HO.Base
open import Snake.Data.AST.Base
open DesugarableShape desugarable

--------------------------------------------------------------------------------

AppShape = PrevShape app-e

Shape : SHAPE
Shape wild-p = ⊥
Shape app-e  = ⊥
Shape app1-e = AppShape
Shape l      = PrevShape l

import Snake.Data.AST.HO PrevShape as I
import Snake.Data.AST.HO Shape as O

dePatn : ∀ {V R₁ R₂} → (R₁ → R₂) → I.Patn V R₁ → O.Patn V R₂
dePatn f (I.wild s x) = O.name (wild⇒name-p s) λ _ → f x
dePatn f (I.name s g) = O.name s (f ∘ g)
dePatn f (I.litl s x) = O.litl s (f x)

mutual
  deExpr : ∀ {V} → I.Expr V → O.Expr V
  deExpr (I.var s v)    = O.var s v
  deExpr (I.litl s)     = O.litl s
  deExpr (I.app1 s f e) = O.app1 (app1⇒app-e s) (deExpr f) (deExpr e)
  deExpr (I.app s f (e ∷ es)) = deApp s es (O.app1 s (deExpr f) (deExpr e))

  deApp : ∀ {V} → AppShape → List (I.Expr V) → O.Expr V → O.Expr V
  deApp s []       f = f
  deApp s (e ∷ es) f = deApp s es (O.app1 s f (deExpr e))

deFun : ∀ {V} → ∀[ I.Fun V ⇒ O.Fun V ]
deFun (I.body e)  = O.body (deExpr e)
deFun (I.arg s p) = O.arg s (dePatn deFun p)

deProg : ∀ {V} → ∀[ I.Prog V ⇒ O.Prog V ]
deProg I.empty = O.empty
deProg (I.more (I.fun s body))
  = O.more $ O.fun s λ v →
    Prod.map deFun deProg (body v)

desugar : I.ClosedOverProgram → O.ClosedOverProgram
desugar prog V = deProg (prog V)
