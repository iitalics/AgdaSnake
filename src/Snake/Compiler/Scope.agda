module Snake.Compiler.Scope where

open import Function
open import Relation.Nullary  using (yes; no)
open import Relation.Unary   hiding (_∈_; Decidable)
open import Relation.Binary   using (Decidable)
open import Category.Monad

open import Data.Product               using (_×_; _,_)
open import Data.Sum.Base       as Sum using (_⊎_)
open import Data.String.Base           using (String)
open import Data.List.Base     as List using (List; []; _∷_)
open import Data.List.NonEmpty   as NE using (List⁺; _∷_)
open import Text.Parser.Position       using (Position)

open import Snake.Data.AST.Base
import Snake.Data.AST.HO as HO
import Snake.Data.AST.Raw Position as Raw

------------------------------------------------------------------------

-- Errors

data Error : Set where
  unbound-ident : Position → String → Error

-- Fallible monad

module M {a} where
  M : Set a → Set a
  M = Error ⊎_

  fail : ∀ {A} → Error → M A
  fail = Sum.inj₁

  open import Data.Sum.Categorical.Left Error a
    public using (monad; applicative)

  open RawMonad monad public
  open import Extra.Category.Applicative.Combinators applicative public

-- Contexts
--   "G" = context specification
--   "g" = environment that matches a specification

module Cx where
  open import Data.List.Base using (List; []; _∷_)
  open import Data.List.Relation.Unary.All as All using (All)
  open import Data.List.Relation.Unary.Any using (any)
  open import Data.List.Membership.Propositional using () renaming (_∈_ to _∈ₗ_)
  open import Data.String using (_≟_)

  Context = List String

  empty : Context
  empty = []

  insert : String → Context → Context
  insert x G = x ∷ G

  ⟦_⟧ : Context → Set → Set
  ⟦ G ⟧ V = All (const V) G

  _∈_ : String → Context → Set
  _∈_ = _∈ₗ_

  _∈?_ : Decidable _∈_
  x ∈? G = any (x ≟_) G

  ⟦empty⟧ : ∀ {V} → ⟦ empty ⟧ V
  ⟦empty⟧ = All.[]

  extend : ∀ {V G} → ⟦ G ⟧ V → (x : String) (v : V) → ⟦ insert x G ⟧ V
  extend g x v = v All.∷ g

  get : ∀ {G x} → x ∈ G → ∀ {V} → ⟦ G ⟧ V → V
  get mem g = All.lookup g mem

-- Expressions that are Well Formed under a context

module WF where
  open Cx using (Context; ⟦_⟧; _∈_)
  open import Data.List.Relation.Unary.All using (lookup)

  WF : (Set → Set) → Context → Set₁
  WF T G = ∀ V (g : ⟦ G ⟧ V) → T V

  Expr = WF HO.Expr
  Patn = λ (T : Set → Set) → WF λ V → HO.Patn V (T V)
  Fun  = WF HO.Fun
  Prog = WF HO.Prog

  app : ∀ {G} → Expr G → List (Expr G) → Expr G
  app = List.foldl (λ e₁ e₂ V g → HO.app1 (e₁ V g) (e₂ V g))

  body : ∀ {G} → Expr G → Fun G
  body e V g = HO.body (e V g)

----------------------------------------

open M public using (M)
open WF public using (WF)
open Cx public using (Context)
open M using (return; _>>=_)

wfPatn : ∀ G (R : Set → Set) → Π[ M ∘ WF R ] →
         ∀ {i} → Raw.Patn i → M (WF.Patn R G)
wfPatn G R wfR (Raw.wildcard _)
  = do body ← wfR G
       return λ V g → HO.wild (body V g)
wfPatn G R wfR (Raw.litl _ l)
  = do body ← wfR G
       return λ V g → HO.litl l (body V g)
wfPatn G R wfR (Raw.ident _ name)
  = do body ← wfR (Cx.insert name G)
       return λ V g → HO.name name λ v →
                      body V (Cx.extend g name v)

wfExpr : ∀ G {i} → Raw.Expr i → M (WF.Expr G)
wfExpr G (Raw.litl _ l)
  = return λ _ _ → HO.litl l
wfExpr G (Raw.app f es)
  = do f′  ← wfExpr G f
       es′ ← M.traverse⁺ (wfExpr G) es
       return (WF.app f′ (NE.toList es′))
wfExpr G (Raw.ident pos x)
  with x Cx.∈? G
...  | yes mem = return λ V g → HO.var (Cx.get mem g)
...  | no _    = M.fail (unbound-ident pos x)

wfFun : ∀ G {i} → List (Raw.Patn i) → Raw.Expr i → M (WF.Fun G)
wfFun G [] e
  = do e′ ← wfExpr G e
       return λ V g → HO.body (e′ V g)
wfFun G (p ∷ ps) e
  = do p′ ← wfPatn G _ (λ G → wfFun G ps e) p
       return λ V g → HO.arg (p′ V g)

wfProg : ∀ G {i} → Raw.Prog i → M (WF.Prog G)
wfProg G [] = return λ V g → HO.empty
wfProg G (Raw.fun _ name params body ∷ ds)
  = do let G+f = Cx.insert name G
       f′ ← wfFun G+f params body
       p′ ← wfProg G+f ds
       return λ V g → HO.more $ HO.fun name λ v →
                      let g+f = Cx.extend g name v in
                      f′ V g+f , p′ V g+f

rawToHO : ∀ {i} → Raw.Prog i → Error ⊎ HO.ClosedOverProgram
rawToHO p = do p′ ← wfProg Cx.empty p
               return λ V → p′ V Cx.⟦empty⟧
