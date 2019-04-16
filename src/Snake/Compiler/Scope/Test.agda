module Snake.Compiler.Scope.Test where

open import Function
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Data.Sum             as Sum using (_⊎_; inj₁; inj₂)
open import Data.Product        as Prod using (_×_; _,_)
open import Data.List.Base              using (_∷_; [])
open import Data.List.NonEmpty          using (_∷_)
open import Text.Parser.Position as Pos using (Position)

open import Snake.Data.AST.Base
open import Snake.Compiler.Scope
import Snake.Data.AST.HO Shape as HO
import Snake.Data.AST.Raw Position as Raw

--------------------------------------------------------------------------------

_=>_ : {T : Set → Set} →
          Error ⊎ WF T Cx.empty →
          (∀ {V} → T V) → Set₁
m => x = ∀ {V} → Sum.map₂ (λ e → e V Cx.⟦empty⟧) m ≡ inj₂ x

_=error>_ : {T : Set → Set} →
          Error ⊎ WF T Cx.empty →
          Error → Set₁
m =error> x = ∀ {V} → Sum.map₂ (λ e → e V Cx.⟦empty⟧) m ≡ inj₁ x

p = Pos.start
∅ = Cx.empty

----

module Exprs where
  wf = wfExpr ∅

  -- 5
  t1 : wf (Raw.litl p 5) => HO.litl (5 , _)
  -- x
  t2 : wf (Raw.ident p "x") =error> unbound-ident p "x"
  -- 1 2 3
  t3 : wf (Raw.app (Raw.litl p 1) (Raw.litl p 2 ∷ Raw.litl p 3 ∷ []))
       => HO.app _ (HO.litl (1 , _))
                   (HO.litl (2 , _) ∷ HO.litl (3 , _) ∷ [])
  t1 = refl
  t2 = refl
  t3 = refl

module Patns where
  wf = λ p e → wfPatn ∅ (λ G → wfExpr G e) p

  -- _ -> 5
  t1 : wf (Raw.wildcard p) (Raw.litl p 5) => HO.wild _ (HO.litl (5 , _))
  -- x -> x
  t2 : wf (Raw.ident p "x") (Raw.ident p "x") => HO.name ("x" , _) λ x → HO.var _ x
  -- y -> x
  t3 : wf (Raw.ident p "y") (Raw.ident p "x") =error> unbound-ident p "x"
  t1 = refl
  t2 = refl
  t3 = refl

module Funs where
  wf = λ d → wfProg ∅ (d ∷ [])

  -- id x = x
  t1 : wf (Raw.fun p "id" (Raw.ident p "x" ∷ []) (Raw.ident p "x"))
       => (HO.more $ HO.fun ("id" , _) λ id →
           (HO.arg _ $ HO.name ("x" , _) λ x →
            HO.body $ HO.var _ x)
         , HO.empty)
  -- loop = loop
  t2 : wf (Raw.fun p "loop" [] (Raw.ident p "loop"))
       => (HO.more $ HO.fun ("loop" , _) λ loop →
           (HO.body $ HO.var _ loop)
         , HO.empty)
  -- k x _ = x
  t3 : wf (Raw.fun p "k" (Raw.ident p "x" ∷ Raw.wildcard p ∷ []) (Raw.ident p "x"))
       => (HO.more $ HO.fun ("k" , _) λ k →
           (HO.arg _ $ HO.name ("x" , _) λ x →
            HO.arg _ $ HO.wild _ $
            HO.body $ HO.var _ x)
          , HO.empty)
  -- ap x f = f x
  t4 : wf (Raw.fun p "ap" (Raw.ident p "x" ∷ Raw.ident p "f" ∷ [])
                          (Raw.app (Raw.ident p "f") (Raw.ident p "x" ∷ [])))
       => (HO.more $ HO.fun ("ap" , _) λ ap →
           (HO.arg _ $ HO.name ("x" , _) λ x →
            HO.arg _ $ HO.name ("f" , _) λ f →
            HO.body $ HO.app _ (HO.var _ f) (HO.var _ x ∷ []))
          , HO.empty)
  t1 = refl
  t2 = refl
  t3 = refl
  t4 = refl

module Progs where
  wf = λ ds → wfProg ∅ ds

  -- n = 1; m = n
  t1 : wf (Raw.fun p "n" [] (Raw.litl p 1) ∷
           Raw.fun p "m" [] (Raw.ident p "n") ∷ [])
       => (HO.more $ HO.fun ("n" , _) λ n →
           (HO.body $ HO.litl (1 , _))
        , (HO.more $ HO.fun ("m" , _) λ m →
           (HO.body $ HO.var _ n)
        , HO.empty))
  t1 = refl
