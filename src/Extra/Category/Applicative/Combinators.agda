open import Category.Applicative.Indexed using (IFun)
open import Category.Applicative using (RawApplicative)

module Extra.Category.Applicative.Combinators
  {f} {F : Set f → Set f}
  (applicative : RawApplicative F) where

open import Data.List.Base     using (List; _∷_; [])
open import Data.List.NonEmpty using (List⁺; _∷_)
open RawApplicative applicative

open RawApplicative applicative public
  using () renaming (_⊛_ to _<*>_)

module _ {a} {A : Set a} {B : Set f} where

  traverse : (A → F B) → List A → F (List B)
  traverse f []       = pure []
  traverse f (x ∷ xs) = (| f x ∷ traverse f xs |)

  traverse⁺ : (A → F B) → List⁺ A → F (List⁺ B)
  traverse⁺ f (x ∷ xs) = (| f x ∷ traverse f xs |)
