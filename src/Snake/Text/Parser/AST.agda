module Snake.Text.Parser.AST where


open import Data.Bool.Base     as Bool using (Bool; not; T)
open import Data.Nat.Base       as Nat using (ℕ)
open import Data.List.Base     as List using (List; []; _∷_; _++_; null)
open import Data.List.NonEmpty   as NE using (List⁺)
open import Data.Maybe        as Maybe using (Maybe; just; nothing)
open import Data.Char          as Char using (Char)
open import Data.String      as String using (String) renaming (_++_ to _<>_)
open import Data.Unit

open import Text.Parser.Position using (Position)
open import Text.Parser.Combinators
open import Text.Parser.Combinators.Char as Ch

open import Function
open import Size using (∞)
open import Relation.Unary
open import Category.Monad

-- instances
open import Data.List.Sized.Interface                       using (vec)
open import Data.Subset                                     using (Subset-refl)
open import Relation.Binary.PropositionalEquality.Decidable using (decide-char)

--------------------------------------------------------------------------------

open import Snake.Data.AST.Raw Position as AST using (Litl; Patn; Expr; Decl)
open import Snake.Text.Parser.Base
-- open RawMonadPlus monadPlus

----------------------------------------
-- Character classes

wsChars delChars opChars nonIdChars : List Char
wsChars    = String.toList " \t\n"
delChars   = String.toList ";,|()[]{}"
opChars    = String.toList "+-*/@$<>="
nonIdChars = wsChars ++ delChars ++ opChars

----------------------------------------
-- Whitespace and comments

whitespace : ∀[ Parser _ ]
whitespace = tt <$ list⁺ (anyOf wsChars)

comment : ∀[ Parser ⊤ ]
comment = iterate (tt <$ char ';') $ box $ _ <$ anyCharBut '\n'

lexeme : String → ∀ {A} → ∀[ Parser A ⇒ Parser A ]
lexeme ann p = iterate (annot ann p) $ box $
               id <$ (whitespace <|> comment)

----------------------------------------
-- Identifiers and keywords

isKeyword : (s : String) → Maybe (T (not $ null $ String.toList s))
isKeyword "fun" = just _
isKeyword "_"   = just _
isKeyword _     = nothing

IsKeyword : String → Set
IsKeyword = T ∘ Maybe.is-just ∘ isKeyword

rawIdent : ∀[ Parser String ]
rawIdent = String.fromList ∘ NE.toList <$> list⁺ (noneOf nonIdChars)

kw : (s : String) {_ : IsKeyword s} → ∀[ Parser ⊤ ]
kw s {pr} = lexeme ("keyword `" <> s <> "'") $ tt <$
            guard (s String.==_) rawIdent
  where pr′ = Maybe.to-witness-T (isKeyword s) pr

ident : ∀[ Parser String ]
ident = lexeme "non-keyword identifier" $
        guard (Maybe.is-nothing ∘ isKeyword) rawIdent

----------------------------------------
-- AST

patn : ∀[ Parser (Patn ∞) ]
patn = withPos λ pos →
  AST.wildcard pos <$  kw "_"      <|>
  AST.ident pos    <$> ident

expr : ∀[ Parser (Expr ∞) ]
expr = annot "expression" $ withPos λ pos →
  AST.ident pos    <$> ident
