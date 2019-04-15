module Snake.Text.Parser.AST where


open import Data.Bool.Base     as Bool using (Bool; not; T; true; false)
open import Data.Nat.Base       as Nat using (ℕ)
open import Data.List.Base     as List using (List; []; _∷_; _++_; null)
open import Data.List.NonEmpty   as NE using (List⁺)
open import Data.Maybe        as Maybe using (Maybe; just; nothing)
open import Data.Char          as Char using (Char)
open import Data.String      as String using (String) renaming (_++_ to _<>_)
open import Data.Unit

open import Text.Parser.Position using (Position)
open import Text.Parser.Combinators
import Text.Parser.Combinators.Char as Ch

open import Function
open import Size                 using (∞)
open import Relation.Unary
open import Category.Monad
open import Induction.Nat.Strong using (□_; fix)

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

wsChars delChars opChars : List Char
wsChars    = String.toList " \t\n"
delChars   = String.toList ";,|()[]{}"
opChars    = String.toList "+-*/@$<>="
numChars   = String.toList "0123456789"

nonIdChars nonIdHeadChars : List Char
nonIdChars     = wsChars ++ delChars ++ opChars
nonIdHeadChars = numChars ++ nonIdChars

----------------------------------------
-- Whitespace and comments

whitespace : ∀[ Parser _ ]
whitespace = tt <$ list⁺ (anyOf wsChars)

comment : ∀[ Parser ⊤ ]
comment = iterate (tt <$ Ch.char ';') $ box $ _ <$ Ch.anyCharBut '\n'

lexeme : String → ∀ {A} → ∀[ Parser A ⇒ Parser A ]
lexeme ann p = iterate (annot ann p) $ box $
               id <$ (whitespace <|> comment)

char : Char → ∀[ Parser Char ]
char c = lexeme (String.fromList ('`' ∷ c ∷ '\'' ∷ [])) (Ch.char c)

----------------------------------------
-- Identifiers and keywords

isKeyword : (s : String) → Bool
isKeyword "fun" = true
isKeyword "_"   = true
isKeyword _     = false

IsKeyword : String → Set
IsKeyword = T ∘ isKeyword

rawIdent : ∀[ Parser String ]
rawIdent = String.fromList ∘ NE.toList <$>
           head+tail (noneOf nonIdHeadChars)
                     (box (noneOf nonIdChars))

kw : (s : String) {_ : IsKeyword s} → ∀[ Parser ⊤ ]
kw s = lexeme ("keyword `" <> s <> "'") $
       tt <$ guard (s String.==_) rawIdent

ident : ∀[ Parser String ]
ident = lexeme "non-keyword identifier" $
        guard (not ∘ isKeyword) rawIdent

----------------------------------------
-- Numbers

private
  index : ∀ {A : Set} → (A → Bool) → List A → ℕ → Maybe ℕ
  index f []       i = nothing
  index f (x ∷ xs) i with f x
  ... | true  = just i
  ... | false = index f xs (Nat.suc i)

  toDig : Char → Maybe ℕ
  toDig c = index (c Char.==_) (String.toList "0123456789") 0

  digit : ∀[ Parser ℕ ]
  digit = guardM toDig anyTok

nat : ∀[ Parser ℕ ]
nat = iterate digit (box $ (λ d n → n * 10 + d) <$> digit)
  where open Nat

----------------------------------------
-- AST

litl : ∀[ Parser Litl ]
litl = lexeme "number" nat

patn : ∀[ Parser (Patn ∞) ]
patn = withPos λ pos →
  AST.wildcard pos <$  kw "_"      <|>
  AST.ident pos    <$> ident       <|>
  AST.litl pos     <$> litl

expr : ∀[ Parser (Expr ∞) ]
expr = fix _ λ expr →
  let
    term =
      between (char '(') (box (char ')')) expr <|>
      (withPos λ pos →
        AST.ident pos <$> ident  <|>
        AST.litl pos  <$> litl)

    app =
      (λ es f → AST.app f es) <$> list⁺ term
  in
    iterate term (box app)

decl : ∀[ Parser (Decl ∞) ]
decl = withPos λ pos → ident >>= λ name → box $
  let
    body = char '=' &> box expr
    pats = NE.toList <$> list⁺ patn
  in
    (AST.fun pos name []       <$> body)       <|>
    (AST.fun pos name <$> pats <*> box body)
