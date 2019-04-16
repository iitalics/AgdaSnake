module Snake.Compiler.Desugar.Base where

open import Snake.Data.AST.HO.Base
open import Text.Parser.Position using (Position)

record DesugarableShape (Shape : SHAPE) : Set where
  field
    wild⇒name-p : Shape wild-p → Shape name-p
    app1⇒app-e  : Shape app1-e → Shape app-e
