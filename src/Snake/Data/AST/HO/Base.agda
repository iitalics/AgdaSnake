module Snake.Data.AST.HO.Base where

data Label : Set where
  wild-p litl-p name-p : Label
  litl-e var-e app-e app1-e : Label
  fun arg : Label

SHAPE = Label → Set
