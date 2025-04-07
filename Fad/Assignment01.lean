
namespace Assignment01

/- ## Question 1: Terms

Complete the following definitions, by replacing the `sorry` markers by terms
of the expected type.

Hint: A procedure for doing so systematically is described in Section 1.4 of
the Hitchhiker's Guide. As explained there, you can use `_` as a placeholder
while constructing a term. By hovering over `_`, you will see the current
logical context. -/

def I : α → α :=
  fun a ↦ a

def K : α → β → α :=
  fun a b ↦ a

def C : (α → β → γ) → β → α → γ :=
  sorry

def projFst : α → α → α :=
  sorry

/- Give a different answer than for `projFst`. -/

def projSnd : α → α → α :=
  sorry

def someNonsense : (α → β → γ) → α → (α → γ) → β → γ :=
  sorry


/- ## Question 2

   Define a structure named RectangularPrism that contains the height, width,
   and depth of a rectangular prism, each as a Float.

structure RectangularPrism where
 sorry
-/


/- ## Question 3

   Define a function named volume : RectangularPrism → Float that computes the
   volume of a rectangular prism. -/

def volume (r : RectangularPrism) : Float := sorry


/- ## Question 4

   Define a structure named Segment that represents a line segment by its endpoints,
   and define a function length : Segment → Float that computes the length of a line
   segment. Segment should have at most two fields. -/

structure Point where
  x : Float
  y : Float
deriving Repr

/-
structure Segment where
 sorry
-/

/- ## Question 5

   Which names are introduced by the declaration of RectangularPrism? -/

def Names1 : List String := [""]

/- ## Question 6

   Which names are introduced by the following declarations of Hamster and Book?
   What are their types? -/

structure Hamster where
  name : String
  fluffy : Bool

structure Book where
  makeBook ::
  title : String
  author : String
  price : Float

def Names2 : List String := [""]

/- ## Question 7

   Define a function product that produces the product of a list of
   numbers, and show using your definition that product [2,3,4].  -/

def product (ns : List Nat) : Nat := sorry



end Assignment01
