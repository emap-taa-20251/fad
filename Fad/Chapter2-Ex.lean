import Fad.Chapter2
import Fad.Chapter1

namespace Chapter2
open Chapter1


-- 2.9

def op1 {a : Type} : (List a) → a → a
| [], y => y
| (x::_), _ => x

example {xss : List (List α)} {e : α} (h : (concat1 xss) ≠ []) :
  List.head (concat1 xss) h = foldr op1 e xss:= by
    induction xss with
    | nil => contradiction
    | cons xs xss ih =>
      cases xs with
      | nil => simp [concat1, List.head, foldr, op1]; exact ih h
      | cons x xs => simp [concat1, List.head, foldr, op1]


-- 2.12

def inits (as : List a) : List (List a) :=
  let rec help (f : List a → List a) : List a → List (List a)
  | []      => (f []) :: []
  | x :: xs =>
    (f []) :: help (f ∘ List.cons x) xs
  help id as


-- 2.14

def tails1 (xs : List α) : List (List α) :=
  List.takeWhile (¬ ·.isEmpty) (iterate xs.length List.tail xs)


end Chapter2
