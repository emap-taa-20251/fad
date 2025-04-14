import Fad.Chapter1
import Fad.«Chapter1-Ex»

namespace Chapter5

namespace Quicksort

inductive Tree a where
| null : Tree a
| node : (Tree a) → a → (Tree a) → Tree a

def mkTree [LT a] [DecidableRel (α := a) (· < ·)] : List a → Tree a
| [] => Tree.null
| x :: xs =>
  let p := xs.partition (. < x)
  Tree.node (mkTree p.1) x (mkTree p.2)
 termination_by l => l.length
 decreasing_by
  all_goals simp
   [List.partition_eq_filter_filter,
    List.length_filter_le,
    Nat.lt_add_one_of_le]

def Tree.flatten : Tree a → List a
| null => []
| node l x r => l.flatten ++ [x] ++ r.flatten

def qsort₀ [LT a] [DecidableRel (α := a) (· < ·)] : List a → List a :=
 Tree.flatten ∘ mkTree

def qsort₁ [h₁ : LT a] [h₂ : DecidableRel (α := a) (· < ·)] : List a → List a
 | []        => []
 | (x :: xs) =>
  let p := xs.partition (· < x)
  (qsort₁ p.1) ++ [x] ++ (qsort₁ p.2)
 termination_by xs => xs.length
 decreasing_by
  all_goals simp
   [List.partition_eq_filter_filter,
    List.length_filter_le, Nat.lt_add_one_of_le]

def qsort₂ [Ord a] (f : a → a → Ordering) : List a → List a
  | []        => []
  | (x :: xs) =>
    let p := xs.partition (λ z => f z x = Ordering.lt)
    (qsort₂ f p.1) ++ [x] ++ (qsort₂ f p.2)
 termination_by xs => xs.length
 decreasing_by
  all_goals simp
   [List.partition_eq_filter_filter,
    List.length_filter_le, Nat.lt_add_one_of_le]

/-
#eval qsort₀ (List.iota 145)
#eval qsort₁ (List.iota 145)
#eval qsort₂ compare ['c','b','a']
-/

structure Person where
  name : String
  age : Nat
 deriving Repr

instance : Ord Person where
  compare p q := compare p.age q.age

/- alternative syntax
instance : LT Person where
  lt a b := a.age < b.age
-/

instance : LT Person :=
 { lt := fun a b => a.age < b.age }

instance (a b : Person) : Decidable (a < b) :=
  inferInstanceAs (Decidable (a.age < b.age))

def people := [
  Person.mk "Alice" 23,
  Person.mk "Bob" 25,
  Person.mk "Eve" 22]

/-
#eval qsort₂ compare people
#eval qsort₁ people
-/

end Quicksort


namespace S52 -- Mergesort

inductive Tree (α : Type) : Type where
 | null : Tree α
 | leaf : α → Tree α
 | node : Tree α → Tree α → Tree α
 deriving Repr, Inhabited

def merge [LE a] [DecidableRel (α := a) (· ≤ ·)] : List a → List a → List a
 | []       , ys        => ys
 | xs       , []        => xs
 | (x :: xs), (y :: ys) =>
   if x ≤ y then
    x :: merge xs (y :: ys)
   else
    y :: merge (x :: xs) ys


def flatten [LE a] [DecidableRel (α := a) (· ≤ ·)] : Tree a → List a
 | Tree.null     => []
 | Tree.leaf x   => [x]
 | Tree.node l r => merge (flatten l) (flatten r)


def halve₀ (xs : List a) : (List a × List a) :=
 let m := xs.length / 2
 (xs.take m,xs.drop m)

def halve : (xs : List a) → (List a × List a) :=
 let op x p := (p.2, x :: p.1)
 List.foldr op ([],[])

/-
#eval halve₁ [1,2,3,4,5,6,7,8,9,10]
#eval halve₁ ([] : List Nat)
-/

-- https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Nat/Defs.html#Nat.twoStepInduction

def twoStepInduction {P : List a → Prop}
  (empty : P [])
  (single : ∀ as, as.length = 1 → P as)
  (more : ∀ a b as, P as → P (a :: b :: as)) : ∀ as, P as
  | []           => empty
  | [a]          => single [a] (by simp)
  | a :: b :: cs => more _ _ _ (twoStepInduction empty single more _)


theorem length_halve_fst : (halve xs).fst.length = xs.length / 2 := by
 induction xs using twoStepInduction with
 | empty          => simp [halve]
 | single a h     =>
   have _ :: [] := a
   simp [halve]
 | more a b cs ih =>
   rw [halve, List.foldr, List.foldr, ←halve]
   simp
   omega


theorem length_halve_snd : (halve xs).snd.length = (xs.length + 1) / 2 := by
 induction xs using twoStepInduction with
 | empty          => simp [halve]
 | single a h     =>
   have _ :: [] := a
   simp [halve]
 | more a b cs ih =>
   rw [halve, List.foldr, List.foldr, ←halve]
   simp
   omega


def mkTree : (as : List a) → Tree a
 | []      => Tree.null
 | x :: xs =>
   if h : xs.length = 0 then Tree.leaf x
   else
    let p := halve (x :: xs)
    have : (halve (x :: xs)).fst.length < xs.length + 1 :=
     by simp [length_halve_fst]; omega
    have : (halve (x :: xs)).snd.length < xs.length + 1 :=
     by simp [length_halve_snd]; omega
    Tree.node (mkTree p.1) (mkTree p.2)
 termination_by xs => xs.length


partial def mkPair [Inhabited a] : (n : Nat) → (xs : List a) → (Tree a × List a)
 | 0, xs => (Tree.null, xs)
 | 1, xs => (Tree.leaf xs.head!, xs.tail)
 | n, xs =>
   let m := n / 2
   let (t₁, ys) := mkPair m xs
   let (t₂, zs) := mkPair (n - m) ys
   (Tree.node t₁ t₂, zs)

def mkTree₀ [Inhabited a] (as : List a) : Tree a :=
  mkPair as.length as |>.fst


def msort₀ [LE a] [DecidableRel (α := a) (· ≤ ·)] (xs : List a) : List a :=
  (flatten ∘ mkTree) xs


def msort₁ [LE a] [DecidableRel (α := a) (· ≤ ·)] : List a → List a
 | []      => []
 | x :: xs =>
   if h: xs.length = 0 then [x]
   else
    let p := halve (x :: xs)
    have : (halve (x :: xs)).fst.length < xs.length + 1 := by
      simp [length_halve_fst]; omega
    have : (halve (x :: xs)).snd.length < xs.length + 1 := by
      simp [length_halve_snd]; omega
    merge (msort₁ p.1) (msort₁ p.2)
 termination_by xs => xs.length


def pairWith (f : α → α → α) : (List α) → List α
 | []             => []
 | [x]            => [x]
 | (x :: y :: xs) => f x y :: pairWith f xs


open Chapter1 (wrap unwrap single until') in

def mkTree₁ : List a → Tree a
 | []      => .null
 | a :: as =>
    unwrap (until' single (pairWith .node) (List.map .leaf (a::as))) |>.getD .null

def msort₂ [LE a] [DecidableRel (α := a) (· ≤ ·)] (xs : List a) : List a :=
  (flatten ∘ mkTree₁) xs

open Chapter1 (wrap unwrap single until') in

def msort₃ [LE a] [DecidableRel (α := a) (· ≤ ·)] : List a → List a
 | []    => []
 | x::xs =>
   unwrap (until' single (pairWith merge) (List.map wrap (x::xs))) |>.getD []


/-
#eval msort₁ [5,3,4,2,1,1]
#eval msort₁ [1,2,3,4,5]
#eval msort₁ ['a','b','a']
-/

end S52

namespace Heapsort

inductive Tree (α : Type) : Type
 | null : Tree α
 | node : α → Tree α → Tree α → Tree α
 deriving Inhabited


def flatten [LE a] [DecidableRel (α := a) (· ≤ ·)] : Tree a → List a
| Tree.null       => []
| Tree.node x u v => x :: S52.merge (flatten u) (flatten v)


open Std.Format in

def Tree.toFormat [ToString α] : (t: Tree α) → Std.Format
| .null => Std.Format.text "."
| .node x t₁ t₂ =>
  bracket "(" (f!"{x}" ++
   line ++ nest 2 t₁.toFormat ++ line ++ nest 2 t₂.toFormat) ")"

instance [ToString a] : Repr (Tree a) where
 reprPrec e _ := Tree.toFormat e


end Heapsort


end Chapter5
