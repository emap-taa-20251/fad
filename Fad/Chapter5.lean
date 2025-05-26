import Fad.Chapter1
import Fad.«Chapter1-Ex»

namespace Chapter5

namespace Quicksort

variable {a : Type} [h₁ : LT a] [h₂ : DecidableRel (α := a) (· < ·)]

inductive Tree a where
| null : Tree a
| node : (Tree a) → a → (Tree a) → Tree a

def mkTree: List a → Tree a
| [] => Tree.null
| x :: xs =>
  let p := xs.partition (. < x)
  Tree.node (mkTree p.1) x (mkTree p.2)
 termination_by l => l.length
 decreasing_by
  all_goals simp
   [List.partition_eq_filter_filter,
    List.length_filter_le, Nat.lt_add_one_of_le]

def Tree.flatten : Tree a → List a
| null => []
| node l x r => l.flatten ++ [x] ++ r.flatten

def qsort₀ : List a → List a :=
 Tree.flatten ∘ mkTree

def qsort₁ : List a → List a
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
#eval qsort₁ (List.iota 145)
#eval qsort₂ (fun a b => Ordering.swap <| compare a b) ['c','a','b']
#eval qsort₂ compare ['c','a','b']
-/


end Quicksort


namespace Mergesort

variable {a : Type} [Inhabited a]
 [LE a] [DecidableRel (α := a) (· ≤ ·)]

inductive Tree (a : Type) : Type where
 | null : Tree a
 | leaf : a → Tree a
 | node : Tree a → Tree a → Tree a
 deriving Repr, Inhabited


def merge : List a → List a → List a
 | []       , ys        => ys
 | xs       , []        => xs
 | (x :: xs), (y :: ys) =>
   if x ≤ y then
    x :: merge xs (y :: ys)
   else
    y :: merge (x :: xs) ys


def Tree.flatten : Tree a → List a
 | Tree.null     => []
 | Tree.leaf x   => [x]
 | Tree.node l r => merge l.flatten r.flatten


def halve₀ (xs : List a) : (List a × List a) :=
 let m := xs.length / 2
 (xs.take m,xs.drop m)


def halve : List a → (List a × List a) :=
 let op x p := (p.2, x :: p.1)
 List.foldr op ([],[])

-- #eval halve [10,2,3,4,5,6,8,7,9,1]

def twoStepInduction {P : List a → Prop}
  (empty : P [])
  (single : ∀ as, as.length = 1 → P as)
  (more : ∀ a b as, P as → P (a :: b :: as)) : ∀ as, P as
  | []           => empty
  | [a]          => single [a] (by simp)
  | a :: b :: cs =>
    more _ _ _ (twoStepInduction empty single more _)


theorem length_halve_fst
 : (halve xs).fst.length = xs.length / 2 := by
 induction xs using twoStepInduction with
 | empty          => simp [halve]
 | single a h     =>
   have b :: [] := a
   simp [halve]
 | more a b cs ih =>
   repeat rw [halve, List.foldr, ←halve]
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


def mkTree₀ : (as : List a) → Tree a
 | []      => Tree.null
 | x :: xs =>
   if h : xs.length = 0 then
    Tree.leaf x
   else
    let p := halve (x :: xs)
    have : (halve (x :: xs)).fst.length < xs.length + 1 :=
     by simp [length_halve_fst]; omega
    have : (halve (x :: xs)).snd.length < xs.length + 1 :=
     by simp [length_halve_snd]; omega
    Tree.node (mkTree₀ p.1) (mkTree₀ p.2)
 termination_by xs => xs.length


def msort₀ (xs : List a) : List a :=
  (Tree.flatten ∘ mkTree₀) xs


def mkPair (n : Nat) (xs : List a) : (Tree a × List a) :=
 if n = 0 then
  (Tree.null, xs)
 else
  if n = 1 then
   (Tree.leaf xs.head!, xs.tail)
  else
   let m := n / 2
   let (t₁, ys) := mkPair m xs
   let (t₂, zs) := mkPair (n - m) ys
   (Tree.node t₁ t₂, zs)
 termination_by (n, xs)

def mkTree₁ (as : List a) : Tree a :=
  mkPair as.length as |>.fst

def msort₁ (xs : List a) : List a :=
  (Tree.flatten ∘ mkTree₁) xs

def msort₂ : List a → List a
 | []      => []
 | x :: xs =>
   if h: xs.length = 0 then [x]
   else
    let p := halve (x :: xs)
    have : (halve (x :: xs)).fst.length < xs.length + 1 := by
      simp [length_halve_fst]; omega
    have : (halve (x :: xs)).snd.length < xs.length + 1 := by
      simp [length_halve_snd]; omega
    merge (msort₂ p.1) (msort₂ p.2)
 termination_by xs => xs.length


def pairWith (f : a → a → a) : (List a) → List a
 | []             => []
 | [x]            => [x]
 | (x :: y :: xs) => f x y :: pairWith f xs


open Chapter1 (wrap unwrap single until') in

def mkTree₂ : List a → Tree a
 | []      => .null
 | a :: as =>
    unwrap (until' single (pairWith .node) ((a::as).map .leaf))
    |>.getD .null

def msort₃ (xs : List a) : List a :=
  (Tree.flatten ∘ mkTree₂) xs


open Chapter1 (wrap unwrap single until') in

def msort₄ : List a → List a
 | []    => []
 | x::xs =>
   unwrap (until' single (pairWith merge) ((x::xs).map wrap))
   |>.getD []

/-
#eval msort₁ [5,3,4,2,1,1]
-/

end Mergesort


namespace Heapsort

inductive Tree (α : Type) : Type
 | null : Tree α
 | node : α → Tree α → Tree α → Tree α
 deriving Inhabited


def flatten [LE a] [DecidableRel (α := a) (· ≤ ·)] : Tree a → List a
| Tree.null       => []
| Tree.node x u v => x :: Mergesort.merge (flatten u) (flatten v)


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
