import Fad.Chapter1
import Fad.«Chapter1-Ex»
import Mathlib.Order.BoundedOrder.Basic
import Mathlib.Order.Interval.Finset.Defs

namespace Chapter5

-- ## Section 5.1 Quicksort

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

-- ## Section 5.2 MergeSort

namespace Mergesort

open Chapter1 (wrap unwrap single until')

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


theorem length_halve_snd
 : (halve xs).snd.length = (xs.length + 1) / 2 := by
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
    have : (halve <| x :: xs).1.length < xs.length + 1 :=
     by simp [length_halve_fst]; omega
    have : (halve <| x :: xs).2.length < xs.length + 1 :=
     by simp [length_halve_snd]; omega
    Tree.node (mkTree₀ p.1) (mkTree₀ p.2)
 termination_by xs => xs.length


def msort₀ (xs : List a) : List a :=
  (Tree.flatten ∘ mkTree₀) xs


def msort₁ : List a → List a
 | []      => []
 | x :: xs =>
   if h: xs.length = 0 then [x]
   else
    let p := halve (x :: xs)
    have : (halve $ x :: xs).1.length < xs.length + 1 := by
      simp [length_halve_fst]; omega
    have : (halve $ x :: xs).2.length < xs.length + 1 := by
      simp [length_halve_snd]; omega
    merge (msort₁ p.1) (msort₁ p.2)
 termination_by xs => xs.length


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
  mkPair as.length as |>.1

def msort₂ (xs : List a) : List a :=
  (Tree.flatten ∘ mkTree₁) xs

def pairWith (f : a → a → a) : List a → List a
 | []             => []
 | [x]            => [x]
 | (x :: y :: xs) => f x y :: pairWith f xs

def mkTree₂ : List a → Tree a
 | []  => .null
 | as  =>
   unwrap (until' single (pairWith .node) (as.map .leaf))
    |>.getD .null

def msort₃ (xs : List a) : List a :=
  (Tree.flatten ∘ mkTree₂) xs

def msort₄ : List a → List a
 | []   => []
 | as   =>
   unwrap (until' single (pairWith merge) (as.map wrap))
    |>.getD []

def msort₅ : List a → List a
  | []  => []
  | xs  =>
    let op (x : a) : List (List a) → List (List a)
    | []               => [[x]]
    | [] :: yss        => [x] :: yss -- unreachable case
    | (y :: ys) :: yss =>
      if x ≤ y then
        (x :: y :: ys) :: yss
      else
        [x] :: (y :: ys) :: yss
    let runs := List.foldr op []
  unwrap (until' single (pairWith merge) (runs xs)) |>.getD []

end Mergesort


-- ## Section 5.3 Heapsort

namespace Heapsort

variable {a : Type} [LE a] [ToString a]

inductive Tree (a : Type) : Type
 | null : Tree a
 | node : a → Tree a → Tree a → Tree a
 deriving Inhabited

def flatten [DecidableRel (α := a) (· ≤ ·)] : Tree a → List a
| Tree.null       => []
| Tree.node x u v => x :: Mergesort.merge (flatten u) (flatten v)

open Std.Format in

def Tree.toFormat : (t: Tree a) → Std.Format
| .null => Std.Format.text "."
| .node x t₁ t₂ =>
  bracket "(" (f!"{x}" ++
   line ++ nest 2 t₁.toFormat ++ line ++ nest 2 t₂.toFormat) ")"

instance : Repr (Tree a) where
 reprPrec e _ := Tree.toFormat e

end Heapsort


-- ## Section 5.4 Bucketsort and Radixsort

namespace Bucketsort

variable {α : Type}

inductive Tree (α : Type)
| leaf : α → Tree α
| node : List (Tree α) → Tree α
deriving Repr


def Tree.flatten (r : Tree (List α)) : List α :=
 match r with
 | .leaf v  => v
 | .node ts =>
   List.flatten <| ts.map flatten

def ptn₀ {α β : Type} [BEq β] (rng : List β)
  (f : α → β) (xs : List α) : List (List α) :=
  rng.map (λ m => xs.filter (λ x => f x == m))

def mkTree {α β : Type} [BEq β]
  (rng : List β)
  (ds : List (α → β)) (xs : List α) : Tree (List α) :=
  match ds with
  | []       => .leaf xs
  | d :: ds' =>
    .node ((ptn₀ rng d xs).map (mkTree rng ds'))

def bsort₀ {β : Type} [BEq β] (rng : List β)
  (ds : List (α → β)) (xs : List α) : List α :=
  Tree.flatten (mkTree rng ds xs)

/-
#eval bsort₀ "abc".toList
  [fun s => s.toList[0]!,fun s => s.toList[1]!]
  ["ba", "ab", "aab", "bba"]
-/

instance : BoundedOrder Char where
  top := ⟨1114111, by decide⟩
  bot := ⟨0, by decide⟩
  le_top x := x.valid.by_cases
    (fun h => (h.trans (by decide)).le)
    (fun h => Nat.le_of_lt_add_one h.right)
  bot_le x := Nat.zero_le x.val.toNat

-- #eval (Finset.Icc ⊥ ⊤ : Finset Char)


end Bucketsort


end Chapter5
