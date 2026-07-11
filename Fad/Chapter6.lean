import Fad.Chapter1
import Fad.Chapter5
import Fad.«Chapter1-Ex»
import Fad.«Chapter4-Ex»

namespace Chapter6

open Chapter1 (unwrap until' single)
open Chapter5.Mergesort (merge pairWith halve length_halve_fst length_halve_snd)
open Chapter5.Quicksort (qsort₁)
open Chapter4.BST2 (partition3 Tree rotl Tree.height)


-- # Section 6.1: minimum and maximum

variable {a : Type}
  [Inhabited a] [DecidableRel (α := a) (· = ·)]
  [Max a] [Min a]
  [LT a] [DecidableRel (α := a) (· < ·)]
  [LE a] [DecidableRel (α := a) (· ≤ ·)]


def foldr1₀ (f : a → a → a) (xs : List a) (h : xs ≠ []) : a
  :=
  if h₁ : xs.length = 1 then
    xs.head (by simp [h])
  else
    let b :: bs := xs
    f b (foldr1₀ f bs (by
      intro h₂; apply h₁ ; rw [h₂]; simp))

def foldr1 (f : a → a → a) : List a → a
  | []    => default
  | [x]   => x
  | x::xs => f x (foldr1 f xs)

def foldl1 (f : a → a → a) : List a → a
  | []    => default
  | x::xs => xs.foldl f x

def minimum : List a → a :=
  foldr1 min

def maximum : List a → a :=
  foldr1 max

theorem maximum_eq_foldrmax {a : Type} [LinearOrder a] [Inhabited a]
  (x : a) (xs : List a)
  : maximum (x::xs) = xs.foldr max x := by
  simp [maximum]
  induction xs generalizing x with
  | nil => rfl
  | cons y ys ih =>
    simp [foldr1, ← ih]
    induction ys generalizing x y with
    | nil => exact max_comm x y
    | cons z zs ih2 => grind [foldr1]

theorem minimum_eq_foldrmin {a : Type} [LinearOrder a] [Inhabited a]
  (x : a) (xs : List a)
  : minimum (x::xs) = xs.foldr min x := by
  simp [minimum]
  induction xs generalizing x with
  | nil => rfl
  | cons y ys ih =>
    simp [foldr1, ← ih]
    induction ys generalizing x y with
    | nil => exact min_comm x y
    | cons z zs ih2 => grind [foldr1]

def minmax₀ : List a → (a × a)
  | []      => default
  | x :: xs =>
    let op x q := (min x q.1, max x q.2)
    xs.foldr op (x,x)

def minmax₁ : List a → (a × a)
  | []      => default
  | x :: xs =>
    let op x q :=
      if      x < q.1 then (x, q.2)
      else if x > q.2 then (q.1, x)
      else (q.1, q.2)
    xs.foldr op (x,x)

def minmax₂ : List a → (a × a)
  | []      => default
  | x :: xs =>
    if      h₁ : xs.length = 0 then (x, x)
    else if h₂ : xs.length = 1 then
     have h₃ : xs ≠ [] := by
      intro h; apply h₁
      apply List.length_eq_zero_iff.mpr; assumption
     if x ≤ xs.head h₃ then (x, xs.head h₃) else (xs.head h₃, x)
    else
     let p := halve xs
     have : (halve xs).fst.length < xs.length := by
      simp [length_halve_fst]; omega
     have : (halve xs).snd.length < xs.length := by
      simp [length_halve_snd]; omega
     let q := minmax₂ p.1
     let r := minmax₂ p.2
     (min q.1 r.1, max q.2 r.2)
termination_by xs => xs.length


def mkPairs : List a → List (a × a)
  | []           => []
  | [x]          => [(x, x)]
  | x :: y :: xs =>
    if x ≤ y then
     (x, y) :: mkPairs xs
    else
     (y, x) :: mkPairs xs


def minmax (xs : List a) : (a × a) :=
  let op p q := (min p.1 q.1, max p.2 q.2)
  (unwrap ∘ until' single (pairWith op) ∘ mkPairs) xs
    |>.getD default


-- # Section 6.2: selection from one set

/-
#check let xs := [1,2,3];
 xs.get (Fin.mk 2 (by simp [List.length]) : Fin xs.length)
-/

def select₀ (k : Nat) (xs : List a) : a :=
 (qsort₁ xs)[k - 1]!

def median (xs : List a) : a :=
  let k := (xs.length + 1) / 2
  select₀ k xs


def group (n : Nat) (xs : List a) : List (List a) :=
  if      h₁ : n = 0   then []
  else if h₂ : xs = [] then []
  else
   let p := xs.splitAt n
   have : xs.length - n < xs.length := by
    induction xs with
    | nil => simp at *
    | cons b bs ih =>
      simp ; omega
   p.1 :: (group n p.2)
 termination_by xs.length

-- #eval group 5 (List.range' 1 12)

/- `qsort₁` or `qsort` ? -/
def medians : List a → List a :=
  let middle (xs : List a) := xs[((xs.length + 1) / 2) - 1]!
  List.map (middle ∘ qsort₁) ∘ group 5

-- #eval medians (List.range' 1 12)

/- `select₀` or `select` ? -/
def pivot : List a → a
  | [x] => x
  | xs  =>
    let median xs := select₀ ((xs.length + 1) / 2) xs
    median (medians xs)


partial def qsort : List a → List a
  | [] => []
  | xs =>
    let p := partition3 (pivot xs) xs
    qsort p.1 ++ p.2.1 ++ qsort p.2.2


/- this function breaks with k > xs.length -/
partial def select
  (k : Nat) (xs : List a) (ok : k ≤ xs.length) : a :=
  match partition3 (pivot xs) xs with
  | (us, vs, ws) =>
    let m := us.length
    let n := vs.length
    if      h₁ : k ≤ m then select k us (by grind)
    else if h₂ : k ≤ m + n then vs[k - m - 1]'(by grind)
    else if k > m + n then select (k - m - n) ws (by sorry)
    else panic! "unreachable code"

theorem partition3_length {a : Type} [LT a] [DecidableRel (α := a) (· < ·)]
 [DecidableRel (α := a) (· = ·)]
 (y :a) (xs : List a) :
  (partition3 y xs).2.2.length +
  (partition3 y xs).2.1.length +
  (partition3 y xs).1.length =
  xs.length := by
  induction' xs with x xs ih
  . rfl
  . grind [partition3]

/- may not be necessary -/
def select' (k : Nat) (xs : List a) (q: k ≤ xs.length): a :=
  let rec help (k : Nat) (xs : List a) (q: k ≤ xs.length) (fuel: Nat) : a :=
   match fuel with
   | 0 => panic!"Never here"
   | fuel+1 =>
     let us := (partition3 (pivot xs) xs).1
     let vs := (partition3 (pivot xs) xs).2.1
     let ws := (partition3 (pivot xs) xs).2.2
     let m := us.length
     let n := vs.length
     if      h₁:  k ≤ m     then   help k us (by omega) fuel
     else if h₂:  k ≤ m + n then vs[k - m - 1]
     else                        help (k-m-n) ws (by
     simp [m, n]; rw [partition3_length]; simp [q]) fuel
  termination_by fuel
  help k xs q xs.length

-- # Section 6.3: selection from two set

def select2₀ (k: Nat) (as bs : List a): a :=
  (merge as bs)[k]!

def select2 (k : Nat) (as bs : List a) : a :=
  match as, bs with
  | [], bs => bs[k]!
  | as, [] => as[k]!
  | a₀ :: as, b₀ :: bs =>
    let p  := (a₀ :: as).length / 2
    let q  := (b₀ :: bs).length / 2
    let xs := (a₀ :: as).take p
    let a  := ((a₀ :: as).drop p).head (by
      have h: p < (a₀ :: as).length := by grind
      simp_all
    )
    let ys := ((a₀ :: as).drop p).tail
    let us := (b₀ :: bs).take q
    let b  := ((b₀ :: bs).drop q).head (by
      have h: q < (b₀ :: bs).length := by grind
      simp_all
    )
    let vs := ((b₀ :: bs).drop q).tail
    if      a ≤ b ∧ k ≤ p + q then select2 k (a₀ :: as) us
    else if a ≤ b ∧ k ≤ p + q then select2 (k - p - 1) ys (b₀ :: bs)
    else if b ≤ a ∧ k ≤ p + q then select2 k xs (b₀ :: bs)
    else                           select2 (k - q - 1) (a₀ :: as) vs
termination_by as.length + bs.length

-- #eval select2 6 [1, 4, 4, 7, 8, 11, 15] [2, 5, 9, 11, 15, 16, 20]

-- For some reason, there's a confusion with the Tree of Mathlib
-- #check Tree
-- #check _root_.Tree
abbrev BTree := Chapter4.BST2.Tree

def selectT₀ (k : Nat) (t₁ t₂ : BTree a) : a :=
  (merge (t₁.flatten) (t₂.flatten))[k]!

def index₀ (t : BTree a) (k : Nat) : a :=
  (t.flatten)[k]!

def index (t : BTree a) (k : Nat) : a :=
  match t with
  | .null => default
  | .node _ l x r =>
    let p := l.height
    if      k < p then index l k
    else if k = p then x
    else               index r (k - p - 1)

def selectT (k : Nat) (t₁ t₂ : BTree a) : a :=
  match t₁, t₂ with
  | t₁ ,             .null           => index t₁ k
  | .null ,         t₂               => index t₂ k
  | .node h₁ l₁ a r₁, .node h₂ l₂ b r₂ =>
    let p := l₁.height
    let q := l₂.height
    if      a ≤ b ∧ k ≤ p + q then selectT k (.node h₁ l₁ a r₁) l₂
    else if a ≤ b             then selectT (k - p - 1) r₁ (.node h₂ l₂ b r₂)
    else if b ≤ a ∧ k ≤ p + q then selectT k l₁ (.node h₂ l₂ b r₂)
    else                           selectT (k - q - 1) (.node h₁ l₁ a r₁) r₂



end Chapter6
