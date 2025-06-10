
import Fad.Chapter1
import Fad.Chapter5
import Fad.«Chapter1-Ex»
import Fad.«Chapter4-Ex»

namespace Chapter6

open Chapter1 (unwrap until' single)
open Chapter5.Mergesort (pairWith halve length_halve_fst length_halve_snd)
open Chapter5.Quicksort (qsort₁)
open Chapter4.BST2 (partition3)


-- # Section 6.1: minimum and maximum

variable {a : Type}
  [Inhabited a] [DecidableRel (α := a) (· = ·)]
  [LT a] [DecidableRel (α := a) (· < ·)]
  [LE a] [DecidableRel (α := a) (· ≤ ·)] [Max a] [Min a]


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
partial def select (k : Nat) (xs : List a) : a :=
  match partition3 (pivot xs) xs with
  | (us, vs, ws) =>
    let m := us.length
    let n := vs.length
    if          k ≤ m then select k us
    else if k ≤ m + n then vs[k - m - 1]!
    else if k > m + n then select (k - m - n) ws
    else panic! "unreachable code"


end Chapter6
