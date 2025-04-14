
import Fad.Chapter1
import Fad.Chapter5
import Fad.«Chapter1-Ex»
import Fad.«Chapter4-Ex»

namespace Chapter6
open Chapter1 (unwrap until' single)
open Chapter5.S52 (halve length_halve_fst length_halve_snd)
open Chapter5.Quicksort (qsort₁)
open Chapter4.BST2 (partition3)

-- # Section 6.1: minimum and maximum

def foldr1 [Inhabited a] (f : a → a → a) : List a → a
  | []    => default
  | [x]   => x
  | x::xs => f x (foldr1 f xs)

def foldl1 [Inhabited a] (f : a → a → a) : List a → a
  | []    => default
  | x::xs => xs.foldl f x

def minimum [Inhabited a] [LE a] [DecidableRel (α := a) (· ≤ ·)]
  : List a → a :=
  foldr1 (fun x y => if x ≤ y then x else y)

def maximum [Inhabited a] [Max a] : List a → a :=
  foldr1 max


def minmax₀ [Inhabited a] [Min a] [Max a]
  : List a → (a × a)
  | []    => (default, default)
  | x::xs =>
    let op x q := (min x q.1, max x q.2)
    xs.foldr op (x,x)


def minmax₁ [Inhabited a] [LT a] [DecidableRel (α := a) (· < ·)]
  : List a → (a × a)
  | []    => (default, default)
  | x::xs =>
    let op x q :=
      if      x < q.1 then (x, q.2)
      else if q.2 < x then (q.1, x)
      else    (q.1, q.2)
    xs.foldr op (x,x)


def minmax₂ [Inhabited a] [Min a] [Max a] [LE a] [DecidableRel (α := a) (· ≤ ·)]
  : List a → (a × a)
  | []    => (default, default)
  | x::xs =>
    if      h₁ : xs.length = 0 then (x, x)
    else if h₂ : xs.length = 1 then
      if x ≤ xs.head! then (x, xs.head!) else (xs.head!, x)
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


def pairWith (f : a → a → a) : List a →  List a
 | []       => []
 | [x]      => [x]
 | x::y::xs => (f x y) :: pairWith f xs

def mkPairs [LE a] [DecidableRel (α := a) (· ≤ ·)]
  : List a → List (a × a)
  | []       => []
  | [x]      => [(x, x)]
  | x::y::xs =>
    if x ≤ y then
     (x, y) :: mkPairs xs
    else
     (y, x) :: mkPairs xs

def minmax [Inhabited a] [LE a] [DecidableRel (α := a) (· ≤ ·)]
  [Min a] [Max a] (xs : List a)
  : (a × a) :=
  let op p q := (min p.1 q.1, max p.2 q.2)
  (unwrap ∘ until' single (pairWith op) ∘ mkPairs) xs
    |>.getD (default, default)


-- # Section 6.2: selection from one set

/-
#check let xs := [1,2,3];
 xs.get (Fin.mk 2 (by simp [List.length]) : Fin xs.length)
-/

def select₀ [Inhabited a] [LT a] [DecidableRel (α := a) (· < ·)]
 (k : Nat) (xs : List a) : a :=
 (qsort₁ xs).get! (k - 1)


def median [Inhabited a] [LT a] [DecidableRel (α := a) (· < ·)]
  (xs : List a) : a :=
  let k := (xs.length + 1) / 2
  select₀ k xs


partial def group [Inhabited a] (n : Nat) (xs : List a) : List (List a) :=
 match xs with
 | [] => []
 | xs =>
  let p := xs.splitAt n
  p.1 :: (group n p.2)


/-- `qsort₁` or `qsort` ? -/
def medians [Inhabited a] [LT a]
  [DecidableRel (α := a) (· < ·)] [DecidableRel (α := a) (· = ·)]
  : List a → List a :=
  let middle (xs : List a) := xs.get! (((xs.length + 1) / 2) - 1)
  List.map (middle ∘ qsort₁) ∘ group 5


/- `select₀` or `select` ? -/
def pivot [Inhabited a] [LT a]
  [DecidableRel (α := a) (· < ·)] [DecidableRel (α := a) (· = ·)]
  : List a → a
  | [x] => x
  | xs  =>
    let median xs := select₀ ((xs.length + 1) / 2) xs
    median (medians xs)


partial def qsort [Inhabited a] [LT a]
  [DecidableRel (α := a) (· < ·)] [DecidableRel (α := a) (· = ·)]
  : List a → List a
  | [] => []
  | xs =>
    let p := partition3 (pivot xs) xs
    qsort p.1 ++ p.2.1 ++ qsort p.2.2


/- this function breaks with k > xs.length -/
partial def select [Inhabited a] [LT a]
  [DecidableRel (α := a) (· < ·)] [DecidableRel (α := a) (· = ·)]
  (k : Nat) (xs : List a) : a :=
  match partition3 (pivot xs) xs with
  | (us, vs, ws) =>
    let m := us.length
    let n := vs.length
    if          k ≤ m then select k us
    else if k ≤ m + n then vs.get! (k - m - 1)
    else if k > m + n then select (k - m - n) ws
    else panic! "unreachable code"


end Chapter6
