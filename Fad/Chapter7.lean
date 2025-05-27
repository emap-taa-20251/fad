import Fad.Chapter1
import Fad.Chapter6

namespace Chapter7

-- # Section 7.1 A generic greedy algorithm

def NonEmptyList (α : Type) : Type :=
 {l : List α // l.length > 0}

def foldr1₀ (f : a → a → a) (as : NonEmptyList a) : a :=
  let x := as.val.head (List.ne_nil_of_length_pos as.property)
  if h₂ : as.val.length = 1 then
    x
  else
    let as' := as.val.tail
    have : as.val.length - 1 < as.val.length := by
      have h₁ := as.property; omega
    f x (foldr1₀ f (Subtype.mk as' (by
      -- change as.val.tail.length > 0
      have h₁ := as.property
      rw [List.length_tail]
      omega)))
 termination_by as.val.length

-- #eval foldr1₀ (fun a b => a + b ) (Subtype.mk [1,2,3,4,5,6] (by simp))

def foldr1₁ (f : a → a → a) (as : List a) (h : as.length > 0 := by decide) : a :=
  let x := as.head (List.ne_nil_of_length_pos h)
  if h₂ : as.length = 1 then
    x
  else
    f x (foldr1₁ f as.tail (by rw [List.length_tail]; omega))

-- #eval foldr1₁ (fun a b => a + b ) [1,2,3]

def foldr1 [Inhabited a] (f : a → a → a) : List a → a
  | []    => default
  | x::xs => xs.foldr f x

example : foldr1 (fun a b => a + b ) [1,2,3] = 6 := by rfl

def minWith {a b : Type} [LE b] [Inhabited a] [DecidableRel (α := b) (· ≤ ·)]
  (f : a → b) (as : List a) : a :=
  let smaller f x y := cond (f x ≤ f y) x y
  foldr1 (smaller f) as


-- # Section 7.2 Greedy sorting algorithms

open Chapter1 (tails) in

def pairs (xs : List a) : List (Prod a a) :=
 let step₁ : List a → List (Prod a a) → List (Prod a a)
  | [], acc => acc
  | x::ys, acc =>
    let step₂ : List a → List (Prod a a) → List (Prod a a)
     | [], acc => acc
     | y::_, acc => (x, y) :: acc
    (tails ys).foldr step₂ acc
 (tails xs).foldr step₁ []


def ic [LT a] [DecidableRel (@LT.lt a _)]
 (xs : List a) : Nat :=
 (pairs xs).filter (λ p => p.1 > p.2) |>.length


def extend : a → List a → List (List a)
| x, []      => [[x]]
| x, (y::xs)  => (x :: y :: xs) :: (extend x xs).map (y:: ·)


open Chapter1 in

def perms : List a → List (List a) :=
 List.foldr (concatMap ∘ extend) [[]]

def sort [LT a] [DecidableRel (@LT.lt a _)]
  : List a → List a :=
  minWith ic ∘ perms


def gstep [LT a] [DecidableRel (@LT.lt a _)]
  (x : a) : List a → List a :=
  (minWith ic) ∘ extend x


def picks (xs : List a) : List (a × List a) :=
  let rec helper : a → List (a × List a) → List (a × List a)
   | _, []                => []
   | x, ((y, ys) :: rest) => (y, x :: ys) :: (helper x rest)
  match xs with
  | []      => []
  | x :: xs => (x, xs) :: helper x (picks xs)


def pick [LE a] [h : DecidableRel (α := a) (· ≤ ·)] [Inhabited a]
 (xs : List a) : (a × List a) :=
  match picks xs with
  | []      => (default, []) -- unreachable
  | [p]     => p
  | p :: ps =>
    let rec aux : (a × List a) → List (a × List a) → (a × List a)
     | (x, xs), []              => (x, xs)
     | (x, xs), (y, ys) :: rest =>
       if x ≤ y then aux (x, xs) rest else aux (y, ys) rest
    aux p ps


-- # Section 7.3 Coin-changing

namespace S73

abbrev Denom := Nat
abbrev Tuple := List Nat

instance : Max Tuple where
  max x y := if x > y then x else y

def usds : List Denom := [100,50,25,10,5,1]
def ukds : List Denom := [200,100,50,20,10,5,2,1]

def amount (ds : List Denom) (cs : Tuple) : Nat :=
 List.sum (ds.zipWith (· * ·) cs)

-- #eval amount usds [2,1,0,0,1,1]

def mktuples₀ : List Denom → Nat → List Tuple
  | [1]    , n => [[n]]
  | []     , _ => panic! "mktuples: invalid empty list"
  | d :: ds, n =>
    (List.range (n / d + 1)).flatMap (λ c =>
      mktuples₀ ds (n - c * d) |>.map (λ cs => c :: cs))

def mkchange₀ (ds : List Denom) : Nat → Tuple :=
  minWith List.sum ∘ mktuples₀ ds

def mkchange₁ (ds : List Denom) : Nat → Tuple :=
  Chapter6.maximum ∘ mktuples₀ ds

/-
#eval mkchange₀ [7,3,1] 54
#eval mkchange₁ [7,3,1] 54
-/

partial def mktuples₁ : List Denom → Nat → List Tuple
  | [1]    , n => [[n]]
  | []     , _ => panic! "mktuples: invalid empty list"
  | d :: ds, n =>
    let extend ds c := mktuples₁ ds (n - c * d) |>.map (c :: ·)
    Chapter1.concatMap (extend ds) (List.range (n / d + 1))

/-
#eval mktuples₀ [7,3,1] 23
#eval mktuples₁ [7,3,1] 23
-/

def mkchange : List Denom → Nat → Tuple
  | [1]    , n => [n]
  | []     , _ => panic! "mkchange: invalid empty list"
  | d :: ds, n =>
    let c := n / d
    c :: mkchange ds (n - c * d)

/-
#eval mkchange ukds 256
#eval mkchange usds 256
#eval mkchange [7,3,1] 54
-/

end S73

end Chapter7
