
import Fad.Chapter1

namespace Chapter4

/- # Section 4.1: a one-dimensional search problem -/

namespace D1

def search₀ (f : Nat → Nat) (t : Nat) : List Nat :=
 (List.range $ t + 1).filter (t = f ·)

-- #eval search₀ (fun _ => 3) 3

def search₁ (f : Nat → Nat) (t : Nat) : List Nat :=
  seek (0, t)
 where
  seek : (Nat × Nat) → List Nat
  | (a, b) => List.range' a (b - a + 1) |>.filter (t = f ·)


def search₂ (f : Nat → Nat) (t : Nat) : List Nat :=
 let rec seek (a b : Nat) : List Nat :=
  let m := (a + b) / 2
  let v := f m
  if      h₁ : a = b then
   if t = v then [m] else []
  else if h₉ : a > b then []
  else if h₂ : t = v then [m]
  else if h₃ : t < v then
    seek a (m - 1)
  else
    seek (m + 1) b
 termination_by (b - a) -- see https://tinyurl.com/57szywn5
 seek 0 t

-- #eval search₂ (λ a => dbg_trace "f {a}"; a * a) 1024

def bound (f : Nat → Nat) (t : Nat) : (Nat × Nat) :=
  if t ≤ f 0 then (0, 0) else (b / 2, b)
 where
  b := Chapter1.until' done (· * 2) 1
  done b := t ≤ f b

-- #eval bound (fun x => dbg_trace "fun {x}"; x + 10) 10

def smallest (f : Nat → Nat) (t : Nat) (p : Nat × Nat) : Nat :=
 match p with
 | (a, b) =>
   let m := (a + b) / 2
   let v := f m
   if      h₀ : a = b then b
   else if h₁ : a > b then b
   else if h₃ : t = v then m
   else if h₂ : t < v then
    smallest f t (a, m)
   else
    smallest f t (m + 1, b)
 termination_by (p.2 - p.1)

def search₃ (f : Nat → Nat) (t : Nat) : List Nat :=
  if f x = t then [x] else []
 where
  x := smallest f t (bound f t)

/-
#eval search₁ (fun x => dbg_trace "fun {x}"; x * x) 1024
#eval search₂ (fun x => dbg_trace "fun {x}"; x * x) 1048576
#eval search₃ (fun x => dbg_trace "fun {x}"; x ^ 3) 175616
-/

end D1


/- # Section 4.2 A two-dimensional search problem -/

namespace D2

def search₀ (f : (Nat × Nat) → Nat) (t : Nat) : List (Nat × Nat) :=
 ps.filter (λ p => t = f p)
 where
  as := (List.range $ t + 1)
  ps := Chapter1.concatMap (λ x => as.map (λ y => (x, y))) as

-- #eval search₀ (λ p => dbg_trace "fun {p}"; p.1 + p.2) 5

/- https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/.E2.9C.94.20proof.20termination -/

def search₁ (f : Nat × Nat → Nat) (t : Nat) : List (Nat × Nat) :=
  searchIn 0 t []
where
  searchIn (x y : Nat) (sofar : List (Nat × Nat)) : List (Nat × Nat) :=
    let z := f (x, y)
    if x > t then sofar
    else if z < t then
      searchIn (x + 1) y sofar
    else if z = t then
      match y with
      | 0 => (x,y) :: sofar
      | y' + 1 => searchIn (x + 1) y ((x, y) :: sofar)
    else
      match y with
      | 0 => sofar
      | y + 1 => searchIn x y sofar
  termination_by (t + 1 - x, y)

-- #eval search₁ (λ (x, y) => dbg_trace "fun {x} {y}"; x + y) 5
-- #eval search₁ (λ (x, y) => dbg_trace "fun {x} {y}"; x^2 + 3^y) 12
-- #eval search₁ (λ (x, y) => x^2 + 3^y) 2223
-- #eval search₁ (λ (x, y) => x^2 + 3^y) 20259


-- BUG #eval helper 12 (λ (x, y) => x^2 + 3^y) (0, 12) (12,0)

partial def helper (t : Nat) (f : Nat × Nat → Nat)
 : (Nat × Nat) → (Nat × Nat) → List (Nat × Nat)
 | (x₁, y₁), (x₂, y₂) =>
  let c := (x₁ + x₂) / 2
  let r := (y₁ + y₂) / 2
  let x := D1.smallest (λ x => f (x,r)) t (x₁ - 1, x₂)
  let y := D1.smallest (λ y => f (c,y)) t (y₂ - 1, y₁)
  if x₂ < x₁ ∨ y₁ < y₂ then
   []
  else
   if y₁ - y₂ ≤ x₂ - x₁ then
    let z := f (x,r)
    if z < t then
     helper t f (x₁, y₁) (x₂, r + 1)
    else if z = t then
     (x, r) :: helper t f (x₁, y₁) (x - 1, r + 1) ++ helper t f (x + 1, r - 1) (x₂, y₂)
    else
     helper t f  (x₁, y₁) (x - 1, r + 1) ++ helper t f (x, r - 1) (x₂, y₂)
   else
    let z := f (c, y)
    if z < t then
     helper t f (c + 1, y₁) (x₂, y₂)
    else if z = t then
     (c, y) :: helper t f (x₁, y₁) (c - 1, y + 1) ++ helper t f (c + 1, y - 1) (x₂, y₂)
    else
     helper t f (x₁, y₁) (c - 1, y) ++ helper t f (c + 1, y - 1) (x₂, y₂)

partial def search₂ (f : Nat × Nat → Nat) (t : Nat) : List (Nat × Nat) :=
 let p := D1.smallest (λ y => f (0, y)) t (0, t)
 let q := D1.smallest (λ x => f (x, 0)) t (0, t)
 helper t f (0, p) (q, 0)


/- https://kmill.github.io/informalization/ucsc_cse_talk.pdf -/

def scale (a : Array Int) (c : Int) : Array Int := Id.run do
  let mut b : Array Int := #[]
  for h: i in [0:a.size] do
   b := b.push (c * a[i])
  return b

-- #eval scale #[1,2,3,4] 4
-- #eval for i in [0:12] do println! i

def myhead₁ (xs : List a) (h : xs.length ≠ 0) : a :=
 match xs with
 | [] => absurd rfl h
 | x :: _ => x

def myhead₂ (xs : List a) (h : xs.length ≠ 0) : a :=
 match xs, h with
 | x :: _, _ => x

end D2


/- # Section 4.3 Binary search trees -/

namespace BST1

variable {α : Type}

inductive Tree (α : Type) : Type
| null : Tree α
| node : (Tree α) → α → (Tree α) → Tree α
deriving Inhabited

open Std.Format in

def Tree.toFormat [ToString α] : (t : Tree α) → Std.Format
| .null => Std.Format.text "."
| .node t₁ x t₂ =>
  bracket "(" (f!"{x}" ++
   line ++ nest 2 t₁.toFormat ++ line ++ nest 2 t₂.toFormat) ")"

instance [ToString α] : Repr (Tree α) where
 reprPrec e _ := e.toFormat

def Tree.size : Tree α → Nat
| null => 0
| node t₁ _ t₂ => 1 + t₁.size + t₂.size

def Tree.flatten : Tree α → List α
| null => []
| node l x r => l.flatten ++ [x] ++ r.flatten

def search (f : Nat → Nat) : Nat → Tree Nat → Option Nat
| _, Tree.null       => none
| k, Tree.node l x r =>
  if f x < k then
   search f k r
  else
   if f x = k then
    some x
   else
    search f k l

def Tree.height : Tree α → Nat
| null => 0
| node l _ r => 1 + (max l.height r.height)


def mkTree [LT α] [DecidableRel (α := α) (· < ·)]
: List α → Tree α
| [] => Tree.null
| x :: xs =>
  let p := xs.partition (· < x)
  Tree.node (mkTree p.1) x (mkTree p.2)
 termination_by l => l.length
 decreasing_by
  all_goals
   simp [List.partition_eq_filter_filter,
         List.length_filter_le,
         Nat.lt_add_one_of_le]


end BST1


namespace BST2

variable {α : Type}

inductive Tree (α : Type) : Type
| null : Tree α
| node : Nat → (Tree α) → α → (Tree α) → Tree α
deriving Nonempty

open Std.Format in

def Tree.toFormat [ToString α] : (t : Tree α) → Std.Format
| .null => Std.Format.text "."
| .node _ t₁ x t₂ =>
  bracket "(" (f!"{x}" ++
   line ++ nest 2 t₁.toFormat ++ line ++ nest 2 t₂.toFormat) ")"

instance [ToString α] : Repr (Tree α) where
 reprPrec e _ := e.toFormat

def Tree.height : Tree α → Nat
 | .null => 0
 | .node x _ _ _ => x

def Tree.flatten : Tree α → List α
| null => []
| node _ l x r => l.flatten ++ [x] ++ r.flatten

def node (l : Tree α) (x : α) (r : Tree α): Tree α :=
  Tree.node h l x r
 where h := 1 + (max l.height r.height)

def bias : Tree α → Int
 | .null => 0
 | .node _ l _ r => l.height - r.height

def rotr : Tree α → Tree α
| .null => .null
| .node _ (.node _ ll y rl) x r => node ll y (node rl x r)
| .node _ .null _ _ => .null

def rotl : Tree α → Tree α
| .null => .null
| .node _ ll y (.node _ lrl z rrl) => node (node ll y lrl) z rrl
| .node _ _ _ .null => .null

def balance (t1 : Tree α)  (x : α)  (t2 : Tree α) : Tree α :=
 if Int.natAbs (h1 - h2) ≤ 1 then
   node t1 x t2
 else if h1 == h2 + 2 then
   rotateR t1 x t2
 else
   rotateL t1 x t2
 where
  h1 := t1.height
  h2 := t2.height
  rotateR t1 x t2 :=
   if 0 <= bias t1 then
    rotr (node t1 x t2)
   else rotr (node (rotl t1) x t2)
  rotateL t1 x t2 :=
   if bias t2 <= 0 then
    rotl (node t1 x t2)
   else rotl (node t1 x (rotr t2))


def insert {α : Type} [LT α] [DecidableRel (α := α) (· < ·)]
 : (x : α) -> Tree α -> Tree α
 | x, .null => node .null x .null
 | x, .node h l y r =>
   if x < y then balance (insert x l) y r else
   if x > y then balance l y (insert x r) else .node h l y r


def mkTree [LT α] [DecidableRel (α := α) (· < ·)] : (xs : List α) → Tree α :=
 Chapter1.foldr insert (.null : Tree α)


def balanceR (t₁ : Tree α) (x : α) (t₂ : Tree α) : Tree α :=
 match t₁ with
 | Tree.null => Tree.null
 | Tree.node _ l y r =>
   if r.height ≥ t₂.height + 2
   then balance l y (balanceR r x t₂)
   else balance l y (node r x t₂)

end BST2

namespace DSet
open BST2 (insert node)

abbrev Set a := BST2.Tree a

def member {a : Type} [LT a] [DecidableRel (α := a) (· < ·)] (x : a) : Set a → Bool
| .null => false
| .node _ l y r =>
  if x < y      then member x l
  else if x > y then member x r
  else true

end DSet

end Chapter4
