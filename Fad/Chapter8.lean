import Fad.Chapter1
import Fad.«Chapter1-Ex»
import Fad.Chapter3
import Fad.Chapter5
import Fad.Chapter6
import Fad.Chapter7

namespace Chapter8

namespace S1

/- 8.1 Minimum-height trees -/

open Chapter5.S52 (halve length_halve_fst length_halve_snd pairWith)
open Chapter1 (wrap unwrap single until' concatMap)
open Chapter6 (foldl1)
open Chapter7 (minWith)

inductive Tree (α : Type) : Type where
 | leaf : α → Tree α
 | node : Tree α → Tree α → Tree α
 deriving Repr, Inhabited


def Tree.size {α : Type} : Tree α → Nat
 | Tree.leaf _ => 1
 | Tree.node t₁ t₂ => t₁.size + t₂.size


def Tree.height {α : Type} : Tree α → Nat
 | Tree.leaf _ => 0
 | Tree.node t₁ t₂ => Nat.max t₁.height t₂.height + 1


def Tree.fringe {α : Type} : Tree α → List α
 | Tree.leaf x => [x]
 | Tree.node t₁ t₂ => t₁.fringe ++ t₂.fringe


def mkTree {a : Type} [Inhabited a] : (as : List a) → Tree a
 | []      => .leaf default
 | x :: xs =>
   if h : xs.length = 0 then
    .leaf x
   else
    let p := halve (x :: xs)
    have : (halve (x :: xs)).1.length < xs.length + 1 :=
     by simp [length_halve_fst]; omega
    have : (halve (x :: xs)).2.length < xs.length + 1 :=
     by simp [length_halve_snd]; omega
    .node (mkTree p.1) (mkTree p.2)
 termination_by xs => xs.length

def mkTree₁ {a : Type} [Inhabited a] : List a → Tree a
 | [] => .leaf default
 | xs =>
   unwrap (until' single (pairWith .node) (xs.map .leaf)) |>.getD default


def cost : Tree Nat → Nat
 | Tree.leaf x     => x
 | Tree.node t₁ t₂ => 1 + Nat.max (cost t₁) (cost t₂)


def extend {a : Type} (x : a) : Tree a → List (Tree a)
 | Tree.leaf y     => [.node (.leaf x) (.leaf y)]
 | Tree.node t₁ t₂ =>
   [.node (.leaf x) (.node t₁ t₂)] ++ (extend x t₁).map (.node · t₂)


def mkTrees {a : Type} [Inhabited a] : List a → List (Tree a)
 | []      => []
 | [x]     => [Tree.leaf x]
 | x :: xs => concatMap (extend x) (mkTrees xs)


/- this should be defined only for nonempty lists -/
def foldrn {α β : Type} [Inhabited β] (f : α → β → β) (g : α → β) : List α → β
 | []      => default
 | [x]     => g x
 | x :: xs => f x (foldrn f g xs)

def mkTrees₁ {a : Type} [Inhabited a] : List a → List (Tree a) :=
 foldrn (concatMap ∘ extend) (wrap ∘ .leaf)


abbrev Forest (a : Type) := List (Tree a)


def rollup [Inhabited (Tree a)] : List (Tree a) → Tree a :=
  Chapter6.foldl1 .node

def spine {a : Type} : Tree a → List (Tree a)
 | .leaf x   => [.leaf x]
 | .node u v => spine u ++ [v]

example [Inhabited a] (ts : List (Tree a)) :
 spine (rollup ([Tree.leaf x] ++ ts)) = [Tree.leaf x] ++ ts := by
  induction ts with
  | nil =>
    simp [rollup, foldl1, spine]
  | cons t ts ih =>
    simp [rollup, foldl1, List.foldl, spine]
    simp [rollup, foldl1] at ih
    sorry


def extend₁ {a : Type} [Inhabited a] (x : a) (ts : Forest a) : List (Forest a) :=
  (List.range' 1 ts.length).map
    (λ i => .leaf x :: rollup (ts.take i) :: ts.drop i)

def mkForests {a : Type} [Inhabited a] : List a → List (Forest a) :=
 foldrn (concatMap ∘ extend₁) (wrap ∘ wrap ∘ .leaf)

def mkTrees₂ {a : Type} [Inhabited a] : List a → List (Tree a) :=
 List.map rollup ∘ mkForests


def mct₀ : List Nat → Tree Nat :=
 minWith cost ∘ mkTrees₂


def scanl1 (f : a → a → a) : List a → List a
 | x :: xs => Chapter1.scanl f x xs
 | []      => []

def lcost : Tree Nat → List Nat :=
  let op (x y : Nat) : Nat := 1 + Nat.max x y
  List.reverse ∘ scanl1 op ∘ List.map cost ∘ spine


def add (x : Nat) (ts : List (Tree Nat)) : List (Tree Nat) :=
  let rec join (x : Nat) : List (Tree Nat) → List (Tree Nat)
   | [u] => [u]
   | []  => []  -- not used
   | (u :: v :: ts) =>
     if Nat.max x (cost u) < cost v then
       u :: v :: ts
     else
       join x (Tree.node u v :: ts)
  termination_by ts => ts.length
  (Tree.leaf x) :: join x ts

def mct₁ : List Nat → Tree Nat :=
 let gstep (x : Nat) : Tree Nat → Tree Nat :=
  rollup ∘ add x ∘ spine
 foldrn gstep .leaf


abbrev Pair := (Tree Nat × Nat)

def node : Pair → Pair → Pair
 | (u, c), (v, d) => (Tree.node u v, 1 + Nat.max c d)

def leaf : Nat → Pair
 | x => (Tree.leaf x, x)

def join (x : Nat) : List Pair → List Pair
 | [u] => [u]
 | []  => [] -- not used
 | u :: v :: ts =>
   if Nat.max x u.snd < v.snd then
     u :: v :: ts
   else
     join x (node u v :: ts)
 termination_by ts => ts.length

def mct : List Nat → Tree Nat :=
 let hstep (x : Nat) (ts : List Pair) : List Pair :=
  leaf x :: join x ts
 rollup ∘ List.map Prod.fst ∘ foldrn hstep (wrap ∘ leaf)

end S1


/- 8.2 Huffman coding trees -/

namespace S2
open S1 (Tree Forest)
open Chapter1 (concatMap wrap unwrap unwrap! single until' single picks apply)
open Chapter3.SymList (nil singleSL headSL headSL! snocSL isEmpty tailSL)


def depths : Tree a → List Nat :=
 let rec frm (n : Nat) : Tree a → List Nat
  | Tree.leaf _   => [n]
  | Tree.node u v => frm (n + 1) u ++ frm (n + 1) v
 frm 0

abbrev Weight := Nat
abbrev Elem   := Char × Weight
abbrev Cost   := Nat

def cost (t : Tree Elem) : Cost :=
 let t := t.fringe.zip (depths t)
 List.sum $ t.map (λ (c, d) => d * c.snd)

def weight : Tree Elem → Nat
 | Tree.leaf (_, w) => w
 | Tree.node u v    => weight u + weight v

def cost₁ : Tree Elem → Cost
 | Tree.leaf _   => 0
 | Tree.node u v => cost u + cost v + weight u + weight v

def pairs (xs : List α) : List ((α × α) × List α) :=
  (picks xs).flatMap
    fun (x, ys) =>
     (picks ys).map
      fun (y, zs) => ((x, y), zs)

/- Exercise 8.11 -/
def insert (t₁ : Tree Elem) : Forest Elem → Forest Elem
 | [] => [t₁]
 | t₂ :: ts =>
   if weight t₁ ≤ weight t₂ then
     t₁ :: t₂ :: ts
   else
     t₂ :: insert t₁ ts

def combine (ts : Forest Elem) : List (Forest Elem) :=
  (pairs ts).map fun (p, us) =>
    insert (Tree.node p.1 p.2) us

def mkForests : List (Tree Elem) → List (Forest Elem) :=
 until' (flip List.all single) (concatMap combine) ∘ wrap

def mkTrees : List Elem → List (Tree Elem) :=
 List.map unwrap! ∘ mkForests ∘ List.map Tree.leaf

def mkForests₁ (ts : List (Tree Elem)) : List (Forest Elem) :=
 apply (ts.length - 1) (concatMap combine) [ts]

def mkTrees₁ : List Elem → List (Tree Elem) :=
 List.map unwrap! ∘ mkForests₁ ∘ List.map Tree.leaf


/- quadractic version -/

def huffman₁ (es : List Elem) : Tree Elem :=
 let gstep : Forest Elem → Forest Elem
  | t₁ :: t₂ :: ts => insert (Tree.node t₁ t₂) ts
  | []             => dbg_trace "error"; []       -- not used
  | t₁ :: ts       => dbg_trace "error"; t₁ :: ts -- not used
 unwrap! (until' single gstep (List.map Tree.leaf es))

-- #eval huffman₁ [('a', 2), ('b', 3), ('c', 1), ('d', 20)]

/- linear time version -/

abbrev Queue (α : Type) := Chapter3.SymList α
abbrev Stack (α : Type) := List α
abbrev SQ (α : Type)    := Stack α × Queue α
abbrev Pair             := Tree Elem × Weight

def leaf : Elem → Pair
 | (c, w) => (Tree.leaf (c, w), w)

def node : Pair → Pair → Pair
 | (t₁, w₁), (t₂, w₂) => (Tree.node t₁ t₂, w₁ + w₂)

def makeSQ (xs : List Pair) : SQ Pair :=
  (xs, nil)

def singleSQ (sq : SQ a) : Bool :=
  sq.1.isEmpty ∧ singleSL sq.2

def extractSQ (sq : SQ Pair) : Tree Elem :=
  (headSL! sq.2).1


def extractMin (ps : SQ Pair) : Pair × SQ Pair :=
  let (xs, ys) := ps
  if isEmpty ys then
   (xs.head!, (xs.tail, ys))
  else if xs.isEmpty then
   (headSL! ys, (xs, tailSL ys))
  else
   let x := xs.head!
   let y := headSL! ys
   if x.snd ≤ y.snd then
    (x, (xs.tail, ys))
   else
    (y, (xs, tailSL ys))

def gstep (ps : SQ Pair) : SQ Pair :=
  let add : Pair → SQ Pair → SQ Pair
   | y, (xs, ys) => (xs, snocSL y ys)
  let (p₁, qs) := extractMin ps
  let (p₂, rs) := extractMin qs
  add (node p₁ p₂) rs

def huffman : List Elem → Tree Elem :=
 extractSQ ∘ until' singleSQ gstep ∘ makeSQ ∘ List.map leaf

-- #eval huffman [('a', 2), ('b', 3), ('c', 1), ('d', 20)]

end S2
end Chapter8
