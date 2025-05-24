import Fad.Chapter4
import Fad.Chapter3

namespace Chapter4

/- 4.2
We have smallest (a,b) = x such that f x < t ≤ f (x + 1)
But for t = 1024 and f x = x^2 below f x = t and f (x + 1) > t

#eval D1.smallest (fun x => dbg_trace "fun {x}"; x * x) 1024 (0, 1024)
#eval (fun x => dbg_trace "fun {x}"; x * x) 32
#eval (fun x => dbg_trace "fun {x}"; x * x) 33
-/

/- 4.3

Vamos provar por indução que

T(x) = ⌈log(n-1)⌉.

Para o caso base (n=2)

T(2) = ⌈log(2-1)⌉ = ⌈log(1)⌉ = ⌈0⌉ = 0.

Supondo valido para k < n, vamos provar para n. Como ⌈(n+1)/2⌉ < n,
vale a hipotese de indução, então temos que provar que:

T(n) = ⌈log(⌈(n+1)/2⌉ -1)⌉ + 1 = ⌈log(n-1)⌉.

Podemos mostrar por desigualdade indireta, mostrando que o lado
esquerdo é menor que k se e somente o lado direito é menor que k, para
qualquer k natural.  Pelo lado direito temos que ⌈log(n-1)⌉ <= k <=>
n-1 <= 2^k.  Pelo lado esquerdo:

    ⌈log(⌈(n+1)/2⌉ -1)⌉ + 1 <= k <=> ⌈log(⌈(n+1)/2⌉ -1)⌉ <= k-1,
                                 <=> log(⌈(n+1)/2⌉ -1) <= k-1,
                                 <=> ⌈(n+1)/2⌉ -1 <= 2^(k-1),
                                 <=> ⌈(n+1)/2⌉ <= 2^(k-1) + 1,
                                 <=> (n+1)/2 <= 2^(k-1) + 1,
                                 <=> n+1 <= 2^k + 2,
                                 <=> n-1 <= 2^k.

O que completa a prova, uma vez que ambos os lados chegam na mesma
proposição.

-/


/- 4.4 : see the book -/

/-!
# Exercicio 4.5

Indexing the coordinates from zero, the positions are
(0, 9), (5, 6), (7, 5), (9, 0)
-/

-- # Exercicio 4.6

-- #eval D2.search₁ (λ (x, y) => x ^ 3 + y ^ 3) 1729


-- # Exercicio 4.7

namespace BST1

def flatcat : (t : Tree a) → (xs: List a) → List a
| .null, xs => xs
| .node l x r, xs => flatcat l (x :: flatcat r xs)

def Tree.flatten₁ (t : Tree a) : List a :=
 flatcat t []


example (t: Tree a) :
  t.flatten = t.flatten₁ := by
  induction t with
  | null => exact rfl
  | node l x r ihl ihr =>
    simp [Tree.flatten₁]
    simp [Tree.flatten]
    simp [flatcat]
    simp [ihl, ihr]
    simp [Tree.flatten₁]
    sorry

end BST1

-- # Exercicio 4.8


namespace BST1

example {α : Type} (t : Tree α) :
  t.height ≤ t.size ∧ t.size < 2 ^ t.height := by
  apply And.intro
  {
   induction t with
   | null  => simp [Tree.height, Tree.size]
   | node t₁ x t₂ ihl ihr =>
     simp [Tree.height, Tree.size]
     sorry
  }
  {
  induction t with
  | null => simp [Tree.height, Tree.size]
  | node t₁ x t₂ ihl ihr =>
    simp [Tree.height, Tree.size]
    sorry
  }

end BST1

/-
namespace Chapter3

example {α : Type} (t : Tree α) :
  t.height ≤ t.size ∧ t.size < 2 ^ t.height := by
 induction t with
  | leaf n =>
    split
    case left =>
      dsimp [Chapter3.Tree.height, Chapter3.Tree.size]
      exact nat.le_refl 1
    case right =>
      dsimp [Tree.height, Tree.size]
      exact nat.lt_succ_self 1
  | node n t₁ t₂ =>
    cases ih_t₁ with | intro ih_t₁_height ih_t₁_size
    cases ih_t₂ with | intro ih_t₂_height ih_t₂_size
    split
    case left =>
      dsimp [Tree.height, Tree.size]
      exact nat.succ_le_of_lt (max_le ih_t₁_height ih_t₂_height)
    case right =>
      dsimp [Tree.height, Tree.size]
      calc
        n < 2 ^ (1 + max t₁.height t₂.height) : by linarith [ih_t₁_size, ih_t₂_size]
        _ = 2 ^ t.height : by rw max_comm

end Chapter3
-/

-- # Exercise 4.9

def partition {α : Type} (p : α → Bool) : List α → List α × List α :=
  let op (x : α) (r : List α × List α) :=
   if p x then (x :: r.1, r.2) else (r.1, x :: r.2)
  List.foldr op ([], [])


-- # Exercicio 4.10

namespace BST2

def partition3 [LT a]
 [DecidableRel (α := a) (· < ·)] [DecidableRel (α := a) (· = ·)]
 (y : a) (xs : List a) : (List a × List a × List a) :=
 let op x acc :=
   let (us, vs, ws) := acc
     if      x < y then (x :: us, vs, ws)
     else if x = y then (us, x :: vs, ws)
     else (us, vs, x :: ws)
 xs.foldr op ([], [], [])

partial def mkTree₂ : (xs : List Nat) → Tree (List Nat)
| [] => .null
| (x :: xs) =>
   match partition3 x (x :: xs) with
   | (us, vs, ws) => node (mkTree₂ us) vs (mkTree₂ ws)


end BST2

/- # Exercicio 4.13 -/

namespace DSet

def merge [LT a] [DecidableEq a] [DecidableRel (α := a) (· < ·)]
  : List a → List a → List a
  | [], ys => ys
  | xs, [] => xs
  | (x :: xs), (y :: ys) =>
    if x < y then x :: merge xs (y :: ys)
    else if x = y then x :: merge xs ys
    else y :: merge (x :: xs) ys

end DSet


/- # Exercicio 4.14 -/

namespace DSet
open BST2 (Tree insert node)

def union₁ [LT a] [DecidableRel (α := a) (· < ·)]
  (t₁ t₂ : Set a) : Set a :=
  List.foldr insert t₁ (Tree.flatten t₂)

partial def frm [Inhabited a] (l r : Nat) (xa : Array a) : Set a :=
  if l = r then .null
  else
   let m := (l + r) / 2
   node (frm l m xa) xa[m]! (frm (m + 1) r xa)

def build [Inhabited a] [LT a] [DecidableRel (α := a) (· < ·)]
  (xs : List a) : Set a :=
  frm 0 xs.length xs.toArray

def union₂ [Inhabited a] [LT a] [DecidableEq a] [DecidableRel (α := a) (· < ·)]
  (t₁ t₂ : Set a) : Set a :=
  build $ merge (Tree.flatten t₁) (Tree.flatten t₂)

-- #eval union₂ (BST2.mkTree [1,2,3]) (BST2.mkTree [4,2,6]) |>.flatten

end DSet


-- # Exercicio 4.16

-- See Chapter4.lean

-- # Exercicio 4.17

namespace DSet
open BST2

def pair {α β : Type} (f : α -> β) (p : α × α) : (β × β) := (f p.1, f p.2)

def split {α : Type} [LT α] [LE α]
  [DecidableRel (α := α) (· < ·)]
  [DecidableRel (α := α) (· ≤ ·)]
  (x : α) : Set α → Set α × Set α :=
  pair mkTree ∘ List.partition (· ≤ x) ∘ Tree.flatten


end DSet

end Chapter4
