import Fad.Chapter3
import Fad.Chapter4
import Fad.Chapter5

/- # Ex 1

implementar as modificações necessárias no Chapter4.BST para que
listas com valores repetidos sejam processadas corretamente criando
uma arvore balanceada sem perda dos valores repetidos. Vc deve mostrar
que

(sort xs).length = xs.length

Seu código ficará dentro do namespace Chapter4.BST

-/

section
open Chapter4.BST2 (search mkTree₁ sort Tree.flatten)

variable {a : Type} [LT a] [BEq a] [Hashable a]
  [DecidableRel (α := a) (· < ·)]

def compress (xs : List a) : List (a × Nat) :=
  let as := Std.HashMap.emptyWithCapacity
  let counts := xs.foldl (init := as) fun acc x =>
    if acc.contains x then
     acc.modify x (· + 1)
    else
     acc.insert x 1
  counts.toList

def uncompress : List (a × Nat) → List a :=
 List.foldr (λ p r => (List.replicate p.2 p.1) ++ r) []

instance : LT (a × Nat) where
  lt x y := x.1 < y.1

def sort₁ : List a → List a :=
  uncompress ∘ Tree.flatten ∘ mkTree₁ ∘ compress

#eval sort₁ [10,20,20,45,60,78,10,67]

example : ∀ xs : List Nat, xs.length = (sort₁ xs).length := by
  intro xs
  induction xs with
  | nil =>
    simp [sort₁, compress, mkTree₁,
     Chapter4.BST2.Tree.null, Tree.flatten,
     Chapter4.BST2.insert₁, List.foldr]
    sorry
  | cons n ns h =>
    rw [List.length_cons, h]
    unfold sort₁
    sorry

end

/- # Ex 2

Considere a estrutura

structure Book where
  title : String
  price : Float
 deriving Repr

Implemente as instâncias necessárias de `Book` para que uma lista de
livros possa ser ordenada por `price` (usando
`Chapter5.Quicksort.qsort₂`) e pesquisada por `title` usando a
`Chapter4.BST2.search`.

-/


/-
section

structure Point (a : Type) where
  x : a
 deriving Repr

instance {a : Type} [LT a] : LT (Point a) where
 lt a b := a.x < b.x

#eval "as" < "bs"
#check (Point.mk "1")
#eval (Point.mk "1") < (Point.mk "3")

end
-/


section
open Chapter5.Quicksort (qsort₂)
open Chapter4.BST2 (search mkTree mkTree₁ mkTree₂)

structure Book where
  title : String
  price : Float
 deriving Repr

instance : ToString Book where
  toString b := s!"B {b.title} {b.price}"

instance : LT Book where
  lt a b := a.price < b.price

instance : DecidableRel (fun (a b : Book) => a < b) :=
  fun a b => Float.decLt a.price b.price

def books := List.range 12
  |>.map (λ n => Book.mk s!"{n}" n.toFloat)

/- Both `search` and `mkTree₁` need to use the same field for
   insertion and lookup.-/

instance : Ord Float where
  compare a b :=
    if      a < b then Ordering.lt
    else if a > b then Ordering.gt
    else Ordering.eq

/-
#eval
  let tb := mkTree₂ (·.price) books
  search (·.price) 10 tb
-/

end


/- # Ex 3

Escolha uma das seções a seguir para desenvolver, anuncie sua escolha
no fórum do curso (como comentário no anúncio deste assignment) para
evitarmos alunos trabalhando na mesma seção.

Para todas as seções, ver também exercícios relacionados à seção no
mesmo capítulo e fazer, indicando com comentários o número do
exercício.

opções de seções:

- 4.2 A two-dimensional search problem : o código final da figura 4.4
  está incompleto.

- 4.4 Dynamic sets : o código está incompleto.

- 5.3 Heapsort : confirmar se códigos estão completos.

- 5.4 Bucketsort and Radixsort

- 5.5 Sorting sums

- 6.2 Selection from one set

- 6.3 Selection from two sets

- 6.4 Selection from the complement of a set

- 7.4 Decimal fractions in TEX

-/

-- ## Section 5.4 Bucketsort and Radixsort

namespace Bucketsort

variable {α: Type}

inductive Tree (α : Type)
| leaf : α → Tree α
| node : List (Tree α) → Tree α
deriving Repr

def ptn₀ {β : Type} [BEq β] (rng : List β)
  (f : α → β) (xs : List α) : List (List α) :=
  rng.map (λ b => xs.filter (λ x => f x == b))

def mktree {β : Type} [BEq β]
  (rng : List β)
  (ds : List (α → β)) (xs : List α) : Tree (List α) :=
  match ds with
  | []       => .leaf xs
  | d :: ds' =>
    .node (List.map (mktree rng ds') (ptn₀ rng d xs))

def Tree.flatten (r : Tree (List α)) : List α :=
 match r with
 | .leaf v  => v
 | .node ts =>
   List.flatten <| ts.map flatten

def bsort₀ {β : Type} [BEq β]
  (rng : List β) (ds : List (α → β)) (xs : List α) : List α :=
  Tree.flatten (mktree rng ds xs)

/-
#eval bsort₀ "abc".toList
      [fun s => s.toList[0]!,fun s => s.toList[1]!]
      ["ba", "ab", "aab", "bba"]
-/

def bsort₁ {β : Type} [BEq β]
  (rng : List β) (ds : List (α → β)) (xs : List α) : List α :=
  match ds with
  | [] => xs
  | d :: ds' =>
    List.flatten <| List.map (bsort₁ rng ds') (ptn₀ rng d xs)

-- bsort₀ = bsort₁

theorem bsort_eq_bsort {β : Type} [BEq β]
 (rng : List β) (ds : List (α → β)): bsort₀ rng ds = bsort₁ rng ds := by
 induction ds with
 | nil =>
  funext xs
  simp [bsort₀, bsort₁, mktree, Tree.flatten]
 | cons d ds ih =>
  funext xs
  simp [bsort₀, mktree, Tree.flatten, bsort₁]
  simp [bsort₀] at ih
  rw [<- ih]
  congr 1

-- # Exercício 5.18

def tmap {β : Type} (f : α → β) : Tree α → Tree β
| .leaf x => .leaf (f x)
| .node ts => .node (ts.map (tmap f))

-- Claim da comutação de filters

theorem filter_comm {α: Type} (p q : α → Bool) (xs : List α) :
  (xs.filter p).filter q = (xs.filter q).filter p := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.filter_cons]
    split <;> split <;> simp_all

-- (5.6)

theorem ptn_filter_comm
  {β : Type} [BEq β]
  (rng : List β) (d : α → β) (p : α → Bool) (xs : List α) :
  List.map (List.filter p) (ptn₀ rng d xs) = ptn₀ rng d (xs.filter p) := by
  simp  [ptn₀]
  intro a ha
  apply List.filter_congr
  intro x hx
  rw [Bool.and_comm]

-- (5.4)

theorem mktree_filter_comm
  {β : Type} [BEq β]
  (rng : List β) (ds : List (α → β)) (p : α → Bool) :
  (mktree rng ds) ∘ (List.filter p) = tmap (List.filter p) ∘ (mktree rng ds) := by
  induction ds with
  | nil =>
    funext xs
    simp [mktree, tmap]
  | cons d ds ih =>
    funext xs
    simp [mktree]
    rw [<- ptn_filter_comm]
    simp[ih, tmap]

-- Claim do Filter e Concat

theorem map_filter_concat_eq_filter_concat
  (p : α → Bool) :
  (List.map (List.filter p) xss).flatten = List.filter p (xss.flatten):= by
  induction xss with
  | nil =>
    simp [List.flatten, List.map, List.foldr]
  | cons xs xss ih =>
    simp [List.flatten, List.map, List.foldr]

-- Auxiliares para a prova por indução de (5.5)

def Tree.size {α : Type} : Tree α → Nat
| leaf _ => 1
| node ts => 1 + (List.map (Tree.size) ts).sum

theorem size_in_list {α : Type} (t : Tree α) (ts : List (Tree α))
    (h : t ∈ ts) : t.size < (Tree.node ts).size := by
  simp [Tree.size, List.foldl]
  induction ts with
  | nil => contradiction
  | cons t' ts ih =>
    simp [List.map]
    simp [List.mem_cons] at h
    cases h with
    | inl h_eq =>
    simp [h_eq]
    rw [Nat.add_comm]
    apply Nat.lt_succ_of_le
    apply Nat.le_add_right
    | inr h_tail =>
    have h_aux₁: t.size < 1 + (List.map Tree.size ts).sum := by simp [ih, h_tail]
    have h_aux₂: t.size < 1 + (t'.size + (List.map Tree.size ts).sum) := by
      apply Nat.lt_of_lt_of_le h_aux₁
      apply Nat.add_le_add_left
      exact Nat.le_add_left _ _
    exact h_aux₂

-- (5.5)

theorem flatten_tmap_filter_eq_filter_flatten
  (p : α → Bool):
  (Tree.flatten ∘ tmap (List.filter p)) = List.filter p ∘ Tree.flatten := by
  funext t
  rw [Function.comp_apply, Function.comp_apply]
  induction h : t.size using Nat.strong_induction_on generalizing t with
  | h k ih =>
    cases t with
    | leaf xs => simp [Tree.flatten, tmap]
    | node ts =>
      simp only [Tree.flatten, tmap]
      rw [<- map_filter_concat_eq_filter_concat]
      congr 1
      simp only [List.map_map]
      cases ts with
      | nil => simp
      | cons t' ts' =>
        simp only [List.map]
        congr 1
        case cons.e_head =>
          apply ih t'.size
          rw [<- h]
          apply size_in_list
          apply List.Mem.head
          rfl
        case cons.e_tail =>
          simp
          intro t'' h'
          apply ih t''.size
          rw [<- h]
          have h_aux₁: t''.size < (Tree.node ts').size := by
            apply size_in_list
            exact h'
          simp [Tree.size] at h_aux₁
          simp [Tree.size]
          have h_aux₂: 1 + (List.map Tree.size ts').sum ≤ 1 + (t'.size + (List.map Tree.size ts').sum) := by
            rw [Nat.add_le_add_iff_left]
            apply Nat.le_add_left
          apply Nat.lt_of_lt_of_le h_aux₁ h_aux₂
          rfl

theorem flatten_tmap_filter_eq_filter_flatten₁
  (p : α → Bool):
  (tmap (List.filter p) t).flatten = List.filter p (Tree.flatten t) := by
  cases t with
  | leaf xs => simp [Tree.flatten, tmap]
  | node ts =>
    simp only [Tree.flatten, tmap]
    rw [<- map_filter_concat_eq_filter_concat]
    simp only [List.map_map]
    rw [flatten_tmap_filter_eq_filter_flatten]

-- (5.3)

theorem bsort_partition_comm
  {α β : Type} [BEq β]
  (rng : List β) (ds : List (α → β)) (d : α → β) (xs : List α) :
  (List.map (bsort₀ rng ds) (ptn₀ rng d xs)) = ptn₀ rng d (bsort₀ rng ds xs) := by
  simp [bsort₀, ptn₀]
  intro a ha
  rw [← Function.comp_apply (f := mktree rng ds), mktree_filter_comm,
      Function.comp_apply (g := mktree rng ds),
      ← Function.comp_apply (f := Tree.flatten),
      flatten_tmap_filter_eq_filter_flatten]
  simp

def rsort₀ {β : Type} [BEq β] (rng : List β) (ds : List (α → β)) (xs : List α) : List α :=
  match ds with
  | [] => xs
  | d :: ds' => List.flatten (ptn₀ rng d (rsort₀ rng ds' xs))

-- rsort₀ = bsort₁ = bsort₀

theorem rsort_eq_bsort {β : Type} [BEq β]
  (rng : List β) (ds : List (α → β)): rsort₀ rng ds = bsort₁ rng ds := by
  induction ds with
  | nil =>
    funext xs
    simp [rsort₀, bsort₁]
  | cons d ds' ih =>
    funext xs
    simp [rsort₀, bsort₁]
    rw [<- bsort_eq_bsort] at ih
    rw [<- bsort_eq_bsort, bsort_partition_comm, ih]

open Chapter3

def ptn₁ {α: Type} (r : Nat) (d : α → Nat) (xs : List α) : List (List α) :=
  let buckets := accumArray (flip List.cons) [] r (List.zip (xs.map d) xs)
  buckets.toList.map List.reverse

def rsort₁ {α: Type} (r : Nat) (ds : List (α → Nat)) (xs : List α) : List α :=
  match ds with
  | [] => xs
  | d :: ds' => List.flatten (ptn₁ r d (rsort₁ r ds' xs))

/-
#eval rsort₁ 26
      [fun s => s.toList[0]!.toNat - 'a'.toNat,
      fun s => s.toList[1]!.toNat  - 'a'.toNat]
      ["ba", "ab", "aab", "bba"]
-/

def pad (k : Nat) (s : String) : String :=
  List.foldl (· ++ ·) "" (List.replicate (k - s.length) "0") ++ s

def discs (xs : List Nat) : List (Nat → Nat) :=
  let k := (xs.map (λ x => (toString x).length)).foldr max 0
  List.range k |>.map (λ i => λ n =>
    let s := pad k (toString n)
    s.toList[i]! |>.toNat - '0'.toNat)

def insort (xs : List Nat) : List Nat :=
  rsort₁ 10 (discs xs) xs

/-
#eval insort [42, 7, 13, 105, 0, 99, 4, 300]
-/
