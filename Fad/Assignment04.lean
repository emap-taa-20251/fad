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
open Chapter4.BST2 (search mkTree mkTree₁)

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

def books := List.range 12 |>.map (λ n => Book.mk s!"{n}" n.toFloat)

#eval mkTree₁ books |>.toFormat

/- Both `search` and `mkTree₁` need to use the same field for
   insertion and lookup.-/

-- #eval mkTree₁ books
#eval search (fun x => x.title) "10" (mkTree₁ books)

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
