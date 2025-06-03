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

namespace Chapter4.BST2


end Chapter4.BST2

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

section
open Chapter5.Quicksort (qsort₂)
open Chapter4.BST2 (search mkTree mkTree₁)

structure Book where
  title : String
  price : Float
 deriving Repr

instance : LT Book where
  lt a b := a.title < b.title

instance : DecidableRel (fun (a b : Book) => a < b) :=
  fun a b => String.decidableLT a.title b.title

def books := List.range 100 |>.map (λ n => Book.mk s!"{n}" n.toFloat)

/- Both `search` and `mkTree₁` need to use the same field for
   insertion and lookup.-/

#eval mkTree₁ books
#eval search (·.title) "5" (mkTree₁ books)


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
