import Fad.Chapter3
import Fad.Chapter1

namespace Assignment03

def compress (s : String) : List (Nat × Nat) := sorry

/-
#eval compress "1333332222211" -- returns [(1, 1), (3, 5), (2, 5), (1, 2)]
-/

def uncompress : List (Nat × Nat) → String := sorry

/-
#eval uncompress [(1, 1), (3, 5), (2, 5), (1, 2)] -- returns "1333332222211"
#eval let s := "1333332222211" ; uncompress (compress s) = s -- returns true
-/

end Assignment03


namespace Chapter3

variable {a : Type}

def SymList.reverse : SymList a → SymList a
 | ⟨as, bs, ok⟩ => ⟨bs, as, by exact And.intro ok.2 ok.1⟩

#eval List.toSL [1,2,3] |>.reverse |>.fromSL

/- qual a complexidade de SymList.reverse? -/

def answer₁ := "O(???)"

/- tente completar a prova -/

example : ∀ sl : SymList a,
  List.reverse sl.fromSL = sl.reverse.fromSL := sorry


/-
Em vez de basicamente duplicar o código para as funções no elemento
da frente e as funções no elemento de trás, poderíamos definir as
funções no elemento de trás em termos de reverse e das funções
correspondentes no elemento da frente.

Defina `init` como uma expressão usando outras funções sobre SymList
sem recorrer as sublistas?
-/

def SymList.init (q : SymList a) : SymList a := sorry

-- #eval [1,2,3].toSL |>.init |>.fromSL -- returns [1,2]


/- qual a complexidade de SymList.init? -/

def answer₂ := "O(???)"

def List.init {α : Type} : List α → List α
  | []      => []
  | [_]     => []
  | x :: xs => x :: init xs


/- agora tente completar a prova seguinte -/

example : ∀ sl : SymList a,
  List.init sl.fromSL = sl.init.fromSL := sorry
