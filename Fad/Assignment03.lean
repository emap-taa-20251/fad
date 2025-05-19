import Fad.Chapter3
import Fad.Chapter1

namespace Assignment03

def compress (s : String) : List (Nat × Nat) :=
  help (s.toList.map (·.toNat - '0'.toNat)) []
 where
  help : List Nat → List (Nat × Nat) → List (Nat × Nat)
  | []     , acc      => acc.reverse
  | x :: xs, []       => help xs [(x, 1)]
  | x :: xs, p :: acc =>
    if x = p.1
    then help xs ((p.1, p.2 + 1) :: acc)
    else help xs ((x, 1) :: p :: acc)

-- #eval compress "1333332222211" -- returns [(1, 1), (3, 5), (2, 5), (1, 2)]

def uncompress : List (Nat × Nat) → String :=
  let h (xs : List Nat) := xs.foldr (λ a r => s!"{a}{r}") ""
  List.foldr (λ p r => h (List.replicate p.2 p.1) ++ r) ""

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

example : ∀ sl : SymList a,
  List.reverse sl.fromSL = sl.reverse.fromSL := sorry


/-
Em vez de basicamente duplicar o código para as funções no elemento
da frente e as funções no elemento de trás, poderíamos definir as
funções no elemento de trás em termos de reverse e das funções
correspondentes no elemento da frente.

Defina `init` como uma expressão usando `tailSL` e `SymList.reverse`?
-/

def SymList.init (q : SymList a) : SymList a  :=
  q.reverse.tailSL.reverse

-- #eval [1,2,3].toSL |>.init |>.fromSL -- returns [1,2]

def List.init {α : Type} : List α → List α
  | []      => []
  | [_]     => []
  | x :: xs => x :: init xs

/- agora tente completar a prova seguinte -/

example : ∀ sl : SymList a,
  List.init sl.fromSL = sl.init.fromSL := sorry
