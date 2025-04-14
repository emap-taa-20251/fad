import Fad.Chapter1
import Fad.«Chapter1-Ex»

namespace Chapter2
open Chapter1 (dropWhile)

/-
#eval List.append [1,2,3] [4,5,6]
#eval List.head! (List.iota 1000)
-/

def concat₀ : List (List a) → List a
 | [] => []
 | (xs :: xss) => xs ++ concat₀ xss

def concat₁ (xss : List (List a)) : List a :=
 dbg_trace "concat₁ {xss.length}"
 match xss with
  | [] => []
  | (xs :: xss) => xs ++ concat₁ xss

-- #eval concat₁ [[1, 2], [3, 4], [5, 6]]


-- 2.4 Amortised running times

def build (p : a → a → Bool) : List a → List a :=
 List.foldr insert []
 where
  insert x xs := x :: dropWhile (p x) xs

-- #eval build (· = ·) [4,4,2,1,1,1,2,5]

example :
 build (fun x y => x = y) [4,4,2,1] = [4, 2, 1] := by
 unfold build
 unfold List.foldr
 unfold build.insert
 unfold List.foldr
 unfold dropWhile; simp
 rfl


/- primeiro argumento evita lista infinita -/
def iterate : Nat → (a → a) → a → List a
 | 0, _, x => [x]
 | Nat.succ n, f, x => x :: iterate n f (f x)

def bits (n : Nat) : List (List Bool) :=
  iterate n inc []
 where
   inc : List Bool → List Bool
   | [] => [true]
   | (false :: bs) => true :: bs
   | (true :: bs) => false :: inc bs


def init₀ : List α → List α
| []      => panic! "no elements"
| [_]     => []
| x :: xs => x :: init₀ xs

def init₁ : List α → Option (List α)
| []      => none
| [_]     => some []
| x :: xs =>
   match init₁ xs with
   | none => none
   | some ys => some (x :: ys)

def init₂ : List α → Option (List α)
| []      => none
| [_]     => some []
| x :: xs => init₂ xs >>= (fun ys => pure (x :: ys))

def prune (p : List a → Bool) (xs : List a) : List a :=
 List.foldr cut [] xs
  where
    cut x xs := Chapter1.until' done init₀ (x :: xs)
    done (xs : List a) := xs.isEmpty ∨ p xs

def ordered : List Nat → Bool
 | [] => true
 | [_] => true
 | x :: y :: xs => x ≤ y ∧ ordered (y :: xs)

-- #eval prune ordered [3,7,8,2,3]

end Chapter2
