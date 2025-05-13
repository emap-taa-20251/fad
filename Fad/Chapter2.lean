import Fad.Chapter1
import Fad.«Chapter1-Ex»
import Lean

namespace Chapter2
open Chapter1 (dropWhile)

-- # 2.0 Complexity

def fib : Nat → Nat
  | 0     => 1
  | 1     => 1
  | n + 2 => fib (n + 1) + fib n

def fibFast (n : Nat) : Nat :=
  (loop n).2
where
  loop : Nat → Nat × Nat
  | 0   => (0, 1)
  | n+1 => let p := loop n; (p.2, p.1 + p.2)

/-
#eval fibFast 100
#reduce fib 100 -- try eval
#print fib
-/

example : fibFast 4 = 5 := by
  unfold fibFast
  unfold fibFast.loop
  unfold fibFast.loop
  unfold fibFast.loop
  unfold fibFast.loop
  unfold fibFast.loop
  rfl


-- # 2.2 Estimating running times

/-
#eval List.append [1,2,3] [4,5,6]
#eval List.head! (List.iota 1000)
-/

def concat₀ : List (List a) → List a
 | [] => []
 | (xs :: xss) => xs ++ concat₀ xss

def concat₁ (xss : List (List a)) : List a :=
 -- dbg_trace "concat₁ with {xss.length}"
 match xss with
  | [] => []
  | (xs :: xss) => xs ++ concat₁ xss

/-
#eval concat₁ [[1, 2], [3, 4], [5, 6]]

#eval timeit "concat₁" (pure $
  Chapter1.concat₁
   (List.replicate 2000 <| List.replicate 100 1) |>.length)

#eval timeit "concat₂" (pure $
  Chapter1.concat₂
   (List.replicate 2000 <| List.replicate 100 1) |>.length)

-/

-- # 2.4 Amortised running times

def build (p : a → a → Bool) : List a → List a :=
 List.foldr insert []
 where
  insert x xs := x :: dropWhile (p x) xs

example : build (· = ·) [4,4,2,1,1] = [4, 2, 1] := by
 unfold build
 unfold List.foldr
 unfold List.foldr
 unfold List.foldr
 unfold List.foldr
 unfold List.foldr
 unfold build.insert
 rw [dropWhile]
 rw [dropWhile]
 rw [dropWhile]
 simp
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
