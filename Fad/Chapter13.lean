import Fad.Chapter1
import Fad.API

namespace Chapter13
open Chapter1 (scanr₀)


-- # Section 13.1 Two numeric examples

def fib₀ : Nat → Int
| 0 => 0
| 1 => 1
| n + 2 => fib₀ (n + 1) + fib₀ n

def fib₀T : Nat → TimeM Int
| 0     => TimeM.pure 0
| 1     => TimeM.pure 1
| n + 2 => do
    let x ← fib₀T (n + 1)
    let y ← fib₀T n
    ✓ (x + y)

-- #eval fib₀ 10
-- #eval fib₀T 10
-- The complexity is exponential
-- #eval [5, 10, 15, 20].map fun n => (n, (fib₀T n).time)

-- Haskell is a lazy language so we will append another tab function using thunk to get the O(n) complexity
private def badDependency [Inhabited α] : Thunk α :=
  Thunk.mk fun _ => panic! "undefined lazy-array entry"

def tabulate [Inhabited α]
    (f : (Nat → Thunk α) → Nat → Thunk α)
    (bounds : Nat × Nat) : Array (Thunk α) :=
  let (lo, hi) := bounds
  if hi < lo then
    #[]
  else
    (List.range (hi - lo + 1)).foldl
      (fun cells k =>
        let i := lo + k
        let fetch := fun j =>
          match cells[j - lo]? with
          | some cell => cell
          | none      => badDependency
        cells.push (f fetch i))
      #[]

def tabulateT [Inhabited α]
    (f : (Nat → Thunk α) → Nat → Thunk α)
    (bounds : Nat × Nat) : TimeM (Array (Thunk α)) :=
  let (lo, hi) := bounds
  if hi < lo then
    TimeM.pure #[]
  else
    (List.range (hi - lo + 1)).foldl
      (fun timedCells k => do
        let cells ← timedCells
        let i := lo + k
        let fetch := fun j =>
          match cells[j - lo]? with
          | some cell => cell
          | none      => badDependency
        ✓ (cells.push (f fetch i)))
      (TimeM.pure #[])

private def forceAt [Inhabited α]
    (cells : Array (Thunk α)) (bounds : Nat × Nat) (i : Nat) : α :=
  let (lo, _) := bounds
  match cells[i - lo]? with
  | some cell => cell.get
  | none      => panic! "index outside lazy-array bounds"


-- Lazy tabulation, corresponding to `a = tabulate f (0,n)` in the book.
private def fibF (a : Nat → Thunk Int) (i : Nat) : Thunk Int :=
  if i ≤ 1 then
    Thunk.mk fun _ => Int.ofNat i
  else
    let previous := a (i - 1)
    let beforePrevious := a (i - 2)
    Thunk.mk fun _ => previous.get + beforePrevious.get

def fib₁ (n : Nat) : Int :=
  let bounds := (0, n)
  let a := tabulate fibF bounds
  forceAt a bounds n

def fib₁T (n : Nat) : TimeM Int := do
  let bounds := (0, n)
  let a ← tabulateT fibF bounds
  TimeM.pure (forceAt a bounds n)

--#eval fib₁ 10
--#eval fib₁T 10
-- The complexity is O(n)
--#eval [10, 20, 40, 80].map fun n => (n, (fib₁T n).time)

def fib₂ (n : Nat) : Int :=
  let step := fun (a b : Int) => (b, a + b)
  let rec apply : Nat → Int × Int → Int × Int
    | 0, p => p
    | n+1, (a, b) => apply n (step a b)
  let (a, _) := apply n (0, 1)
  a

def fib₂T (n : Nat) : TimeM Int :=
  let step := fun (a b : Int) => (b, a + b)
  let rec applyT : Nat → Int × Int → TimeM (Int × Int)
    | 0, p          => TimeM.pure p
    | k + 1, (a, b) => do
        let next ← (✓ (step a b))
        applyT k next
  do
    let (a, _) ← applyT n (0, 1)
    TimeM.pure a

--#eval fib₂ 10
--#eval fib₂T 10
-- The complexity is O(n)
--#eval [10, 20, 40, 80].map fun n => (n, (fib₂T n).time)

def fact (n : Nat) : Int :=
  ((List.range (n + 1)).drop 1).map Int.ofNat |>.foldl (· * ·) 1

private def productT : List Int → TimeM Int
| []      => TimeM.pure 1
| x :: xs => do
    let p ← productT xs
    ✓ (x * p)

def factT (n : Nat) : TimeM Int :=
  productT (((List.range (n + 1)).drop 1).map Int.ofNat)


def bin₀ (n r : Nat) : Int :=
  fact n / (fact r * fact (n - r))

def bin₀T (n r : Nat) : TimeM Int :=
  if r > n then
    TimeM.pure 0
  else do
    let fn ← factT n
    let fr ← factT r
    let fnr ← factT (n - r)
    let denominator ← (✓ (fr * fnr))
    ✓ (fn / denominator)

--#eval bin₀ 6 3
--#eval bin₀T 6 3
--#eval [10, 20, 40, 80].map fun n =>((n, n / 2), (bin₀T n (n / 2)).time)

def bin₁ : Nat → Nat → Int
| _, 0               => 1
| 0, _           => 0
| n + 1, r + 1       =>
  if r + 1 = n + 1 then 1
  else bin₁ n (r + 1) + bin₁ n r

def bin₁T : Nat → Nat → TimeM Int
| _, 0         => TimeM.pure 1
| 0, _         => TimeM.pure 0
| n + 1, r + 1 =>
  if r + 1 = n + 1 then
    TimeM.pure 1
  else do
    let x ← bin₁T n (r + 1)
    let y ← bin₁T n r
    ✓ (x + y)

--#eval bin₁ 6 3
--#eval bin₁T 6 3


def bin₂ (n r : Nat) : Int := Id.run do
  let mut a : Array ((Nat × Nat) × Int) := #[]
  for i in [0:n+1] do
    for j in [0:Nat.min (r + 1) (i + 1)] do
      let value :=
        if j = 0 ∨ i = j then 1
        else
          let get := fun i j =>
            (a.find? (fun (x, _) => x = (i, j))).map Prod.snd |>.getD 0
          get (i - 1) j + get (i - 1) (j - 1)
      a := a.push ((i, j), value)
  return (a.find? (fun (x, _) => x = (n, r))).map Prod.snd |>.getD 0

--#eval bin₂ 6 3

def apl {α : Type} : Nat → (List α → List α) → List α → List α
| 0, _, acc => acc
| n + 1, f, acc => apl n f (f acc)

def bin₃ (n r : Nat) : Int :=
  let row := apl (n - r) (scanr₀ (· + ·) 0) (List.replicate (r + 1) 1)
  row.headD 1

--#eval bin₃ 6 3

end Chapter13
