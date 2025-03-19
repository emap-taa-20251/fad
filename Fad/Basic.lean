

def hello : String := "Hello world!"

def hello₂ (s : String) :=
 s!"Hello {s}!"


def factorial₀ (n : Nat) : Nat :=
  if n = 0 then
   1
  else
   n * factorial₀ (n - 1)


def factorial₁ (n : Nat) : Nat :=
  if n ≤ 0 then
   1
  else
   n * factorial₁ (n - 1)

-- #eval 2 - 3

def factorial₂ (n : Nat) : Nat :=
  if h : n == 0 then
   1
  else
   have : n - 1 < n := by
    induction n with
    | zero => contradiction
    | succ n ih => omega
   n * factorial₂ (n - 1)

def factorial₃ : Nat → Nat
| 0     => 1
| n + 1 => factorial₃ n * (n + 1)


/-
#eval factorial₁ 11
#eval factorial₂ 11
#eval factorial₃ 11
-/
