import Fad.Chapter1

namespace Assignment02

/- ## Exercise 1.9

Escreva a definições em Lean dos códigos alternativos de foldr e foldl.

Response: See Chapter1-Ex.lean
-/


/- ## Exercise 1.12

pode-se completar as equações. Apresente as mesmas como `example` abaixo.

Response: See Chapter1-Ex.lean
-/

/- ## Question L.1: Snoc

Define the function `snoc` that appends a single element to the
end of a list. Your function should be defined by recursion and not using `++`
(`List.append`). -/

def snoc {α : Type} : List α → α → List α
 | [], n => [n]
 | m :: ms, n => m :: snoc ms n

-- #eval snoc [1] 2


/- ## Question L.2: Sum

Define a `sum` function that computes the sum of all the numbers
in a list. -/

def sum : List Nat → Nat :=
  List.foldr (fun n acc => n + acc) 0

-- #eval sum [1, 12, 3]

/- State (without proving them) the following properties of `sum` as theorems.
   Schematically:

     sum (snoc ms n) = n + sum ms
     sum (ms ++ ns) = sum ms + sum ns
     sum (reverse ns) = sum ns

Try to give meaningful names to your theorems. Use `sorry` as the proof. -/

theorem sum_snoc (ms : List Nat) (n : Nat) :
  sum (snoc ms n) = n + sum ms := by
  unfold sum
  induction ms with
  | nil =>
    simp [snoc, sum]
  | cons m ms ih =>
    simp[snoc, ih]
    rw [<- Nat.add_assoc, Nat.add_comm m n, Nat.add_assoc]

-- sum (ms ++ ns) = sum ms + sum ns --

theorem foldr_append (f : α → β → β) (e : β) (xs ys : List α) :
  List.foldr f e (xs ++ ys) = List.foldr f (List.foldr f e ys) xs := by
  induction xs with
  | nil => simp [List.foldr]
  | cons x xs hd => simp [List.foldr]

theorem sum_append (ms ns : List Nat) :
  sum (ms ++ ns) = sum ms + sum ns := by
  unfold sum
  induction ms with
  | nil =>
    simp [sum, List.foldr]
  | cons m ms ih =>
    simp[sum]
    rw [<- foldr_append, ih, Nat.add_assoc]

-- sum (reverse ns) = sum ns --

theorem snoc_eq_append (xs : List Nat) (x : Nat) :
  snoc xs x = xs ++ [x] := by
  induction xs with
  | nil => simp [snoc]
  | cons y ys ih =>
    simp [snoc]
    exact ih

theorem sum_cons (n : Nat) (ns : List Nat) :
  sum (n :: ns) = n + sum ns := by
  unfold sum
  simp [List.foldr]

theorem sum_reverse (ns : List Nat) :
  sum (ns.reverse) = sum ns := by
  induction ns with
  | nil => simp [sum]
  | cons n ns ih =>
    rw [List.reverse_cons]
    rw [← snoc_eq_append, sum_snoc, sum_cons, ih]


/- ## Question L.3

State (without proving them) the so-called functorial properties of `map` as theorems.
Schematically:

     map (fun x ↦ x) xs = xs
     map (fun x ↦ g (f x)) xs = map g (map f xs)

Try to give meaningful names to your theorems. Also, make sure to state the
second property as generally as possible, for arbitrary types. -/

theorem map_id {a : Type} (xs : List a) : xs.map (fun x ↦ x) = xs := by
  induction xs with
  | nil =>
    simp [List.map]
  | cons x xs ih =>
    simp [List.map, ih]
    done

theorem map_map {a b c : Type} (xs : List a) (f : a → b) (g : b → c) :
  xs.map (fun x ↦ g (f x)) = (xs.map f).map g := by
  funext
  induction xs with
  | nil => repeat rw [List.map_nil]
  | cons a as ih =>
    repeat rw [List.map_cons]
    rw [ih]

/- ## Question L.4 Arithmetic Expressions

Consider the type `AExp` below

-/

inductive AExp : Type where
  | num : Int → AExp
  | var : String → AExp
  | add : AExp → AExp → AExp
  | sub : AExp → AExp → AExp
  | mul : AExp → AExp → AExp
  | div : AExp → AExp → AExp

def eval (env : String → Int) : AExp → Int
  | AExp.num i     => i
  | AExp.var x     => env x
  | AExp.add e₁ e₂ => eval env e₁ + eval env e₂
  | AExp.sub e₁ e₂ => eval env e₁ - eval env e₂
  | AExp.mul e₁ e₂ => eval env e₁ * eval env e₂
  | AExp.div e₁ e₂ => eval env e₁ / eval env e₂

-- #eval eval (fun x ↦ 7) (AExp.div (AExp.var "x") (AExp.num 0))

/- Test that `eval` behaves as expected. Make sure to exercise each
constructor at least once. You can use the following environment in your tests.
What happens if you divide by zero?

Note that `#eval` (Lean's evaluation command) and `eval` (our evaluation
function on `AExp`) are unrelated. -/

def someEnv : String → Int
  | "x" => 3
  | "y" => 17
  | _   => 201

-- #eval eval someEnv (AExp.var "x")   -- expected: 3

/- The following function simplifies arithmetic expressions involving
addition. It simplifies `0 + e` and `e + 0` to `e`. Complete the definition so
that it also simplifies expressions involving the other three binary
operators. -/

def simplify : AExp → AExp
  | AExp.add (AExp.num 0) e₂ => simplify e₂
  | AExp.add e₁ (AExp.num 0) => simplify e₁
  | AExp.mul (AExp.num 1) e₂ => simplify e₂
  | AExp.mul e₁ (AExp.num 1) => simplify e₁
  | AExp.mul _ (AExp.num 0) => (AExp.num 0)
  | AExp.mul (AExp.num 0) _ => (AExp.num 0)
  | AExp.div e₁ (AExp.num 1) => simplify e₁
  | AExp.div (AExp.num 0) _ => (AExp.num 0)
  | AExp.sub e₁ (AExp.num 0) => simplify e₁
  | AExp.sub (AExp.num 0) e₂ => AExp.mul (AExp.num (-1)) (simplify e₂)
  | AExp.num i               => AExp.num i
  | AExp.var x               => AExp.var x
  | AExp.add e₁ e₂           => AExp.add (simplify e₁) (simplify e₂)
  | AExp.sub e₁ e₂           => AExp.sub (simplify e₁) (simplify e₂)
  | AExp.mul e₁ e₂           => AExp.mul (simplify e₁) (simplify e₂)
  | AExp.div e₁ e₂           => AExp.div (simplify e₁) (simplify e₂)


/- Is the `simplify` function correct? In fact, what would it mean for it
to be correct or not? Intuitively, for `simplify` to be correct, it must
return an arithmetic expression that yields the same numeric value when
evaluated as the original expression.

Given an environment `env` and an expression `e`, state (without proving it)
the property that the value of `e` after simplification is the same as the
value of `e` before. -/

theorem simplify_correct (env : String → Int) (e : AExp)
 : eval env (simplify e) = eval env e := by
induction e with
| num i =>
  simp [simplify]
| var x =>
  simp [simplify]
| add e₁ e₂ ih₁ ih₂ =>
  if h₁: e₁ = AExp.num 0 then
    rw [h₁]
    simp [simplify, ih₂, eval]
  else if h₂ : e₂ = AExp.num 0 then
    rw [h₂]
    simp [simplify, ih₁, eval]
  else
    simp [simplify, eval, ih₁, ih₂]
| sub e₁ e₂ ih₁ ih₂ =>
  if h₁: e₂ = AExp.num 0 then
    rw [h₁]
    simp [simplify, ih₁, eval]
  else if h₂: e₁ = AExp.num 0 then
    rw [h₂]
    simp [simplify, ih₂, eval]
  else
    simp [simplify, eval, ih₁, ih₂]
| mul e₁ e₂ ih₁ ih₂ =>
  if h₁: e₁ = AExp.num 1 then
    rw [h₁]
    simp [simplify, eval, ih₂]
  else if h₂ : e₂ = AExp.num 1 then
    rw [h₂]
    simp [simplify, eval, ih₁]
  else if h₃ : e₂ = AExp.num 0 then
    rw [h₃]
    simp [simplify, eval]
  else if h₄ : e₁ = AExp.num 0 then
    rw [h₄]
    simp [simplify, eval]
  else
    simp [simplify, eval, ih₁, ih₂]
| div e₁ e₂ ih₁ ih₂ =>
  if h₁ : e₂ = AExp.num 1 then
    rw [h₁]
    simp [simplify, eval, ih₁]
  else if h₂ : e₁ = AExp.num 0 then
    rw [h₂]
    simp [simplify, eval]
  else
    simp [simplify, eval, ih₁, ih₂]


end Assignment02
