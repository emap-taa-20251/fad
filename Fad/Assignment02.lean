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

def snoc {α : Type} : List α → α → List α :=
  sorry

/- Convince yourself that your definition of `snoc` works by
testing it on a few examples. -/

-- #eval snoc [1] 2
-- invoke `#eval` or `#reduce` here


/- ## Question L.2: Sum

Define a `sum` function that computes the sum of all the numbers
in a list. -/

def sum : List Nat → Nat :=
  sorry

-- #eval sum [1, 12, 3]   -- expected: 16

/- State (without proving them) the following properties of `sum` as theorems.
   Schematically:

     sum (snoc ms n) = n + sum ms
     sum (ms ++ ns) = sum ms + sum ns
     sum (reverse ns) = sum ns

Try to give meaningful names to your theorems. Use `sorry` as the proof. -/

-- enter your theorem statements here


/- ## Question L.3

State (without proving them) the so-called functorial properties of `map` as theorems.
Schematically:

     map (fun x ↦ x) xs = xs
     map (fun x ↦ g (f x)) xs = map g (map f xs)

Try to give meaningful names to your theorems. Also, make sure to state the
second property as generally as possible, for arbitrary types. -/

-- enter your theorem statements here


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

#eval eval (fun x ↦ 7) (AExp.div (AExp.var "y") (AExp.num 0))

/- Test that `eval` behaves as expected. Make sure to exercise each
constructor at least once. You can use the following environment in your tests.
What happens if you divide by zero?

Note that `#eval` (Lean's evaluation command) and `eval` (our evaluation
function on `AExp`) are unrelated. -/

def someEnv : String → Int
  | "x" => 3
  | "y" => 17
  | _   => 201

#eval eval someEnv (AExp.var "x")   -- expected: 3

/- The following function simplifies arithmetic expressions involving
addition. It simplifies `0 + e` and `e + 0` to `e`. Complete the definition so
that it also simplifies expressions involving the other three binary
operators. -/

def simplify : AExp → AExp
  | AExp.add (AExp.num 0) e₂ => simplify e₂
  | AExp.add e₁ (AExp.num 0) => simplify e₁
  -- insert the missing cases here
  -- catch-all cases below
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

theorem simplify_correct (env : String → ℤ) (e : AExp) :
  True := sorry   -- replace `True` by your theorem statement


end Assignment02
