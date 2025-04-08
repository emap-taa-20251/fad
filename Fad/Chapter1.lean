
namespace Chapter1

-- ## Section 1.1 Basic types and functions

def map₁ (f : a → b) (xs : List a) : List b :=
 match xs with
 | [] => []
 | (x :: xs) => f x :: map₁ f xs

def map₂ : (a → b) → List a → List b
| _, [] => []
| f, (x :: xs) => f x :: map₂ f xs

def map (f : a → b) : List a → List b
| [] => []
| (x :: xs) => f x :: map f xs


-- #eval map (· + 10) [1,2,3]
example : map (· * 10) [1,2,3] = [10,20,30] := rfl


def makeInc (n : Nat) : (Nat → Nat) :=
  fun x => x + n

-- #eval (makeInc 10) 45

def filter {a : Type} (p : a → Bool) : List a → List a
| [] => []
| x :: xs => if p x then x :: filter p xs else filter p xs

example : filter (· > 5) [1,2,2,4,5,8,6] = [8,6] := rfl

-- #eval filter (λ x => x % 2 ≠ 0) [1,2,3,4,5,6,7,8,9,10]

def foldr {a b : Type} : (a → b → b) → b → List a → b
| _, e, [] => e
| f, e, (x::xs) => f x (foldr f e xs)

#eval foldr (λ x y => x + y) 0 [1,2,3]

example : foldr Nat.add 0 [1,2,3] = 6 := by
 unfold foldr
 unfold foldr
 unfold foldr
 unfold foldr
 rw [Nat.add]


example : ∀ xs : List α, foldr List.cons [] xs = xs := by
  intro xs
  induction xs with
  | nil =>
    rewrite [foldr.eq_1]
    rfl
  | cons a as ih =>
    rewrite [foldr]
    rewrite [ih]
    rfl


def label {α : Type} (xs : List α) : List (Nat × α) :=
  List.zip (List.range xs.length) xs


def length₁ (xs : List a) : Nat :=
  foldr (fun _ y => y + 1) 0 xs

def length₂ : List a → Nat :=
  foldr succ 0
  where succ _ n := n + 1

def length₃ : List α → Nat :=
  let aux (_ : α) (n : Nat) : Nat := n + 1
  foldr aux 0


example : length₂ ["a", "b", "c"] = 3 := by
  unfold length₂
  unfold foldr
  unfold foldr
  unfold foldr
  rewrite [length₂.succ]
  rewrite [length₂.succ]
  rewrite [length₂.succ]
  rewrite [foldr.eq_1]
  rfl

example : foldr Nat.add 0 [1,2,3] = 6 := by
  unfold foldr
  unfold foldr
  unfold foldr
  unfold foldr
  rewrite (config := {occs := .pos [3]}) [Nat.add]
  rewrite (config := {occs := .pos [2]}) [Nat.add]
  rewrite (config := {occs := .pos [1]}) [Nat.add]
  rfl

def foldl {a b : Type} (f : b → a → b) (e : b) : List a → b
| []      => e
| x :: xs => foldl f (f e x) xs

example : foldl Nat.add 0 [1,2,3] = 6 := by
  unfold foldl
  unfold foldl
  unfold foldl
  unfold foldl
  rewrite (config := {occs := .pos [3]}) [Nat.add]
  rewrite (config := {occs := .pos [2]}) [Nat.add]
  rewrite (config := {occs := .pos [1]}) [Nat.add]
  rfl

def foldl₀ {a b : Type} (f : b → a → b) (e : b) : List a → b :=
  foldr (flip f) e ∘ List.reverse

def foldl₁ {a b : Type} (f : b → a → b) (e : b) (xs : List a) : b :=
  foldr (flip f) e xs.reverse


example (f : b → a → b) (e : b) (xs : List a)
 : foldl f e xs = foldl₀ f e xs := by
 unfold foldl₀
 induction xs with
 | nil =>
   rw [Function.comp, List.reverse, foldl]
   simp
   rw [foldr]
 | cons y ys ih =>
   rw [Function.comp, List.reverse]; simp
   rw [Function.comp] at ih
   sorry


-- ## Section 1.2 Processing lists

structure Point where
  x : Float
  y : Float
deriving Repr

instance : Inhabited Point where
 default := Point.mk 0 0

def head {α : Type} [Inhabited α] : List α → α :=
  let f x _ := x
  List.foldr f default

/-
#eval head [Point.mk 1 2, Point.mk 3 4]
#eval head ([] : List Point)
-/

def concat₁ {a : Type} : List (List a) → List a :=
 List.foldr List.append []

def concat₂ {a : Type} : List (List a) → List a :=
 List.foldl List.append []

example : concat₁ [[1,2,3,4], [5], [6]] = [1,2,3,4,5,6] := by
  unfold concat₁
  unfold List.foldr
  rw [List.append.eq_2]
  rw [List.append.eq_2]
  rw [List.append.eq_2]
  rw [List.append.eq_2]
  rw [List.append.eq_1]
  unfold List.foldr
  rw [List.append.eq_2]
  rw [List.append.eq_1]
  unfold List.foldr
  rw [List.append.eq_2]
  rw [List.append.eq_1]
  unfold List.foldr
  rfl

example : concat₂ [[1,2,3,4], [5], [6]] = [1,2,3,4,5,6] := by
  unfold concat₂
  unfold List.foldl
  rw [List.append.eq_1]
  unfold List.foldl
  rw [List.append.eq_2]
  rw [List.append.eq_2]
  rw [List.append.eq_2]
  rw [List.append.eq_2]
  rw [List.append.eq_1]
  unfold List.foldl
  rw [List.append.eq_2]
  rw [List.append.eq_2]
  rw [List.append.eq_2]
  rw [List.append.eq_2]
  rw [List.append.eq_2]
  rw [List.append.eq_1]
  unfold List.foldl
  rfl


def scanl : (b → a → b ) → b → List a → List b
| _, e, [] => [e]
| f, e, (x :: xs) => e :: scanl f (f e x) xs

/-
#eval scanl Nat.add 0 [1,2,3,4]
#eval scanl Nat.add 42 []
#eval scanl (λ r n => n :: r)
  "foo".toList ['a', 'b', 'c', 'd'] |>.map List.asString
-/

def scanr₀ (f : a → b → b) (q₀ : b) (as : List a) : List b :=
 let rec aux : List a → {l : List b // l ≠ []}
  | [] => Subtype.mk [q₀] (by simp)
  | (x :: xs) =>
    let qs := aux xs
    Subtype.mk (f x (List.head qs qs.property) :: qs) (by simp)
 aux as

def scanr : (a → b → b) → b → List a → List b
| _, q₀, [] => [q₀]
| f, q₀, (x :: xs) =>
  match scanr f q₀ xs with
  | [] => []
  | qs@(q :: _) => f x q :: qs

/-
#eval scanr Nat.add 0 [1,2,3,4]
#eval scanr Nat.add 42 []
-/

-- ## Section 1.3 Inductive and recursive definitions

def inserts {a : Type} (x : a) : List a → List (List a)
| []      => [[x]]
| y :: ys => (x :: y :: ys) :: map (y :: ·) (inserts x ys)

-- #eval inserts 1 [2,3,4]


def concatMap (f : a → List b) : List a → List b :=
 concat₁ ∘ (List.map f)

-- #eval concatMap (String.toList ·) ["foo", "bar" ]

def perm₁ : List a → List (List a)
 | [] => [[]]
 | (x :: xs) => concatMap (inserts x ·) (perm₁ xs)

def perm₁' : List a → List (List a) :=
 foldr step [[]]
 where
  step x xss := concatMap (inserts x) xss

def perm₁'' : List a → List (List a) :=
  foldr (concatMap ∘ inserts) [[]]

def perm₁''' (xs : List a) : List (List a) :=
  foldr step [[]] xs
 where
   step a b := concatMap (inserts a) b

-- #eval perm₁ (List.range 5) |>.length

def picks {a : Type} : List a → List (a × List a)
| []      => []
| x :: xs =>
  (x, xs) :: ((picks xs).map (λ p => (p.1, x :: p.2)))

-- #eval picks [1,2,3,4]

theorem picks_less {a : Type} (xs : List a) :
  ∀ (p : a × List a), p ∈ picks xs → p.2.length < xs.length := by
  intro p h
  induction xs with
  | nil =>
    cases h -- no elements in picks []
  | cons x xs ih =>
    rw [picks] at h
    cases h with
    | head => simp
    | tail ys h1 =>
      simp at h1
      done






partial def perm₂ : List a → List (List a)
  | [] => [[]]
  | xs =>
    let subperms p := (perm₂ p.2).map (p.1 :: ·)
    concatMap subperms (picks xs)


def perm₃ : List a → List (List a)
  | [] => [[]]
  | x :: xs => concatMap (λ ⟨p, hp⟩ ↦
      have : p.2.length < (x :: xs).length := by
       apply picks_less (x :: xs)
       exact hp
      (perm₃ p.2).map (p.1 :: ·))
      (picks (x :: xs)).attach
 termination_by xs => xs.length



partial def until' (p: a → Bool) (f: a → a) (x : a) : a :=
  if p x then x
  else until' p f (f x)

partial def while' (p : a → Bool) := until' (not ∘ p)

-- #eval until' (· > 10) (· + 1) 0


-- ## Section 1.4 Fusion


def inits {a : Type} : List a → List (List a)
| [] => [[]]
| (x :: xs) => [] :: (inits xs).map (fun ys => x :: ys)

def tails {a : Type} : List a → List (List a)
| [] => [[]]
| (x :: xs) => (x :: xs) :: tails xs

theorem foldl_comp {α β: Type} (y: α) (e : β) (f : β → α → β):
foldl f e ∘ (fun x => y :: x) = foldl f (f e y) := by rfl

theorem map_map {α : Type} (g : α -> α ) (a : List α): List.map g a = map g a := by
  induction a with
  | nil => rfl
  | cons a as ih =>
    rw [map,List.map]
    rw [ih]
    done

theorem map_compose {α β γ : Type} (f : β → γ) (g : α → β) (l : List α) :
  map (f ∘ g) l = map f (map g l) := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
  simp [map, ih]

example {a b : Type} (f : b → a → b) (e : b) :
   map (foldl f e) ∘ inits = scanl f e := by
  funext xs
  induction xs generalizing e with
  | nil => simp [map, inits, foldl, scanl]
  | cons x xs ih =>
    rw [Function.comp]
    rw [inits,map,foldl,map_map,← map_compose]
    rw [foldl_comp,scanl]
    have hx := ih (f e x)
    rw [← hx]
    simp

example {a b c : Type} (f : b → c) (g : a → b) : map f ∘ map g = map (f ∘ g) := by
  funext xs
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [Function.comp, map]; rw [← ih]; rfl

theorem append_left_nil : ∀ xs : List a, [] ++ xs = xs := by
 intro h1
 induction h1 with
 | nil => rfl
 | cons ha hs => simp [List.append]; done

example (xs ys : List a) (f : a → b → b) (e : b)
 : foldr f e (xs ++ ys) = foldr f (foldr f e ys) xs := by
  have h1 := append_left_nil ys
  induction xs with
  | nil => rw [foldr.eq_1]; rewrite [h1]; rfl
  | cons x xs ih => simp [List.append, foldr]; rw [ih]

theorem foldr_append {α β : Type} (f : α → β → β) (e : β) (xs ys : List α) :
  foldr f e (xs ++ ys) = foldr f (foldr f e ys) xs := by
  induction xs with
  |nil => rfl
  |cons x xs ih =>
    simp [foldr, ih]

example (f : a → a → a)
 : foldr f e ∘ concat₁ = foldr (flip (foldr f)) e := by
  funext xs
  induction xs with
  | nil =>
    rw [foldr.eq_1, Function.comp]
    simp [concat₁, foldr.eq_1]
  | cons y ys ih =>
    rw [Function.comp]
    simp [concat₁]
    rw [←concat₁]
    rw [foldr_append]
    rw [foldr]
    rw [flip]
    exact congrArg (λ x => foldr f x y) ih

theorem fusion_th (g : a → b → b) (h : a → b) (h₁ : ∀ x y, h (f x y) = g x (h y))
 : h (foldr f e xs) = foldr g (h e) xs := by
 induction xs with
  | nil =>
    rewrite [foldr.eq_1]
    rewrite [foldr.eq_1]
    rfl
  | cons x xs ih =>
    rewrite [foldr]
    rewrite [h₁ x (foldr f e xs)]
    rewrite [ih]
    rewrite [foldr]
    rfl


-- ## Seciton 1.5 Accumulating and tupling

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


partial def collapse₀ (xss : List (List Int)) : List Int :=
 help [] xss
 where
  help : List Int → List (List Int) → List Int
  | xs, xss =>
    if xs.sum > 0 ∨ xss.isEmpty then xs
    else help (xs.append xss.head!) xss.tail

def collapse₁ (xss : List (List Int)) : List Int :=
 help [] xss
 where
  help : List Int → List (List Int) → List Int
  | xs, [] => xs
  | xs, (as :: bss) =>
    if xs.sum > 0 then xs
    else help (xs.append as) bss

partial def collapse₂ (xss : List (List Int)) : List Int :=
  help (0, []) (labelsum xss)
  where
   labelsum (xss : List (List Int)) : List (Int × List Int) :=
     List.zip (map List.sum xss) xss
   help : (Int × List Int) → List (Int × List Int) → List Int
   | (_, xs), [] => xs
   | (s, xs), xss => if s > 0 then xs else help (cat (s, xs) xss.head!) xss.tail
   cat : (Int × List Int) → (Int × List Int) → (Int × List Int)
   | (s, xs), (t, ys) => (s + t, xs ++ ys)

def collapse₃ (xss : List (List Int)) : List Int :=
  help (0, id) (labelsum xss) []
  where
    labelsum (xss : List (List Int)) : List (Int × List Int) :=
     List.zip (map List.sum xss) xss
    help :
    let tf := List Int → List Int
    (Int × tf) → List (Int × List Int) → tf
    | (_, f), [] => f
    | (s, f), (as :: bs) =>
      if s > 0 then f
      else help (s + as.1, f ∘ (as.2 ++ ·)) bs

/-
#eval collapse₃ [[1],[-3],[2,4]]
#eval collapse₃ [[-2,1],[-3],[2,4]]
#eval collapse₃ [[-2,1],[3],[2,4]]
-/


end Chapter1
