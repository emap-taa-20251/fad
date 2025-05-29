import Fad.Chapter6
import Fad.Chapter7

namespace Chapter7

/- # Exercicio 7.1 -/

def minimumBy {α : Type} (cmp : α → α → Ordering) : List α → Option α
  | []      => none
  | x :: xs =>
    some (xs.foldr (λ y r => cond (cmp y r = Ordering.lt) y r) x)

def minWith₁ {α β : Type} [Ord β] (f : α → β) (xs : List α) : Option α :=
  let helper (x y : α) : Ordering := compare (f x) (f y)
  minimumBy helper xs

def minWith₂ {α β : Type} [Ord β] (f : α → β) (xs : List α) : Option α :=
  let tuple (x : α) : β × α := (f x, x)
  let cmp (x y : β × α) := compare x.1 y.1
  minimumBy cmp (xs.map tuple) >>= (λ pair => some pair.2)

instance : Ord Float where
  compare x y :=
    if x < y then Ordering.lt
    else if x == y then Ordering.eq
    else Ordering.gt


/- # Exercicio 7.2 -/

def minsWith {α β : Type} [Ord β] (f : α → β) (xs : List α) : List α :=
  let step (x : α) (ys : List α) : List α :=
    match ys with
    | [] => [x]
    | y :: ys =>
      match compare (f x) (f y) with
      | Ordering.lt => [x]
      | Ordering.eq => x :: y :: ys
      | Ordering.gt => y :: ys
  xs.foldr step []

def minsWith' {α β : Type} [Ord β] (f : α → β) (xs : List α) : List α :=
  let step (x : β × α) (ys : List (β × α)) :=
    match ys with
    | [] => [x]
    | y :: ys =>
      match compare (x.fst) (y.fst) with
      | Ordering.lt => [x]
      | Ordering.eq => x :: y :: ys
      | Ordering.gt => y :: ys
  xs.map tuple |>.foldr step [] |>.map (·.snd)
    where tuple x := (f x, x)


/- # Exercicio 7.4 -/

def interleave {α : Type} : List α → List α → List (List α)
| xs, []            => [xs]
| [], ys            => [ys]
| x :: xs, y :: ys  =>
  let l := interleave xs (y :: ys) |>.map (x :: ·)
  let r := interleave (x :: xs) ys |>.map (y :: ·)
  l ++ r

def cp {α β : Type} (xs : List α) (ys : List β) : List (α × β) :=
 Chapter1.concatMap (λ x ↦ ys.map (λ y ↦ (x, y))) xs

def perms₁ {α : Type} : List α → List (List α)
| []  => [[]]
| [x] => [[x]]
| xs  =>
  let p := List.MergeSort.Internal.splitInTwo (Subtype.mk xs rfl)
  let yss := perms p.1
  let zss := perms p.2
  Chapter1.concatMap (Function.uncurry interleave) (cp yss zss)


/- # Exercicio 7.5 -/

open Chapter6 (minimum)

example (x : Nat) : minimum [x] = x := by
  unfold minimum
  rewrite [Chapter6.foldr1]
  rfl

def min_list_list : List Nat → List Nat → List Nat
 | [], _  => []
 |  _, [] => []
 | xs@(a :: as), ys@(b :: bs) =>
   if      a < b then xs
   else if a > b then ys
   else
    a :: (min_list_list as bs)

instance : Min (List Nat) where
 min := min_list_list

example (x : Nat) : ∀ xs, xs ≠ [] →
 minimum (xs.map (x :: ·)) = (x :: ·) (minimum xs)
 := by
 intro xs h
 simp [Function.comp]
 induction xs with
 | nil => contradiction
 | cons a as ih =>
   rw [List.map]
   rw [minimum]
   sorry


/- # Exercicio 7.10  -/

def pick₁ : List Nat → Option (Nat × List Nat)
| []       => none
| [x]      => some (x, [])
| x :: xs  =>
  match pick₁ xs with
  | none => none
  | some (y, ys) =>
    if x ≤ y then some (x, xs) else some (y, x :: ys)


-- # Exercicio 7.12

namespace S73

/- response: both have the same 'cost' (here 'sum') and
   'minWith' takes the first smallest from the list.
   If `mktuples` produces decreasing order, it would
   return the other `minimum`. -/

def mktuples' : List Denom → Nat → List Tuple
  | [1]    , n => [[n]]
  | []     , _ => panic! "mktuples: invalid empty list"
  | d :: ds, n =>
    let rs := List.range (n / d + 1)
    rs.flatMap (λ c => mktuples₀ ds (n - c * d) |>.map
     (λ cs => c :: cs))

def mkchange' (ds : List Denom) : Nat → Tuple :=
  minWith List.sum ∘ mktuples' ds

-- #eval mkchange₀ [7,3,1] 54
-- #eval mkchange' [7,3,1] 54

end S73

/- # Exercicio 7.16
   not clear how to prove formally
-/

namespace S73

def urds := [100, 50, 20, 15, 5, 2, 1]

/-
#eval mkchange₀ urds 30
#eval mkchange₁ urds 30
#eval mkchange  urds 30
#eval mkchange₀ [4,3,1] 6
#eval mkchange₁ [4,3,1] 6
-/

end S73

end Chapter7
