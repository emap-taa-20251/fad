
import Mathlib.Tactic
import Mathlib.Data.List.Sublists
import Fad.Chapter7

namespace Chapter10

open List
open Chapter7

-- ## Section 10.1 Theory

universe u

variable {a : Type u}
  [Inhabited a] [DecidableRel (α := a) (· = ·)]
  [Max a] [Min a]
  [LT a] [DecidableRel (α := a) (· < ·)]
  [LE a] [DecidableRel (α := a) (· ≤ ·)]

set_option linter.unusedSectionVars false

/-! ### Subsequences

`ys <+ xs` means that `ys` is a subsequence of `xs`.
The List.Sublist module will be really helpful.
-/

example : [1, 3] <+ [1, 2, 3] := by
  apply List.Sublist.cons_cons
  apply List.Sublist.cons
  apply List.Sublist.cons_cons
  apply List.Sublist.slnil


-- ### The predicate `ThinBy`

/-- `Dominates r ys xs` : every element of `xs` is dominated under `r` by some
    element of `ys`, i.e. `∀ x ∈ xs, ∃ y ∈ ys, y ⪯ x`. -/
def Dominates (r : a → a → Prop) (ys xs : List a) : Prop :=
  ∀ x ∈ xs, ∃ y ∈ ys, r y x

def ThinBy (r : a → a → Prop) (xs ys : List a) : Prop :=
  ys <+ xs ∧ Dominates r ys xs

@[simp] theorem mem_ThinBy {r : a → a → Prop} {xs ys : List a} :
    ThinBy r xs ys ↔ ys <+ xs ∧ Dominates r ys xs := by
    rfl

-- ### A linear-time implementation `thinBy`

/-- One step of `thinBy`, processing from the right. -/
def bump (le : a → a → Bool) (x : a) : List a → List a
  | []      => [x]
  | y :: ys =>
      match le x y, le y x with
      | true,  _     => x :: ys
      | false, true  => y :: ys
      | false, false => x :: y :: ys

/-- A sub-optimal, linear-time implementation of `ThinBy`. -/
def thinBy (le : a → a → Bool) : List a → List a :=
  List.foldr (bump le) []

theorem thinBy_nil (le : a → a → Bool) : thinBy le [] = [] := by
  rfl

theorem thinBy_cons (le : a → a → Bool) (z : a) (zs : List a) :
    thinBy le (z :: zs) = bump le z (thinBy le zs) := by
  rfl


-- ### Examples

/-- `(a,b) ⪯ (c,d) = (a ≥ c) ∧ (b ≤ d)`, as a `Bool` test on `ℕ × ℕ`. -/
def le₁ (p q : Nat × Nat) : Bool := decide (q.1 ≤ p.1 ∧ p.2 ≤ q.2)

/--
info: [(1, 2), (4, 3), (5, 4), (3, 1)]
-/
#guard_msgs in
#eval thinBy le₁ [(1,2),(4,3),(2,3),(5,4),(3,1)]

/--
info: [(3, 1), (4, 3), (5, 4)]
-/
#guard_msgs in
#eval thinBy le₁ [(1,2),(2,3),(3,1),(4,3),(5,4)]

/--
info: [(3, 1), (4, 3), (5, 4)]
-/
#guard_msgs in
#eval thinBy le₁ [(3,1),(1,2),(2,3),(4,3),(5,4)]


/-! ### `thinBy` refines `ThinBy` (correctness)

We prove that the concrete `thinBy` always returns a valid thinning, provided
the comparison is reflexive and transitive (i.e. a preorder). This splits into
the subsequence property and the domination property. -/

/-- `bump` preserves being a subsequence. -/
theorem bump_sublist (le : a → a → Bool) (z : a) {t zs : List a}
    (ht : t <+ zs) : bump le z t <+ z :: zs := by
  cases t with
  | nil =>
      simp only [bump]
      exact List.Sublist.cons_cons z (List.nil_sublist zs)
  | cons y ys =>
      have hys : ys <+ zs := (List.Sublist.cons y (List.Sublist.refl ys)).trans ht
      cases h1 : le z y <;> cases h2 : le y z <;> simp only [bump, h1, h2]
      · exact List.Sublist.cons_cons z ht     -- (false,false): z :: y :: ys
      · exact List.Sublist.cons z ht          -- (false,true):  y :: ys
      · exact List.Sublist.cons_cons z hys    -- (true,false):  z :: ys
      · exact List.Sublist.cons_cons z hys    -- (true,true):   z :: ys

/-- Every output of `thinBy` is a subsequence of the input. -/
theorem thinBy_sublist (le : a → a → Bool) :
    ∀ xs : List a, thinBy le xs <+ xs := by
  intro xs
  induction xs with
  | nil => exact List.Sublist.refl []
  | cons z zs ih =>
      rw [thinBy_cons]
      exact bump_sublist le z ih

/-- After a `bump`, the new element `z` is dominated by some element of the
    result. -/
theorem bump_dom_self (le : a → a → Bool) (hrefl : ∀ x, le x x = true)
    (z : a) (t : List a) : ∃ y ∈ bump le z t, le y z = true := by
  cases t with
  | nil => exact ⟨z, by simp [bump], hrefl z⟩
  | cons y ys =>
      cases h1 : le z y <;> cases h2 : le y z <;> simp only [bump, h1, h2]
      · exact ⟨z, by simp, hrefl z⟩       -- (false,false): z :: y :: ys
      · exact ⟨y, by simp, h2⟩            -- (false,true):  y :: ys
      · exact ⟨z, by simp, hrefl z⟩       -- (true,false):  z :: ys
      · exact ⟨z, by simp, hrefl z⟩       -- (true,true):   z :: ys

/-- A `bump` preserves domination of any element `w` that was already
    dominated by the accumulator. -/
theorem bump_dom_pres (le : a → a → Bool)
    (htrans : ∀ x y z, le x y = true → le y z = true → le x z = true)
    (z : a) (t : List a) (w : a) (h : ∃ y ∈ t, le y w = true) :
    ∃ y ∈ bump le z t, le y w = true := by
  obtain ⟨y₀, hy₀_mem, hy₀⟩ := h
  cases t with
  | nil => simp at hy₀_mem
  | cons y ys =>
      cases h1 : le z y <;> cases h2 : le y z <;> simp only [bump, h1, h2]
      · -- (false,false): bump = z :: y :: ys ⊇ (y :: ys)
        exact ⟨y₀, List.mem_cons_of_mem z hy₀_mem, hy₀⟩
      · -- (false,true): bump = y :: ys (unchanged)
        exact ⟨y₀, hy₀_mem, hy₀⟩
      · -- (true,false): bump = z :: ys ; the head y was dropped in favour of z
        rcases List.mem_cons.mp hy₀_mem with hy0y | hy0ys
        · subst hy0y
          exact ⟨z, by simp, htrans z y₀ w h1 hy₀⟩
        · exact ⟨y₀, List.mem_cons_of_mem z hy0ys, hy₀⟩
      · -- (true,true): bump = z :: ys (same reasoning)
        rcases List.mem_cons.mp hy₀_mem with hy0y | hy0ys
        · subst hy0y
          exact ⟨z, by simp, htrans z y₀ w h1 hy₀⟩
        · exact ⟨y₀, List.mem_cons_of_mem z hy0ys, hy₀⟩

/-- Every element of the input is dominated by some output of `thinBy`. -/
theorem thinBy_dominates (le : a → a → Bool)
    (hrefl : ∀ x, le x x = true)
    (htrans : ∀ x y z, le x y = true → le y z = true → le x z = true) :
    ∀ xs, Dominates (fun y x => le y x = true) (thinBy le xs) xs := by
  intro xs
  induction xs with
  | nil => intro x hx; cases hx
  | cons z zs ih =>
      rw [thinBy_cons]
      intro x hx
      rcases List.mem_cons.mp hx with hxz | hxzs
      · subst hxz
        exact bump_dom_self le hrefl x (thinBy le zs)
      · exact bump_dom_pres le htrans z (thinBy le zs) x (ih x hxzs)

/-- Correctness of `thinBy`: it always returns a valid thinning. -/
theorem thinBy_refines (le : a → a → Bool)
    (hrefl : ∀ x, le x x = true)
    (htrans : ∀ x y z, le x y = true → le y z = true → le x z = true) :
    ∀ xs, ThinBy (fun y x => le y x = true) xs (thinBy le xs) := by
  intro xs
  constructor
  · exact thinBy_sublist le xs
  · exact thinBy_dominates le hrefl htrans xs

/-- `le₁` is reflexive. -/
theorem le₁_refl (p : Nat × Nat) : le₁ p p = true := by
  simp [le₁]

/-- `le₁` is transitive. -/
theorem le₁_trans (p q s : Nat × Nat) :
    le₁ p q = true → le₁ q s = true → le₁ p s = true := by
  simp only [le₁, decide_eq_true_eq]
  rintro ⟨h1, h2⟩ ⟨h3, h4⟩
  exact ⟨le_trans h3 h1, le_trans h2 h4⟩

/-- Concrete capstone: the thinning computed for the book's example is indeed a
    valid member of the specification `ThinBy`. -/
example :
    ThinBy (fun y x => le₁ y x = true) [(1,2),(4,3),(2,3),(5,4),(3,1)]
      (thinBy le₁ [(1,2),(4,3),(2,3),(5,4),(3,1)]) := by
  -- apply thinBy_refines le₁ le₁_refl le₁_trans
  unfold thinBy
  simp [bump, le₁]
  constructor
  · apply List.Sublist.cons_cons
    apply List.Sublist.cons_cons
    apply List.Sublist.cons
    apply List.Sublist.refl
  · intro x h
    cases h
    use (1, 2)
    grind
    expose_names
    cases h
    use (4, 3)
    grind
    expose_names
    cases h
    use (4, 3)
    grind
    expose_names
    cases h
    use (5, 4)
    grind
    expose_names
    cases h
    use (3, 1)
    grind
    expose_names
    cases h


/-! ### The laws of thinning

  * identity              `id ← ThinBy r`
  * idempotence           `ThinBy r = ThinBy r · ThinBy r`
  * thin introduction     `MinWith cost = MinWith cost · ThinBy r`
  * thin elimination      `wrap · MinWith cost ← ThinBy r`
  * thin-map (one flavour)`map f · ThinBy r ← ThinBy r · map f`

The remaining laws (the distributive law and the thin-filter law) are stated in
comments; they are left as exercises. -/

/-- **Identity law.**  `id ← ThinBy r`, given reflexivity. -/
theorem thin_identity (r : a → a → Prop) (hrefl : ∀ x, r x x) :
    ∀ xs : List a, ThinBy r xs xs := by
  intro xs
  constructor
  · exact List.Sublist.refl xs
  · intro x hx
    use x
    constructor
    · assumption
    · exact hrefl x

/-- **Idempotence law.**  `ThinBy r = ThinBy r · ThinBy r`, for a preorder `r`. -/
theorem thin_idem (r : a → a → Prop)
    (hrefl : ∀ x, r x x)
    (htrans : ∀ x y z, r x y → r y z → r x z) :
    ∀ xs zs : List a, ThinBy r xs zs ↔ ∃ ys : List a,
    ThinBy r ys zs ∧ ThinBy r xs ys := by
  intro xs zs
  constructor
  · intro h
    use zs
    constructor
    · exact thin_identity r hrefl zs
    · assumption
  · intro h
    obtain ⟨ys, hys⟩ := h
    constructor
    · exact List.Sublist.trans (hys.1.1) (hys.2.1)
    · intro x hx
      have h₁ := hys.2.2
      obtain ⟨y, hy⟩ := h₁ x hx
      have h₂ := hys.1.2
      obtain ⟨z, hz⟩ := h₂ y hy.1
      use z
      constructor
      · exact hz.1
      · exact htrans z y x hz.2 hy.2

-- def foldr1 (f : a → a → a) : List a → a
--   | []    => default
--   | [x]   => x
--   | x::xs => f x (foldr1 f xs)

-- def minWith {a b : Type} [LE b] [Inhabited a]
--   [DecidableRel (α := b) (· ≤ ·)]
--   (f : a → b) (as : List a) : a :=
--   let smaller f x y := cond (f x ≤ f y) x y
--   foldr1 (smaller f) as

/-- **Thin introduction.**  `MinWith cost = MinWith cost · ThinBy r`,
    provided `x ⪯ y ⇒ cost x ≤ cost y`. This is the law that turns an
    optimisation problem into a thinning problem. -/
theorem thin_introduction [LE b] [DecidableRel (α := b) (· ≤ ·)]
    (r : a → a → Prop)
    (cost : a → b) (hrefl : ∀ x, r x x)
    (xs ys : List a)
    (hmono : ∀ x y, r x y → cost x ≤ cost y)
    (h : ThinBy r xs ys) :
    (minWith cost xs) = minWith cost ys := by
  sorry

/-- `wrap x = [x]`. -/
def wrap (x : a) : List a := [x]

/-- **Thin elimination.**  `wrap · MinWith cost ← ThinBy r`,
    provided `cost x ≤ cost y ⇒ x ⪯ y`. Dual to thin introduction. -/
theorem thin_elimination {β : Type*} [LE β] [DecidableRel (α := β) (· ≤ ·)]
    (r : a → a → Prop) (cost : a → β)
    (hmono : ∀ x y, cost x ≤ cost y → r x y) :
    ∀ xs : List a, ThinBy r xs (wrap (minWith cost xs)) := by
  sorry

/-- **Thin-map law** (first flavour).  `map f · ThinBy r ← ThinBy r · map f`,
    provided `x ⪯ y ⇒ f x ⪯ f y`. -/
theorem thin_map (r : a → a → Prop) (f : a → a)
    (hmono : ∀ x y, r x y → r (f x) (f y))
    (xs ys : List a)
    (h : ThinBy r xs ys) :
    ThinBy r (map f xs) (map f ys) := by
  sorry

/-
  Remaining laws (left as exercises, as in the book):

  * Distributive law:
        ThinBy r · concat = ThinBy r · concatMap (ThinBy r)
    with the weaker refinement
        concatMap (ThinBy r) ← ThinBy r · concat.

  * Thin-map law (second flavour):
        ThinBy r · map f ← map f · ThinBy r          if  f x ⪯ f y ⇒ x ⪯ y,
    giving the equality  map f · ThinBy r = ThinBy r · map f  when  x ⪯ y ⇔ f x ⪯ f y.

  * Thin-filter law:
        ThinBy r · filter p = filter p · ThinBy r     provided (x ⪯ y ∧ p y) ⇒ p x.
-/

end Chapter10
