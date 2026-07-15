
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

/-- Folding with `smaller cost` always returns an element of the list. -/
private lemma foldrSmaller_mem {α β : Type*} [LE β]
    [DecidableRel (α := β) (· ≤ ·)] (cost : α → β) (x : α) :
    ∀ ys : List α,
      List.foldr (fun u v => cond (cost u ≤ cost v) u v) x ys ∈ x :: ys := by
  intro ys
  induction' ys with z zs ih
  · simp
  · simp only [List.foldr_cons]
    by_cases h : cost z ≤ cost (List.foldr (fun u v => cond (cost u ≤ cost v) u v) x zs)
    · simp [h]
    · simp only [h, decide_false, cond_false]
      rcases List.mem_cons.1 ih with hx | hz
      · simp [hx]
      · exact List.mem_cons.2 (Or.inr (List.mem_cons.2 (Or.inr hz)))


/-- Folding with `smaller cost` yields a cost-minimal element of the list. -/
private lemma foldrSmaller_le {α β : Type*} [LinearOrder β] (cost : α → β) (x : α) :
    ∀ (ys : List α) (z : α), z ∈ x :: ys →
      cost (List.foldr (fun u v => cond (cost u ≤ cost v) u v) x ys) ≤ cost z := by
  intro ys
  induction' ys with w ws ih
  · intro z hz
    simp at hz
    subst hz
    simp
  · intro z hz
    simp only [List.foldr_cons]
    set t := List.foldr (fun u v => cond (cost u ≤ cost v) u v) x ws with ht
    by_cases h : cost w ≤ cost t
    · simp only [h, decide_true, cond_true]
      rcases List.mem_cons.1 hz with hzx | hz'
      · rw [hzx]; exact le_trans h (ih x (by simp))
      · rcases List.mem_cons.1 hz' with hzw | hz''
        · rw [hzw]
        · exact le_trans h (ih z (by simp [hz'']))
    · simp only [h, decide_false, cond_false]
      have hwt : cost t ≤ cost w := le_of_lt (lt_of_not_ge h)
      rcases List.mem_cons.1 hz with hzx | hz'
      · rw [hzx]; exact ih x (by simp)
      · rcases List.mem_cons.1 hz' with hzw | hz''
        · rw [hzw]; exact hwt
        · exact ih z (by simp [hz''])

/-- `minWith cost` returns an element of the (non-empty) list. -/
theorem minWith_mem {α β : Type*} [Inhabited α] [LE β]
    [DecidableRel (α := β) (· ≤ ·)] (cost : α → β) :
    ∀ {xs : List α}, xs ≠ [] → minWith cost xs ∈ xs := by
  intro xs hxs
  match xs with
  | [] => exact absurd rfl hxs
  | x :: xs => exact foldrSmaller_mem cost x xs

/-- `minWith cost` returns a cost-minimal element of the list. -/
theorem minWith_le {α β : Type*} [Inhabited α] [LinearOrder β] (cost : α → β) :
    ∀ {xs : List α}, ∀ z ∈ xs, cost (minWith cost xs) ≤ cost z := by
  intro xs
  match xs with
  | [] => intro z hz; simp at hz
  | x :: xs => intro z hz; exact foldrSmaller_le cost x xs z hz

/-- **Thin introduction.**  `MinWith cost = MinWith cost · ThinBy r`,
    provided `x ⪯ y ⇒ cost x ≤ cost y`. This is the law that turns an
    optimisation problem into a thinning problem. -/
theorem thin_introduction [LinearOrder b]
    (r : a → a → Prop)
    (cost : a → b)
    (xs ys : List a)
    (hmono : ∀ x y, r x y → cost x ≤ cost y)
    (h : ThinBy r xs ys) :
  cost (minWith cost xs) = cost (minWith cost ys) := by
  obtain ⟨hsub, hdom⟩ := h
  by_cases hxs : xs = []
  · subst hxs
    rw [List.sublist_nil.1 hsub]
  · have hys : ys ≠ [] := by
      rintro rfl
      obtain ⟨y, hy, _⟩ := hdom _ (minWith_mem cost hxs)
      simp at hy
    have hmemx : minWith cost xs ∈ xs := minWith_mem cost hxs
    have hl : cost (minWith cost xs) ≤ cost (minWith cost ys) := by
      have hmy : minWith cost ys ∈ ys := minWith_mem cost hys
      exact minWith_le cost (minWith cost ys) (hsub.subset hmy)
    have hr : cost (minWith cost xs) ≥ cost (minWith cost ys) := by
      obtain ⟨y, hymem, hry⟩ := hdom _ hmemx
      exact le_trans (minWith_le cost y hymem) (hmono y (minWith cost xs) hry)
    grind

/-- `wrap x = [x]`. -/
def wrap (x : a) : List a := [x]

/-- **Thin elimination.**  `wrap · MinWith cost ← ThinBy r`,
    provided `cost x ≤ cost y ⇒ x ⪯ y`. Dual to thin introduction. -/
theorem thin_elimination {β : Type*} [LinearOrder β]
    (r : a → a → Prop) (cost : a → β)
    (hmono : ∀ x y, cost x ≤ cost y → r x y) :
    ∀ (xs : List a), xs ≠ [] → ThinBy r xs (wrap (minWith cost xs)) := by
  intro xs hxs
  constructor
  · have h₁ := minWith_mem cost hxs
    simpa [wrap]
  · intro x hx
    simp [wrap]
    have h₂ := minWith_le cost x hx
    apply hmono at h₂
    exact h₂

/-- **Thin-map law** (first flavour).  `map f · ThinBy r ← ThinBy r · map f`,
    provided `x ⪯ y ⇒ f x ⪯ f y`. -/
theorem thin_map (r : a → a → Prop) (f : a → a)
    (hmono : ∀ x y, r x y → r (f x) (f y))
    (xs ys : List a)
    (h : ThinBy r xs ys) :
    ThinBy r (map f xs) (map f ys) := by
  constructor
  · have h1 := h.1
    exact Sublist.map f h1
  · have h2 := h.2
    intro x hx
    simp at hx
    obtain ⟨z, hz⟩ := hx
    have h₀ := h2 z hz.1
    obtain ⟨w, hw⟩ := h₀
    use f w
    constructor
    · simp
      use w
      constructor
      · exact hw.1
      · rfl
    · have h₁ := hmono w z hw.2
      simp [hz] at h₁
      assumption

/-
  Remaining laws (exercises):

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

-- ## Section 10.2 Paths in a layered network

namespace LayeredNetwork

/-! A layered network is given by a list of lists of edges, each list describing
the edges between two adjacent layers. Each edge is a triple `(u,v,w)`, where
`u` is the source, `v` the target and `w` a numerical weight, not necessarily
positive. The problem is to find a path from the top layer to the bottom layer
with minimum total weight. -/

abbrev Vertex := Nat
abbrev Weight := Int
abbrev Edge := Vertex × Vertex × Weight
abbrev Path := List Edge
abbrev Net := List (List Edge)

def source (e : Edge) : Vertex := e.1
def target (e : Edge) : Vertex := e.2.1
def weight (e : Edge) : Weight := e.2.2

def cost (p : Path) : Weight := (p.map weight).sum

/- `thinBy` drags along the instances of the section variable `a` -/
instance : Max Path := ⟨fun p q => if cost p ≤ cost q then q else p⟩
instance : Min Path := ⟨fun p q => if cost p ≤ cost q then p else q⟩

@[simp] theorem cost_nil : cost [] = 0 := rfl

@[simp] theorem cost_cons (e : Edge) (p : Path) : cost (e :: p) = weight e + cost p := by
  simp [cost]


/-! ### The network of Figure 10.1

Four layers of four vertices each: `1..4`, `5..8`, `9..12` and `13..16`.  There
are 27 paths from the top layer to the bottom one. -/

def layer₁ : List Edge := [(1,5,2), (1,6,7), (2,6,1), (3,6,4), (3,7,5), (4,7,2), (4,8,3)]
def layer₂ : List Edge := [(5,9,5), (6,9,3), (6,10,9), (6,11,8), (7,11,2), (8,11,7), (8,12,1)]
def layer₃ : List Edge := [(9,13,4), (9,14,8), (10,14,2), (10,15,5), (11,15,6), (11,16,3), (12,16,7)]

/-- The network of Figure 10.1. Note that each list of edges is sorted so that
    edges with the same source vertex appear together: this is what makes the
    thinning step below produce just one path per source vertex. -/
def net₁ : Net := [layer₁, layer₂, layer₃]


/-! ### The specification -/

/-- The Cartesian-product function `cp`. -/
def cp {γ : Type u} : List (List γ) → List (List γ) :=
  List.foldr (fun xs yss => xs.flatMap (fun x => yss.map (x :: ·))) [[]]

theorem cp_nil {γ : Type u} : cp ([] : List (List γ)) = [[]] := rfl

theorem cp_cons {γ : Type u} (xs : List γ) (xss : List (List γ)) :
    cp (xs :: xss) = xs.flatMap (fun x => (cp xss).map (x :: ·)) := rfl

#guard cp [["a","b","c"],["d","e"],["f"]] =
  [["a","d","f"],["a","e","f"],["b","d","f"],["b","e","f"],["c","d","f"],["c","e","f"]]

def linked (e₁ : Edge) : Path → Bool
  | []      => true
  | e₂ :: _ => target e₁ == source e₂

def connected : Path → Bool
  | []      => true
  | e :: es => linked e es && connected es

/-- `paths = filter connected · cp`. -/
def paths₀ (net : Net) : List Path := (cp net).filter connected

/-- `mcp ← MinWith cost · paths` -/
def mcp₀ (net : Net) : Path := minWith cost (paths₀ net)


/-! ### Fusing `filter connected` and `cp`

`paths = foldr step [[]]` where `step es ps = [e : p | e ← es, p ← ps, linked e p]`,
which we write in the equivalent form `step es ps = concat [cons e ps | e ← es]`. -/

def cons (e : Edge) (ps : List Path) : List Path :=
  (ps.filter (linked e)).map (e :: ·)

def step (es : List Edge) (ps : List Path) : List Path :=
  es.flatMap (fun e => cons e ps)

def paths (net : Net) : List Path := net.foldr step [[]]

private lemma filter_connected_map (e : Edge) :
    ∀ ps : List Path, (ps.map (e :: ·)).filter connected = cons e (ps.filter connected) := by
  intro ps
  induction ps with
  | nil => rfl
  | cons q qs ih =>
      by_cases h₁ : linked e q = true <;> by_cases h₂ : connected q = true <;>
        simp_all [cons, connected]

/-- The fusion step: `filter connected · cp = foldr step [[]]`. -/
theorem paths₀_eq_paths : ∀ net : Net, paths₀ net = paths net := by
  intro net
  induction net with
  | nil => rfl
  | cons es net ih =>
      simp only [paths₀] at ih ⊢
      have h : ∀ e : Edge,
          ((cp net).map (e :: ·)).filter connected = cons e (paths net) := by
        intro e
        rw [filter_connected_map, ih]
      rw [cp_cons, filter_flatMap]
      simp only [h]
      rfl

#guard (paths net₁).length = 27
#guard (paths net₁) = (paths₀ net₁)


/-! ### Introducing thinning

A greedy algorithm is not possible: the source of a minimum-cost path at one
level may not be among the target vertices of the edges at the next level up.
The thin-introduction law says we may rewrite the specification as

  `mcp ← MinWith cost · ThinBy (⪯) · paths`

provided `p₁ ⪯ p₂ ⇒ cost p₁ ≤ cost p₂`.  The appropriate choice is the *partial*
preorder below: there is no point in keeping a path if there is another path
with the same source vertex and lower cost. -/

def le₂ (p₁ p₂ : Path) : Bool :=
  decide (p₁.head?.map source = p₂.head?.map source ∧ cost p₁ ≤ cost p₂)

/-- `le₂` is reflexive. -/
theorem le₂_refl (p : Path) : le₂ p p = true := by simp [le₂]

/-- `le₂` is transitive. -/
theorem le₂_trans (p q r : Path) : le₂ p q = true → le₂ q r = true → le₂ p r = true := by
  simp only [le₂, decide_eq_true_eq]
  rintro ⟨h₁, h₂⟩ ⟨h₃, h₄⟩
  exact ⟨h₁.trans h₃, h₂.trans h₄⟩

/-- The proviso of thin introduction: `p₁ ⪯ p₂ ⇒ cost p₁ ≤ cost p₂`. -/
theorem le₂_cost (p q : Path) (h : le₂ p q = true) : cost p ≤ cost q := by
  simp only [le₂, decide_eq_true_eq] at h
  exact h.2

/-- The proviso of the **thin-filter law**: `p₁ ⪯ p₂ ∧ linked e p₂ ⇒ linked e p₁`. -/
theorem linked_of_le₂ (e : Edge) (p₁ p₂ : Path)
    (h : le₂ p₁ p₂ = true) (h₂ : linked e p₂ = true) : linked e p₁ = true := by
  simp only [le₂, decide_eq_true_eq] at h
  obtain ⟨hs, -⟩ := h
  cases p₁ with
  | nil => rfl
  | cons f fs =>
      cases p₂ with
      | nil => simp at hs
      | cons g gs =>
          simp only [List.head?_cons, Option.map_some] at hs
          have hs' : source f = source g := by simpa using hs
          simp only [linked, beq_iff_eq] at h₂ ⊢
          rw [hs']
          exact h₂

/-- The proviso of the **thin-map law**: `p₁ ⪯ p₂ ⇒ e : p₁ ⪯ e : p₂`.
    Note that no context is needed in this direction. -/
theorem cons_mono (e : Edge) (p₁ p₂ : Path) (h : le₂ p₁ p₂ = true) :
    le₂ (e :: p₁) (e :: p₂) = true := by
  simp only [le₂, decide_eq_true_eq] at h ⊢
  refine ⟨rfl, ?_⟩
  simp only [cost_cons]
  exact Int.add_le_add_left h.2 _

/-- The converse direction of the thin-map law *relies on context*: it holds for
    paths `p₁` and `p₂` that are both linked to `e` (and are both empty, or both
    non-empty, which in the fold is automatic since all candidates have the same
    length). -/
theorem cons_mono' (e : Edge) (p₁ p₂ : Path)
    (h₁ : linked e p₁ = true) (h₂ : linked e p₂ = true) (hne : p₁ = [] ↔ p₂ = [])
    (h : le₂ (e :: p₁) (e :: p₂) = true) : le₂ p₁ p₂ = true := by
  simp only [le₂, decide_eq_true_eq, cost_cons] at h ⊢
  refine ⟨?_, le_of_add_le_add_left h.2⟩
  cases p₁ with
  | nil =>
      have : p₂ = [] := hne.mp rfl
      subst this; rfl
  | cons f fs =>
      cases p₂ with
      | nil => exact absurd (hne.mpr rfl) (by simp)
      | cons g gs =>
          simp only [linked, beq_iff_eq] at h₁ h₂
          simp [h₁ ▸ h₂]


/-! ### The algorithm

`tstep es ps ← ThinBy (⪯) (step es ps)`, so that

  `foldr tstep [[]] ← ThinBy (⪯) · foldr step [[]]`

The claim justifying the fusion is `ThinBy (⪯) (cons e ps) = cons e (ThinBy (⪯) ps)`,
proved with the thin-map and thin-filter laws whose provisos are the three
lemmas above. -/

def tstep (es : List Edge) (ps : List Path) : List Path :=
  thinBy le₂ (step es ps)

def mcp (net : Net) : Path := minWith cost (net.foldr tstep [[]])

-- The first step produces exactly one singleton path per source vertex,
-- just as in the book.
/--
info: [[(9, 13, 4)], [(10, 14, 2)], [(11, 16, 3)], [(12, 16, 7)]]
-/
#guard_msgs in
#eval tstep layer₃ [[]]

-- Each additional step also produces exactly four paths, because each layer
-- has four vertices.
/--
info: 4
-/
#guard_msgs in
#eval (net₁.foldr tstep [[]]).length

#guard mcp net₁ = [(4,7,2), (7,11,2), (11,16,3)]
#guard cost (mcp net₁) = 7
#guard mcp net₁ = mcp₀ net₁

/-
  Running time. The number of paths maintained at each step is at most the
  number of vertices in the current layer, so each step costs at most the
  product of the number of edges between two layers and the number of vertices
  in the lower layer. With at most `k` vertices per layer the running time is
  `O(e*k)`, where `e` is the total number of edges; with `d` layers,
  `e ≤ (d-1)*k^2`, so thinning takes `O(d*k^3)` steps against Dijkstra's
  `O(d^2*k^2)`: thinning wins when the network is deeper than it is wide.
  Exercise 10.14 shaves a factor of `k` off, giving an optimal `O(d*k^2)`.

  Exercise: as a further optimisation, tuple paths with their costs to avoid
  recomputation of `cost`.
-/

end LayeredNetwork

-- ## Section 10.3 Coin-changing revisited

namespace CoinChanging

/-! The greedy algorithm of Chapter 7 is not guaranteed to produce the smallest
number of coins for all denominations; in particular it fails for the United
Regions. Thinning gives an algorithm that works for *any* set of denominations.

Denominations are taken in increasing order, so that `foldr` considers them in
decreasing order of value. -/

abbrev Denom := Nat
abbrev Coin := Nat
abbrev Residue := Nat
abbrev Count := Nat

/-- A tuple consists of a list of coin counts `[cₖ,...,c₁]` for the
    denominations considered so far, the residual amount, and the number of
    coins used. -/
abbrev Tuple := List Coin × Residue × Count

def coins   (t : Tuple) : List Coin := t.1
def residue (t : Tuple) : Residue   := t.2.1
def count   (t : Tuple) : Count     := t.2.2

instance : Max Tuple := ⟨fun x y => if count x ≤ count y then y else x⟩
instance : Min Tuple := ⟨fun x y => if count x ≤ count y then x else y⟩

def ukds : List Denom := [1,2,5,10,20,50,100,200]
def urds : List Denom := [1,2,5,15,20,50,100]

/-- At each step the next lower denomination is considered, and every possible
    choice for a number of coins of this denomination is considered. -/
def extend (d : Denom) (t : Tuple) : List Tuple :=
  (List.range (residue t / d + 1)).map
    (fun c => (coins t ++ [c], residue t - c * d, count t + c))

def mktuples (n : Nat) (ds : List Denom) : List Tuple :=
  ds.foldr (fun d ts => ts.flatMap (extend d)) [([], n, 0)]

-- Unlike Chapter 7, `mktuples` returns all the *partial* tuples, including
-- those with a non-zero residue: `(mktuples 256 ukds).length = 10640485`.

/--
info: 293
-/
#guard_msgs in
#eval (mktuples 20 ukds).length

/-- `cost t = (residue t, count t)`, ordered lexicographically: a candidate with
    minimum cost is one whose residue is as small as possible and, among such
    candidates, one with minimum count. Since there is a denomination of value
    1, a minimum-cost candidate has zero residue and minimum count. -/
def cost (t : Tuple) : Residue ×ₗ Count := toLex (residue t, count t)

/-- `mkchange n ← coins · MinWith cost · mktuples n` -/
def mkchange₀ (n : Nat) (ds : List Denom) : List Coin :=
  coins (minWith cost (mktuples n ds))

/-! ### Introducing thinning

`mkchange n ← coins · MinWith cost · ThinBy (⪯) · mktuples n`, where `⪯` must
satisfy `t₁ ⪯ t₂ ⇒ cost t₁ ≤ cost t₂`. There is no point in keeping a tuple in
play if there is another tuple whose residue is the same but whose count is
smaller.

It might be thought that the stronger `residue t₁ ≤ residue t₂ ∧ count t₁ ≤
count t₂` would do, but that statement is false; see Exercise 10.16. -/

def le₃ (t₁ t₂ : Tuple) : Bool :=
  decide (residue t₁ = residue t₂ ∧ count t₁ ≤ count t₂)

theorem le₃_refl (t : Tuple) : le₃ t t = true := by simp [le₃]

theorem le₃_trans (t₁ t₂ t₃ : Tuple) :
    le₃ t₁ t₂ = true → le₃ t₂ t₃ = true → le₃ t₁ t₃ = true := by
  simp only [le₃, decide_eq_true_eq]
  rintro ⟨h₁, h₂⟩ ⟨h₃, h₄⟩
  exact ⟨h₁.trans h₃, h₂.trans h₄⟩

/-- The proviso of thin introduction: `t₁ ⪯ t₂ ⇒ cost t₁ ≤ cost t₂`. -/
theorem le₃_cost (t₁ t₂ : Tuple) (h : le₃ t₁ t₂ = true) : cost t₁ ≤ cost t₂ := by
  simp only [le₃, decide_eq_true_eq] at h
  obtain ⟨hr, hk⟩ := h
  simp only [cost, Prod.Lex.toLex_le_toLex, hr]
  right
  simpa

/-! ### Why the usual calculation breaks down

The distributive law rewrites `ThinBy (⪯) (step d ts)` into
`ThinBy (⪯) (concatMap (ThinBy (⪯) · extend d) ts)`, but the calculation can
proceed no further, because `ThinBy (⪯) · extend d = extend d`: the tuples in
`extend d t` have *different* residues, so thinning can never eliminate any of
them. -/

theorem thin_extend_useless (d : Denom) (t : Tuple) :
    thinBy le₃ (extend d t) = extend d t := by
  sorry -- Exercise: no two tuples in `extend d t` are comparable under `le₃`.

/-! Instead we back up and prove the *key fact* (10.2) directly: if `t₁ ⪯ t₂`,
then every extension of `t₂` is dominated by some extension of `t₁`. This is
exactly the hypothesis needed by the general fusion theorem of Section 10.5. -/

/-- **Key fact (10.2)**: `t₁ ⪯ t₂ ⇒ ∀ e₂ ∈ extend d t₂, ∃ e₁ ∈ extend d t₁, e₁ ⪯ e₂`. -/
theorem key_fact (d : Denom) (t₁ t₂ : Tuple) (h : le₃ t₁ t₂ = true) :
    ∀ e₂ ∈ extend d t₂, ∃ e₁ ∈ extend d t₁, le₃ e₁ e₂ = true := by
  simp only [le₃, decide_eq_true_eq] at h
  obtain ⟨hr, hk⟩ := h
  intro e₂ he₂
  simp only [extend, List.mem_map, List.mem_range] at he₂
  obtain ⟨c, hc, rfl⟩ := he₂
  refine ⟨(coins t₁ ++ [c], residue t₁ - c * d, count t₁ + c), ?_, ?_⟩
  · simp only [extend, List.mem_map, List.mem_range]
    exact ⟨c, by rw [hr]; exact hc, rfl⟩
  · simp only [le₃, decide_eq_true_eq, residue, count]
    constructor
    · simp [residue] at hr
      rw [hr]
    · exact Nat.add_le_add_right hk c


/-! ### The algorithm

`tstep d ← ThinBy (⪯) · concatMap (extend d)`.  The thinning step is more
effective if tuples with the same residue are brought together, which is
achieved by keeping tuples in decreasing order of residue; since `extend`
already produces tuples in that order, it suffices to merge. -/

def cmp₃ (t₁ t₂ : Tuple) : Bool := decide (residue t₂ ≤ residue t₁)

/-- Merging two lists that are ordered according to `cmp`. -/
def merge2By {α : Type*} (cmp : α → α → Bool) : List α → List α → List α
  | [], ys => ys
  | xs, [] => xs
  | x :: xs, y :: ys =>
      if cmp x y then x :: merge2By cmp xs (y :: ys)
      else y :: merge2By cmp (x :: xs) ys
  termination_by xs ys => xs.length + ys.length

/-- `mergeBy :: (a → a → Bool) → [[a]] → [a]`, left as an exercise in the book.
    Merging sublists at each step is what lets us *maintain* the order of the
    candidates, which is what makes `thinBy` effective. -/
def mergeBy {α : Type*} (cmp : α → α → Bool) : List (List α) → List α :=
  List.foldr (merge2By cmp) []

def tstep (d : Denom) (ts : List Tuple) : List Tuple :=
  thinBy le₃ (mergeBy cmp₃ (ts.map (extend d)))

def mkchange (n : Nat) (ds : List Denom) : List Coin :=
  coins (minWith cost (ds.foldr tstep [([], n, 0)]))

-- `256 = 200 + 50 + 5 + 1`, four coins.
/--
info: [1, 0, 1, 0, 0, 1, 0, 1]
-/
#guard_msgs in
#eval mkchange 256 ukds

-- The greedy algorithm gives `20 + 5 + 5`; thinning finds `15 + 15`.
#guard mkchange 30 urds = [0,0,0,2,0,0,0]

#guard mkchange 20 ukds = [0,0,0,1,0,0,0,0]

/-
  Running time: `O(n^2 * k)` steps, where `n` is the amount for which change is
  required and `k` is the number of denominations. At each step at most `n+1`
  candidates are in play, since there is at most one candidate for each residual
  amount `0 ≤ r ≤ n`; a candidate with residue `r` has `O(r)` extensions, so
  there are `O(n^2)` new candidates before thinning.

  Coin-changing is an instance of the layered-network problem (Figure 10.2):
  each layer contains one vertex per residual amount, and the edges correspond
  to the choices for the number of coins of the next denomination. This is no
  accident: all thinning algorithms involving a fold can be regarded as a
  shortest-path problem on a directed acyclic graph.
-/

end CoinChanging

end Chapter10
