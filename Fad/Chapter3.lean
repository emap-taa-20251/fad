import Fad.Chapter1
import Fad.«Chapter1-Ex»

namespace Chapter3

open List (reverse tail cons)

-- # Section 3.1 Symmetric lists

def _root_.List.single (xs : List α) : Bool := xs.length = 1

def snoc {a : Type} (x : a) (xs : List a) : List a :=
  xs ++ [x]


namespace SL1

variable {α : Type}

abbrev SymList (α : Type u) := (List α) × (List α)

def nilSL : SymList α := ([], [])

def fromSL (sl : SymList α) : List α :=
 sl.1 ++ sl.2.reverse

def snocSL : α → SymList α → SymList α
| z, ([], ys) => (ys, [z])
| z, (bs, ys) => (bs, z :: ys)

def consSL : α  → SymList α → SymList α
| z, (xs, []) => ([z], xs)
| z, (xs, ys) => (z :: xs, ys)

example (x : α) (xs : SymList α)
 : (snoc x ∘ fromSL) xs = (fromSL ∘ snocSL x) xs
 := by
 have (as, bs) := xs
 unfold Function.comp snoc
 induction as generalizing bs with
 | nil =>
   simp [snocSL, fromSL]; sorry
 | cons y ys ih => sorry


end SL1

/-
#check ([] : List Nat)
#eval ([] : List Nat).head?
#eval [1,2].head?
#eval [].head (by simp)
#eval [1,2].head (by simp)

def test (xs : List α) (ok : xs.length > 2) : α := xs[2]
#eval test [1, 2, 3, 4] (by simp)
-/

open Chapter1 (dropWhile)

/- it may simplify the proofs

structure SymList' (a : Type) where
  lhs : List a
  rhs : List a
  ok : (lhs.length = 0 → rhs.length ≤ 1) ∧
       (rhs.length = 0 → lhs.length ≤ 1)
 deriving Repr
-/

structure SymList (a : Type) where
  lhs : List a
  rhs : List a
  ok : (lhs.isEmpty → rhs.isEmpty ∨ rhs.length = 1) ∧
       (rhs.isEmpty → lhs.isEmpty ∨ lhs.length = 1)
 deriving Repr

namespace SymList

variable {a : Type}

def nil : SymList a := SymList.mk [] [] (by simp)

instance : Inhabited (SymList a) where
  default := nil

def fromSL (sl : SymList a) : List a :=
 sl.lhs ++ sl.rhs.reverse

def consSL : a → SymList a → SymList a
| z, ⟨xs, [], _⟩ => SymList.mk [z] xs (by simp)
| z, ⟨xs, y :: ys, _⟩ => SymList.mk (z :: xs) (y :: ys) (by simp)

def snocSL : a → SymList a → SymList a
| z, ⟨ [], bs, _ ⟩ => ⟨bs, [z], by simp⟩
| z, ⟨ a :: as, bs, _ ⟩ => ⟨a :: as, z :: bs, by simp⟩

example (x : a) : cons x ∘ fromSL = fromSL ∘ consSL x := by
 funext s
 cases s with
 | mk as bs h =>
   cases bs with
   | nil =>
     simp [consSL, fromSL]
     simp at h
     apply Or.elim h
     intro h1 ; rw [h1]; simp
     intro h1
     cases as with
     | nil => simp
     | cons z zs =>
       simp at h1
       rw [h1]; simp
   | cons z zs => simp [consSL, fromSL]

example (x : a) : snoc x ∘ fromSL = fromSL ∘ snocSL x := by
  funext sl
  simp [Function.comp]
  have ⟨lhs, rhs, ok⟩ := sl
  unfold snoc snocSL fromSL
  match h: lhs with
  | [] =>
    simp [h]
    simp at ok
    apply ok.elim <;> intro h2; simp [h2]
    have a :: [] := rhs
    simp
  | y :: ys => simp

def isEmpty (sl : SymList a) : Bool :=
  sl.lhs.isEmpty ∧ sl.rhs.isEmpty

theorem sl_empty_l_empty :
  ∀ sl : SymList a, isEmpty sl → (fromSL sl).isEmpty
  := by
  intro sl h
  have ⟨as, bs, h₁⟩ := sl
  unfold isEmpty at h
  simp at h
  simp [fromSL]
  assumption

theorem sl_noempty_l_noempty :
  ∀ sl : SymList a, ¬ isEmpty sl → (fromSL sl) ≠ []
  := by
  intro sl h
  have ⟨as, bs, h₁⟩ := sl
  unfold isEmpty at h
  simp at h
  simp [fromSL]
  assumption


def lastSL (sl : SymList a) (ne : ¬ isEmpty sl) : a :=
 match sl with
 | ⟨xs, ys, _⟩ =>
   if h₁ : ys.isEmpty then
     xs.head (by
      unfold isEmpty at ne; simp at ne
      intro h₂
      apply ne
      exact h₂
      simp at h₁
      exact h₁)
   else
     ys.head (by simp at h₁ ; exact h₁)

def lastSL? : SymList a → Option a
| ⟨[], [], _⟩ => none
| ⟨x :: _, [], _⟩ => x
| ⟨[], y :: _, _⟩ => y
| ⟨_, y :: _, _⟩ => y

example (sl : SymList a) (h : ¬ isEmpty sl)
  : (fromSL sl).getLast (sl_noempty_l_noempty sl h) = lastSL sl h := by
  have ⟨as, bs, h₂⟩ := sl
  unfold lastSL fromSL
  have h₃ := sl_noempty_l_noempty _ h
  simp [fromSL] at h₃ ; simp
  sorry

/-
example {a : Type} : List.getLast? ∘ fromSL = @lastSL a := by
  funext sl
  have ⟨lhs, rhs, ok⟩ := sl
  simp [Function.comp, lastSL, fromSL]
  split <;> rename_i h
  rw [List.isEmpty_iff] at h
  subst h
  simp at ok ⊢
  apply ok.elim <;> intro h2
  simp [h2]
  have y :: [] := lhs
  simp
  have z :: _ := rhs
  simp
-/


def _root_.List.toSL : List a → SymList a
 | [] => nil
 | x :: xs => consSL x (toSL xs)

def headSL : SymList a → Option a
 | ⟨[], [], _⟩     => none
 | ⟨[], y :: _, _⟩ => some y
 | ⟨x::_, _, _⟩    => some x

def headSL! [Inhabited a] : SymList a → a
 | ⟨[], [], _⟩     => panic!"empty list"
 | ⟨[], y :: _, _⟩ => y
 | ⟨x::_, _, _⟩    => x


def singleSL (sl : SymList a): Bool :=
  (List.single sl.lhs ∧ sl.rhs.isEmpty) ∨
  (List.single sl.rhs ∧ sl.lhs.isEmpty)

def lengthSL (sl : SymList a) : Nat :=
  sl.lhs.length + sl.rhs.length


/- subtipos -/

def splitInTwoSL (xs : List a) : SymList a :=
  let p := List.MergeSort.Internal.splitInTwo (Subtype.mk xs (by rfl))
  SymList.mk p.1.val p.2.val.reverse (by
    have ⟨⟨as, aok⟩, ⟨bs, bok⟩⟩ := p
    simp [aok, bok]
    apply And.intro <;>
     (intro h; simp [h] at bok aok)
    if h2: bs.length = 0 then simp at h2; simp [h2] else omega
    if h2: as.length = 0 then simp at h2; simp [h2] else omega)

def tailSL {a : Type} (as : SymList a) : SymList a :=
  match as with
  | ⟨xs, ys, ok⟩ =>
    if h : xs.isEmpty then nil
    else
      if h2 : xs.length = 1 then
        splitInTwoSL ys.reverse
      else
        SymList.mk xs.tail ys (by
         simp [← not_congr List.length_eq_zero_iff] at h
         apply And.intro
         all_goals intro h3; have k :: (l :: ms) := xs
         repeat simp [ok] at *)

example : ∀ (as : SymList a), fromSL (tailSL as) = tail (fromSL as) := by
  intro sl
  have ⟨xs, ys, ok⟩ := sl
  cases xs with
  | nil =>
    induction ys with
    | nil => simp [tailSL, fromSL, nil]
    | cons b bs ih =>
      simp [fromSL, tailSL, nil]
      simp [ok] at *
      rw [ok]
      rw [List.reverse_nil, List.nil_append, List.tail]
  | cons a as =>
    induction ys with
    | nil =>
      by_cases h : as = [] <;> simp [h, fromSL, tailSL, splitInTwoSL]
    | cons b bs ih =>
      by_cases h: as = []
      . simp [h, List.tail, fromSL] at ih
        simp [h, fromSL, tailSL]
        simp [splitInTwoSL]
      . simp [tailSL, h, fromSL]


theorem length_sl_eq_length (xs : List a)
 : lengthSL (splitInTwoSL xs) = List.length xs := by
  simp [splitInTwoSL, lengthSL]
  omega


theorem length_tail_lt_length (sl : SymList a) (h : sl ≠ nilSL)
 : lengthSL sl > lengthSL (tailSL sl) := by
  have ⟨lsl, rsl, _⟩ := sl
  unfold lengthSL tailSL
  sorry


theorem headSL_none_iff_nilSL {sl : SymList a} : headSL sl = none ↔ sl = nil := by
  apply Iff.intro <;> intro h
  unfold headSL at h
  split at h
  unfold nil
  exact rfl
  repeat simp [eq_comm, <-Option.isNone_iff_eq_none] at h
  rw [h]
  unfold headSL nil
  simp

theorem lengthSL_zero_iff_nilSL: lengthSL sl = 0 ↔ sl = nil := by
  apply Iff.intro <;> intro h
  rw [lengthSL] at h
  rw [Nat.add_eq_zero_iff] at h
  repeat rw [List.length_eq_zero_iff] at h
  unfold nil
  have ⟨h1, h2⟩ := h
  have ⟨lhs, rhs, ok⟩ := sl
  simp at h1 h2
  simp [h1, h2]
  rw [h]
  unfold nil lengthSL
  simp

def dropWhileSL (p : a → Bool) (sl : SymList a) : SymList a :=
  if sl.lhs.isEmpty ∧ sl.rhs.isEmpty then nil else
    match h: headSL sl with
    | none => nil
    | some hsl =>
      if p hsl then
        let tl := tailSL sl
        have : lengthSL (tailSL sl) < lengthSL sl := length_tail_lt_length sl (by
          if h2: sl = nil then
            rw [← headSL_none_iff_nilSL] at h2
            rw [h2] at h
            contradiction
          else
            exact h2
        )
        dropWhileSL p tl
      else sl
  termination_by lengthSL sl


example : List.head? ∘ fromSL = @headSL a := by
  funext sl
  have ⟨lhs, rhs, ok⟩ := sl
  simp [Function.comp, headSL, fromSL]
  split <;> (
    rename_i h
    simp at h
    have ⟨ha, hb⟩ := h
    subst ha hb
    simp
  )
  simp at ok
  simp [ok]


/-
example : List.dropLast ∘ fromSL = fromSL ∘ @initSL a := by
  funext sl
  have ⟨lhs, rhs, ok⟩ := sl
  simp [fromSL]
  unfold List.dropLast
  by_cases hl: lhs = []
  subst hl
  simp at ok
  . by_cases hr: rhs = []
    . subst hr
      simp [initSL, nil]
    . have _ :: [] := rhs
      simp [initSL, splitInTwoSL]
  . by_cases hr: rhs = []
    . subst hr
      simp [hl] at ok
      have _ :: [] := lhs
      simp [initSL, nil]
    . match hc: lhs ++ rhs.reverse with
      | [] =>
        rw [List.append_eq_nil_iff] at hc
        have ⟨hln, _⟩ := hc
        contradiction
      | [_] =>
        rw [←(not_congr (List.length_eq_zero_iff)),
            ← ne_eq, Nat.ne_zero_iff_zero_lt] at hl hr
        have h2 : lhs.length + rhs.length > 1 := by omega
        have h3 := congrArg List.length hc
        simp at h3
        simp [h3] at h2
      | a :: as =>
        induction lhs ++ rhs.reverse with
        | nil =>
          have j :: js := lhs
          have k :: ks := rhs
          simp [← hc, initSL]
          by_cases hk: ks = [] <;> (
            by_cases hj: js = [] <;>
              simp [hk, hj, splitInTwoSL]
          )
        | cons _ _ ih =>
          assumption
-/

example (p : a → Bool)
  : dropWhile p ∘ fromSL = fromSL ∘ dropWhileSL p := by
  funext sl
  have ⟨lhs, rhs, ok⟩ := sl
  simp [Function.comp]
  sorry

end SymList

/- examples of use -/

open List (map reverse tails) in

def inits₁ {a : Type} : List a → List (List a) :=
 map reverse ∘ reverse ∘ tails ∘ reverse

def inits₂ {a : Type} : List a → List (List a) :=
 List.map SymList.fromSL ∘ List.scanl (flip SymList.snocSL) SymList.nil


/- trying to prove inits₁ = inits₂ -/

theorem tails_append_singleton (xs : List α) (x : α) :
    (xs ++ [x]).tails = xs.tails.map (fun ys => ys ++ [x]) ++ [[]] := by
  induction xs with
  | nil      => simp
  | cons y ys ih =>
      simp [List.tails, ih, List.map_append]

theorem map_reverse_tails_snoc (x : α) (xs : List α) :
    List.map reverse (snoc x xs).tails =
      List.map (fun ys : List α => x :: reverse ys) xs.tails ++ [[]] := by
  simp [snoc, tails_append_singleton, List.map_append, List.map_map, Function.comp]

theorem map_reverse (f : α → β) (xs : List α) :
    List.map f xs.reverse = (List.map f xs).reverse := by
  induction xs
  all_goals
  simp

theorem scanl_cons {α β}
        (f : β → α → β) (b : β) (a : α) (as : List α) :
    List.scanl f b (a :: as) = b :: List.scanl f (f b a) as := rfl

theorem fromSL_snoc {α} (z : α) (sl : SymList α) :
    SymList.fromSL (SymList.snocSL z sl) = SymList.fromSL sl ++ [z] := by
  cases sl with
  | mk lhs rhs ok =>
      cases lhs with
      | nil =>
          cases rhs with
          | nil =>
              unfold SymList.fromSL
              unfold SymList.snocSL
              simp
          | cons y ys =>
              cases ys with
              | nil =>
                  unfold SymList.fromSL
                  unfold SymList.snocSL
                  simp
              | cons z zs =>
                  have hFalse : False := by
                    have h := (ok.left) (by simp)
                    cases h with
                    | inl h0 =>
                        simp at h0
                    | inr hlen1 =>
                        have : (List.length (y :: z :: zs)) = 1 := by
                          simp at hlen1
                        simp at this
                  cases hFalse
      | cons a as =>
          simp [SymList.snocSL, SymList.fromSL, List.reverse_cons, List.append_assoc]


theorem inits_eq {a : Type} : ∀ xs : List a, inits₁ xs = inits₂ xs
  | [] => by
    unfold inits₁ inits₂ SymList.fromSL SymList.nil
    simp
  | x :: xs => by
    have ih := inits_eq xs
    simp [ inits₁, inits₂,
            List.reverse_cons,
            map_reverse_tails_snoc,
            scanl_cons, fromSL_snoc, ih,
            Function.comp, flip, map_reverse] at *
    sorry


-- # Section 3.2 Random-access lists

def fetch {a : Type} : Nat → List a → Option a
 | _, [] => none
 | k, x :: xs => if k = 0 then x else fetch (k - 1) xs

/-
#eval [1,2,3,4].get? 2
#eval fetch 2 [1,2,3,4]
-/

inductive Tree (α : Type) : Type where
 | leaf (n : α) : Tree α
 | node (n : Nat) (t₁ : Tree α) (t₂ : Tree α) : Tree α
 deriving Repr

def Tree.toString {α : Type} [ToString α] : Tree α → String
 | leaf x => s!"leaf {x}"
 | node n t₁ t₂ => s!"node {n} ({t₁.toString}) ({t₂.toString})"

instance {α : Type} [ToString α] : ToString (Tree α) where
  toString := Tree.toString

def Tree.size {a : Type} : Tree a → Nat
 | leaf _ => 1
 | node n _ _ => n

def Tree.height : Tree α → Nat
 | leaf _ => 1
 | node _ t₁ t₂ => 1 + max t₁.height t₂.height

def Tree.mk (t₁ t₂ : Tree a) : Tree a :=
 node (t₁.size + t₂.size) t₁ t₂

open Tree

-- #eval mk (mk (leaf 'a') (leaf 'b')) (mk (leaf 'c') (leaf 'd'))

inductive Digit (a : Type) : Type where
 | zero : Digit a
 | one (t : Tree a) : Digit a
 deriving Repr

def Digit.toString [ToString α] : Digit α → String
  | zero => "zero"
  | one t => s!"one ({t.toString})"

instance {α : Type} [ToString α] : ToString (Digit α) where
  toString := Digit.toString

open Digit

-- works with def too
abbrev RAList (a : Type) : Type := List (Digit a)

-- #check ([Digit.zero, Digit.zero] : RAList Nat)

def concat1 {a : Type} : List (List a) → List a :=
 List.foldr List.append []

def concatMap (f : a → List b) : List a → List b :=
 concat1 ∘ (List.map f)


def fromT : Tree a → List a
 | (leaf x) => [x]
 | (node _ t₁ t₂) => fromT t₁ ++ fromT t₂

def fromRA : RAList a → List a :=
  concatMap frm
 where
  frm : Digit a → List a
   | Digit.zero => []
   | Digit.one t => fromT t

/-
#eval fromRA [zero,
        one (mk (leaf 'a') (leaf 'b')),
        one (mk (mk (leaf 'c') (leaf 'd'))
                (mk (leaf 'e') (leaf 'f')))]
-/

def fetchT [ToString a] (n : Nat) (t : Tree a) : Option a :=
 match n, t with
 | 0, leaf x => x
 | k, (node n t₁ t₂) =>
   let m := n / 2
   if k < m then fetchT k t₁ else fetchT (k - m) t₂
 | _, leaf _ => none

def fetchRA [ToString a] (n : Nat) (ra : RAList a) : Option a :=
 match n, ra with
 | _, [] => none
 | k, (zero :: xs) => fetchRA k xs
 | k, (one t :: xs) =>
   if k < size t then fetchT k t else fetchRA (k - size t) xs

/-
#eval fetchRA 10 [zero,
        one (mk (leaf 'a') (leaf 'b')),
        one (mk (mk (leaf 'c') (leaf 'd'))
                (mk (leaf 'e') (leaf 'f')))]
-/

def nilRA {a : Type} : RAList a := []

def consRA {a : Type} (x : a) (xs : RAList a) : RAList a :=
 consT (Tree.leaf x) xs
where
 consT : Tree a → RAList a → RAList a
 | t1, [] => [Digit.one t1]
 | t1, Digit.zero :: xs => Digit.one t1 :: xs
 | t1, Digit.one t2 :: xs => Digit.zero :: consT (Tree.mk t1 t2) xs

-- #eval [3,1,6,8,9,0,5] |>.foldl (λ a r => consRA r a) nilRA

/- # Section 3.3 Arrays -/

def listArray (xs : List α) : Array α :=
  xs.toArray

def accumArray (f : α → β → α) (ini : α) (r : Nat)
               (xs : List (Nat × β)) : Array α :=
 let helper (i : Nat) :=
    xs.filter (·.1 = i) |>.foldl (λ ac p ↦ f ac p.2) ini
 (List.range r).map helper |>.toArray

/-
#eval accumArray (· + ·) 0 4
 [(1, 20),(1, 56),(1, 10),(1, 20), (2, 30), (1, 40), (2, 50)]

#eval accumArray (flip List.cons) [] 3
  [(0, "Apple"), (0, "Apricot")]
-/

end Chapter3
