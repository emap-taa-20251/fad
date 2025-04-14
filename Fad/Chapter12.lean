import Fad.Chapter1

namespace Chapter12
open Chapter1 (concatMap)

abbrev Segment (a : Type) := List a
abbrev Partition (a : Type) := List (Segment a)

def splits {a : Type} : List a → List (List a × List a)
 | [] => []
 | x :: xs => ([x], xs) :: (splits xs).map fun ⟨ys, zs⟩ => (x :: ys, zs)

partial def parts: List a → List (Partition a)
 | [] => [[]]
 | xs =>
   (splits xs).flatMap fun ⟨ys, zs⟩ =>
     (parts zs).map fun yss => ys :: yss


def cons (x : a) (p : Partition a) : Partition a :=
 [x] :: p

def glue (x : a) : Partition a → Partition a
 | s :: p => (x :: s) :: p
 | []     => panic! "glue: empty partition"

def extendl (x : a) : Partition a → List (Partition a)
 | [] => [cons x []]
 | p  => [cons x p, glue x p]

def parts₁ : List Nat → List (Partition Nat) :=
  List.foldr (concatMap ∘ extendl) [[]]


def last [Inhabited a] : List a → a
 | [x]   => x
 | []    => panic! "last: empty list"
 | _::xs => last xs

def init [Inhabited a] : List a → List a
 | [_]     => []
 | []      => panic! "init: empty list"
 | x :: xs => x :: init xs

def snoc (x : a) (p : Partition a) : Partition a :=
 p ++ [[x]]

def bind (x : a) (p : Partition a) : Partition a :=
 init p ++ [last p ++ [x]]

def extendr (x : a) : Partition a → List (Partition a)
 | [] => [snoc x []]
 | p  => [snoc x p, bind x p]

def parts₂ : List Nat → List (Partition Nat) :=
  List.foldl (flip (concatMap ∘ extendr)) [[]]



end Chapter12
