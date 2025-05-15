import Fad.Chapter9
import Fad.Chapter3

namespace Chapter9
open Chapter3 (accumArray)

def toAdj (g : Graph) : AdjArray :=
  accumArray (flip List.cons) [] g.1.length (edges g)

def toGraph (adj : AdjArray) : Graph :=
  let vs := List.range adj.size
  let es : List Edge := adj.toList.zipIdx.map (λ (a,b) => (b,a))
    |>.flatMap
   (λ (v, ps) => ps.map (λ p => (v, p.1, p.2)))
  (vs, es)

def g : Graph :=
 ([0, 1, 2, 3],
  [(0, 1, 1), (1, 2, 5), (1, 3, 10), (2, 3, 2), (3, 0, 4)])

-- #eval toAdj g |> toGraph

end Chapter9
