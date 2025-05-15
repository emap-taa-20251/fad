
namespace Chapter9

/- 9.1 Graphs and spanning trees -/

abbrev Vertex := Nat
abbrev Weight := Int
abbrev Edge   := (Vertex × Vertex × Weight)
abbrev Graph  := (List Vertex × List Edge)

def nodes (g : Graph) : List Vertex := g.1
def edges (g : Graph) : List Edge := g.2
def souce  (e : Edge) : Vertex := e.1
def target (e : Edge) : Vertex := e.2.1
def weight (e : Edge) : Weight := e.2.2

abbrev AdjArray := Array (List (Vertex × Weight))


end Chapter9
