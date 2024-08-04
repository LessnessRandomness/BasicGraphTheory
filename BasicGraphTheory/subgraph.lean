import BasicGraphTheory.inductive_graphs

def subgraph {n} (g: simple_graph n) := {sg: simple_graph n // ∀ x y, adjacent sg x y → adjacent g x y}
