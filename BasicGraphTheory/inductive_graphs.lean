import Batteries.Data.Fin.Basic
import Batteries.Data.Fin.Lemmas
import Mathlib

-- inductive simple_graph: Nat → Type :=
--   | Empty: simple_graph 0
--   | Cons: forall n, Set (Fin (n + 1)) → simple_graph n → simple_graph (n + 1)


inductive pre_simple_graph: Nat → Type :=
  | Empty: pre_simple_graph 0
  | Cons: forall n, List Nat → pre_simple_graph n → pre_simple_graph (n + 1)

def correct_simple_graph {n} (g: pre_simple_graph n): Prop :=
  match g with
  | .Empty => True
  | .Cons m h t => h.Nodup ∧ (∀ x, x ∈ h → x < m) ∧ correct_simple_graph t

def simple_graph n := { g: pre_simple_graph n // correct_simple_graph g}

def neighbors_aux {n} (g: pre_simple_graph n) (x: Nat): List Nat :=
  match g with
  | .Empty => []
  | .Cons m L g' => if m = x
                    then L ++ neighbors_aux g' x
                    else if x ∈ L
                         then m :: neighbors_aux g' x
                         else neighbors_aux g' x

def neighbors {n} (g: simple_graph n) (x: Nat): List Nat := neighbors_aux g.1 x

def adjacent {n} (g: simple_graph n) (x y: Nat): Prop := y ∈ neighbors g x

def degree {n} (g: simple_graph n) (x: Nat): Nat := (neighbors g x).length

theorem adjacent_symm {n} (g: simple_graph n) (x y: Nat):
  adjacent g x y → adjacent g y x := by
  unfold adjacent
  unfold neighbors
  cases g; rename_i g Hg
  simp
  induction g with
  | Empty => unfold neighbors_aux
             simp
  | Cons m L g' iH => simp at *
                      obtain ⟨Hg1, Hg2, Hg3⟩ := Hg
                      unfold neighbors_aux
                      split_ifs
                      . have H: x = y := by omega
                        cases H
                        tauto
                      . simp
                        omega
                      . intros H
                        simp at H
                        have H1: y ∈ neighbors_aux g' x := by tauto
                        exact (iH Hg3 H1)
                      . simp
                        tauto
                      . simp
                        intros H1
                        obtain H1 | H1 := H1
                        . omega
                        . right
                          exact (iH Hg3 H1)
                      . simp
                        intros H1
                        obtain H1 | H1 := H1
                        . omega
                        . exact (iH Hg3 H1)
                      . simp
                        intros H1
                        right
                        exact (iH Hg3 H1)
                      . intros H1
                        simp
                        right
                        exact (iH Hg3 H1)
                      . exact (iH Hg3)

theorem adjacent_irrefl {n} (g: simple_graph n) (x: Nat): adjacent g x x → False := by
  unfold adjacent
  intro H
  unfold neighbors at H
  cases g; rename_i g Hg
  simp at H
  induction g with
  | Empty => clear Hg
             unfold neighbors_aux at H
             simp at *
  | Cons m L g' iH => simp at *
                      unfold correct_simple_graph at Hg
                      obtain ⟨H0, H1, H2⟩ := Hg
                      unfold neighbors_aux at H
                      split_ifs at H with H3 H4
                      . simp at H
                        obtain H | H := H
                        . have H4 := iH H2
                          apply H4; clear H4
                          unfold neighbors_aux
                          split
                          . simp at *
                            exact (H1 x H)
                          . have H4 := H1 _ H
                            omega
                        . tauto
                      . simp at H
                        obtain H | H := H
                        . omega
                        . tauto
                      . tauto

-- One direction
def simple_graph_to_SimpleGraph {n} (g: simple_graph n): SimpleGraph (Fin n) := by
  refine (SimpleGraph.mk (λ x y => adjacent g x y) ?_ ?_)
  . unfold Symmetric
    simp
    intros x y
    apply adjacent_symm
  . unfold Irreflexive
    simp
    intros x
    apply adjacent_irrefl

def increase_fin_limit {n}: Fin n → Fin (n + 1) := by
  intros f
  cases f; rename_i x p
  exists x
  omega

def fin_max n: Fin (n + 1) := by
  exists n
  omega

def remove_last {n} (G: SimpleGraph (Fin (n + 1))): SimpleGraph (Fin n) := by
  refine (SimpleGraph.mk (λ x y => G.Adj (increase_fin_limit x) (increase_fin_limit y)) ?_ ?_)
  . cases G; rename_i Adj symm irrefl
    simp
    intros x y
    apply symm
  . cases G; rename_i Adj symm irrefl
    simp
    intros x
    apply irrefl

instance remove_last_adj_dec: ∀ {n} (G: SimpleGraph (Fin (n + 1))) [inst: DecidableRel G.Adj],
  DecidableRel (remove_last G).Adj := by
  unfold DecidableRel
  intros n G H a b
  unfold remove_last
  simp
  infer_instance

-- Second direction

def SimpleGraph_to_pre_simple_graph {n: Nat} (G: SimpleGraph (Fin n)) (inst: DecidableRel G.Adj):
  pre_simple_graph n :=
  match n with
  | 0 => .Empty
  | m + 1 => .Cons m
              (List.filter (λ x => if G.Adj (fin_max m) x then true else false) (Fin.list m))
              (SimpleGraph_to_pre_simple_graph (remove_last G) (remove_last_adj_dec G))

-- def SimpleGraph_to_pre_simple_graph {n: Nat} (G: SimpleGraph (Fin n))
--   [inst: DecidableRel G.Adj]: pre_simple_graph n := by
--   induction n with
--   | zero => exact .Empty
--   | succ m iH => refine (.Cons m ?_ (iH (remove_last G)))
--                  exact (List.filter (λ x => if G.Adj (fin_max m) x then true else false) (Fin.list m))

-- testing

instance topgraph_adj_dec: DecidableRel (⊤: SimpleGraph (Fin 5)).Adj := by
  intros x y
  infer_instance

#reduce (SimpleGraph_to_pre_simple_graph (⊤: SimpleGraph (Fin 5)) topgraph_adj_dec)
#reduce (neighbors_aux (SimpleGraph_to_pre_simple_graph (⊤: SimpleGraph (Fin 5)) topgraph_adj_dec) 0)
#reduce (neighbors_aux (SimpleGraph_to_pre_simple_graph (⊤: SimpleGraph (Fin 5)) topgraph_adj_dec) 1)


def pathgraph: SimpleGraph (Fin 4) := by
  refine (SimpleGraph.mk (λ (x y: Fin 4) => (y.1 < 3 ∧ x.1 = y.1 + 1) ∨ (x.1 < 3 ∧ y.1 = x.1 + 1)) ?_ ?_)
  . intros x y
    simp
    cases x
    cases y
    intros H
    simp at *
    tauto
  . intros x
    simp

instance pathgraph_adj_dec: DecidableRel pathgraph.Adj := by
  unfold DecidableRel
  intros x y
  unfold pathgraph
  simp
  infer_instance

#reduce (SimpleGraph_to_pre_simple_graph pathgraph pathgraph_adj_dec)
#reduce (neighbors_aux (SimpleGraph_to_pre_simple_graph pathgraph pathgraph_adj_dec) 2)
#reduce (neighbors_aux (SimpleGraph_to_pre_simple_graph pathgraph pathgraph_adj_dec) 3)



theorem fin_list_nodup n: (Fin.list n).Nodup := by
  sorry

def SimpleGraph_to_simple_graph {n: Nat} (G: SimpleGraph (Fin n))
  [inst: DecidableRel G.Adj]: simple_graph n := by
  exists (SimpleGraph_to_pre_simple_graph G inst)
  induction n with
  | zero => cases G; rename_i Adj symm irrefl
            unfold correct_simple_graph
            unfold SimpleGraph_to_pre_simple_graph
            simp
  | succ m iH => cases G; rename_i Adj symm irrefl
                 unfold correct_simple_graph
                 unfold SimpleGraph_to_pre_simple_graph
                 simp
                 refine ⟨?_, ?_, ?_⟩
                 . apply List.Nodup.filter
                   rw [List.nodup_bind]
                   refine ⟨?_, ?_⟩
                   . simp
                   . simp
                     have H := fin_list_nodup m
                     generalize (Fin.list m) = W at *
                     clear Adj symm irrefl inst iH
                     induction W with
                     | nil => simp
                     | cons x t iH => simp at *
                                      obtain ⟨H, H0⟩ := H
                                      constructor
                                      . intros f Hf H1
                                        rw [<- Fin.ext_iff] at H1
                                        cases H1
                                        tauto
                                      . tauto
                 . intros x Hx
                   rw [List.mem_filter] at Hx
                   simp at Hx
                   obtain ⟨H, H0⟩ := Hx
                   cases H; rename_i w Hw
                   cases Hw; rename_i H1 H2
                   cases w
                   simp at *
                   omega
                 . apply iH

-- Proofs of adjacency relation preservation

theorem adj_proof_1 {n} (g: simple_graph n) (x y: Fin n): adjacent g ↑x ↑y ↔ (simple_graph_to_SimpleGraph g).Adj x y := by
  constructor <;> intros H
  . induction n with
    | zero => cases x; omega
    | succ m iH => cases g; rename_i g Hg
                   unfold simple_graph_to_SimpleGraph
                   simp
                   assumption
  . induction n with
    | zero => cases x; omega
    | succ m iH => cases g; rename_i g Hg
                   unfold simple_graph_to_SimpleGraph at H
                   simp at *
                   assumption

instance inst2: ∀ {n} (g: simple_graph n), DecidableRel (simple_graph_to_SimpleGraph g).Adj := by
  unfold simple_graph_to_SimpleGraph
  simp
  intros n g
  unfold DecidableRel
  intros x y
  unfold adjacent neighbors neighbors_aux
  simp
  cases g; rename_i g Hg
  cases n <;> simp at *
  . cases x
    omega
  . cases g; simp at *
    split_ifs
    . infer_instance
    . infer_instance
    . infer_instance

theorem adj_proof_2 {n} (G: SimpleGraph (Fin n)) [inst: DecidableRel G.Adj] (x y: Fin n):
  G.Adj x y ↔ adjacent (SimpleGraph_to_simple_graph G) ↑x ↑y := by
  sorry
