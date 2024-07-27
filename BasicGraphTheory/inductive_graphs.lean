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
              (List.filter (λ x => if G.Adj (fin_max m) x then true else false) (List.finRange m))
              (SimpleGraph_to_pre_simple_graph (remove_last G) (remove_last_adj_dec G))


def SimpleGraph_to_pre_simple_graph_correct {n: Nat} (G: SimpleGraph (Fin n))
  [inst: DecidableRel G.Adj]: correct_simple_graph (SimpleGraph_to_pre_simple_graph G inst) := by
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
                     have H := List.nodup_finRange m
                     clear Adj symm irrefl inst iH
                     generalize (List.finRange m) = W at *
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
                   cases Hw
                   cases w
                   simp at *
                   assumption
                 . apply iH

def SimpleGraph_to_simple_graph {n} (G: SimpleGraph (Fin n)) [inst: DecidableRel G.Adj]: simple_graph n :=
  ⟨SimpleGraph_to_pre_simple_graph G inst, SimpleGraph_to_pre_simple_graph_correct G⟩

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

theorem fin_aux00: ∀ {n} (f: Fin n), f ∈ List.finRange n := by
  intro n m
  refine List.mem_iff_get.mpr ?_
  have : m.val < (List.finRange n).length := by
    rw [List.length_finRange]
    exact m.2
  refine ⟨⟨m.val,this⟩,?_⟩
  simp only [List.get_eq_getElem, List.getElem_finRange, Fin.cast_mk, Fin.eta]


theorem aux00 {n} (x y: Nat) (t: simple_graph n) (H: y ∈ neighbors_aux t.1 x): x ≤ n ∧ y ≤ n := by
  cases t; rename_i t Ht
  induction n with
  | zero => cases t
            unfold neighbors_aux at H
            simp at *
  | succ m iH => cases t; rename_i h t
                 unfold neighbors_aux at H
                 split_ifs at H with H0 H1
                 . simp at H
                   obtain H | H := H
                   . unfold correct_simple_graph at Ht
                     obtain ⟨Ht1, Ht2, Ht3⟩ := Ht
                     apply Ht2 at H
                     omega
                   . unfold correct_simple_graph at Ht
                     obtain ⟨Ht1, Ht2, Ht3⟩ := Ht
                     apply (iH _ Ht3) at H
                     omega
                 . unfold correct_simple_graph at Ht
                   simp at *
                   obtain H | H := H
                   . obtain ⟨Ht1, Ht2, Ht3⟩ := Ht
                     apply Ht2 at H1
                     omega
                   . obtain ⟨Ht1, Ht2, Ht3⟩ := Ht
                     apply (iH _ Ht3) at H
                     omega
                 . unfold correct_simple_graph at Ht
                   obtain ⟨Ht1, Ht2, Ht3⟩ := Ht
                   apply (iH _ Ht3) at H
                   omega


theorem adj_proof_2 {n} (G: SimpleGraph (Fin n)) [inst: DecidableRel G.Adj] (x y: Fin n):
  G.Adj x y ↔ adjacent (SimpleGraph_to_simple_graph G) ↑x ↑y := by
  induction n with
  | zero => cases x; omega
  | succ m iH => have Hx: x = fin_max m ∨ x.1 < m := by
                   cases x
                   unfold fin_max
                   simp
                   omega
                 have Hy: y = fin_max m ∨ y.1 < m := by
                   cases y
                   unfold fin_max
                   simp
                   omega
                 obtain Hx | Hx := Hx <;> obtain Hy | Hy := Hy
                 . rw [Hx, Hy]
                   simp
                   apply adjacent_irrefl
                 . constructor <;> intro H
                   . clear iH
                     unfold SimpleGraph_to_simple_graph SimpleGraph_to_pre_simple_graph
                     unfold adjacent neighbors neighbors_aux
                     simp
                     split_ifs with H0 H1
                     . simp
                       left
                       rw [List.mem_filter]
                       simp
                       constructor
                       . exists ⟨↑y, Hy⟩
                       . rw [Hx] at H
                         assumption
                     . unfold fin_max at Hx
                       cases x
                       simp at H0 Hx
                       omega
                     . unfold fin_max at Hx
                       cases x
                       simp at H0 Hx
                       omega
                   . clear iH
                     unfold SimpleGraph_to_simple_graph SimpleGraph_to_pre_simple_graph at H
                     unfold adjacent neighbors neighbors_aux at H
                     simp at H
                     split_ifs at H with H0 H1
                     . simp at H
                       obtain H | H := H
                       . rw [List.mem_filter] at H
                         simp at H
                         obtain ⟨H, H1⟩ := H
                         rw [Hx]
                         assumption
                       . unfold neighbors_aux at H
                         split at H
                         . simp at *
                         . rename_i heq
                           split_ifs at H with H1 H2
                           . linarith
                           . simp at *
                             exfalso
                             have H3 := SimpleGraph_to_pre_simple_graph_correct (remove_last G)
                             rewrite [heq] at H3
                             unfold correct_simple_graph at H3
                             obtain ⟨H4, H5, H6⟩ := H3
                             apply H5 at H2
                             linarith
                           . exfalso
                             have H3 := SimpleGraph_to_pre_simple_graph_correct (remove_last G)
                             rewrite [heq] at H3
                             unfold correct_simple_graph at H3
                             obtain ⟨H4, H5, H6⟩ := H3
                             have H7 := aux00 _ _ ⟨_, H6⟩ H
                             linarith
                     . cases x
                       unfold fin_max at *
                       simp at *
                       omega
                     . cases x
                       unfold fin_max at *
                       simp at *
                       omega
                 . constructor <;> intro H
                   . clear iH
                     apply G.symm at H
                     apply adjacent_symm
                     unfold SimpleGraph_to_simple_graph SimpleGraph_to_pre_simple_graph
                     unfold adjacent neighbors neighbors_aux
                     simp
                     split_ifs with H0 H1
                     . simp
                       left
                       rw [List.mem_filter]
                       simp
                       constructor
                       . exists ⟨↑x, Hx⟩
                       . rw [Hy] at H
                         assumption
                     . unfold fin_max at Hy
                       cases y
                       simp at H0 Hy
                       omega
                     . unfold fin_max at Hy
                       cases y
                       simp at H0 Hy
                       omega
                   . clear iH
                     apply G.symm
                     apply adjacent_symm at H
                     unfold SimpleGraph_to_simple_graph SimpleGraph_to_pre_simple_graph at H
                     unfold adjacent neighbors neighbors_aux at H
                     simp at H
                     split_ifs at H with H0 H1
                     . simp at H
                       obtain H | H := H
                       . rw [List.mem_filter] at H
                         simp at H
                         obtain ⟨H, H1⟩ := H
                         rw [Hy]
                         assumption
                       . unfold neighbors_aux at H
                         split at H
                         . simp at *
                         . rename_i heq
                           split_ifs at H with H1 H2
                           . linarith
                           . simp at *
                             exfalso
                             have H3 := SimpleGraph_to_pre_simple_graph_correct (remove_last G)
                             rewrite [heq] at H3
                             unfold correct_simple_graph at H3
                             obtain ⟨H4, H5, H6⟩ := H3
                             apply H5 at H2
                             linarith
                           . exfalso
                             have H3 := SimpleGraph_to_pre_simple_graph_correct (remove_last G)
                             rewrite [heq] at H3
                             unfold correct_simple_graph at H3
                             obtain ⟨H4, H5, H6⟩ := H3
                             have H7 := aux00 _ _ ⟨_, H6⟩ H
                             linarith
                     . cases y
                       unfold fin_max at *
                       simp at *
                       omega
                     . cases y
                       unfold fin_max at *
                       simp at *
                       omega
                 . have H := iH (remove_last G) ⟨_, Hx⟩ ⟨_, Hy⟩
                   clear iH
                   constructor <;> intro H0
                   . unfold SimpleGraph_to_simple_graph at *
                     unfold SimpleGraph_to_pre_simple_graph
                     simp
                     unfold adjacent at *
                     unfold neighbors at *
                     unfold neighbors_aux
                     have H1: (remove_last G).Adj ⟨_, Hx⟩ ⟨_, Hy⟩ := by
                       unfold remove_last
                       simp
                       cases x
                       cases y
                       unfold increase_fin_limit
                       simp at *
                       apply H0
                     rw [H] at H1
                     clear H
                     simp at *
                     split_ifs with H2 H3
                     . omega
                     . rw [List.mem_filter] at H3
                       simp at *
                       have H4: ↑y = m ∨ ↑y < m := by
                         cases y
                         simp at *
                         omega
                       obtain H4 | H4 := H4
                       . tauto
                       . right
                         exact H1
                     . clear H3
                       exact H1
                   . unfold SimpleGraph_to_simple_graph at *
                     unfold SimpleGraph_to_pre_simple_graph at H0
                     simp at *
                     unfold adjacent at *
                     unfold neighbors at *
                     unfold neighbors_aux at H0
                     simp at *
                     split_ifs at H0 with H1 H2
                     . simp at *
                       obtain H0 | H0 := H0
                       . omega
                       . rw [<- H] at H0
                         unfold remove_last at H0
                         simp at H0
                         unfold increase_fin_limit at H0
                         simp at H0
                         assumption
                     . clear H2
                       simp at H0
                       obtain H0 | H0 := H0
                       . omega
                       . rewrite [<- H] at H0
                         unfold remove_last at H0
                         simp at *
                         unfold increase_fin_limit at H0
                         simp at H0
                         assumption
                     . rewrite [<- H] at H0
                       unfold remove_last at H0
                       simp at H0
                       unfold increase_fin_limit at H0
                       simp at H0
                       assumption
