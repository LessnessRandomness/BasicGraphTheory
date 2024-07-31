import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Tactic

-- inductive simple_graph: Nat → Type :=
--   | Empty: simple_graph 0
--   | Cons: forall n, Set (Fin (n + 1)) → simple_graph n → simple_graph (n + 1)
-- This version looks nicer but it didn't quite work out for me


-- definition of simple_graph

inductive pre_simple_graph: Nat → Type :=
  | Empty: pre_simple_graph 0
  | Cons: forall n, List Nat → pre_simple_graph n → pre_simple_graph (n + 1)

def correct_simple_graph {n} (g: pre_simple_graph n): Prop :=
  match g with
  | .Empty => True
  | .Cons m h t => h.Nodup ∧ (∀ x, x ∈ h → x < m) ∧ correct_simple_graph t

def simple_graph n := {g: pre_simple_graph n // correct_simple_graph g}


-- neighbors, degree and adjacency

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


-- basic properties of adjacency - symmetry and irreflexivity, also decidability instance

theorem adjacent_symm {n} (g: simple_graph n): Symmetric (adjacent g) := by
  intros x y
  unfold adjacent neighbors
  cases g; rename_i g Hg
  induction g with
  | Empty => unfold neighbors_aux
             simp
  | Cons m L g' iH => simp at *
                      unfold neighbors_aux
                      obtain ⟨Hg1, Hg2, Hg3⟩ := Hg
                      split_ifs with H1 H2 H3 H4 <;> intros H
                      . rw [<- H1, <- H2] at *
                        tauto
                      . simp
                        omega
                      . simp at *
                        apply iH Hg3
                        tauto
                      . simp at *
                        tauto
                      . simp at *
                        tauto
                      . simp at *
                        tauto
                      . simp
                        right
                        exact (iH Hg3 H)
                      . simp
                        right
                        exact (iH Hg3 H)
                      . exact (iH Hg3 H)

theorem adjacent_irrefl {n} (g: simple_graph n): Irreflexive (adjacent g) := by
  intros x
  unfold adjacent neighbors
  cases g; rename_i g Hg
  induction g with
  | Empty => unfold neighbors_aux
             simp
  | Cons m L g' iH => simp at *
                      unfold neighbors_aux
                      obtain ⟨Hg1, Hg2, Hg3⟩ := Hg
                      split_ifs with H1 H2 <;> intros H
                      . simp at *
                        obtain H | H := H
                        . apply Hg2 at H
                          omega
                        . exact (iH Hg3 H)
                      . simp at *
                        tauto
                      . tauto

instance adjacent_decidable: ∀ {n} (g: simple_graph n), DecidableRel (adjacent g) := by
  intros n g x y
  unfold adjacent
  infer_instance


-- Nodup for neighbors of node

theorem size_limit_on_adjacent_nodes {n} (x y: Nat) (g: simple_graph n) (H: adjacent g x y): x < n ∧ y < n := by
  cases g; rename_i g Hg
  unfold adjacent neighbors at *
  induction n with
  | zero => cases g
            unfold neighbors_aux at H
            simp at *
  | succ m iH => cases g; rename_i h g
                 unfold neighbors_aux at H
                 obtain ⟨Hg1, Hg2, Hg3⟩ := Hg
                 split_ifs at H with H0 H1
                 . simp at H
                   obtain H | H := H
                   . apply Hg2 at H
                     omega
                   . apply (iH _ Hg3) at H
                     omega
                 . simp at H
                   obtain H | H := H
                   . apply Hg2 at H1
                     omega
                   . apply (iH _ Hg3) at H
                     omega
                 . apply (iH _ Hg3) at H
                   omega

theorem neighbors_Nodup {n} (g: simple_graph n) x: (neighbors g x).Nodup := by
  induction n with
  | zero => cases g; rename_i g Hg
            unfold neighbors neighbors_aux
            split
            . simp
            . linarith
  | succ m iH => cases g; rename_i g Hg
                 cases g; rename_i h g
                 unfold neighbors neighbors_aux
                 obtain ⟨Hg1, Hg2, Hg3⟩ := Hg
                 split_ifs with H1 H2
                 . have H2: ∀ y, y ∈ neighbors_aux g x → False := by
                     intros y Hy
                     apply size_limit_on_adjacent_nodes _ _ ⟨g, Hg3⟩ at Hy
                     omega
                   have H3: neighbors_aux g x = [] := by
                     generalize (neighbors_aux g x) = W at *
                     cases W
                     . simp
                     . simp at H2
                       exfalso
                       rename_i head tail
                       have H3 := (H2 head).1
                       tauto
                   rw [H3]
                   simp
                   exact Hg1
                 . simp
                   constructor
                   . intros H3
                     apply size_limit_on_adjacent_nodes _ _ ⟨g, Hg3⟩ at H3
                     omega
                   . have H3 := iH ⟨g, Hg3⟩
                     unfold neighbors at H3
                     simp at H3
                     assumption
                 . have H3 := iH ⟨g, Hg3⟩
                   unfold neighbors at H3
                   simp at H3
                   exact H3


-- Edges - definition and few theorems

def edges_aux {n} (g: pre_simple_graph n): List (Nat × Nat) :=
  match g with
  | .Empty => []
  | .Cons m h t => edges_aux t ++ List.map (λ x => (m, x)) h

def edges {n} (g: simple_graph n) := edges_aux g.1

def edges_correctness {n} (g: simple_graph n): ∀ x y, y < x → ((x, y) ∈ edges g ↔ adjacent g x y) := by
  cases g; rename_i g Hg
  induction g with
  | Empty => intros x y _
             unfold edges edges_aux adjacent neighbors neighbors_aux
             simp
  | Cons _ h t iH => intros x y H
                     simp at *
                     obtain ⟨Hg1, Hg2, Hg3⟩ := Hg
                     rw [edges, edges_aux]
                     simp
                     unfold edges at iH
                     simp at *
                     rw [iH] <;> try assumption
                     unfold adjacent neighbors
                     simp
                     constructor <;> intro H0
                     . unfold neighbors_aux
                       split_ifs with H1 H2
                       . simp
                         tauto
                       . simp
                         obtain H0 | H0 := H0
                         . tauto
                         . apply Hg2 at H2
                           linarith
                       . obtain H0 | H0 := H0
                         . assumption
                         . tauto
                     . unfold neighbors_aux at H0
                       split_ifs at H0 with H1 H2
                       . simp at *
                         tauto
                       . simp at *
                         obtain H0 | H0 := H0
                         . apply Hg2 at H2
                           linarith
                         . tauto
                       . tauto
