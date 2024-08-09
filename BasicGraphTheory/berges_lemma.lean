import Mathlib.Data.List.Dedup
import BasicGraphTheory.inductive_graphs
import BasicGraphTheory.basic_operations
import BasicGraphTheory.relation_to_SimpleGraph

def subgraph {n} (g: simple_graph n) := {sg: simple_graph n // ∀ x y, adjacent sg x y → adjacent g x y}

def subgraph_complement {n} (g: simple_graph n) (sg: subgraph g): subgraph g := by
  exists (diff g sg.1)
  intros x y H
  have H0 := size_limit_on_adjacent_nodes x y ⟨_, diff_aux_correct_graph g sg.1⟩ H
  have H1: x = y ∨ x ≠ y := by omega
  obtain H1 | H1 := H1
  . subst H1
    apply adjacent_irrefl at H
    tauto
  . rw [diff_thm g sg.1 H0.1 H0.2 H1] at H
    tauto

def matching {n} (g: simple_graph n) :=
  { L: List (Nat × Nat) //
    L.Pairwise (λ p1 p2 => List.Disjoint [p1.1, p1.2] [p2.1, p2.2]) ∧
    ∀ p ∈ L, adjacent g p.1 p.2 }


def matching_to_SimpleGraph {n} {g: simple_graph n} (m: matching g): SimpleGraph (Fin n) := by
  refine (SimpleGraph.mk (λ x y => (x.1, y.1) ∈ m.1 ∨ (y.1, x.1) ∈ m.1) ?_ ?_)
  . intros x y H
    tauto
  . intro x H
    cases m; rename_i m Hm
    obtain ⟨Hm1, Hm2⟩ := Hm
    obtain H | H := H
    . apply Hm2 at H
      simp at H
      apply adjacent_irrefl at H
      tauto
    . apply Hm2 at H
      simp at H
      apply adjacent_irrefl at H
      tauto

def matching_to_simple_graph {n} {g: simple_graph n} (m: matching g): simple_graph n := by
  refine (@SimpleGraph_to_simple_graph n (matching_to_SimpleGraph m) ?_)
  unfold matching_to_SimpleGraph
  simp
  infer_instance

def matching_to_subgraph {n} {g: simple_graph n} (m: matching g): subgraph g := by
  exists (matching_to_simple_graph m)
  unfold matching_to_simple_graph
  intros x y H
  have H0 := size_limit_on_adjacent_nodes x y _ H
  let inst: DecidableRel (matching_to_SimpleGraph m).Adj := by
    unfold matching_to_SimpleGraph
    simp
    infer_instance
  rw [<- adj_preserved_SG_to_sg _ ⟨x, H0.1⟩ ⟨y, H0.2⟩] at H
  unfold matching_to_SimpleGraph at H
  simp at H
  cases m; rename_i m Hm
  obtain ⟨Hm1, Hm2⟩ := Hm
  obtain H | H := H
  . apply Hm2 at H
    simp at H
    tauto
  . apply Hm2 at H
    simp at H
    apply adjacent_symm
    tauto

def is_maximum_matching {n} {g: simple_graph n} (m: matching g) :=
  ∀ (m': matching g), m'.1.length ≤ m.1.length

inductive walk {n} (g: simple_graph n): Nat → Nat → Type u
  | nil {u} (H: u < n): walk g u u
  | cons {u v w} (h: adjacent g u v) (p: walk g v w): walk g u w

def verts_of_walk {n} {g: simple_graph n} {x y} (w: walk g x y): List Nat :=
  match w with
  | @walk.nil _ _ u _ => [u]
  | @walk.cons _ _ u _ _ _ p => u :: verts_of_walk p

def is_path {n} {g: simple_graph n} {x y} (w: walk g x y): Prop :=
  match w with
  | walk.nil _ => True
  | @walk.cons _ _ u v _ _ w' => u ≠ v ∧ is_path w'

def alternating_walk {n} {g: simple_graph n} (s1 s2: subgraph g) {x y: Nat} (b: Bool) (W: walk g x y): Prop :=
  match b, W with
  | _, walk.nil H => True
  | true, @walk.cons _ _ x' y' _ _ p => adjacent s1.1 x' y' ∧ alternating_walk s1 s2 false p
  | false, @walk.cons _ _ x' y' _ _ p => adjacent s2.1 x' y' ∧ alternating_walk s1 s2 true p

def augmenting_path {n} {g: simple_graph n} (s: subgraph g) {x y} (p: { w: walk g x y // is_path w }): Prop :=
  x ∉ verts_of_walk p.1 ∧ y ∉ verts_of_walk p.1 ∧ alternating_walk s (subgraph_complement g s) false p.1

def subgraph_symmdiff {n} {g: simple_graph n} (s1 s2: subgraph g): subgraph g := by
  exists (symm_diff s1.1 s2.1)
  intros x y H
  unfold symm_diff at H
  have H0 := size_limit_on_adjacent_nodes x y ⟨_, union_aux_correct_graph _ _⟩ H
  have H1: x = y ∨ x ≠ y := by omega
  obtain H1 | H1 := H1
  . subst H1
    apply adjacent_irrefl at H
    tauto
  . rw [union_thm _ _ H0.1 H0.2 H1] at H
    rw [diff_thm _ _ H0.1 H0.2 H1, diff_thm _ _ H0.1 H0.2 H1] at H
    cases s1
    cases s2
    tauto


def disjoint_subgraphs {n} {g: simple_graph n} (s1 s2: subgraph g): Prop :=
  ∀ x y, adjacent s1.1 x y → adjacent s2.1 x y → False

theorem aux0 {n} {g: simple_graph n} {s1 s2: subgraph g} (H: disjoint_subgraphs s1 s2):
  forall x, x < n → degree (union s1.1 s2.1) x = degree s1.1 x + degree s2.1 x := by
  sorry

theorem aux1 {n} {g: simple_graph n} (m1 m2: matching g):
  let s1 := matching_to_subgraph m1
  let s2 := matching_to_subgraph m2
  let S := subgraph_symmdiff s1 s2
  ∀ x, x < n → degree S.1 x ≤ 2 := by
  sorry


theorem Berge's_lemma {n} {g: simple_graph n} {m: matching g}:
  is_maximum_matching m ↔ (∀ x y (p: { w: walk g x y // is_path w }), ¬ augmenting_path (matching_to_subgraph m) p)
