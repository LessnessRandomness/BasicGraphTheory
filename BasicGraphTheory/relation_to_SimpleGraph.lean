import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import BasicGraphTheory.auxiliary_lemmas
import BasicGraphTheory.inductive_graphs


-- Conversion from simple_graph to SimpleGraph of Fin

def simple_graph_to_SimpleGraph {n} (g: simple_graph n): SimpleGraph (Fin n) := by
  refine (SimpleGraph.mk (λ x y ↦ adjacent g x y) ?_ ?_)
  . intros x y
    apply adjacent_symm
  . intros x
    apply adjacent_irrefl


-- Conversion from SimpleGraph (Fin n) to simple_graph n

def fin_limit_succ {n}: Fin n → Fin (n + 1)
  | ⟨i, h⟩ => ⟨i, by omega⟩

def remove_last {n} (G: SimpleGraph (Fin (n + 1))): SimpleGraph (Fin n) := by
  refine (SimpleGraph.mk (λ x y ↦ G.Adj (fin_limit_succ x) (fin_limit_succ y)) ?_ ?_)
  . intros x y
    apply G.symm
  . intros x
    apply G.irrefl

instance remove_last_adj_dec {n} (G: SimpleGraph (Fin (n + 1))) [DecidableRel G.Adj]: DecidableRel (remove_last G).Adj := by
  unfold DecidableRel remove_last
  simp
  infer_instance

-- Why can't I change (inst: DecidableRel G.Adj) to [DecidableRel G.Adj]?
def SimpleGraph_to_pre_simple_graph {n: Nat} (G: SimpleGraph (Fin n)) (inst: DecidableRel G.Adj): pre_simple_graph n :=
  match n with
  | 0 => .Empty
  | m + 1 => .Cons m
              (List.filter (λ x => decide (G.Adj (Fin.last m) x)) (List.finRange m))
              (SimpleGraph_to_pre_simple_graph (remove_last G) (remove_last_adj_dec G))

def SimpleGraph_to_pre_simple_graph_correct {n: Nat} (G: SimpleGraph (Fin n)) [inst: DecidableRel G.Adj]:
  correct_simple_graph (SimpleGraph_to_pre_simple_graph G inst) := by
  induction n with
  | zero => unfold correct_simple_graph SimpleGraph_to_pre_simple_graph
            simp
  | succ m iH => unfold correct_simple_graph SimpleGraph_to_pre_simple_graph
                 simp
                 refine ⟨?_, ?_, ?_⟩
                 . apply List.Nodup.filter
                   rw [List.nodup_bind]
                   refine ⟨?_, ?_⟩
                   . simp
                   . simp
                     simp_rw [<- Fin.ext_iff, Eq.comm]
                     have H := List.nodup_finRange m
                     unfold List.Nodup Ne at H
                     exact H
                 . intros x Hx
                   rw [List.mem_filter] at Hx
                   simp at Hx
                   obtain ⟨H, H0⟩ := Hx
                   cases H; rename_i w Hw
                   cases w
                   simp at *
                   omega
                 . apply iH

def SimpleGraph_to_simple_graph {n} (G: SimpleGraph (Fin n)) [inst: DecidableRel G.Adj]: simple_graph n :=
  ⟨SimpleGraph_to_pre_simple_graph G inst, SimpleGraph_to_pre_simple_graph_correct G⟩


-- Proofs of adjacency relation preservation

theorem adj_preserved_sg_to_SG {n} (g: simple_graph n) (x y: Fin n): adjacent g ↑x ↑y ↔ (simple_graph_to_SimpleGraph g).Adj x y := by
  constructor <;> intros H
  . cases n with
    | zero => cases x; omega
    | succ m => cases g; rename_i g Hg
                unfold simple_graph_to_SimpleGraph
                simp
                assumption
  . cases n with
    | zero => cases x; omega
    | succ m => cases g; rename_i g Hg
                unfold simple_graph_to_SimpleGraph at H
                simp at *
                assumption

instance sg_to_SG_adj_dec {n} (g: simple_graph n): DecidableRel (simple_graph_to_SimpleGraph g).Adj := by
  unfold simple_graph_to_SimpleGraph
  simp
  intros x y
  unfold adjacent neighbors neighbors_aux
  cases g; rename_i g Hg
  cases n <;> simp at *
  . cases x
    omega
  . cases g; simp at *
    infer_instance

theorem adj_preserved_SG_to_sg {n} (G: SimpleGraph (Fin n)) [DecidableRel G.Adj] (x y: Fin n):
  G.Adj x y ↔ adjacent (SimpleGraph_to_simple_graph G) ↑x ↑y := by
  induction n with
  | zero => cases x; omega
  | succ m iH => have Hx: x = Fin.last m ∨ x.1 < m := by
                   cases x
                   unfold Fin.last
                   simp
                   omega
                 have Hy: y = Fin.last m ∨ y.1 < m := by
                   cases y
                   unfold Fin.last
                   simp
                   omega
                 obtain Hx | Hx := Hx <;> obtain Hy | Hy := Hy
                 . rw [Hx, Hy]
                   simp
                   apply adjacent_irrefl
                 . constructor <;> intro H
                   . unfold SimpleGraph_to_simple_graph SimpleGraph_to_pre_simple_graph adjacent neighbors neighbors_aux
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
                     . unfold Fin.last at Hx
                       cases x
                       simp at *
                       omega
                     . unfold Fin.last at Hx
                       cases x
                       simp at *
                       omega
                   . unfold SimpleGraph_to_simple_graph SimpleGraph_to_pre_simple_graph adjacent neighbors neighbors_aux at H
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
                             obtain ⟨H4, H5, H6⟩ := H3
                             apply H5 at H2
                             linarith
                           . exfalso
                             have H3 := SimpleGraph_to_pre_simple_graph_correct (remove_last G)
                             rewrite [heq] at H3
                             obtain ⟨H4, H5, H6⟩ := H3
                             have H7 := size_limit_on_adjacent_nodes _ _ ⟨_, H6⟩ H
                             linarith
                     . cases x
                       unfold Fin.last at *
                       simp at *
                       omega
                     . cases x
                       unfold Fin.last at *
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
                     . unfold Fin.last at Hy
                       cases y
                       simp at H0 Hy
                       omega
                     . unfold Fin.last at Hy
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
                             have H7 := size_limit_on_adjacent_nodes _ _ ⟨_, H6⟩ H
                             linarith
                     . cases y
                       unfold Fin.last at *
                       simp at *
                       omega
                     . cases y
                       unfold Fin.last at *
                       simp at *
                       omega
                 . have H := iH (remove_last G) ⟨_, Hx⟩ ⟨_, Hy⟩
                   constructor <;> intro H0
                   . unfold SimpleGraph_to_simple_graph at *
                     unfold SimpleGraph_to_pre_simple_graph
                     simp
                     unfold adjacent neighbors at *
                     unfold neighbors_aux
                     have H1: (remove_last G).Adj ⟨_, Hx⟩ ⟨_, Hy⟩ := by
                       unfold remove_last
                       simp
                       cases x
                       cases y
                       unfold fin_limit_succ
                       simp at *
                       apply H0
                     rw [H] at H1
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
                     . exact H1
                   . unfold SimpleGraph_to_simple_graph at *
                     unfold SimpleGraph_to_pre_simple_graph at H0
                     simp at *
                     unfold adjacent neighbors at *
                     unfold neighbors_aux at H0
                     simp at H
                     split_ifs at H0 with H1 H2
                     . simp at H0
                       obtain H0 | H0 := H0
                       . omega
                       . rw [<- H] at H0
                         unfold remove_last at H0
                         simp at H0
                         unfold fin_limit_succ at H0
                         simp at H0
                         assumption
                     . clear H2
                       simp at H0
                       obtain H0 | H0 := H0
                       . omega
                       . rewrite [<- H] at H0
                         unfold remove_last at H0
                         simp at H0
                         unfold fin_limit_succ at H0
                         simp at H0
                         assumption
                     . rewrite [<- H] at H0
                       unfold remove_last at H0
                       simp at H0
                       unfold fin_limit_succ at H0
                       simp at H0
                       assumption


-- Some theorems about conversion about degree conservation

def remove_last_from_pre_simple_graph {n} (g: pre_simple_graph (n + 1)): pre_simple_graph n :=
  match g with | .Cons _ _ g' => g'

theorem SG_to_sg_of_remove_last {n} (G: SimpleGraph (Fin (n + 1))) [inst: DecidableRel G.Adj]:
  (SimpleGraph_to_simple_graph (remove_last G)).1 = remove_last_from_pre_simple_graph (SimpleGraph_to_simple_graph G).1 := by
  unfold remove_last remove_last_from_pre_simple_graph
  unfold SimpleGraph_to_simple_graph SimpleGraph_to_pre_simple_graph
  simp at *
  induction n with
  | zero => congr
  | succ m _ => congr

theorem degree_preserved {n} (G: SimpleGraph (Fin n)) v [inst: DecidableRel G.Adj]:
  G.degree v = degree (SimpleGraph_to_simple_graph G) v := by
  unfold SimpleGraph.degree
  unfold SimpleGraph.neighborFinset SimpleGraph.neighborSet
  simp_rw [adj_preserved_SG_to_sg]
  unfold adjacent degree neighbors
  simp
  have H: (SimpleGraph_to_simple_graph G).1 = SimpleGraph_to_pre_simple_graph G inst := by
    unfold SimpleGraph_to_simple_graph
    simp
  have aux: (neighbors_aux (SimpleGraph_to_simple_graph G).1 ↑v).Nodup := by
    have H0 := neighbors_Nodup (SimpleGraph_to_simple_graph G) ↑v
    unfold neighbors at H0
    exact H0
  have aux0: ∀ y ∈ neighbors_aux (SimpleGraph_to_simple_graph G).1 ↑v, y < n := by
    intros y Hy
    have H0 := @size_limit_on_adjacent_nodes n ↑v y (SimpleGraph_to_simple_graph G)
    unfold adjacent neighbors at H0; simp at H0
    tauto
  generalize (neighbors_aux (SimpleGraph_to_simple_graph G).1 ↑v) = W at *
  convert (aux02 n W aux0 aux)
