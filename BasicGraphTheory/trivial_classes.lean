import BasicGraphTheory.inductive_graphs
import BasicGraphTheory.auxiliary_lemmas


def pre_null_graph n: pre_simple_graph n :=
  match n with
  | 0 => .Empty
  | m + 1 => .Cons m [] (pre_null_graph m)

theorem null_graph_correct n: correct_simple_graph (pre_null_graph n) := by
  induction n with
  | zero => unfold pre_null_graph correct_simple_graph
            tauto
  | succ m iH => rw [pre_null_graph]
                 unfold correct_simple_graph
                 simp
                 exact iH

def null_graph n: simple_graph n := ⟨pre_null_graph n, null_graph_correct n⟩


def pre_complete_graph n: pre_simple_graph n :=
  match n with
  | 0 => .Empty
  | m + 1 => .Cons m (List.range m) (pre_complete_graph m)

theorem complete_graph_correct n: correct_simple_graph (pre_complete_graph n) := by
  induction n with
  | zero => unfold correct_simple_graph
            split
            . tauto
            . linarith
  | succ m iH => unfold pre_complete_graph
                 unfold correct_simple_graph
                 refine ⟨?_, ?_, ?_⟩
                 . exact List.nodup_range m
                 . intros x Hx
                   exact List.mem_range.mp Hx
                 . exact iH

def complete_graph n: simple_graph n := ⟨pre_complete_graph n, complete_graph_correct n⟩

theorem null_graph_no_adjacent {n} x y: adjacent (null_graph n) x y → False := by
  induction n with
  | zero => unfold null_graph pre_null_graph
            unfold adjacent neighbors neighbors_aux
            simp
  | succ m iH => intro H
                 unfold null_graph pre_null_graph at H
                 unfold adjacent neighbors neighbors_aux at H
                 split_ifs at H
                 . simp at H
                   apply iH
                   exact H
                 . simp at *
                 . apply iH
                   exact H

theorem complete_graph_all_adjacent {n}: ∀ {x y} (Hx: x < n) (Hy: y < n) (Hxy: x ≠ y), adjacent (complete_graph n) x y := by
  induction n with
  | zero => intros x y Hx Hy
            linarith
  | succ m iH => unfold complete_graph pre_complete_graph
                 unfold adjacent neighbors neighbors_aux
                 simp
                 intros x y Hx Hy Hxy
                 split_ifs with H1 H2
                 . simp
                   left
                   omega
                 . simp
                   have H3: y = m ∨ y < m := by omega
                   obtain H3 | H3 := H3
                   . tauto
                   . right
                     exact (iH H2 H3 Hxy)
                 . omega
