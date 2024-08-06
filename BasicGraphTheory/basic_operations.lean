import BasicGraphTheory.inductive_graphs


-- difference

def diff_aux {n} (g g': pre_simple_graph n): pre_simple_graph n :=
  match g, g' with
  | .Empty, .Empty => .Empty
  | .Cons m h g, .Cons _ h' g' => .Cons m (List.diff h h') (diff_aux g g')

def diff_aux_correct_graph {n} (g g': simple_graph n): correct_simple_graph (diff_aux g.1 g'.1) := by
  cases g; rename_i g Hg
  cases g'; rename_i g' Hg'
  simp
  induction n with
  | zero => cases g
            cases g'
            unfold correct_simple_graph diff_aux
            tauto
  | succ m iH => cases g; rename_i h g
                 cases g'; rename_i h' g'
                 obtain ⟨Hg1, Hg2, Hg3⟩ := Hg
                 obtain ⟨Hg1', Hg2', Hg3'⟩ := Hg'
                 unfold diff_aux correct_simple_graph
                 simp
                 refine ⟨?_, ?_, ?_⟩
                 . exact List.Nodup.diff Hg1
                 . simp_rw [List.Nodup.mem_diff_iff Hg1]
                   intros
                   tauto
                 . apply (iH g Hg3 g' Hg3')

def diff {n} (g g': simple_graph n): simple_graph n := ⟨diff_aux g.1 g'.1, diff_aux_correct_graph g g'⟩

def diff_thm {n} (g g': simple_graph n): ∀ {x y} (Hx: x < n) (Hy: y < n) (Hxy: x ≠ y),
  (adjacent (diff g g') x y ↔ (adjacent g x y ∧ ¬ adjacent g' x y)) := by
  cases g; rename_i g Hg
  cases g'; rename_i g' Hg'
  . induction n with
    | zero => intros x y Hx Hy Hxy
              linarith
    | succ m iH => intros x y Hx Hy Hxy
                   cases g; rename_i h g
                   cases g'; rename_i h' g'
                   unfold diff adjacent neighbors
                   simp
                   rw [diff_aux]
                   rw [neighbors_aux, neighbors_aux, neighbors_aux]
                   obtain ⟨Hg1, Hg2, Hg3⟩ := Hg
                   obtain ⟨Hg1', Hg2', Hg3'⟩ := Hg'
                   split_ifs with H1 H2 H3 H4
                   . simp
                     constructor <;> intro H
                     . obtain H | H := H
                       . rw [List.Nodup.mem_diff_iff Hg1] at H
                         obtain ⟨H2, H3⟩ := H
                         refine ⟨?_, ?_, ?_⟩
                         . tauto
                         . tauto
                         . intro H4
                           have H5 := size_limit_on_adjacent_nodes x y ⟨g', Hg3'⟩ H4
                           omega
                       . have H2 := size_limit_on_adjacent_nodes x y ⟨_, diff_aux_correct_graph ⟨g, Hg3⟩ ⟨g', Hg3'⟩⟩ H
                         omega
                     . obtain ⟨H2, H3, H4⟩ := H
                       obtain H2 | H2 := H2
                       . left
                         rw [List.Nodup.mem_diff_iff Hg1]
                         tauto
                       . have H5 := size_limit_on_adjacent_nodes x y ⟨g, Hg3⟩ H2
                         omega
                   . simp
                     rw [List.Nodup.mem_diff_iff Hg1] at H2
                     tauto
                   . simp
                     constructor <;> intro H
                     . constructor
                       . obtain H | H := H
                         . tauto
                         . right
                           have H5 := size_limit_on_adjacent_nodes x y ⟨_, diff_aux_correct_graph ⟨g, Hg3⟩ ⟨g', Hg3'⟩⟩ H
                           have H6 := iH g Hg3 g' Hg3' H5.1 H5.2 Hxy
                           unfold adjacent neighbors diff at H6
                           simp at H6
                           tauto
                       . intro H5
                         obtain H | H := H
                         . have H6 := size_limit_on_adjacent_nodes x y ⟨g', Hg3'⟩ H5
                           omega
                         . have H6 := size_limit_on_adjacent_nodes x y ⟨g', Hg3'⟩ H5
                           have H7 := iH g Hg3 g' Hg3' H6.1 H6.2 Hxy
                           unfold adjacent neighbors diff at H7
                           simp at H7
                           tauto
                     . obtain ⟨H5, H6⟩ := H
                       obtain H5 | H5 := H5
                       . tauto
                       . right
                         have H7 := size_limit_on_adjacent_nodes x y ⟨g, Hg3⟩ H5
                         have H8 := iH g Hg3 g' Hg3' H7.1 H7.2 Hxy
                         unfold adjacent neighbors diff at H8
                         simp at H8
                         tauto
                   . rw [List.Nodup.mem_diff_iff Hg1] at H2
                     tauto
                   . rw [List.Nodup.mem_diff_iff Hg1] at H2
                     tauto
                   . constructor <;> intro H
                     . have H3 := size_limit_on_adjacent_nodes x y ⟨_, diff_aux_correct_graph ⟨g, Hg3⟩ ⟨g', Hg3'⟩⟩
                       unfold adjacent neighbors at H3
                       simp at H3
                       have H4 := H3 H
                       have H5 := iH g Hg3 g' Hg3' H4.1 H4.2 Hxy
                       unfold adjacent neighbors diff at H5
                       simp at *
                       rw [H5] at H
                       have H6: y ≠ m := by omega
                       tauto
                     . simp at H
                       obtain ⟨H3, H4, H5⟩ := H
                       obtain H3 | H3 := H3
                       . omega
                       . have Hx0: x < m := by omega
                         have Hy0: y < m := by omega
                         have H6 := iH g Hg3 g' Hg3' Hx0 Hy0 Hxy
                         unfold adjacent neighbors at H6
                         simp at H6
                         tauto
                   . rw [List.Nodup.mem_diff_iff Hg1] at H2
                     simp at H2
                     tauto
                   . simp
                     constructor <;> intro H
                     . have H3 := size_limit_on_adjacent_nodes x y ⟨_, diff_aux_correct_graph ⟨g, Hg3⟩ ⟨g', Hg3'⟩⟩
                       unfold adjacent neighbors at H3
                       simp at H3
                       have H4 := H3 H
                       have H5 := iH g Hg3 g' Hg3' H4.1 H4.2 Hxy
                       unfold adjacent neighbors diff at H5
                       simp at H5
                       rw [H5] at H
                       refine ⟨?_, ?_, ?_⟩
                       . tauto
                       . omega
                       . tauto
                     . obtain ⟨H3, H4, H5⟩ := H
                       have H6 := size_limit_on_adjacent_nodes x y ⟨_, Hg3⟩ H3
                       have H7 := iH g Hg3 g' Hg3' H6.1 H6.2 Hxy
                       unfold adjacent neighbors diff at H7
                       simp at H7
                       rw [H7]
                       tauto
                   . constructor <;> intro H
                     . have H3 := size_limit_on_adjacent_nodes x y ⟨_, diff_aux_correct_graph ⟨g, Hg3⟩ ⟨g', Hg3'⟩⟩
                       unfold adjacent neighbors at H3
                       simp at H3
                       have H4 := H3 H
                       have H5 := iH g Hg3 g' Hg3' H4.1 H4.2 Hxy
                       unfold adjacent neighbors diff at H5
                       simp at H5
                       tauto
                     . obtain ⟨H3, H4⟩ := H
                       have H5 := size_limit_on_adjacent_nodes x y ⟨g, Hg3⟩ H3
                       have H6 := iH g Hg3 g' Hg3' H5.1 H5.2 Hxy
                       unfold adjacent neighbors diff at H6
                       simp at H6
                       tauto



--- intersection

def inter_aux {n} (g g': pre_simple_graph n): pre_simple_graph n :=
  match g, g' with
  | .Empty, .Empty => .Empty
  | .Cons m h g, .Cons _ h' g' => .Cons m (h ∩ h') (inter_aux g g')

def inter_aux_correct_graph {n} (g g': simple_graph n): correct_simple_graph (inter_aux g.1 g'.1) := by
  cases g; rename_i g Hg
  cases g'; rename_i g' Hg'
  simp
  induction n with
  | zero => cases g
            cases g'
            unfold correct_simple_graph inter_aux
            split
            . tauto
            . linarith
  | succ m iH => cases g; rename_i h g
                 cases g'; rename_i h' g'
                 obtain ⟨Hg1, Hg2, Hg3⟩ := Hg
                 obtain ⟨Hg1', Hg2', Hg3'⟩ := Hg'
                 unfold inter_aux correct_simple_graph
                 simp
                 refine ⟨?_, ?_, ?_⟩
                 . exact (List.Nodup.inter h' Hg1)
                 . intro x H1 H2
                   tauto
                 . apply (iH g Hg3 g' Hg3')

def inter {n} (g g': simple_graph n): simple_graph n := ⟨inter_aux g.1 g'.1, inter_aux_correct_graph g g'⟩

def inter_thm {n} (g g': simple_graph n): ∀ {x y} (Hx: x < n) (Hy: y < n) (Hxy: x ≠ y),
  (adjacent (inter g g') x y ↔ (adjacent g x y ∧ adjacent g' x y)) := by
  cases g; rename_i g Hg
  cases g'; rename_i g' Hg'
  . induction n with
    | zero => intros x y Hx Hy Hxy
              linarith
    | succ m iH => intros x y Hx Hy Hxy
                   cases g; rename_i h g
                   cases g'; rename_i h' g'
                   unfold inter adjacent neighbors
                   simp
                   rw [inter_aux]
                   rw [neighbors_aux, neighbors_aux, neighbors_aux]
                   obtain ⟨Hg1, Hg2, Hg3⟩ := Hg
                   obtain ⟨Hg1', Hg2', Hg3'⟩ := Hg'
                   split_ifs with H1 H2 H3 H4
                   . simp
                     constructor <;> intro H
                     . obtain H | H := H
                       . tauto
                       . have H2 := size_limit_on_adjacent_nodes x y ⟨_, inter_aux_correct_graph ⟨g, Hg3⟩ ⟨g', Hg3'⟩⟩ H
                         have H3 := iH g Hg3 g' Hg3' H2.1 H2.2 Hxy
                         unfold adjacent neighbors inter at H3
                         tauto
                     . obtain ⟨H2 | H2, H3 | H3⟩ := H
                       . tauto
                       . have H4 := size_limit_on_adjacent_nodes x y ⟨g', Hg3'⟩ H3
                         linarith
                       . have H4 := size_limit_on_adjacent_nodes x y ⟨g, Hg3⟩ H2
                         linarith
                       . have H4 := size_limit_on_adjacent_nodes x y ⟨g, Hg3⟩ H2
                         have H5 := iH g Hg3 g' Hg3' H4.1 H4.2 Hxy
                         tauto
                   . constructor <;> intro H
                     . simp at *
                       obtain H | H := H
                       . tauto
                       . have H5 := size_limit_on_adjacent_nodes x y ⟨_, inter_aux_correct_graph ⟨g, Hg3⟩ ⟨g', Hg3'⟩⟩ H
                         have H6 := iH g Hg3 g' Hg3' H5.1 H5.2 Hxy
                         tauto
                     . simp at *
                       obtain ⟨H5 | H5, H6 | H6⟩ := H
                       . tauto
                       . tauto
                       . tauto
                       . have H7 := size_limit_on_adjacent_nodes x y ⟨g, Hg3⟩ H5
                         have H8 := iH g Hg3 g' Hg3' H7.1 H7.2 Hxy
                         tauto
                   . simp at H2
                     tauto
                   . simp at H2
                     tauto
                   . simp at H2
                     tauto
                   . simp at H2
                     tauto
                   . constructor <;> intro H
                     . simp
                       have H3 := size_limit_on_adjacent_nodes x y ⟨_, inter_aux_correct_graph ⟨g, Hg3⟩ ⟨g', Hg3'⟩⟩ H
                       have H4 := iH g Hg3 g' Hg3' H3.1 H3.2 Hxy
                       tauto
                     . obtain ⟨H3, H4⟩ := H
                       obtain H5 := size_limit_on_adjacent_nodes x y ⟨g', Hg3'⟩ H4
                       have H6 := iH g Hg3 g' Hg3' H5.1 H5.2 Hxy
                       simp at H3
                       obtain H3 | H3 := H3
                       . linarith
                       . tauto
                   . constructor <;> intro H
                     . simp
                       have H3 := size_limit_on_adjacent_nodes x y ⟨_, inter_aux_correct_graph ⟨g, Hg3⟩ ⟨g', Hg3'⟩⟩ H
                       have H4 := iH g Hg3 g' Hg3' H3.1 H3.2 Hxy
                       tauto
                     . obtain ⟨H3, H4⟩ := H
                       have H5 := size_limit_on_adjacent_nodes x y ⟨g, Hg3⟩ H3
                       have H6 := iH g Hg3 g' Hg3' H5.1 H5.2 Hxy
                       simp at H4
                       obtain H4 | H4 := H4
                       . linarith
                       . tauto
                   . constructor <;> intro H
                     . have H3 := size_limit_on_adjacent_nodes x y ⟨_, inter_aux_correct_graph ⟨g, Hg3⟩ ⟨g', Hg3'⟩⟩ H
                       have H4 := iH g Hg3 g' Hg3' H3.1 H3.2 Hxy
                       tauto
                     . obtain ⟨H3, H4⟩ := H
                       have H5 := size_limit_on_adjacent_nodes x y ⟨g, Hg3⟩ H3
                       have H6 := iH g Hg3 g' Hg3' H5.1 H5.2 Hxy
                       tauto


-- union

def union_aux {n} (g g': pre_simple_graph n): pre_simple_graph n :=
  match g, g' with
  | .Empty, .Empty => .Empty
  | .Cons m h g, .Cons _ h' g' => .Cons m (h ∪ h') (union_aux g g')

def union_aux_correct_graph {n} (g g': simple_graph n): correct_simple_graph (union_aux g.1 g'.1) := by
  cases g; rename_i g Hg
  cases g'; rename_i g' Hg'
  simp
  induction n with
  | zero => cases g
            cases g'
            unfold correct_simple_graph union_aux
            simp
  | succ m iH => cases g; rename_i h g
                 cases g'; rename_i h' g'
                 obtain ⟨Hg1, Hg2, Hg3⟩ := Hg
                 obtain ⟨Hg1', Hg2', Hg3'⟩ := Hg'
                 unfold union_aux correct_simple_graph
                 simp
                 refine ⟨?_, ?_, ?_⟩
                 . exact (List.Nodup.union h Hg1')
                 . intros x Hx
                   tauto
                 . apply (iH g Hg3 g' Hg3')

def union {n} (g g': simple_graph n): simple_graph n := ⟨union_aux g.1 g'.1, union_aux_correct_graph g g'⟩

def union_thm {n} (g g': simple_graph n): ∀ {x y} (Hx: x < n) (Hy: y < n) (Hxy: x ≠ y),
  (adjacent (union g g') x y ↔ (adjacent g x y ∨ adjacent g' x y)) := by
  cases g; rename_i g Hg
  cases g'; rename_i g' Hg'
  . induction n with
    | zero => intros x y Hx Hy Hxy
              linarith
    | succ m iH => intros x y Hx Hy Hxy
                   cases g; rename_i h g
                   cases g'; rename_i h' g'
                   unfold union adjacent neighbors
                   simp
                   rw [union_aux]
                   rw [neighbors_aux, neighbors_aux, neighbors_aux]
                   obtain ⟨Hg1, Hg2, Hg3⟩ := Hg
                   obtain ⟨Hg1', Hg2', Hg3'⟩ := Hg'
                   split_ifs with H1 H2 H3 H4
                   . constructor <;> intro H
                     . simp at *
                       obtain (H | H) | H := H
                       . tauto
                       . tauto
                       . have H2 := size_limit_on_adjacent_nodes x y ⟨_, union_aux_correct_graph ⟨g, Hg3⟩ ⟨g', Hg3'⟩⟩ H
                         linarith
                     . simp at *
                       obtain (H | H) | H | H := H
                       . tauto
                       . have H2 := size_limit_on_adjacent_nodes x y ⟨g, Hg3⟩ H
                         linarith
                       . tauto
                       . have H2 := size_limit_on_adjacent_nodes x y ⟨g', Hg3'⟩ H
                         linarith
                   . constructor <;> intro H
                     . simp at *
                       obtain H | H := H
                       . tauto
                       . have H3 := size_limit_on_adjacent_nodes x y ⟨_, union_aux_correct_graph ⟨g, Hg3⟩ ⟨g', Hg3'⟩⟩ H
                         have H4 := iH g Hg3 g' Hg3' H3.1 H3.2 Hxy
                         tauto
                     . simp at *
                       obtain (H | H) | H | H := H
                       . tauto
                       . have H5 := size_limit_on_adjacent_nodes x y ⟨g, Hg3⟩ H
                         have H6 := iH g Hg3 g' Hg3' H5.1 H5.2 Hxy
                         tauto
                       . tauto
                       . have H5 := size_limit_on_adjacent_nodes x y ⟨g', Hg3'⟩ H
                         have H6 := iH g Hg3 g' Hg3' H5.1 H5.2 Hxy
                         tauto
                   . constructor <;> intro H
                     . simp at *
                       obtain H | H := H
                       . tauto
                       . have H5 := size_limit_on_adjacent_nodes x y ⟨_, union_aux_correct_graph ⟨g, Hg3⟩ ⟨g', Hg3'⟩⟩ H
                         have H6 := iH g Hg3 g' Hg3' H5.1 H5.2 Hxy
                         tauto
                     . simp at *
                       obtain (H | H) | H := H
                       . tauto
                       . have H5 := size_limit_on_adjacent_nodes x y ⟨g, Hg3⟩ H
                         have H6 := iH g Hg3 g' Hg3' H5.1 H5.2 Hxy
                         tauto
                       . have H5 := size_limit_on_adjacent_nodes x y ⟨g', Hg3'⟩ H
                         have H6 := iH g Hg3 g' Hg3' H5.1 H5.2 Hxy
                         tauto
                   . constructor <;> intro H
                     . simp at *
                       obtain H | H := H
                       . tauto
                       . have H4 := size_limit_on_adjacent_nodes x y ⟨_, union_aux_correct_graph ⟨g, Hg3⟩ ⟨g', Hg3'⟩⟩ H
                         have H6 := iH g Hg3 g' Hg3' H4.1 H4.2 Hxy
                         tauto
                     . simp at *
                       obtain H | H | H := H
                       . have H4 := size_limit_on_adjacent_nodes x y ⟨g, Hg3⟩ H
                         have H5 := iH g Hg3 g' Hg3' H4.1 H4.2 Hxy
                         tauto
                       . tauto
                       . have H4 := size_limit_on_adjacent_nodes x y ⟨g', Hg3'⟩ H
                         have H5 := iH g Hg3 g' Hg3' H4.1 H4.2 Hxy
                         tauto
                   . simp at H2
                     tauto
                   . simp at H2
                     tauto
                   . simp at H2
                     tauto
                   . simp at H2
                     tauto
                   . constructor <;> intro H
                     . have H4 := size_limit_on_adjacent_nodes x y ⟨_, union_aux_correct_graph ⟨g, Hg3⟩ ⟨g', Hg3'⟩⟩ H
                       have H5 := iH g Hg3 g' Hg3' H4.1 H4.2 Hxy
                       tauto
                     . obtain H | H := H
                       . have H4 := size_limit_on_adjacent_nodes x y ⟨g, Hg3⟩ H
                         have H5 := iH g Hg3 g' Hg3' H4.1 H4.2 Hxy
                         tauto
                       . have H4 := size_limit_on_adjacent_nodes x y ⟨g', Hg3'⟩ H
                         have H5 := iH g Hg3 g' Hg3' H4.1 H4.2 Hxy
                         tauto


-- symmetrical difference or XOR

def symm_diff {n} (g g': simple_graph n): simple_graph n :=
  union (diff g g') (diff g' g)
