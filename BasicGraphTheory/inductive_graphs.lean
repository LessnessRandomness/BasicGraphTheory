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
  | .Cons _ h t => h.Nodup ∧ (∀ x, x ∈ h → x < n) ∧ correct_simple_graph t

def simple_graph n := { g: pre_simple_graph n // correct_simple_graph g}

def neighbors_aux {n} (g: pre_simple_graph n) (x: Nat): List Nat :=
  match g with
  | .Empty => []
  | .Cons m L g' => if n = x
                    then L ++ neighbors_aux g' x
                    else if x ∈ L
                         then n :: neighbors_aux g' x
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
                      unfold neighbors_aux at H
                      split at H <;> rename_i H0
                      . obtain ⟨_, H1, H2⟩ := Hg
                        simp at H
                        obtain H | H := H
                        . have H2 := H1 _ H
                          omega
                        . exact (iH H2 H)
                      . split at H; rename_i H1
                        . simp at *
                          obtain H | H := H
                          . omega
                          . obtain ⟨_, _, H2⟩ := Hg
                            exact (iH H2 H)
                        . obtain ⟨_, _, H2⟩ := Hg
                          exact (iH H2 H)


def simple_graph_to_SimpleGraph {n} (g: simple_graph n): SimpleGraph (Fin (n + 1)) := by
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

def add_one_more {n} (G: SimpleGraph (Fin n)) (P: Fin n → Prop): SimpleGraph (Fin (n + 1)) := by
  let adj: Fin (n + 1) → Fin (n + 1) → Prop := by
    intros x y
    cases x; rename_i x px
    cases y; rename_i y py
    if Hx:(x < n)
    then if Hy:(y < n)
         then exact (G.Adj ⟨x, Hx⟩ ⟨y, Hy⟩)
         else exact (P ⟨x, Hx⟩)
    else if Hy:(y < n)
         then exact (P ⟨y, Hy⟩)
         else exact False
  refine (SimpleGraph.mk adj ?_ ?_)
  . unfold Symmetric
    intros x y H
    cases G; rename_i Adj symm irrefl
    dsimp only [adj] at *
    split_ifs at *
    . apply symm
      apply H
    . assumption
    . assumption
  . unfold Irreflexive
    intros x
    dsimp only [adj]
    cases G; rename_i Adj symm irrefl
    split_ifs
    . apply irrefl
    . tauto

instance remove_last_adj_dec: ∀ {n} (G: SimpleGraph (Fin (n + 1))) [inst: DecidableRel G.Adj],
  DecidableRel (remove_last G).Adj := by
  unfold DecidableRel
  intros n G H a b
  unfold remove_last
  simp
  infer_instance

def SimpleGraph_to_pre_simple_graph {n: Nat} (G: SimpleGraph (Fin n))
  [inst: DecidableRel G.Adj]: pre_simple_graph n := by
  induction n with
  | zero => exact .Empty
  | succ m iH => refine (.Cons m ?_ (iH (remove_last G)))
                 exact (List.filter (λ x => if G.Adj (fin_max m) x then true else false) (Fin.list m))


theorem fin_list_nodup n: (Fin.list n).Nodup := by
  sorry

def SimpleGraph_to_simple_graph {n: Nat} (G: SimpleGraph (Fin n))
  [inst: DecidableRel G.Adj]: simple_graph n := by
  exists (SimpleGraph_to_pre_simple_graph G)
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



-- Lemmas about fin --

theorem fin_to_nat_injective n: Function.Injective (λ (x: Fin n) => x.1) := by
  unfold Function.Injective
  intros x y h
  simp at *
  apply (Fin.ext h)

-- by https://leanprover.zulipchat.com/#user/684366 (Edward van de Meent)
theorem fin_list_has_all_fins: ∀ {N} (f: Fin N), f ∈ Fin.list N := by
  intro n m
  refine List.mem_iff_get.mpr ?_
  have : m.val < (Fin.list n).length := by
    rw [Fin.length_list]
    exact m.2
  refine ⟨⟨m.val,this⟩,?_⟩
  simp only [List.get_eq_getElem, Fin.getElem_list, Fin.cast_mk, Fin.eta]

-- Complete Graph --

def pre_complete_graph (n: Nat): pre_simple_graph n :=
  match n with
  | 0 => .Empty
  | m + 1 => .Cons m (List.map (λ x => x.1) (Fin.list (m + 1))) (pre_complete_graph m)

theorem complete_graph_correct (n: Nat): correct_simple_graph (pre_complete_graph n) := by
  induction n with
  | zero => unfold pre_complete_graph correct_simple_graph
            simp
  | succ m iH => unfold pre_complete_graph correct_simple_graph
                 refine ⟨?_, ?_, ?_⟩
                 . exact List.Nodup.map (fin_to_nat_injective _) (fin_list_nodup _)
                 . intros x
                   intros H
                   simp at *
                   cases H; rename_i f H
                   obtain ⟨H0, H1⟩ := H
                   cases f
                   simp at *
                   omega
                 . assumption

def complete_graph (n: Nat): simple_graph n :=
  ⟨pre_complete_graph n, complete_graph_correct n⟩

#eval (neighbors (complete_graph 4) 1)
