import Mathlib
import BasicGraphTheory.inductive_graphs

def edges_aux {n} (g: pre_simple_graph n): List (Nat × Nat) :=
  match g with
  | .Empty => []
  | .Cons m h t => edges_aux t ++ List.map (λ x => (m, x)) h

def edges {n} (g: simple_graph n) := edges_aux g.1

def edges_correctness {n} (g: simple_graph n): ∀ x y, y < x → ((x, y) ∈ edges g ↔ adjacent g x y) := by
  cases g
  rename_i g Hg
  induction g with
  | Empty => intros x y H
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
                     clear iH
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

def sum_aux00 A B (f: A → B) x a b [Decidable x]: f (if x then a else b) = if x then f a else f b := by
  split_ifs <;> simp

def sum_aux01 n (f g: Nat → Nat): (∀ x ∈ Finset.range n, f x = g x) → (∑ x ∈ Finset.range n, f x) = (∑ x ∈ Finset.range n, g x) := by
  intros H
  have H0: ∀ (x: Finset.range n), f x = g x := by
    intros x
    cases x; rename_i x Hx
    simp
    tauto
  apply Finset.sum_congr <;> simp at *
  assumption

theorem aux02 n (g: simple_graph n) k (Hk: n ≤ k): neighbors g k = [] := by
  cases g; rename_i g Hg
  induction n with
  | zero => unfold neighbors neighbors_aux
            split
            . simp
            . linarith
  | succ m iH => cases g; rename_i h g
                 unfold neighbors neighbors_aux
                 split_ifs with H H1
                 . linarith
                 . obtain ⟨Hg1, Hg2, Hg3⟩ := Hg
                   apply Hg2 at H1
                   linarith
                 . obtain ⟨Hg1, Hg2, Hg3⟩ := Hg
                   apply iH at Hg3
                   unfold neighbors at Hg3
                   simp at Hg3
                   . assumption
                   . linarith

theorem sum_aux02 (m: Nat) (h: List Nat) (H: ∀ x ∈ h, x < m) (H0: h.Nodup) (f: Nat → Nat):
  ∑ x ∈ Finset.range m, (if x ∈ h then f x + 1 else f x) = ∑ x ∈ Finset.range m, f x + h.length := by
  have H1: ∀ x, (if x ∈ h then f x + 1 else f x) = (f x + if x ∈ h then 1 else 0) := by
    intros
    split <;> simp
  simp_rw [H1, Finset.sum_add_distrib, Finset.sum_ite, Finset.sum_const_zero]
  simp
  clear H1 f
  induction h with
  | nil => simp
  | cons x t iH => simp at *
                   rw [Finset.filter_or]
                   simp
                   split_ifs with H1
                   . rw [Finset.card_union_of_disjoint]
                     . simp
                       rw [iH] <;> tauto
                       omega
                     . simp
                       tauto
                   . omega


theorem sum_of_degrees_twice_of_edges {n} (g: simple_graph n):
  ∑ (i ∈ Finset.range n), degree g i = 2 * (edges g).length := by
  cases g
  rename_i g Hg
  induction g with
  | Empty => simp
             unfold edges edges_aux
             rfl
  | Cons m h t iH => rw [Finset.sum_range_succ]
                     obtain ⟨Hg1, Hg2, Hg3⟩ := Hg
                     unfold degree neighbors neighbors_aux
                     simp
                     have H: ∀ x ∈ Finset.range m,
                        (if m = x then h ++ neighbors_aux t x else if x ∈ h then m :: neighbors_aux t x else neighbors_aux t x).length =
                        (if x ∈ h then m :: neighbors_aux t x else neighbors_aux t x).length := by
                       intros x Hx
                       congr 1
                       simp at Hx
                       simp at *
                       intros H
                       omega
                     apply sum_aux01 at H
                     rw [H]
                     clear H
                     have H: ∑ x ∈ Finset.range m, (if x ∈ h then m :: neighbors_aux t x else neighbors_aux t x).length =
                             ∑ x ∈ Finset.range m, (neighbors_aux t x).length + h.length := by
                       have H: ∀ x, (if x ∈ h then m :: neighbors_aux t x else neighbors_aux t x).length = (if x ∈ h then (neighbors_aux t x).length + 1 else (neighbors_aux t x).length) := by
                         intros x
                         split_ifs
                         . simp
                         . simp
                       simp_rw [H]; clear H
                       apply sum_aux02 <;> assumption
                     rw [H]; clear H
                     unfold degree neighbors at iH
                     simp at iH
                     rw [iH Hg3]
                     unfold edges
                     have H: (edges_aux (pre_simple_graph.Cons m h t)).length = h.length + (edges_aux t).length := by
                       rw [edges_aux]
                       rw [List.length_append]
                       rw [List.length_map]
                       omega
                     simp
                     rw [edges_aux]
                     simp
                     clear iH H
                     have H := aux02 m ⟨t, Hg3⟩ m (by omega)
                     unfold neighbors at H
                     simp at H
                     rw [H]
                     simp
                     omega


instance adjacent_decidable: ∀ {n} (g: simple_graph n), DecidableRel (adjacent g) := by
  intros n g x y
  unfold adjacent
  infer_instance

theorem list_bind_list_map: ∀ (A B: Type) (f: A → B) (L: List A), L.bind (fun a => [f a]) = List.map f L := by
  intros A B f L
  induction L with
  | nil => simp
  | cons head tail iH => simp
                         assumption


theorem aux03 (n w: Nat) (H: w < n):
  (Finset.filter (fun (x: Fin n) ↦ ↑x = w) Finset.univ).card = 1 := by
  rw [← Finset.card_singleton (⟨w, H⟩ : Fin n)]
  congr
  ext -- also solved from here on down by `aesop`
  simp [Fin.ext_iff]

theorem aux04 (n: Nat) (L: List Nat) (H: ∀ x ∈ L, x < n) (H0: L.Nodup):
  (Finset.filter (fun (x: Fin n) ↦ ↑x ∈ L) Finset.univ).card = L.length := by
    rw [← List.toFinset_card_of_nodup H0, ← Finset.card_map ⟨_, Fin.val_injective⟩]
    congr
    ext i
    simpa [Fin.exists_iff] using H i

theorem neighbors_lemma00 {n} g:
  ∀ h (H0: correct_simple_graph (.Cons n h g)) m (Hm: n ≤ m), neighbors_aux g m = [] := by
  induction g with
  | Empty => unfold neighbors_aux
             simp
  | Cons m h' g' iH => intros h H0
                       obtain ⟨H4, H5, H6⟩ := H0
                       unfold neighbors_aux
                       intros m1 Hm1
                       split_ifs with H7 H8
                       . omega
                       . obtain ⟨H9, H10, H11⟩ := H6
                         apply H10 at H8
                         omega
                       . apply iH
                         . exact H6
                         . omega


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
                 split_ifs with H1 H2
                 . have H2: ∀ y, y ∈ neighbors_aux g x → False := by
                     intros y Hy
                     apply aux00 _ _ ⟨g, Hg.2.2⟩ at Hy
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
                   exact Hg.1
                 . simp
                   constructor
                   . intros H3
                     obtain ⟨Hg1, Hg2, Hg3⟩ := Hg
                     apply aux00 _ _ ⟨g, Hg3⟩ at H3
                     omega
                   . have H3 := iH ⟨g, Hg.2.2⟩
                     unfold neighbors at H3
                     simp at H3
                     assumption
                 . have H3 := iH ⟨g, Hg.2.2⟩
                   unfold neighbors at H3
                   simp at H3
                   exact H3

def remove_last_from_pre_simple_graph {n} (g: pre_simple_graph (n + 1)): pre_simple_graph n :=
  match g with | .Cons _ h g' => g'

theorem aux05 {n} (G: SimpleGraph (Fin (n + 1))) [inst: DecidableRel G.Adj]:
  (SimpleGraph_to_simple_graph (remove_last G)).1 = remove_last_from_pre_simple_graph (SimpleGraph_to_simple_graph G).1 := by
  unfold remove_last remove_last_from_pre_simple_graph
  unfold SimpleGraph_to_simple_graph SimpleGraph_to_pre_simple_graph
  simp at *
  induction n with
  | zero => congr
  | succ m iH => congr

theorem degree_conserved {n} (G: SimpleGraph (Fin n)) v [inst: DecidableRel G.Adj]:
  G.degree v = degree (SimpleGraph_to_simple_graph G) v := by
  unfold SimpleGraph.degree
  unfold SimpleGraph.neighborFinset SimpleGraph.neighborSet
  simp_rw [adj_proof_2]
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
    apply aux00 at Hy
    tauto
  generalize (neighbors_aux (SimpleGraph_to_simple_graph G).1 ↑v) = W at *
  apply aux04
  . assumption
  . assumption

theorem finset_filter_ite {n} (p P1 P2: Fin n × Fin n → Prop)
  [DecidablePred p] [DecidablePred P1] [DecidablePred P2]:
  Finset.filter (fun x => if p x then P1 x else P2 x) Finset.univ =
  Finset.filter (fun x => p x ∧ P1 x) Finset.univ ∪
  Finset.filter (fun x => ¬ p x ∧ P2 x) Finset.univ := by
  unfold Finset.filter
  ext
  simp
  split_ifs <;> tauto

theorem finset_product_aux00 {n} (p q: Fin n → Prop)
  [DecidablePred p] [DecidablePred q]:
  (Finset.filter (fun (x: Fin n × Fin n) => p x.1 ∧ q x.2) Finset.univ).card =
  (Finset.filter (fun (x: Fin n) => p x) Finset.univ).card *
  (Finset.filter (fun (x: Fin n) => q x) Finset.univ).card := by
  rw [<- Finset.univ_product_univ]
  rw [Finset.filter_product]
  exact Finset.card_product (Finset.filter p Finset.univ) (Finset.filter q Finset.univ)

theorem finset_aux01 {n} (p q: Fin n × Fin n → Prop) [DecidablePred p] [DecidablePred q]:
  (Finset.filter (fun x => p x ∧ q x) Finset.univ).card +
  (Finset.filter (fun x => ¬ p x ∧ q x) Finset.univ).card =
  (Finset.filter (fun x => q x) Finset.univ).card := by
  have H: (fun x => p x ∧ q x) = (fun x => q x ∧ p x) := by
    ext; intros; tauto
  have H0: (fun x => ¬ p x ∧ q x) = (fun x => q x ∧ ¬ p x) := by
    ext; intros; tauto
  simp_rw [H, H0]
  rw [<- Finset.filter_filter]
  rw [<- Finset.filter_filter]
  rw [Finset.filter_card_add_filter_neg_card_eq_card]

theorem finset_aux02 {n} (P: Nat → Nat → Prop) (H: ∀ x y, P x y → x < n ∧ y < n) [DecidableRel P]:
  (Finset.filter (fun (x: Fin n × Fin n) => P ↑x.1 ↑x.2) Finset.univ).card =
  (Finset.filter (fun (x: Fin (n + 1) × Fin (n + 1)) => P ↑x.1 ↑x.2) Finset.univ).card := by
  apply Finset.card_bij (fun x _ => (Fin.castSucc x.1, Fin.castSucc x.2))
  · simp
  · simp
    intro ⟨a, ha⟩ ⟨b, hb⟩ h ⟨a', ha'⟩ ⟨hb, hb'⟩ h'
    simp (config := {contextual := true}) [H _ _ h, H _ _ h']
  · simp
    intro ⟨a, ha⟩ ⟨b, hb⟩ h
    specialize H _ _ h
    use ⟨a, H.1⟩, ⟨b, H.2⟩
    simpa using h

theorem sum_degrees_eq_twice_card_edges_Fin_variant {n} (G: SimpleGraph (Fin n)) [DecidableRel G.Adj]:
  ∑ v, G.degree v = 2 * G.edgeFinset.card := by
  simp_rw [degree_conserved]
  have H := sum_of_degrees_twice_of_edges (SimpleGraph_to_simple_graph G)
  rw [@Finset.sum_range] at H
  rw [H]
  clear H
  rw [SimpleGraph.two_mul_card_edgeFinset]
  simp_rw [adj_proof_2]
  --
  generalize (SimpleGraph_to_simple_graph G) = W
  rename_i inst; clear inst G
  cases W; rename_i g Hg
  induction n with
  | zero => cases g
            simp at *
            unfold edges edges_aux
            simp
  | succ m iH => cases g
                 rename_i h g
                 unfold edges edges_aux
                 simp
                 obtain ⟨Hg1, Hg2, Hg3⟩ := Hg
                 have H := iH g Hg3
                 unfold edges at H
                 simp at H
                 have H0: 2 * ((edges_aux g).length + h.length) = 2 * (edges_aux g).length + 2 * h.length := by
                   omega
                 rw [H0]
                 rw [H]
                 unfold adjacent neighbors
                 simp_rw [neighbors_aux]
                 have H1: ∀ x: Fin (m + 1) × Fin (m + 1), (↑x.2 ∈
                          if m = ↑x.1 then h ++ neighbors_aux g ↑x.1
                          else if ↑x.1 ∈ h then m :: neighbors_aux g ↑x.1 else neighbors_aux g ↑x.1) ↔
                          (if m = ↑x.1 then ↑x.2 ∈ h ++ neighbors_aux g ↑x.1 else
                           if ↑x.1 ∈ h then ↑x.2 ∈ m :: neighbors_aux g ↑x.1 else
                           ↑x.2 ∈ neighbors_aux g ↑x.1) := by
                   intros p
                   split_ifs <;> tauto
                 simp_rw [H1]
                 clear iH H1 H H0
                 simp
                 repeat rw [finset_filter_ite]
                 rw [Finset.card_union_of_disjoint]
                 . have H: ∀ (x: Fin (m + 1) × Fin (m + 1)),
                           (¬m = ↑x.1 ∧ if ↑x.1 ∈ h then ↑x.2 = m ∨ ↑x.2 ∈ neighbors_aux g ↑x.1 else ↑x.2 ∈ neighbors_aux g ↑x.1) ↔
                           (if ↑x.1 ∈ h then ¬ m = ↑x.1 ∧ (↑x.2 = m ∨ ↑x.2 ∈ neighbors_aux g ↑x.1) else ¬ m = ↑x.1 ∧ ↑x.2 ∈ neighbors_aux g ↑x.1) := by
                     intros x
                     split_ifs <;> tauto
                   simp_rw [H]
                   clear H
                   rw [finset_filter_ite]
                   rw [Finset.card_union_of_disjoint]
                   . have H: (fun (x: Fin (m + 1) × Fin (m + 1)) => m = ↑x.1 ∧ (↑x.2 ∈ h ∨ ↑x.2 ∈ neighbors_aux g ↑x.1)) =
                             (fun (x: Fin (m + 1) × Fin (m + 1)) => m = ↑x.1 ∧ ↑x.2 ∈ h) := by
                       ext; rename_i x
                       constructor <;> intros H
                       . obtain ⟨H1, H2⟩ := H
                         rw [<- H1] at H2
                         have H3 := aux02 m ⟨g, Hg3⟩ m (by omega)
                         unfold neighbors at H3
                         simp at H3
                         rw [H3] at H2
                         simp at H2
                         tauto
                       . tauto
                     simp_rw [H]
                     clear H
                     have H: (fun (x: Fin (m + 1) × Fin (m + 1)) => ↑x.1 ∈ h ∧ ¬m = ↑x.1 ∧ (↑x.2 = m ∨ ↑x.2 ∈ neighbors_aux g ↑x.1)) =
                             (fun (x: Fin (m + 1) × Fin (m + 1)) => ↑x.1 ∈ h ∧ ¬m = ↑x.1 ∧ (↑x.2 = m) ∨ ↑x.1 ∈ h ∧ ¬m = ↑x.1 ∧ ↑x.2 ∈ neighbors_aux g ↑x.1) := by
                       ext; rename_i x
                       tauto
                     simp_rw [H]; clear H
                     rw [Finset.filter_or]
                     repeat rw [Finset.card_union]
                     rw [<- Finset.filter_and]
                     have H: (fun (a: Fin (m + 1) × Fin (m + 1)) => (↑a.1 ∈ h ∧ ¬m = ↑a.1 ∧ ↑a.2 = m) ∧ ↑a.1 ∈ h ∧ ¬m = ↑a.1 ∧ ↑a.2 ∈ neighbors_aux g ↑a.1) =
                             (fun (a: Fin (m + 1) × Fin (m + 1)) => False) := by
                       ext; rename_i x
                       simp
                       intros H1 H2 H3 H4 H5 H6
                       have H7 := aux00 ↑x.1 ↑x.2 ⟨g, Hg3⟩
                       simp at H7
                       apply H7 at H6
                       omega
                     simp_rw [H, Finset.filter_False, Finset.card_empty]
                     clear H
                     simp
                     simp_rw [finset_product_aux00 (fun x => m = ↑x) (fun x => ↑x ∈ h)]
                     simp_rw [@Eq.comm _ m]
                     rw [aux03]
                     simp
                     rw [aux04]
                     . have H: ∀ (x y: Fin (m + 1)), ↑x ∈ h ∧ ¬ ↑x = m ∧ ↑y = m ↔
                               ((fun x => ↑x ∈ h ∧ ¬ ↑x = m) x ∧ (fun y => ↑y = m) y) := by
                         intros x y
                         tauto
                       simp_rw [H]
                       simp_rw [finset_product_aux00 (fun x => ↑x ∈ h ∧ ¬ ↑x = m) (fun x => ↑x = m)]
                       rw [aux03]
                       . simp
                         clear H
                         have H: ∀ (x: Fin (m + 1)), ↑x ∈ h ∧ ¬ ↑x = m ↔ ↑x ∈ h := by
                           intros x
                           constructor <;> intro H0
                           . tauto
                           . have H1 := Hg2 _ H0
                             constructor
                             . tauto
                             . omega
                         simp_rw [H]
                         rw [aux04]
                         . clear H
                           have H := finset_aux01 (fun (x: Fin (m + 1) × Fin (m + 1)) => ↑x.1 ∈ h) (fun x => ¬↑x.1 = m ∧ ↑x.2 ∈ neighbors_aux g ↑x.1)
                           rw [Nat.add_assoc]
                           rw [H]
                           clear H
                           have H: (fun (x: Fin (m + 1) × Fin (m + 1)) => ¬↑x.1 = m ∧ ↑x.2 ∈ neighbors_aux g ↑x.1) =
                                   (fun (x: Fin (m + 1) × Fin (m + 1)) => ↑x.2 ∈ neighbors_aux g ↑x.1) := by
                             ext; rename_i x
                             constructor <;> intros H10
                             . tauto
                             . constructor
                               . have aux := aux00 ↑x.1 ↑x.2 ⟨g, Hg3⟩
                                 simp at aux
                                 apply aux at H10
                                 omega
                               . assumption
                           simp_rw [H]
                           clear H
                           have H: (Finset.filter (fun (x: Fin m × Fin m) ↦ ↑x.2 ∈ neighbors_aux g ↑x.1) Finset.univ).card =
                                   (Finset.filter (fun (x: Fin (m + 1) × Fin (m + 1)) ↦ ↑x.2 ∈ neighbors_aux g ↑x.1) Finset.univ).card := by
                             apply (finset_aux02 (fun x y => y ∈ neighbors_aux g x))
                             intros x y H
                             apply (aux00 x y ⟨g, Hg3⟩)
                             simp
                             assumption
                           rw [H]
                           omega
                         . intros x Hx
                           apply Hg2 at Hx
                           omega
                         . assumption
                       . omega
                     . intros x Hx
                       apply Hg2 at Hx
                       omega
                     . assumption
                     . omega
                   . unfold Disjoint
                     intros p H1 H2 H3 H4
                     simp at *
                     have H5 := H4
                     apply H1 at H4
                     apply H2 at H5
                     simp at *
                     tauto
                 . unfold Disjoint
                   intros p H1 H2 H3 H4
                   simp at *
                   have H5 := H4
                   apply H1 at H4
                   apply H2 at H5
                   simp at *
                   tauto
