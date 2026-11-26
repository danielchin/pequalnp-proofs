import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18806_aux

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm

def wstep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def dstep (d : List ℕ) (g : Gate) : List ℕ :=
  d ++ [g.lineDegree d]

theorem getD_append_left_lt {α : Type} (defv : α) (a b : List α) (i : ℕ) (hi : i < a.length) :
    (a ++ b).getD i defv = a.getD i defv := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem getD_snoc_eq {α : Type} (defv : α) (a : List α) (v : α) :
    (a ++ [v]).getD a.length defv = v := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_concat_length, Option.getD_some]

theorem foldl_len_w (gs : List Gate) (w : List Bool) :
    (gs.foldl wstep w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp only [List.foldl_nil, List.length_nil, Nat.add_zero]
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, wstep, List.length_append, List.length_cons, List.length_nil]
    omega

theorem foldl_len_d (gs : List Gate) (d : List ℕ) :
    (gs.foldl dstep d).length = d.length + gs.length := by
  induction gs generalizing d with
  | nil => simp only [List.foldl_nil, List.length_nil, Nat.add_zero]
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, dstep, List.length_append, List.length_cons, List.length_nil]
    omega

def remapWire (n : ℕ) (e : Equiv.Perm (Fin n)) (w : ℕ) : ℕ :=
  if h : w < n then (e ⟨w, h⟩).val else w

def remapGate (n : ℕ) (e : Equiv.Perm (Fin n)) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (remapWire n e)⟩

theorem remapWire_inj (n : ℕ) (e : Equiv.Perm (Fin n)) : Function.Injective (remapWire n e) := by
  intro u v huv
  dsimp only [remapWire] at huv
  split_ifs at huv with hu hv hv
  · exact congrArg Fin.val (e.injective (Fin.ext huv))
  · have := (e ⟨u, hu⟩).isLt; omega
  · have := (e ⟨v, hv⟩).isLt; omega
  · exact huv

theorem remapWire_lt (n : ℕ) (e : Equiv.Perm (Fin n)) (k w : ℕ) (hw : w < n + k) :
    remapWire n e w < n + k := by
  dsimp only [remapWire]
  split_ifs with h
  · have := (e ⟨w, h⟩).isLt; omega
  · exact hw

theorem remapWire_ge (n : ℕ) (e : Equiv.Perm (Fin n)) (w : ℕ) (hw : n ≤ w) :
    remapWire n e w = w := by
  dsimp only [remapWire]
  rw [dite_eq_right (Nat.not_lt.mpr hw)]

theorem foldl_remap_w (n : ℕ) (e : Equiv.Perm (Fin n)) (gs : List Gate) (x : Fin n → Bool) :
    ∀ w, ((gs.map (remapGate n e)).foldl wstep (List.ofFn x)).getD (remapWire n e w) false =
      (gs.foldl wstep (List.ofFn (x ∘ e))).getD w false := by
  induction gs using List.reverseRecOn with
  | nil =>
    intro w
    simp only [List.map_nil, List.foldl_nil]
    by_cases hw : w < n
    · have hrw : remapWire n e w = (e ⟨w, hw⟩).val := dite_eq_left hw
      rw [hrw]
      have hlt : (e ⟨w, hw⟩).val < n := (e ⟨w, hw⟩).isLt
      simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hw, hlt, dite_true, Option.getD_some, Function.comp_apply]
    · have hrw : remapWire n e w = w := dite_eq_right hw
      rw [hrw, List.getD_eq_default _ _ (by rw [List.length_ofFn]; omega),
          List.getD_eq_default _ _ (by rw [List.length_ofFn]; omega)]
  | append_singleton gs g ih =>
    intro w
    rw [List.map_append, List.map_singleton, List.foldl_append, List.foldl_cons, List.foldl_nil,
        List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hl1 : ((gs.map (remapGate n e)).foldl wstep (List.ofFn x)).length = n + gs.length := by
      rw [foldl_len_w, List.length_ofFn, List.length_map]
    have hl2 : (gs.foldl wstep (List.ofFn (x ∘ e))).length = n + gs.length := by
      rw [foldl_len_w, List.length_ofFn]
    have hval : (remapGate n e g).op.eval ((remapGate n e g).inputs.map fun i => ((gs.map (remapGate n e)).foldl wstep (List.ofFn x)).getD i false) =
        g.op.eval (g.inputs.map fun i => (gs.foldl wstep (List.ofFn (x ∘ e))).getD i false) := by
      simp only [remapGate, List.map_map]
      congr 1
      apply List.map_congr_left
      intro i _
      exact ih i
    by_cases hw : w < n + gs.length
    · have hrw : remapWire n e w < n + gs.length := remapWire_lt n e gs.length w hw
      rw [wstep, wstep, getD_append_left_lt false _ _ _ (by omega), getD_append_left_lt false _ _ _ (by omega)]
      exact ih w
    · by_cases heq : w = n + gs.length
      · subst heq
        have hrw : remapWire n e (n + gs.length) = n + gs.length := remapWire_ge n e _ (by omega)
        rw [wstep, wstep, hrw]
        have h1 : (((gs.map (remapGate n e)).foldl wstep (List.ofFn x)) ++
            [(remapGate n e g).op.eval ((remapGate n e g).inputs.map fun i => ((gs.map (remapGate n e)).foldl wstep (List.ofFn x)).getD i false)]).getD (n + gs.length) false =
            (remapGate n e g).op.eval ((remapGate n e g).inputs.map fun i => ((gs.map (remapGate n e)).foldl wstep (List.ofFn x)).getD i false) := by
          rw [← hl1, getD_snoc_eq]
        have h2 : ((gs.foldl wstep (List.ofFn (x ∘ e))) ++
            [g.op.eval (g.inputs.map fun i => (gs.foldl wstep (List.ofFn (x ∘ e))).getD i false)]).getD (n + gs.length) false =
            g.op.eval (g.inputs.map fun i => (gs.foldl wstep (List.ofFn (x ∘ e))).getD i false) := by
          rw [← hl2, getD_snoc_eq]
        rw [h1, h2, hval]
      · have hrw : remapWire n e w = w := remapWire_ge n e w (by omega)
        rw [wstep, wstep, hrw,
            List.getD_eq_default _ _ (by rw [List.length_append, List.length_singleton, hl1]; omega),
            List.getD_eq_default _ _ (by rw [List.length_append, List.length_singleton, hl2]; omega)]

theorem foldl_remap_d (n : ℕ) (e : Equiv.Perm (Fin n)) (gs : List Gate) (idx : Fin n) :
    let initD := (List.range n).map fun j => if j ∈ ({(e idx).val} : Finset ℕ) then 1 else 0
    let initC := (List.range n).map fun j => if j ∈ ({idx.val} : Finset ℕ) then 1 else 0
    ∀ w, ((gs.map (remapGate n e)).foldl dstep initD).getD (remapWire n e w) 0 =
      (gs.foldl dstep initC).getD w 0 := by
  intro initD initC
  have hlenD : initD.length = n := by simp only [initD, List.length_map, List.length_range]
  have hlenC : initC.length = n := by simp only [initC, List.length_map, List.length_range]
  induction gs using List.reverseRecOn with
  | nil =>
    intro w
    simp only [List.map_nil, List.foldl_nil]
    by_cases hw : w < n
    · have hrw : remapWire n e w = (e ⟨w, hw⟩).val := dite_eq_left hw
      rw [hrw]
      have hlt : (e ⟨w, hw⟩).val < n := (e ⟨w, hw⟩).isLt
      simp only [initD, initC, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hlt,
        List.getElem?_range hw, Option.map_some, Option.getD_some, Finset.mem_singleton]
      have hiff : (e ⟨w, hw⟩).val = (e idx).val ↔ w = idx.val := by
        constructor
        · intro h; exact congrArg Fin.val (e.injective (Fin.ext h))
        · intro h; have : (⟨w, hw⟩ : Fin n) = idx := Fin.ext h; rw [this]
      by_cases h : w = idx.val
      · rw [ite_eq_left (hiff.mpr h), ite_eq_left h]
      · rw [ite_eq_right (fun he => h (hiff.mp he)), ite_eq_right h]
    · have hrw : remapWire n e w = w := dite_eq_right hw
      rw [hrw, List.getD_eq_default _ _ (by rw [hlenD]; omega),
          List.getD_eq_default _ _ (by rw [hlenC]; omega)]
  | append_singleton gs g ih =>
    intro w
    rw [List.map_append, List.map_singleton, List.foldl_append, List.foldl_cons, List.foldl_nil,
        List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hl1 : ((gs.map (remapGate n e)).foldl dstep initD).length = n + gs.length := by
      rw [foldl_len_d, hlenD, List.length_map]
    have hl2 : (gs.foldl dstep initC).length = n + gs.length := by
      rw [foldl_len_d, hlenC]
    have hval : (remapGate n e g).lineDegree ((gs.map (remapGate n e)).foldl dstep initD) =
        g.lineDegree (gs.foldl dstep initC) := by
      have hmap : ((g.inputs.map (remapWire n e)).map fun i => ((gs.map (remapGate n e)).foldl dstep initD).getD i 0) =
          (g.inputs.map fun i => (gs.foldl dstep initC).getD i 0) := by
        rw [List.map_map]
        apply List.map_congr_left
        intro i _
        exact ih i
      unfold Gate.lineDegree
      dsimp only [remapGate]
      rw [hmap]
      rfl
    by_cases hw : w < n + gs.length
    · have hrw : remapWire n e w < n + gs.length := remapWire_lt n e gs.length w hw
      rw [dstep, dstep, getD_append_left_lt 0 _ _ _ (by omega), getD_append_left_lt 0 _ _ _ (by omega)]
      exact ih w
    · by_cases heq : w = n + gs.length
      · subst heq
        have hrw : remapWire n e (n + gs.length) = n + gs.length := remapWire_ge n e _ (by omega)
        rw [dstep, dstep, hrw]
        have h1 : (((gs.map (remapGate n e)).foldl dstep initD) ++
            [(remapGate n e g).lineDegree ((gs.map (remapGate n e)).foldl dstep initD)]).getD (n + gs.length) 0 =
            (remapGate n e g).lineDegree ((gs.map (remapGate n e)).foldl dstep initD) := by
          rw [← hl1, getD_snoc_eq]
        have h2 : ((gs.foldl dstep initC) ++
            [g.lineDegree (gs.foldl dstep initC)]).getD (n + gs.length) 0 =
            g.lineDegree (gs.foldl dstep initC) := by
          rw [← hl2, getD_snoc_eq]
        rw [h1, h2, hval]
      · have hrw : remapWire n e w = w := remapWire_ge n e w (by omega)
        rw [dstep, dstep, hrw,
            List.getD_eq_default _ _ (by rw [List.length_append, List.length_singleton, hl1]; omega),
            List.getD_eq_default _ _ (by rw [List.length_append, List.length_singleton, hl2]; omega)]

theorem main_proof :
    ∀ (n : ℕ) (C : Circuit) (e : Equiv.Perm (Fin n)), IsAO2 n C →
      (∀ g ∈ C.gates, g.inputs.Nodup) → ∃ D : Circuit,
        D.size = C.size ∧ IsAO2 n D ∧ (∀ g ∈ D.gates, g.inputs.Nodup) ∧
        (∀ x : Fin n → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn (x ∘ e))) ∧
        ∀ i : Fin n, D.lineDeg n {(e i).val} = C.lineDeg n {i.val} := by
  intro n C e hao hnd
  let D : Circuit := ⟨C.gates.map (remapGate n e), remapWire n e C.output⟩
  refine ⟨D, by simp only [D, Circuit.size, List.length_map], ?_, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · intro g hg
      simp only [D, List.mem_map] at hg
      rcases hg with ⟨g', hg', rfl⟩
      exact hao.1 g' hg'
    · intro k hk i hi
      have hk' : k < C.gates.length := by simpa only [D, List.length_map] using hk
      have hgk : PEqualNP.MetaComplexity.NestedCover.gateAt D k = remapGate n e (PEqualNP.MetaComplexity.NestedCover.gateAt C k) := by
        simp only [PEqualNP.MetaComplexity.NestedCover.gateAt, D, List.getD_eq_getElem _ _ hk,
          List.getD_eq_getElem _ _ hk', List.getElem_map]
      rw [hgk] at hi
      simp only [remapGate, List.mem_map] at hi
      rcases hi with ⟨i', hi', rfl⟩
      exact remapWire_lt n e k i' (hao.2.1 k hk' i' hi')
    · intro g hg
      simp only [D, List.mem_map] at hg
      rcases hg with ⟨g', hg', rfl⟩
      simp only [remapGate, List.length_map, hao.2.2 g' hg']
  · intro g hg
    simp only [D, List.mem_map] at hg
    rcases hg with ⟨g', hg', rfl⟩
    exact (hnd g' hg').map (remapWire_inj n e)
  · intro x
    exact foldl_remap_w n e C.gates x C.output
  · intro i
    exact foldl_remap_d n e C.gates i C.output

end PEqualNP.Outside.L_meta_18806_aux

theorem PEqualNP.Outside.L_meta_18806 : (∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : Equiv.Perm (Fin x1)), PEqualNP.TopForm.IsAO2 x1 x2 → (∀ x5 ∈ x2.gates, x5.inputs.Nodup) → ∃ (x6 : PEqualNP.CircuitLowerBounds.Circuit), x6.size = x2.size ∧ PEqualNP.TopForm.IsAO2 x1 x6 ∧ (∀ x7 ∈ x6.gates, x7.inputs.Nodup) ∧ (∀ (x7 : Fin x1 → Bool), x6.eval (List.ofFn x7) = x2.eval (List.ofFn (x7 ∘ ⇑x3))) ∧ ∀ (x7 : Fin x1), x6.lineDeg x1 {↑(x3 x7)} = x2.lineDeg x1 {↑x7})  := by
  exact PEqualNP.Outside.L_meta_18806_aux.main_proof
