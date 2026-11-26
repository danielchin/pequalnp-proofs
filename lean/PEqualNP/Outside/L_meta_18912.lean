import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18912_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem forall2_le_props : ∀ (a b : List Bool),
    List.Forall₂ (· ≤ ·) a b →
    a.length = b.length ∧ ∀ i, a.getD i false ≤ b.getD i false := by
  intro a b h
  induction h with
  | nil => exact ⟨rfl, fun _ => le_refl _⟩
  | cons hab _ ih =>
    refine ⟨by simp [ih.1], ?_⟩
    intro i
    cases i with
    | zero => exact hab
    | succ i => exact ih.2 i

theorem foldl_mono (gs : List Gate) (hAO : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ (w1 w2 : List Bool),
      w1.length = w2.length →
      (∀ i, w1.getD i false ≤ w2.getD i false) →
      ∀ i, (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)]) w1).getD i false ≤
           (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)]) w2).getD i false := by
  induction gs with
  | nil => intro w1 w2 _ hle i; exact hle i
  | cons g gs ih =>
    intro w1 w2 hlen hle
    have hg := hAO g (List.mem_cons_self ..)
    have hgs : ∀ g' ∈ gs, g'.op = GateOp.and ∨ g'.op = GateOp.or :=
      fun g' hg' => hAO g' (List.mem_cons_of_mem g hg')
    have hstep : g.op.eval (g.inputs.map fun k => w1.getD k false) ≤
                 g.op.eval (g.inputs.map fun k => w2.getD k false) := by
      rcases hg with hop | hop <;> rw [hop]
      · simp only [GateOp.eval]
        cases h1 : (g.inputs.map fun k => w1.getD k false).all id
        · exact Bool.false_le _
        · have h2 : (g.inputs.map fun k => w2.getD k false).all id = true := by
            rw [List.all_eq_true] at h1 ⊢
            intro b hb
            rcases List.mem_map.mp hb with ⟨k, hk, rfl⟩
            have h1k := h1 (w1.getD k false) (List.mem_map.mpr ⟨k, hk, rfl⟩)
            have hle_k := hle k
            simp only [id] at h1k ⊢
            rw [h1k] at hle_k
            exact Bool.eq_true_of_true_le hle_k
          rw [h2]
      · simp only [GateOp.eval]
        cases h1 : (g.inputs.map fun k => w1.getD k false).any id
        · exact Bool.false_le _
        · have h2 : (g.inputs.map fun k => w2.getD k false).any id = true := by
            rw [List.any_eq_true] at h1 ⊢
            rcases h1 with ⟨b, hb, hbtrue⟩
            rcases List.mem_map.mp hb with ⟨k, hk, rfl⟩
            refine ⟨w2.getD k false, List.mem_map.mpr ⟨k, hk, rfl⟩, ?_⟩
            have hle_k := hle k
            simp only [id] at hbtrue ⊢
            rw [hbtrue] at hle_k
            exact Bool.eq_true_of_true_le hle_k
          rw [h2]
    apply ih hgs
    · simp [hlen]
    · intro i
      by_cases hi : i < w1.length
      · rw [List.getD_append _ _ _ _ hi, List.getD_append _ _ _ _ (by omega)]
        exact hle i
      · by_cases heq : i = w1.length
        · subst heq
          have h1 : (w1 ++ [g.op.eval (g.inputs.map fun k => w1.getD k false)]).getD w1.length false =
              g.op.eval (g.inputs.map fun k => w1.getD k false) := by simp [List.getD_eq_getElem?_getD]
          have h2 : (w2 ++ [g.op.eval (g.inputs.map fun k => w2.getD k false)]).getD w1.length false =
              g.op.eval (g.inputs.map fun k => w2.getD k false) := by rw [hlen]; simp [List.getD_eq_getElem?_getD]
          rw [h1, h2]
          exact hstep
        · have hge1 : (w1 ++ [g.op.eval (g.inputs.map fun k => w1.getD k false)]).length ≤ i := by simp; omega
          have hge2 : (w2 ++ [g.op.eval (g.inputs.map fun k => w2.getD k false)]).length ≤ i := by simp [← hlen]; omega
          rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
              List.getElem?_eq_none hge1, List.getElem?_eq_none hge2]

theorem main_proof :
    ∀ (C : Circuit), Monotone2 C → ∀ a b : List Bool, List.Forall₂ (· ≤ ·) a b →
      ∀ i : ℕ, (C.wires a).getD i false ≤ (C.wires b).getD i false := by
  intro C hm a b hle i
  have hAO : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or := fun g hg => (hm g hg).1
  have hp := forall2_le_props a b hle
  exact foldl_mono C.gates hAO a b hp.1 hp.2 i

end PEqualNP.Outside.L_meta_18912_aux

theorem PEqualNP.Outside.L_meta_18912 : (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → ∀ (x3 x4 : List Bool), List.Forall₂ (fun (x5 x6 : Bool) => x5 ≤ x6) x3 x4 → ∀ (x6 : ℕ), (x1.wires x3).getD x6 Bool.false ≤ (x1.wires x4).getD x6 Bool.false)  := by
  exact PEqualNP.Outside.L_meta_18912_aux.main_proof
