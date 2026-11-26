import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19006_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

lemma eval_op_mono (g : Gate) (h : g.op = .and ∨ g.op = .or) (u v : List Bool)
    (hlen : u.length = v.length) (hle : ∀ i, u.getD i false = true → v.getD i false = true) :
    g.op.eval (g.inputs.map (fun i => u.getD i false)) = true →
    g.op.eval (g.inputs.map (fun i => v.getD i false)) = true := by
  rcases h with hop | hop
  · rw [hop]
    simp only [GateOp.eval, List.all_eq_true, List.mem_map, id_eq]
    intro hall b hb
    rcases hb with ⟨i, hi, rfl⟩
    exact hle i (hall (u.getD i false) ⟨i, hi, rfl⟩)
  · rw [hop]
    simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq]
    rintro ⟨b, ⟨i, hi, rfl⟩, hb⟩
    exact ⟨v.getD i false, ⟨i, hi, rfl⟩, hle i hb⟩

lemma foldl_wires_mono (gs : List Gate) (hgs : ∀ g ∈ gs, g.op = .and ∨ g.op = .or)
    (u v : List Bool) (hlen : u.length = v.length)
    (hle : ∀ i, u.getD i false = true → v.getD i false = true) :
    let step := fun (w : List Bool) (g : Gate) => w ++ [g.op.eval (g.inputs.map (fun i => w.getD i false))]
    (gs.foldl step u).length = (gs.foldl step v).length ∧
    ∀ i, (gs.foldl step u).getD i false = true → (gs.foldl step v).getD i false = true := by
  induction gs generalizing u v with
  | nil => exact ⟨hlen, hle⟩
  | cons g gs ih =>
    have hg : g.op = .and ∨ g.op = .or := hgs g (List.mem_cons_self)
    have hrest : ∀ g' ∈ gs, g'.op = .and ∨ g'.op = .or := fun g' hg' => hgs g' (List.mem_cons_of_mem g hg')
    apply ih hrest
    · simp [hlen]
    · intro i hi
      simp only [List.getD_eq_getElem?_getD] at hi ⊢
      by_cases hlt : i < u.length
      · have hltv : i < v.length := hlen ▸ hlt
        rw [List.getElem?_append_left hlt] at hi
        rw [List.getElem?_append_left hltv]
        exact hle i (by simpa [List.getD_eq_getElem?_getD] using hi)
      · by_cases heq : i = u.length
        · subst heq
          rw [List.getElem?_append_right (le_refl _), Nat.sub_self] at hi
          rw [hlen, List.getElem?_append_right (le_refl _), Nat.sub_self]
          simp only [List.getElem?_cons_zero, Option.getD_some] at hi ⊢
          exact eval_op_mono g hg u v hlen hle hi
        · have hgt : u.length + 1 ≤ i := by omega
          rw [List.getElem?_eq_none (by simp; omega)] at hi
          simp at hi

theorem main_proof :
    ∀ (n : ℕ) (C : Circuit) (x y : Fin n → Bool), Monotone2 C →
      (∀ i, x i = true → y i = true) →
      C.eval (List.ofFn x) = true → C.eval (List.ofFn y) = true := by
  intro n C x y hm hxy hx
  have hgs : ∀ g ∈ C.gates, g.op = .and ∨ g.op = .or := fun g hg => (hm g hg).1
  have hlen : (List.ofFn x).length = (List.ofFn y).length := by simp
  have hle : ∀ i, (List.ofFn x).getD i false = true → (List.ofFn y).getD i false = true := by
    intro i hi
    simp only [List.getD_eq_getElem?_getD] at hi ⊢
    by_cases hlt : i < n
    · rw [List.getElem?_ofFn, dif_pos hlt] at hi
      rw [List.getElem?_ofFn, dif_pos hlt]
      exact hxy ⟨i, hlt⟩ (by simpa using hi)
    · rw [List.getElem?_ofFn, dif_neg hlt] at hi
      simp at hi
  exact (foldl_wires_mono C.gates hgs (List.ofFn x) (List.ofFn y) hlen hle).2 C.output hx

end PEqualNP.Outside.L_meta_19006_aux

theorem PEqualNP.Outside.L_meta_19006 : (∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : Fin x1 → Bool), PEqualNP.MetaComplexity.Monotone2 x2 → (∀ (x6 : Fin x1), x3 x6 = Bool.true → x4 x6 = Bool.true) → x2.eval (List.ofFn x3) = Bool.true → x2.eval (List.ofFn x4) = Bool.true)  := by
  exact PEqualNP.Outside.L_meta_19006_aux.main_proof
