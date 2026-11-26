import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19016_aux

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership
  PEqualNP.MetaComplexity.NestedCover PEqualNP.CleanedNonEdge

lemma wires_getD_lt (gs : List Gate) (w : List Bool) (k : ℕ) (hk : k < w.length) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).getD k false =
      w.getD k false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hk' : k < (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]).length := by simp; omega
    rw [ih _ hk']
    exact List.getD_append w _ false k hk

theorem main_proof :
    ¬∃ (x1 : Circuit),
      have x2 : Finset (Fin 13) := {0, 1, 3, 9};
      have x3 : ℕ → ℕ → Prop := InCone 26 x1;
      have x4 : ℕ → (Fin 26 → Bool) → Bool := gateVal 26 x1;
      have x5 : ℕ → Prop := fun x5 => (gateAt x1 x5).op = GateOp.and;
      have x6 : ℕ → Prop := fun x6 => 26 + x6 = x1.output ∨ x3 x6 (x1.output - 26);
      have x7 : Fin 26 → Bool := pairInput 0 0;
      have x8 : Fin 26 → Bool := pairInput 13 13;
      have x9 : Fin 26 → Bool := pairInput 0 13;
      have x10 : ℕ → (Fin 26 → Bool) → Prop := fun x10 x11 =>
        x5 x10 ∧ x6 x10 ∧ x4 x10 x9 = true ∧ ∀ x12 : Fin 2, wireVal 26 x1 (opnd x1 x10 x12) x11 = false;
      x1.size ≤ 64 ∧ IsAO2 26 x1 ∧ (∀ x11 ∈ x1.gates, x11.inputs.Nodup) ∧
      (∀ x11 : Fin 26 → Bool, x1.eval (List.ofFn x11) = true ↔
        ∃ (x12 x13 : Fin 13), x12 - x13 ∈ x2 ∧ x11 (Fin.castAdd 13 x12) = true ∧ x11 (Fin.natAdd 13 x13) = true) ∧
      (∃ x11 < x1.gates.length, x5 x11 ∧ ∃ x12 : Fin 26 → Bool, x4 x11 x12 = true ∧ x1.eval (List.ofFn x12) = false) ∧
      ∃ (x11 x12 x13 : ℕ), x3 x11 x12 ∧ x3 x12 x13 ∧ x10 x11 x7 ∧ x4 x11 x8 = true ∧
        x5 x12 ∧ x4 x12 x8 = false ∧ x10 x13 x8 ∧ x1.output < 26 := by
  rintro ⟨C, _, _, _, heval, _, _, _, _, _, _, _, _, _, _, _, hout⟩
  let x : Fin 26 → Bool := fun i => decide (i.val = C.output)
  have hlhs : C.eval (List.ofFn x) = true := by
    change (C.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (List.ofFn x)).getD C.output false = true
    rw [wires_getD_lt C.gates (List.ofFn x) C.output (by simp [hout])]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hout, ↓reduceDIte, Option.getD_some,
      x, decide_eq_true_eq]
  rcases (heval x).mp hlhs with ⟨p, l, _, hp, hl⟩
  simp only [x, decide_eq_true_eq, Fin.val_castAdd, Fin.val_natAdd] at hp hl
  omega

end PEqualNP.Outside.L_meta_19016_aux

theorem PEqualNP.Outside.L_meta_19016 : (¬∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit),     have x2 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))};     have x3 : ℕ → ℕ → Prop := PEqualNP.EdgeOwnership.InCone (26 : ℕ) x1;     have x4 : ℕ → (Fin (26 : ℕ) → Bool) → Bool := PEqualNP.EdgeOwnership.gateVal (26 : ℕ) x1;     have x5 : ℕ → Prop := fun (x5 : ℕ) => (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x5).op = PEqualNP.CircuitLowerBounds.GateOp.and;     have x6 : ℕ → Prop := fun (x6 : ℕ) => (26 : ℕ) + x6 = x1.output ∨ x3 x6 (x1.output - (26 : ℕ));     have x7 : Fin (26 : ℕ) → Bool := PEqualNP.EdgeOwnership.pairInput (0 : Fin (26 : ℕ)) (0 : Fin (26 : ℕ));     have x8 : Fin (26 : ℕ) → Bool := PEqualNP.EdgeOwnership.pairInput (13 : Fin (26 : ℕ)) (13 : Fin (26 : ℕ));     have x9 : Fin (26 : ℕ) → Bool := PEqualNP.EdgeOwnership.pairInput (0 : Fin (26 : ℕ)) (13 : Fin (26 : ℕ));     have x10 : ℕ → (Fin (26 : ℕ) → Bool) → Prop := fun (x10 : ℕ) (x11 : Fin (26 : ℕ) → Bool) => x5 x10 ∧ x6 x10 ∧ x4 x10 x9 = Bool.true ∧ ∀ (x12 : Fin (2 : ℕ)), PEqualNP.CleanedNonEdge.wireVal (26 : ℕ) x1 (PEqualNP.TopForm.opnd x1 x10 x12) x11 = Bool.false;     x1.size ≤ (64 : ℕ) ∧ PEqualNP.TopForm.IsAO2 (26 : ℕ) x1 ∧ (∀ x11 ∈ x1.gates, x11.inputs.Nodup) ∧ (∀ (x11 : Fin (26 : ℕ) → Bool), x1.eval (List.ofFn x11) = Bool.true ↔ ∃ (x12 : Fin (13 : ℕ)) (x13 : Fin (13 : ℕ)), x12 - x13 ∈ x2 ∧ x11 (Fin.castAdd (13 : ℕ) x12) = Bool.true ∧ x11 (Fin.natAdd (13 : ℕ) x13) = Bool.true) ∧ (∃ x11 < x1.gates.length, x5 x11 ∧ ∃ (x12 : Fin (26 : ℕ) → Bool), x4 x11 x12 = Bool.true ∧ x1.eval (List.ofFn x12) = Bool.false) ∧ ∃ (x11 : ℕ) (x12 : ℕ) (x13 : ℕ), x3 x11 x12 ∧ x3 x12 x13 ∧ x10 x11 x7 ∧ x4 x11 x8 = Bool.true ∧ x5 x12 ∧ x4 x12 x8 = Bool.false ∧ x10 x13 x8 ∧ x1.output < (26 : ℕ))  := by
  exact PEqualNP.Outside.L_meta_19016_aux.main_proof
