import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18617_aux

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm

def C15 : Circuit :=
  { gates := [
      ⟨GateOp.or, [13, 18]⟩,
      ⟨GateOp.or, [27, 24]⟩,
      ⟨GateOp.and, [1, 28]⟩,
      ⟨GateOp.or, [15, 19]⟩,
      ⟨GateOp.or, [30, 25]⟩,
      ⟨GateOp.and, [2, 31]⟩,
      ⟨GateOp.or, [16, 17]⟩,
      ⟨GateOp.or, [33, 21]⟩,
      ⟨GateOp.and, [4, 34]⟩,
      ⟨GateOp.or, [20, 22]⟩,
      ⟨GateOp.or, [36, 23]⟩,
      ⟨GateOp.and, [10, 37]⟩,
      ⟨GateOp.or, [29, 32]⟩,
      ⟨GateOp.or, [35, 38]⟩,
      ⟨GateOp.or, [39, 40]⟩
    ],
    output := 41 }

theorem h_size : C15.size ≤ 15 := by decide
theorem h_out_lo : 27 ≤ C15.output := by decide
theorem h_out_hi : C15.output < 27 + C15.size := by decide
theorem h_ao2 : IsAO2 27 C15 := by decide
theorem h_nodup : ∀ g ∈ C15.gates, g.inputs.Nodup := by decide

theorem h_eval (x : Fin 26 → Bool) :
    C15.eval (List.ofFn x ++ [x 1 || x 2]) =
      (((x 1 && ((x 13 || x 18) || x 24)) || (x 2 && ((x 15 || x 19) || x 25))) ||
       ((x 4 && ((x 16 || x 17) || x 21)) || (x 10 && ((x 20 || x 22) || x 23)))) := by
  simp [C15, Circuit.eval, Circuit.wires, GateOp.eval, List.ofFn_succ]

theorem h_lines_1 (l : Fin 13) :
    (l ≠ 1 ∧ ((1 : Fin 13) = l ∨ (1 : Fin 13) = l + 1 ∨ (1 : Fin 13) = l + 3 ∨ (1 : Fin 13) = l + 9)) ↔
      (l = 0 ∨ l = 5 ∨ l = 11) := by
  fin_cases l <;> decide

theorem h_lines_2 (l : Fin 13) :
    (l ≠ 1 ∧ ((2 : Fin 13) = l ∨ (2 : Fin 13) = l + 1 ∨ (2 : Fin 13) = l + 3 ∨ (2 : Fin 13) = l + 9)) ↔
      (l = 2 ∨ l = 6 ∨ l = 12) := by
  fin_cases l <;> decide

theorem h_lines_4 (l : Fin 13) :
    (l ≠ 1 ∧ ((4 : Fin 13) = l ∨ (4 : Fin 13) = l + 1 ∨ (4 : Fin 13) = l + 3 ∨ (4 : Fin 13) = l + 9)) ↔
      (l = 3 ∨ l = 4 ∨ l = 8) := by
  fin_cases l <;> decide

theorem h_lines_10 (l : Fin 13) :
    (l ≠ 1 ∧ ((10 : Fin 13) = l ∨ (10 : Fin 13) = l + 1 ∨ (10 : Fin 13) = l + 3 ∨ (10 : Fin 13) = l + 9)) ↔
      (l = 7 ∨ l = 9 ∨ l = 10) := by
  fin_cases l <;> decide

theorem main_proof :
    ∃ C : Circuit,
      C.size ≤ 15 ∧ 27 ≤ C.output ∧ C.output < 27 + C.size ∧
      IsAO2 27 C ∧ (∀ g ∈ C.gates, g.inputs.Nodup) ∧
      ∀ x : Fin 26 → Bool,
        C.eval (List.ofFn x ++ [x 1 || x 2]) = true ↔
          ∃ p l : Fin 13, p ∈ ([1, 2, 4, 10] : List (Fin 13)) ∧ l ≠ 1 ∧
            (p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9) ∧
            x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true := by
  refine ⟨C15, h_size, h_out_lo, h_out_hi, h_ao2, h_nodup, fun x => ?_⟩
  rw [h_eval]
  simp only [Bool.or_eq_true, Bool.and_eq_true, List.mem_cons, List.not_mem_nil, or_false]
  constructor
  · intro h
    rcases h with (⟨hp, (hl | hl) | hl⟩ | ⟨hp, (hl | hl) | hl⟩) | (⟨hp, (hl | hl) | hl⟩ | ⟨hp, (hl | hl) | hl⟩)
    · exact ⟨1, 0, Or.inl rfl, by decide, by decide, hp, hl⟩
    · exact ⟨1, 5, Or.inl rfl, by decide, by decide, hp, hl⟩
    · exact ⟨1, 11, Or.inl rfl, by decide, by decide, hp, hl⟩
    · exact ⟨2, 2, Or.inr (Or.inl rfl), by decide, by decide, hp, hl⟩
    · exact ⟨2, 6, Or.inr (Or.inl rfl), by decide, by decide, hp, hl⟩
    · exact ⟨2, 12, Or.inr (Or.inl rfl), by decide, by decide, hp, hl⟩
    · exact ⟨4, 3, Or.inr (Or.inr (Or.inl rfl)), by decide, by decide, hp, hl⟩
    · exact ⟨4, 4, Or.inr (Or.inr (Or.inl rfl)), by decide, by decide, hp, hl⟩
    · exact ⟨4, 8, Or.inr (Or.inr (Or.inl rfl)), by decide, by decide, hp, hl⟩
    · exact ⟨10, 7, Or.inr (Or.inr (Or.inr rfl)), by decide, by decide, hp, hl⟩
    · exact ⟨10, 9, Or.inr (Or.inr (Or.inr rfl)), by decide, by decide, hp, hl⟩
    · exact ⟨10, 10, Or.inr (Or.inr (Or.inr rfl)), by decide, by decide, hp, hl⟩
  · rintro ⟨p, l, hp, hlne, hinc, hxp, hxl⟩
    rcases hp with rfl | rfl | rfl | rfl
    · rcases (h_lines_1 l).mp ⟨hlne, hinc⟩ with rfl | rfl | rfl
      · exact Or.inl (Or.inl ⟨hxp, Or.inl (Or.inl hxl)⟩)
      · exact Or.inl (Or.inl ⟨hxp, Or.inl (Or.inr hxl)⟩)
      · exact Or.inl (Or.inl ⟨hxp, Or.inr hxl⟩)
    · rcases (h_lines_2 l).mp ⟨hlne, hinc⟩ with rfl | rfl | rfl
      · exact Or.inl (Or.inr ⟨hxp, Or.inl (Or.inl hxl)⟩)
      · exact Or.inl (Or.inr ⟨hxp, Or.inl (Or.inr hxl)⟩)
      · exact Or.inl (Or.inr ⟨hxp, Or.inr hxl⟩)
    · rcases (h_lines_4 l).mp ⟨hlne, hinc⟩ with rfl | rfl | rfl
      · exact Or.inr (Or.inl ⟨hxp, Or.inl (Or.inl hxl)⟩)
      · exact Or.inr (Or.inl ⟨hxp, Or.inl (Or.inr hxl)⟩)
      · exact Or.inr (Or.inl ⟨hxp, Or.inr hxl⟩)
    · rcases (h_lines_10 l).mp ⟨hlne, hinc⟩ with rfl | rfl | rfl
      · exact Or.inr (Or.inr ⟨hxp, Or.inl (Or.inl hxl)⟩)
      · exact Or.inr (Or.inr ⟨hxp, Or.inl (Or.inr hxl)⟩)
      · exact Or.inr (Or.inr ⟨hxp, Or.inr hxl⟩)

end PEqualNP.Outside.L_meta_18617_aux

theorem PEqualNP.Outside.L_meta_18617 : (∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit), x1.size ≤ (15 : ℕ) ∧ (27 : ℕ) ≤ x1.output ∧ x1.output < (27 : ℕ) + x1.size ∧ PEqualNP.TopForm.IsAO2 (27 : ℕ) x1 ∧ (∀ x2 ∈ x1.gates, x2.inputs.Nodup) ∧ ∀ (x2 : Fin (26 : ℕ) → Bool), x1.eval (List.ofFn x2 ++ [x2 (1 : Fin (26 : ℕ)) || x2 (2 : Fin (26 : ℕ))]) = Bool.true ↔ ∃ (x3 : Fin (13 : ℕ)) (x4 : Fin (13 : ℕ)), x3 ∈ [(1 : Fin (13 : ℕ)), (2 : Fin (13 : ℕ)), (4 : Fin (13 : ℕ)), (10 : Fin (13 : ℕ))] ∧ x4 ≠ (1 : Fin (13 : ℕ)) ∧ (x3 = x4 ∨ x3 = x4 + (1 : Fin (13 : ℕ)) ∨ x3 = x4 + (3 : Fin (13 : ℕ)) ∨ x3 = x4 + (9 : Fin (13 : ℕ))) ∧ x2 (Fin.castAdd (13 : ℕ) x3) = Bool.true ∧ x2 (Fin.natAdd (13 : ℕ) x4) = Bool.true)  := by
  exact PEqualNP.Outside.L_meta_18617_aux.main_proof
