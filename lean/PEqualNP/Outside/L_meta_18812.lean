import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18812_aux

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm

def deriv (n : ℕ) (C : Circuit) (s : ℕ) (x : List Bool) : ℕ → Bool
  | w =>
    if w < n then decide (w = s)
    else
      match C.gates[w - n]? with
      | none => false
      | some g =>
        match g.inputs with
        | [u, v] =>
          if h : u < w ∧ v < w then
            match g.op with
            | GateOp.and =>
              ((C.wires x).getD u false && deriv n C s x v) ||
              (deriv n C s x u && (C.wires x).getD v false)
            | _ =>
              deriv n C s x u || deriv n C s x v
          else false
        | _ => false
termination_by w => w

theorem deriv_lt (n : ℕ) (C : Circuit) (s : ℕ) (x : List Bool) (i : ℕ) (hi : i < n) :
    deriv n C s x i = decide (i = s) := by
  unfold deriv
  simp [hi]

theorem main_proof :
    ∀ (n : ℕ) (C : Circuit) (s : ℕ) (x : List Bool), IsAO2 n C →
      ∃ d : ℕ → Bool, (∀ i < n, d i = decide (i = s)) ∧
        ∀ (j : ℕ) (g : Gate) (u v : ℕ), C.gates[j]? = some g → g.inputs = [u, v] →
        (g.op = GateOp.and → d (n + j) = ((C.wires x).getD u false && d v || d u && (C.wires x).getD v false)) ∧
        (g.op = GateOp.or → d (n + j) = (d u || d v)) := by
  intro n C s x hao
  refine ⟨deriv n C s x, fun i hi => deriv_lt n C s x i hi, ?_⟩
  intro j g u v hgj hin
  have hj : j < C.gates.length := by
    by_contra h
    rw [List.getElem?_eq_none (Nat.le_of_not_lt h)] at hgj
    cases hgj
  have hgk : PEqualNP.MetaComplexity.NestedCover.gateAt C j = g := by
    unfold PEqualNP.MetaComplexity.NestedCover.gateAt
    rw [List.getD_eq_getElem?_getD, hgj]
    rfl
  have hu : u < n + j := by
    apply hao.2.1 j hj u
    rw [hgk, hin]
    simp
  have hv : v < n + j := by
    apply hao.2.1 j hj v
    rw [hgk, hin]
    simp
  have hnotlt : ¬ (n + j < n) := by omega
  have hsub : n + j - n = j := by omega
  have hunf : deriv n C s x (n + j) =
      match g.op with
      | GateOp.and =>
        ((C.wires x).getD u false && deriv n C s x v) ||
        (deriv n C s x u && (C.wires x).getD v false)
      | _ =>
        deriv n C s x u || deriv n C s x v := by
    conv_lhs => unfold deriv
    simp only [hnotlt, ↓reduceIte, hsub, hgj, hin, hu, hv, and_self, ↓reduceDIte]
  constructor
  · intro hop
    rw [hunf, hop]
  · intro hop
    rw [hunf, hop]

end PEqualNP.Outside.L_meta_18812_aux

theorem PEqualNP.Outside.L_meta_18812 : (∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : ℕ) (x4 : List Bool), PEqualNP.TopForm.IsAO2 x1 x2 → ∃ (x6 : ℕ → Bool), (∀ x7 < x1, x6 x7 = Decidable.decide (x7 = x3)) ∧ ∀ (x7 : ℕ) (x8 : PEqualNP.CircuitLowerBounds.Gate) (x9 x10 : ℕ), x2.gates[x7]? = Option.some x8 → x8.inputs = [x9, x10] → (x8.op = PEqualNP.CircuitLowerBounds.GateOp.and → x6 (x1 + x7) = ((x2.wires x4).getD x9 Bool.false && x6 x10 || x6 x9 && (x2.wires x4).getD x10 Bool.false)) ∧ (x8.op = PEqualNP.CircuitLowerBounds.GateOp.or → x6 (x1 + x7) = (x6 x9 || x6 x10)))  := by
  exact PEqualNP.Outside.L_meta_18812_aux.main_proof
