import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18711_aux

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm

def wstep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem getD_append_left_lt (a b : List Bool) (i : ℕ) (hi : i < a.length) :
    (a ++ b).getD i false = a.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem getD_snoc_eq (a : List Bool) (v : Bool) :
    (a ++ [v]).getD a.length false = v := by
  simp [List.getD_eq_getElem?_getD]

theorem foldl_len (gs : List Gate) (w : List Bool) :
    (gs.foldl wstep w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => simp [List.foldl_cons, ih, wstep]; omega

def remapWire (n : ℕ) (f : Fin n → Fin n) (w : ℕ) : ℕ :=
  if h : w < n then (f ⟨w, h⟩).val else w

def remapGate (n : ℕ) (f : Fin n → Fin n) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (remapWire n f)⟩

theorem remapWire_inj (n : ℕ) (f : Fin n → Fin n) (hf : Function.Injective f) :
    Function.Injective (remapWire n f) := by
  intro u v huv
  dsimp only [remapWire] at huv
  split_ifs at huv with hu hv hv
  · have hfin : f ⟨u, hu⟩ = f ⟨v, hv⟩ := Fin.ext huv
    have := hf hfin
    exact congrArg Fin.val this
  · have := (f ⟨u, hu⟩).isLt; omega
  · have := (f ⟨v, hv⟩).isLt; omega
  · exact huv

theorem remapWire_lt (n : ℕ) (f : Fin n → Fin n) (k w : ℕ) (hw : w < n + k) :
    remapWire n f w < n + k := by
  dsimp only [remapWire]
  split_ifs with h
  · have := (f ⟨w, h⟩).isLt; omega
  · exact hw

theorem remapWire_ge (n : ℕ) (f : Fin n → Fin n) (w : ℕ) (hw : n ≤ w) :
    remapWire n f w = w := by
  dsimp only [remapWire]
  rw [dif_neg (Nat.not_lt.mpr hw)]

theorem foldl_remap (n : ℕ) (f : Fin n → Fin n) (gs : List Gate) (x : Fin n → Bool) :
    ∀ w, ((gs.map (remapGate n f)).foldl wstep (List.ofFn x)).getD (remapWire n f w) false =
      (gs.foldl wstep (List.ofFn (x ∘ f))).getD w false := by
  induction gs using List.reverseRecOn with
  | nil =>
    intro w
    simp only [List.map_nil, List.foldl_nil]
    by_cases hw : w < n
    · have hrw : remapWire n f w = (f ⟨w, hw⟩).val := dif_pos hw
      rw [hrw]
      have hlt : (f ⟨w, hw⟩).val < n := (f ⟨w, hw⟩).isLt
      simp [List.getD_eq_getElem?_getD, hw, hlt]
    · have hrw : remapWire n f w = w := dif_neg hw
      rw [hrw, List.getD_eq_default _ _ (by simp [List.length_ofFn]; omega),
          List.getD_eq_default _ _ (by simp [List.length_ofFn]; omega)]
  | append_singleton gs g ih =>
    intro w
    rw [List.map_append, List.map_singleton, List.foldl_append, List.foldl_cons, List.foldl_nil,
        List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hl1 : ((gs.map (remapGate n f)).foldl wstep (List.ofFn x)).length = n + gs.length := by
      rw [foldl_len, List.length_ofFn, List.length_map]
    have hl2 : (gs.foldl wstep (List.ofFn (x ∘ f))).length = n + gs.length := by
      rw [foldl_len, List.length_ofFn]
    have hval : (remapGate n f g).op.eval ((remapGate n f g).inputs.map fun i => ((gs.map (remapGate n f)).foldl wstep (List.ofFn x)).getD i false) =
        g.op.eval (g.inputs.map fun i => (gs.foldl wstep (List.ofFn (x ∘ f))).getD i false) := by
      simp only [remapGate, List.map_map]
      congr 1
      apply List.map_congr_left
      intro i _
      exact ih i
    by_cases hw : w < n + gs.length
    · have hrw : remapWire n f w < n + gs.length := remapWire_lt n f gs.length w hw
      rw [wstep, wstep, getD_append_left_lt _ _ _ (by omega), getD_append_left_lt _ _ _ (by omega)]
      exact ih w
    · by_cases heq : w = n + gs.length
      · subst heq
        have hrw : remapWire n f (n + gs.length) = n + gs.length := remapWire_ge n f _ (by omega)
        rw [wstep, wstep, hrw]
        have h1 : (List.foldl wstep (List.ofFn x) (List.map (remapGate n f) gs) ++
            [(remapGate n f g).op.eval (List.map (fun i => (List.foldl wstep (List.ofFn x) (List.map (remapGate n f) gs)).getD i false) (remapGate n f g).inputs)]).getD (n + gs.length) false =
            (remapGate n f g).op.eval (List.map (fun i => (List.foldl wstep (List.ofFn x) (List.map (remapGate n f) gs)).getD i false) (remapGate n f g).inputs) := by
          rw [← hl1, getD_snoc_eq]
        have h2 : (List.foldl wstep (List.ofFn (x ∘ f)) gs ++
            [g.op.eval (List.map (fun i => (List.foldl wstep (List.ofFn (x ∘ f)) gs).getD i false) g.inputs)]).getD (n + gs.length) false =
            g.op.eval (List.map (fun i => (List.foldl wstep (List.ofFn (x ∘ f)) gs).getD i false) g.inputs) := by
          rw [← hl2, getD_snoc_eq]
        rw [h1, h2, hval]
      · have hrw : remapWire n f w = w := remapWire_ge n f w (by omega)
        rw [wstep, wstep, hrw,
            List.getD_eq_default _ _ (by simp [hl1]; omega),
            List.getD_eq_default _ _ (by simp [hl2]; omega)]

theorem main_proof :
    ∀ (n : Nat) (f : Fin n → Fin n) (C : Circuit) (j a b : Nat), Function.Injective f →
      IsAO2 n C → (∀ g ∈ C.gates, g.inputs.Nodup) → C.output = n + j → C.gates[j]? = some ⟨.and, [a, b]⟩ →
      ∃ (D : Circuit) (u v : Nat), D.size = C.size ∧ IsAO2 n D ∧ (∀ g ∈ D.gates, g.inputs.Nodup) ∧
        D.output = n + j ∧ D.gates[j]? = some ⟨.and, [u, v]⟩ ∧ ∀ x : Fin n → Bool,
        D.eval (List.ofFn x) = C.eval (List.ofFn (x ∘ f)) ∧
        (D.wires (List.ofFn x)).getD u false = (C.wires (List.ofFn (x ∘ f))).getD a false ∧
        (D.wires (List.ofFn x)).getD v false = (C.wires (List.ofFn (x ∘ f))).getD b false := by
  intro n f C j a b hf hao hnd hout hgate
  let D : Circuit := ⟨C.gates.map (remapGate n f), C.output⟩
  refine ⟨D, remapWire n f a, remapWire n f b, ?_, ?_, ?_, hout, ?_, ?_⟩
  · simp [D, Circuit.size]
  · refine ⟨?_, ?_, ?_⟩
    · intro g hg
      simp only [D, List.mem_map] at hg
      rcases hg with ⟨g', hg', rfl⟩
      exact hao.1 g' hg'
    · intro k hk i hi
      have hk' : k < C.gates.length := by simpa [D] using hk
      have hgk : PEqualNP.MetaComplexity.NestedCover.gateAt D k = remapGate n f (PEqualNP.MetaComplexity.NestedCover.gateAt C k) := by
        simp [PEqualNP.MetaComplexity.NestedCover.gateAt, D, List.getElem?_eq_getElem hk, List.getElem?_eq_getElem hk']
      rw [hgk] at hi
      simp only [remapGate, List.mem_map] at hi
      rcases hi with ⟨i', hi', rfl⟩
      exact remapWire_lt n f k i' (hao.2.1 k hk' i' hi')
    · intro g hg
      simp only [D, List.mem_map] at hg
      rcases hg with ⟨g', hg', rfl⟩
      simp [remapGate, hao.2.2 g' hg']
  · intro g hg
    simp only [D, List.mem_map] at hg
    rcases hg with ⟨g', hg', rfl⟩
    exact (hnd g' hg').map (remapWire_inj n f hf)
  · simp only [D, List.getElem?_map, hgate, Option.map_some, remapGate, List.map_cons, List.map_nil]
  · intro x
    refine ⟨?_, foldl_remap n f C.gates x a, foldl_remap n f C.gates x b⟩
    change ((C.gates.map (remapGate n f)).foldl wstep (List.ofFn x)).getD C.output false =
      (C.gates.foldl wstep (List.ofFn (x ∘ f))).getD C.output false
    have hro : remapWire n f C.output = C.output := remapWire_ge n f C.output (by omega)
    have hres := foldl_remap n f C.gates x C.output
    rwa [hro] at hres

end PEqualNP.Outside.L_meta_18711_aux

theorem PEqualNP.Outside.L_meta_18711 : (∀ (x1 : ℕ) (x2 : Fin x1 → Fin x1) (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 x5 x6 : ℕ), Function.Injective x2 → PEqualNP.TopForm.IsAO2 x1 x3 → (∀ x9 ∈ x3.gates, x9.inputs.Nodup) → x3.output = x1 + x4 → x3.gates[x4]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x5, x6] : PEqualNP.CircuitLowerBounds.Gate } → ∃ (x12 : PEqualNP.CircuitLowerBounds.Circuit) (x13 : ℕ) (x14 : ℕ), x12.size = x3.size ∧ PEqualNP.TopForm.IsAO2 x1 x12 ∧ (∀ x15 ∈ x12.gates, x15.inputs.Nodup) ∧ x12.output = x1 + x4 ∧ x12.gates[x4]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x13, x14] : PEqualNP.CircuitLowerBounds.Gate } ∧ ∀ (x15 : Fin x1 → Bool), x12.eval (List.ofFn x15) = x3.eval (List.ofFn (x15 ∘ x2)) ∧ (x12.wires (List.ofFn x15)).getD x13 Bool.false = (x3.wires (List.ofFn (x15 ∘ x2))).getD x5 Bool.false ∧ (x12.wires (List.ofFn x15)).getD x14 Bool.false = (x3.wires (List.ofFn (x15 ∘ x2))).getD x6 Bool.false)  := by
  exact PEqualNP.Outside.L_meta_18711_aux.main_proof
