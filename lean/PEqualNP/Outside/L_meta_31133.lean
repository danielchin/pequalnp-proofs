import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_31133_aux


open PEqualNP.CircuitLowerBounds
abbrev Sig := BitVec 256
def zero : Sig := 0
def one : Sig := BitVec.allOnes 256
def neg (a : Sig) : Sig := ~~~a
def bin (d : Nat) (a b : Sig) : Sig :=
  if d=0 then a &&& b else if d=1 then a ||| b else if d=2 then a &&& ~~~b else ~~~a &&& b
def proper (a : Sig) : Prop := a ≠ zero ∧ a ≠ one
def allowed (u : Bool) (d : Nat) : Prop := d<2 ∨ (u=true ∧ d<4)
def flipOp (d : Nat) := if d=2 then 3 else if d=3 then 2 else d
theorem allowed_four {u d} (h : allowed u d) : d=0 ∨ d=1 ∨ (u=true ∧ d=2) ∨ (u=true ∧ d=3) := by
  rcases h with h | ⟨h,j⟩
  · omega
  · have : d=0 ∨ d=1 ∨ d=2 ∨ d=3 := by omega
    rcases this with h1 | h1 | h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr (Or.inl ⟨h,h1⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨h,h1⟩))
theorem bin_flip {u d} (h : allowed u d) (a b : Sig) : bin d a b = bin (flipOp d) b a := by
  rcases allowed_four h with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩ <;> simp [bin,flipOp,BitVec.and_comm,BitVec.or_comm]
theorem flip_flip {u d} (h : allowed u d) : allowed u (flipOp d) ∧ flipOp (flipOp d)=d := by
  rcases allowed_four h with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
  all_goals simp_all [flipOp,allowed]

def Live (u : Bool) (target : Sig) : Nat → Finset Sig → Prop
  | 0,S => S={target} ∧ proper target
  | k+1,S => ∃ (U : Finset Sig) (a b : Sig) (d : Nat), allowed u d ∧ S=insert a (insert b U) ∧
      proper a ∧ proper b ∧ a ≠ b ∧
      bin d a b ∉ insert a (insert b U) ∧ Live u target k (insert (bin d a b) U)
theorem Live.stop {u} {target : Sig} (hp : proper target) : Live u target 0 {target} := ⟨rfl,hp⟩
theorem Live.binary {u} {target : Sig} {k : Nat} {U : Finset Sig} {a b : Sig} {d : Nat} (hd : allowed u d)
    (ha : proper a) (hb : proper b) (hab : a ≠ b)
    (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live u target k (insert (bin d a b) U)) :
    Live u target (k+1) (insert a (insert b U)) :=
  ⟨U,a,b,d,hd,rfl,ha,hb,hab,hfresh,tail⟩
theorem Live.ind {u} {target : Sig} {motive : ∀ (k : Nat) (S : Finset Sig), Live u target k S → Prop}
    (stop : ∀ (hp : proper target), motive 0 {target} (Live.stop hp))
    (binary : ∀ {k : Nat} {U : Finset Sig} {a b : Sig} {d : Nat} (hd : allowed u d)
      (ha : proper a) (hb : proper b) (hab : a ≠ b)
      (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live u target k (insert (bin d a b) U)),
      motive k (insert (bin d a b) U) tail →
      motive (k+1) (insert a (insert b U)) (Live.binary hd ha hb hab hfresh tail))
    {k : Nat} {S : Finset Sig} (h : Live u target k S) : motive k S h := by
  induction k generalizing S with
  | zero =>
    obtain ⟨rfl,hp⟩ := h
    exact stop hp
  | succ k ih =>
    obtain ⟨U,a,b,d,hd,rfl,ha,hb,hab,hf,tail⟩ := h
    exact binary hd ha hb hab hf tail (ih tail)

private lemma live_proper {u target k S} (h : Live u target k S) : ∀ a ∈ S, proper a := by
  induction h using Live.ind with
  | stop hp => simpa using hp
  | binary hd ha hb hab hf _ ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨ha,hb,fun a h => ih a (Finset.mem_insert_of_mem h)⟩

private lemma live_size {u target k S} (h : Live u target k S) : S.card ≤ k+1 := by
  induction h using Live.ind with
  | stop hp => simp
  | @binary k U a b d hd ha hb hab hf _ ih =>
    have hu : bin d a b ∉ U := fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    rw [Finset.card_insert_of_notMem hu] at ih
    have h1 := Finset.card_insert_le (a := a) (s := insert b U)
    have h2 := Finset.card_insert_le (a := b) (s := U)
    omega

def bit (i : Fin 256) (a : Sig) : Bool := a.getLsbD i.val
private lemma bit_zero (i) : bit i zero = false := by simp [bit,zero]
private lemma bit_one (i) : bit i one = true := by unfold bit one; rw [BitVec.getLsbD_allOnes]; simp
private lemma bit_neg (i) (a : Sig) : bit i (neg a) = !(bit i a) := by simp [bit,neg,i.isLt]
private lemma bit_bin (i d) (a b : Sig) : bit i (bin d a b) =
    (if d=0 then bit i a && bit i b else if d=1 then bit i a || bit i b else
      if d=2 then bit i a && !(bit i b) else !(bit i a) && bit i b) := by
  unfold bin
  split_ifs <;> simp [bit]
theorem bit_ext {a b : Sig} (h : ∀ i, bit i a = bit i b) : a=b :=
  BitVec.eq_of_getLsbD_eq fun j hj => h ⟨j,hj⟩

def nrm (u : Bool) (a : Sig) : Sig := if u && bit 0 a then neg a else a
theorem nrm_false (a : Sig) : nrm false a = a := rfl
theorem nrm_bit (a : Sig) : bit 0 (nrm true a) = false := by
  cases h : bit 0 a <;> simp [nrm,h,bit_neg]
theorem nrm_id {u} {a : Sig} (h : bit 0 a = false) : nrm u a = a := by simp [nrm,h]
theorem neg_neg' (a : Sig) : neg (neg a) = a := by simp [neg]
theorem nrm_neg (a : Sig) : nrm true (neg a) = nrm true a := by
  cases h : bit 0 a <;> simp [nrm,h,bit_neg,neg_neg']
theorem proper_neg {a : Sig} (h : proper (neg a)) : proper a := by
  refine ⟨?_,?_⟩
  · rintro rfl
    exact h.2 (by simp [neg,zero,one])
  · rintro rfl
    exact h.1 (by simp [neg,zero,one])
theorem proper_nrm {u} {a : Sig} (h : proper (nrm u a)) : proper a := by
  unfold nrm at h
  split at h
  · exact proper_neg h
  · exact h
def prime (d : Bool) (a b : Sig) := if d then a ||| b else a &&& b
theorem bit_prime (i) (d : Bool) (a b : Sig) : bit i (prime d a b) =
    (if d then bit i a || bit i b else bit i a && bit i b) := by cases d <;> simp [prime,bit]
theorem nrm_prime (d : Bool) (a b : Sig) :
    ∃ e, e<4 ∧ nrm true (prime d a b) = bin e (nrm true a) (nrm true b) := by
  refine ⟨if d then (if bit 0 a then (if bit 0 b then 0 else 2) else (if bit 0 b then 3 else 1))
    else (if bit 0 a then (if bit 0 b then 1 else 3) else (if bit 0 b then 2 else 0)),?_,?_⟩
  · split_ifs <;> omega
  · apply bit_ext
    intro i
    cases d <;> cases ha : bit 0 a <;> cases hb : bit 0 b <;>
      simp only [nrm,bit_prime,ha,hb,bit_bin,bit_neg,Bool.true_and,Bool.false_and,Bool.and_true,Bool.and_false,Bool.false_or,
        Bool.or_false,Bool.true_or,Bool.or_true,Bool.false_eq_true,ite_true,ite_false] <;>
      cases hx : bit i a <;> cases hy : bit i b <;> simp [hx,hy,bit_neg,bit_prime]

def gv (w : List Sig) (g : Gate) : Sig :=
  let xs := g.inputs.map (fun i => w.getD i zero)
  match g.op with
  | .and => xs.foldr (prime false) one
  | .or => xs.foldr (prime true) zero
  | .not => neg (xs.headD zero)
  | _ => zero

def execute (gs : List Gate) (w : List Sig) : List Sig :=
  gs.foldl (fun l g => l ++ [gv l g]) w

def represented (w : List Sig) (v : Sig) : Prop := v ∈ w ∨ ¬proper v
def Repr (u : Bool) (w : List Sig) (v : Sig) : Prop := represented w (nrm u v)

private lemma bin_laws (a : Sig) :
    bin 0 a one = a ∧ bin 1 a zero = a ∧
    bin 0 a zero = zero ∧ bin 1 a one = one ∧
    bin 0 a a = a ∧ bin 1 a a = a ∧ bin 2 a a = zero ∧ bin 3 a a = zero ∧ bin 2 a zero = a ∧
    bin 3 zero a = a ∧ bin 2 zero a = zero ∧ bin 3 a zero = zero ∧ bin 0 zero a = zero ∧ bin 1 zero a = a ∧
    bin 0 one a = a ∧ bin 1 one a = one := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> apply bit_ext <;> intro i <;>
    simp [bit_bin,bit_zero,bit_one]

private lemma neg_laws : neg zero = one ∧ neg one = zero := by simp [neg,zero,one]

private lemma operand_cases {w : List Sig} {a : Sig} (h : represented w a) :
    a = zero ∨ a = one ∨ a ∈ w ∧ proper a := by
  by_cases hz : a = zero
  · exact Or.inl hz
  by_cases ho : a = one
  · exact Or.inr (Or.inl ho)
  exact Or.inr (Or.inr ⟨h.resolve_right (fun x => x ⟨hz,ho⟩),hz,ho⟩)

def witness (u : Bool) (w : List Sig) (z : Sig) : Prop :=
  ∃ d a b, allowed u d ∧ a ∈ w ∧ b ∈ w ∧ proper a ∧ proper b ∧ a ≠ b ∧ z = bin d a b

private lemma bin_rep {u w a b} (d : Nat) (hd : allowed u d) (ha : represented w a) (hb : represented w b)
    (no : u=true → a ≠ one ∧ b ≠ one) :
    represented w (bin d a b) ∨ witness u w (bin d a b) := by
  have rz : represented w zero := Or.inr (fun h => h.1 rfl)
  have ro : represented w one := Or.inr (fun h => h.2 rfl)
  obtain ⟨a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15,a16⟩ := bin_laws a
  obtain ⟨b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,b13,b14,b15,b16⟩ := bin_laws b
  by_cases he : a=b
  · subst b
    left
    rcases allowed_four hd with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩
    · exact a5.symm ▸ ha
    · exact a6.symm ▸ ha
    · exact a7.symm ▸ rz
    · exact a8.symm ▸ rz
  rcases operand_cases ha with rfl | rfl | ⟨ham,hap⟩
  · left
    rcases allowed_four hd with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩
    · exact b13.symm ▸ rz
    · exact b14.symm ▸ hb
    · exact b11.symm ▸ rz
    · exact b10.symm ▸ hb
  · left
    rcases allowed_four hd with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
    · exact b15.symm ▸ hb
    · exact b16.symm ▸ ro
    · exact absurd rfl (no hu).1
    · exact absurd rfl (no hu).1
  rcases operand_cases hb with rfl | rfl | ⟨hbm,hbp⟩
  · left
    rcases allowed_four hd with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩
    · exact a3.symm ▸ rz
    · exact a2.symm ▸ ha
    · exact a9.symm ▸ ha
    · exact a12.symm ▸ rz
  · left
    rcases allowed_four hd with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
    · exact a1.symm ▸ ha
    · exact a4.symm ▸ ro
    · exact absurd rfl (no hu).2
    · exact absurd rfl (no hu).2
  exact Or.inr ⟨d,a,b,hd,ham,hbm,hap,hbp,he,rfl⟩

theorem norm_ne_one (a : Sig) : nrm true a ≠ one := by
  intro h
  have := nrm_bit a
  rw [h,bit_one] at this
  exact Bool.noConfusion this
theorem prime_rep {u w a b} (d : Bool) (ha : Repr u w a) (hb : Repr u w b) :
    Repr u w (prime d a b) ∨ witness u w (nrm u (prime d a b)) := by
  cases u
  · have e : prime d a b = bin (if d then 1 else 0) a b := by cases d <;> rfl
    have h := bin_rep (u:=false) (if d then 1 else 0) (Or.inl (by split <;> omega)) ha hb (by simp)
    unfold Repr
    simp only [nrm_false] at h ⊢
    rwa [e]
  · obtain ⟨e,he,eq⟩ := nrm_prime d a b
    unfold Repr
    rw [eq]
    exact bin_rep e (Or.inr ⟨rfl,he⟩) ha hb (fun _ => ⟨norm_ne_one a,norm_ne_one b⟩)
theorem repr_const {u w} {v : Sig} (h : v=zero ∨ v=one) : Repr u w v := by
  refine Or.inr fun hp => ?_
  have := proper_nrm hp
  rcases h with rfl | rfl
  · exact this.1 rfl
  · exact this.2 rfl
lemma get_rep {u} (w : List Sig) (i : Nat) : Repr u (w.map (nrm u)) (w.getD i zero) := by
  simp only [List.getD_eq_getElem?_getD]
  cases h : w[i]? with
  | none => exact repr_const (Or.inl rfl)
  | some a => exact Or.inl (List.mem_map_of_mem (List.mem_of_getElem? h))
theorem repr_neg {w a} (h : Repr true w a) : Repr true w (neg a) := by
  unfold Repr
  rwa [nrm_neg]

def isNot (g : Gate) : Bool := match g.op with
  | .not => true
  | _ => false
private lemma gate_rep (u : Bool) (w : List Sig) (g : Gate)
    (h : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2)
    (mono : u=false → isNot g=false) :
    Repr u (w.map (nrm u)) (gv w g) ∨ (isNot g=false ∧ witness u (w.map (nrm u)) (nrm u (gv w g))) := by
  obtain ⟨o,l⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at h
  obtain ⟨ho,hl⟩ := h
  have prim (d : Bool) : Repr u (w.map (nrm u)) ((l.map (fun i => w.getD i zero)).foldr (prime d) (if d then zero else one)) ∨
      witness u (w.map (nrm u)) (nrm u ((l.map (fun i => w.getD i zero)).foldr (prime d) (if d then zero else one))) := by
    have unit (v : Sig) : prime d v (if d then zero else one) = v := by
      apply bit_ext
      intro i
      cases d <;> simp [bit_prime,bit_zero,bit_one]
    cases l with
    | nil => exact Or.inl (repr_const (by cases d <;> simp))
    | cons i l =>
      cases l with
      | nil =>
        simp only [List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,unit]
        exact Or.inl (get_rep w i)
      | cons j l =>
        cases l with
        | cons a l => simp at hl
        | nil =>
          simp only [List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,unit]
          exact prime_rep d (get_rep w i) (get_rep w j)
  rcases ho with rfl | rfl | rfl
  · exact (prim false).imp id (fun h => ⟨rfl,h⟩)
  · exact (prim true).imp id (fun h => ⟨rfl,h⟩)
  · cases u
    · exact absurd (mono rfl) (by simp [isNot])
    left
    cases l with
    | nil => exact repr_const (Or.inr (by simp [gv,neg_laws]))
    | cons i l => exact repr_neg (get_rep w i)

private lemma pull_gate {u target} {w : List Sig} {z : Sig} {k S c} (h : Live u target k S)
    (hz : represented w z ∨ (c=1 ∧ witness u w z)) (sub : ∀ a ∈ S, a ∈ w++[z]) :
    ∃ k' S', k' ≤ k+c ∧ Live u target k' S' ∧ ∀ a ∈ S', a ∈ w := by
  by_cases hm : z ∈ S
  · by_cases hw : z ∈ w
    · refine ⟨k,S,by omega,h,?_⟩
      intro a ha
      have hu : a ∈ w ∨ a = z := by simpa using sub a ha
      rcases hu with hu | rfl
      · exact hu
      · exact hw
    · have hp := live_proper h z hm
      rcases hz with hr | ⟨rfl,d,a,b,hd,ha,hb,pa,pb,hab,eq⟩
      · exact False.elim ((hr.resolve_left hw) hp)
      · subst z
        let U := S.erase (bin d a b)
        have ht : Live u target k (insert (bin d a b) U) := by simpa [U,Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U, v ∈ w := by
          intro v hv
          obtain ⟨hne,hm⟩ := Finset.mem_erase.mp hv
          simpa [hne] using sub v hm
        have hf : bin d a b ∉ insert a (insert b U) := by
          intro hh
          rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          rcases Finset.mem_insert.mp u with eq | u
          · exact hw (eq.symm ▸ hb)
          · exact hw (hu _ u)
        exact ⟨_,_,Nat.le_refl _,Live.binary hd pa pb hab hf ht,by simpa using And.intro ha (And.intro hb hu)⟩
  · refine ⟨k,S,by omega,h,?_⟩
    intro a ha
    have hn : a ≠ z := fun hh => hm (hh ▸ ha)
    simpa [hn] using sub a ha

lemma extract {u target} (gs : List Gate) (w : List Sig)
    (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2)
    (mono : u=false → ∀ g ∈ gs, isNot g=false)
    (hp : proper target) (hout : target ∈ (execute gs w).map (nrm u)) :
    ∃ k S, k ≤ gs.countP (fun g => !isNot g) ∧ Live u target k S ∧ ∀ a ∈ S, a ∈ w.map (nrm u) := by
  induction gs generalizing w with
  | nil => exact ⟨0,{target},by simp,Live.stop hp,by simpa [execute] using hout⟩
  | cons g gs ih =>
    obtain ⟨k,S,hk,ht,hs⟩ := ih (w++[gv w g]) (fun a ha => legal a (by simp [ha]))
      (fun hu a ha => mono hu a (by simp [ha])) hout
    have rep := gate_rep u w g (legal g (by simp)) (fun hu => mono hu g (by simp))
    rw [List.map_append] at hs
    have rep' : represented (w.map (nrm u)) (nrm u (gv w g)) ∨
        ((if isNot g then 0 else 1)=1 ∧ witness u (w.map (nrm u)) (nrm u (gv w g))) :=
      rep.imp id (fun h => ⟨by simp [h.1],h.2⟩)
    obtain ⟨l,T,hl,hu,hT⟩ := pull_gate ht rep' hs
    refine ⟨l,T,?_,hu,hT⟩
    rw [List.countP_cons]
    cases hn : isNot g <;> simp [hn] at hl ⊢ <;> omega

lemma b_read (i) (w : List Sig) (j : Nat) :
    (w.map (bit i)).getD j false = bit i (w.getD j zero) := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases w[j]? with
  | none => exact (bit_zero _).symm
  | some a => rfl

private lemma run_bit (i) (g : Gate) (w : List Sig)
    (hg : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
    bit i (gv w g) = g.op.eval (g.inputs.map fun j => (w.map (bit i)).getD j false) := by
  obtain ⟨o,l⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hg
  simp only [b_read]
  rcases hg with rfl | rfl | rfl
  · induction l with
    | nil => exact bit_one _
    | cons a l ih =>
      change bit i (prime false _ _) = (_ && _)
      rw [bit_prime]; exact congrArg (fun x => bit i (w.getD a zero) && x) ih
  · induction l with
    | nil => exact bit_zero _
    | cons a l ih =>
      change bit i (prime true _ _) = (_ || _)
      rw [bit_prime]; exact congrArg (fun x => bit i (w.getD a zero) || x) ih
  · cases l with
    | nil =>
      change bit i (neg zero) = !false
      rw [bit_neg,bit_zero]
    | cons a l => exact bit_neg _ _

lemma execute_bits (gs : List Gate) (i) (w : List Sig)
    (hg : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
    (execute gs w).map (bit i) =
    gs.foldl (fun (l : List Bool) g => l++[g.op.eval (g.inputs.map fun j => l.getD j false)]) (w.map (bit i)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (execute gs (w++[gv w g])).map _ = _
    rw [ih _ (fun a ha => hg a (by simp [ha]))]
    simp only [List.foldl_cons,List.map_append,List.map_singleton,run_bit i g w (hg g (by simp))]

abbrev Wire (R : Type) := R → Bool

def inv {R} (a : Wire R) : Wire R := fun r => !(a r)

def combine {R} (isOr : Bool) (a b : Wire R) : Wire R :=
  if isOr then fun r => a r || b r else fun r => a r && b r
def comb {R} (d : Nat) (a b : Wire R) : Wire R :=
  if d=0 then combine false a b else if d=1 then combine true a b else
    if d=2 then combine false a (inv b) else combine false (inv a) b

def Constant {R} (a : Wire R) : Prop := ∃ b : Bool, a = fun _ => b

noncomputable def cost {R} (a : Wire R) : Nat := by
  classical exact if Constant a then 1 else 0

noncomputable def mass {R} (xs : List (Wire R)) : Nat := (xs.map cost).sum

def Available {R} (u : Bool) (pool : List (Wire R)) (v : Wire R) : Prop :=
  v ∈ pool ∨ Constant v ∨ (u=true ∧ inv v ∈ pool)

def supply {R} (u : Bool) (pool xs : List (Wire R)) := ∀ a ∈ xs, Available u pool a

def Reach {R} (u : Bool) (roots : List (Wire R)) : Nat → List (Wire R) → Prop
  | 0,b => b=roots
  | p+1,c => ∃ (op : Bool) (bank : List (Wire R)) (a b : Wire R), Reach u roots p bank ∧ Available u bank a ∧
      Available u bank b ∧ c=combine op a b :: bank
theorem Reach.start {R u} {roots : List (Wire R)} : Reach u roots 0 roots := rfl
theorem Reach.two {R u} {roots : List (Wire R)} {p bank a b} (op : Bool) (h : Reach u roots p bank)
    (ha : Available u bank a) (hb : Available u bank b) : Reach u roots (p+1) (combine op a b :: bank) :=
  ⟨op,bank,a,b,h,ha,hb,rfl⟩
theorem Reach.ind {R u} {roots : List (Wire R)} {motive : ∀ p bank, Reach u roots p bank → Prop}
    (start : motive 0 roots Reach.start)
    (two : ∀ {p bank a b} (op : Bool) (h : Reach u roots p bank) (ha : Available u bank a)
      (hb : Available u bank b), motive p bank h →
      motive (p+1) (combine op a b :: bank) (Reach.two op h ha hb))
    {p bank} (h : Reach u roots p bank) : motive p bank h := by
  induction p generalizing bank with
  | zero =>
    obtain rfl := h
    exact start
  | succ p ih =>
    obtain ⟨op,bank,a,b,h,ha,hb,rfl⟩ := h
    exact two op h ha hb (ih h)

def kept {α : Type} (save : Bool) (x : α) (xs : List α) := if save then x::xs else xs

def Run {R} (u : Bool) (goal : Wire R) : Nat → List (Wire R) → Prop
  | 0,zs => List.Perm [goal] zs
  | s+1,zs => ∃ (op : Nat) (ka kb : Bool) (a b : Wire R) (rest : List (Wire R)), allowed u op ∧ (a::b::rest).Perm zs ∧
      Run u goal s (comb op a b :: kept ka a (kept kb b rest))
theorem Run.stop {R u} {goal : Wire R} : Run u goal 0 [goal] := List.Perm.refl _
theorem Run.perm {R u} {goal : Wire R} {s : Nat} {xs zs : List (Wire R)} (p : xs.Perm zs)
    (h : Run u goal s xs) : Run u goal s zs := by
  cases s with
  | zero => exact List.Perm.trans h p
  | succ s =>
    obtain ⟨op,ka,kb,a,b,rest,hd,q,h⟩ := h
    exact ⟨op,ka,kb,a,b,rest,hd,q.trans p,h⟩
theorem Run.two {R u} {goal : Wire R} {s : Nat} {a b : Wire R} {rest : List (Wire R)} (op : Nat) (hd : allowed u op) (ka kb : Bool)
    (h : Run u goal s (comb op a b :: kept ka a (kept kb b rest))) : Run u goal (s+1) (a::b::rest) :=
  ⟨op,ka,kb,a,b,rest,hd,List.Perm.refl _,h⟩
theorem Run.ind {R u} {goal : Wire R} {motive : ∀ s ws, Run u goal s ws → Prop}
    (stop : motive 0 [goal] Run.stop)
    (perm : ∀ {s xs zs} (p : List.Perm xs zs) (h : Run u goal s xs), motive s xs h → motive s zs (Run.perm p h))
    (two : ∀ {s a b rest} (op : Nat) (hd : allowed u op) (ka kb : Bool) (h : Run u goal s (comb op a b :: kept ka a (kept kb b rest))),
      motive s _ h → motive (s+1) (a::b::rest) (Run.two op hd ka kb h))
    {s ws} (h : Run u goal s ws) : motive s ws h := by
  induction s generalizing ws with
  | zero => exact perm h Run.stop stop
  | succ s ih =>
    obtain ⟨op,ka,kb,a,b,rest,hd,p,h⟩ := h
    exact perm p (Run.two op hd ka kb h) (two op hd ka kb h (ih h))

theorem mass_cons {R} (a : Wire R) (xs) : mass (a::xs)=cost a + mass xs := by
  simp [mass]

theorem mass_kept {R} (a : Wire R) (xs) (k : Bool) : mass xs ≤ mass (kept k a xs) := by
  cases k <;> simp [kept,mass_cons]

theorem inv_constant {R} {a : Wire R} (h : Constant a) : Constant (inv a) := by
  obtain ⟨v,rfl⟩ := h
  exact ⟨!v,rfl⟩

theorem inv_inv' {R} (a : Wire R) : inv (inv a)=a := by
  funext r
  simp [inv]
theorem cost_inv {R} (a : Wire R) : cost (inv a)=cost a := by
  have : Constant (inv a) ↔ Constant a := ⟨fun h => inv_inv' a ▸ inv_constant h,inv_constant⟩
  by_cases h : Constant a
  · simp only [cost,if_pos h,if_pos (this.mpr h)]
  · simp only [cost,if_neg h,if_neg (fun x => h (this.mp x))]
theorem avail_inv {R u} {bank : List (Wire R)} {a} (hu : u=true) (h : Available u bank a) : Available u bank (inv a) := by
  rcases h with h | h | ⟨_,h⟩
  · exact Or.inr (Or.inr ⟨hu,(inv_inv' a).symm ▸ h⟩)
  · exact Or.inr (Or.inl (inv_constant h))
  · exact Or.inl h
theorem both_constant {R} {a b : Wire R} (op) (h : Constant a) (g : Constant b) :
    Constant (combine op a b) := by
  obtain ⟨v,rfl⟩ := h
  obtain ⟨w,rfl⟩ := g
  cases op <;> exact ⟨_,rfl⟩

theorem from_constant {R u} (op) {a b : Wire R} {bank}
    (h : Constant a ∨ Constant b) (ha : Available u bank a) (hb : Available u bank b) :
    Available u bank (combine op a b) := by
  rcases h with ⟨v,rfl⟩ | ⟨v,rfl⟩
  · cases op <;> cases v
    · exact Or.inr (Or.inl ⟨false, by funext x; simp [combine]⟩)
    · simpa [combine] using hb
    · simpa [combine] using hb
    · exact Or.inr (Or.inl ⟨true, by funext x; simp [combine]⟩)
  · cases op <;> cases v
    · exact Or.inr (Or.inl ⟨false, by funext x; simp [combine]⟩)
    · simpa [combine] using ha
    · simpa [combine] using ha
    · exact Or.inr (Or.inl ⟨true, by funext x; simp [combine]⟩)

theorem available_cons {R u} {bank v} (w : Wire R) (h : Available u bank v) :
    Available u (w::bank) v :=
  h.imp (List.mem_cons_of_mem _) (Or.imp id (And.imp id (List.mem_cons_of_mem _)))

theorem extend_two {R u} (roots : List (Wire R)) {p bank a b} (op) (hp : Reach u roots p bank)
    (ha : Available u bank a) (hb : Available u bank b) :
    ∃ q next, Reach u roots q next ∧ Available u next (combine op a b) ∧
        (∀ v, Available u bank v → Available u next v) ∧
        q+cost a+cost b ≤ p+1+cost (combine op a b) := by
  classical
  by_cases c : Constant a ∨ Constant b
  · refine ⟨p,bank,hp,from_constant op c ha hb,fun _ h => h,?_⟩
    by_cases ca : Constant a <;> by_cases cb : Constant b
    · simp [cost,ca,cb,both_constant op ca cb]
    · simp [cost,ca,cb]
    · simp [cost,ca,cb]
    · exact False.elim (c.elim ca cb)
  · have ca : ¬Constant a := fun h => c (Or.inl h)
    have cb : ¬Constant b := fun h => c (Or.inr h)
    exact ⟨p+1,_,Reach.two op hp ha hb,Or.inl (by simp),fun _ h => available_cons _ h,
      by simp [cost,ca,cb]⟩
theorem comb_prime {R u} {bank : List (Wire R)} {d a b} (hd : allowed u d) (ha : Available u bank a) (hb : Available u bank b) :
    ∃ op x y, comb d a b=combine op x y ∧ Available u bank x ∧ Available u bank y ∧ cost x=cost a ∧ cost y=cost b := by
  rcases allowed_four hd with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
  · exact ⟨false,a,b,rfl,ha,hb,rfl,rfl⟩
  · exact ⟨true,a,b,rfl,ha,hb,rfl,rfl⟩
  · exact ⟨false,a,inv b,rfl,ha,avail_inv hu hb,rfl,cost_inv b⟩
  · exact ⟨false,inv a,b,rfl,avail_inv hu ha,hb,cost_inv a,rfl⟩
theorem extend_comb {R u} (roots : List (Wire R)) {p bank a b} (d) (hd : allowed u d) (hp : Reach u roots p bank)
    (ha : Available u bank a) (hb : Available u bank b) :
    ∃ q next, Reach u roots q next ∧ Available u next (comb d a b) ∧
        (∀ v, Available u bank v → Available u next v) ∧
        q+cost a+cost b ≤ p+1+cost (comb d a b) := by
  obtain ⟨op,x,y,e,hx,hy,cx,cy⟩ := comb_prime hd ha hb
  rw [e,←cx,←cy]
  exact extend_two roots op hp hx hy

theorem mem_kept {α : Type} {k : Bool} {x a : α} {xs} (h : x ∈ kept k a xs) :
    x=a ∨ x∈xs := by cases k <;> simp_all [kept]

theorem contraction {R u} {goal : Wire R} (nc : ¬Constant goal) {s ws}
    (h : Run u goal s ws) (roots : List (Wire R)) {p bank}
    (hp : Reach u roots p bank) (hs : supply u bank ws) :
    ∃ q next, Reach u roots q next ∧ Available u next goal ∧ q+mass ws ≤ p+s := by
  classical
  induction h using Run.ind generalizing p bank with
  | stop =>
    exact ⟨p,bank,hp,hs _ (by simp),by simp [mass,cost,nc]⟩
  | perm eq _ ih =>
    have hsub : supply u bank _ := fun v hv => hs v (eq.mem_iff.mp hv)
    obtain ⟨q,W,hW,hv,hl⟩ := ih hp hsub
    exact ⟨q,W,hW,hv,by simpa only [mass,←(eq.map cost).sum_eq] using hl⟩
  | @two s a b rest op hd ka kb _ ih =>
    obtain ⟨r,T,hT,hz,inc,le⟩ := extend_comb roots op hd hp (hs a (by simp)) (hs b (by simp))
    have ht : supply u T (comb op a b :: kept ka a (kept kb b rest)) := by
      intro v h
      rcases List.mem_cons.mp h with rfl | hh
      · exact hz
      · apply inc v
        apply hs
        rcases mem_kept hh with rfl | hh
        · simp
        · exact List.mem_cons_of_mem _ (List.mem_cons.mpr (mem_kept hh))
    obtain ⟨q,W,hW,hv,hl⟩ := ih hT ht
    have hlen := mass_kept a (kept kb b rest) ka
    have hlen' := mass_kept b rest kb
    rw [mass_cons] at hl
    refine ⟨q,W,hW,hv,?_⟩
    rw [mass_cons,mass_cons]
    omega

def restrictRows {R S : Type} (rows : S → R) (a : Wire R) : Wire S :=
  fun r => a (rows r)

theorem restrict_kept {R S : Type} (rows : S → R) (k : Bool) (a : Wire R) (ws) :
    (kept k a ws).map (restrictRows rows) =
    kept k (restrictRows rows a) (ws.map (restrictRows rows)) := by
  cases k <;> simp [kept]

theorem restrict_comb {R S : Type} (rows : S → R) (d) (a b : Wire R) :
    restrictRows rows (comb d a b) = comb d (restrictRows rows a) (restrictRows rows b) := by
  unfold comb
  split_ifs <;> rfl
theorem restrict_run {R S : Type} {u} (rows : S → R) {goal s ws} (h : Run u goal s ws) :
    Run u (restrictRows rows goal) s (ws.map (restrictRows rows)) := by
  induction h using Run.ind with
  | stop => exact Run.stop
  | perm p _ ih => exact Run.perm (p.map _) ih
  | two op hd ka kb _ ih =>
    simp only [List.map_cons,restrict_kept,restrict_comb] at ih ⊢
    exact Run.two op hd ka kb ih

theorem projected_bound {R S : Type} {u} (rows : S → R) {goal s ws} (h : Run u goal s ws)
    (nc : ¬Constant (restrictRows rows goal)) {roots : List (Wire S)} {p bank L}
    (hp : Reach u roots p bank) (hs : supply u bank (ws.map (restrictRows rows)))
    (hl : ∀ q bs, Reach u roots q bs → Available u bs (restrictRows rows goal) → L ≤ q) :
    L + mass (ws.map (restrictRows rows)) ≤ p+s := by
  obtain ⟨q,bs,hq,ht,hle⟩ := contraction nc (restrict_run rows h) roots hp hs
  have hqle := hl q bs hq ht
  omega


abbrev Row := Fin 256
def observe (a : Sig) : Wire Row := fun r => bit r a
def table (f : Wire Row) : Sig :=
  (BitVec.ofBoolListLE (List.ofFn f)).cast (List.length_ofFn)

theorem bit_table (f : Wire Row) (r : Row) : bit r (table f) = f r := by
  simp only [bit,table,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]; simp [r.isLt]

theorem table_observe (v : Sig) : table (observe v) = v := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  exact bit_table (observe v) ⟨j,hj⟩

theorem observe_table (f : Wire Row) : observe (table f) = f := by
  funext r
  exact bit_table f r

theorem obs_neg (a : Sig) : observe (neg a) = inv (observe a) := by
  funext r
  exact bit_neg _ _

theorem obs_bin (d : Nat) (a b : Sig) :
    observe (bin d a b) = comb d (observe a) (observe b) := by
  funext r
  simp only [observe,bit_bin,comb]
  split_ifs <;> rfl

theorem map_kept {α β : Type} (f : α → β) (d : Bool) (a : α) (l : List α) :
    (kept d a l).map f = kept d (f a) (l.map f) := by cases d <;> rfl

theorem kept_nd {α : Type} (k : Bool) (a : α) (l : List α)
    (hn : l.Nodup) (ha : a ∉ l) : (kept k a l).Nodup := by cases k <;> simp [kept,hn,ha]

theorem kept_fin (k : Bool) (a : Sig) (l : List Sig) :
    (kept k a l).toFinset = if k then insert a l.toFinset else l.toFinset := by
  cases k <;> simp [kept]

theorem list_run {u} {T : Sig} {k S} (h : Live u T k S) (v : List Sig)
    (hv : v.Nodup) (eqv : v.toFinset = S) : Run u (observe T) k (v.map observe) := by
  classical
  induction h using Live.ind generalizing v with
  | stop hp =>
    have eq : [T].Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp) hv
      simpa [eqv]
    exact Run.perm (eq.map _) Run.stop
  | @binary k U a b d hd ha hb hab fresh _ ih =>
    let rest := ((U.erase a).erase b).toList
    let ka := decide (a ∈ U)
    let kb := decide (b ∈ U)
    let mid := kept kb b rest
    let tail := kept ka a mid
    have er : rest.toFinset = (U.erase a).erase b := by simp [rest]
    have ar : a ∉ rest := by simp [rest]
    have br : b ∉ rest := by simp [rest]
    have hr : rest.Nodup := Finset.nodup_toList _
    have bm := kept_nd kb b rest hr br
    have am : a ∉ mid := by cases h : kb <;> simp [mid,kept,h,hab,ar]
    have nd := kept_nd ka a mid bm am
    have ht : tail.toFinset = U := by
      change (kept ka a (kept kb b rest)).toFinset = U
      rw [kept_fin,kept_fin,er]
      ext j
      by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> by_cases aj : j=a <;>
        by_cases bj : j=b <;> simp_all [ka,kb]
    have hf : bin d a b ∉ tail := by
      intro hz
      exact fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (ht ▸ List.mem_toFinset.mpr hz)))
    have progress := ih (bin d a b::tail) (List.nodup_cons.mpr ⟨hf,nd⟩) (by simp [ht])
    change Run _ _ _ ((bin d a b::kept ka a (kept kb b rest)).map observe) at progress
    rw [List.map_cons,map_kept,map_kept,obs_bin] at progress
    have perm : (a::b::rest).Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp [hab,ar,br,hr]) hv
      ext j
      by_cases ja : j=a <;> by_cases jb : j=b <;> simp_all [er]
    exact Run.perm (perm.map _) (Run.two d hd ka kb progress)


theorem table_inv (f : Wire Row) : table (inv f) = neg (table f) := by
  rw [←table_observe (neg (table f)),obs_neg,observe_table]

theorem table_prime (d : Bool) (f g : Wire Row) :
    table (combine d f g) = prime d (table f) (table g) := by
  apply bit_ext
  intro r
  rw [bit_table,bit_prime,bit_table,bit_table]
  cases d <;> rfl

theorem available_rep {u} {bank : List (Wire Row)} {a} (h : Available u bank a) :
    Repr u ((bank.map table).map (nrm u)) (table a) := by
  rcases h with hm | ⟨b,rfl⟩ | ⟨rfl,hm⟩
  · exact Or.inl (List.mem_map_of_mem (List.mem_map_of_mem hm))
  · apply repr_const
    cases b
    · exact Or.inl (bit_ext fun i => (bit_table _ i).trans (bit_zero i).symm)
    · exact Or.inr (bit_ext fun i => (bit_table _ i).trans (bit_one i).symm)
  · have := table_inv a
    refine Or.inl ?_
    rw [←nrm_neg,←this]
    exact List.mem_map_of_mem (List.mem_map_of_mem hm)

theorem reach_live_sub {u} {roots : List (Wire Row)} {p bank}
    (h : Reach u roots p bank) {T k S} (run : Live u T k S)
    (sub : ∀ a ∈ S, a ∈ (bank.map table).map (nrm u)) :
    ∃ l V, l ≤ p+k ∧ Live u T l V ∧ ∀ a ∈ V, a ∈ (roots.map table).map (nrm u) := by
  induction h using Reach.ind generalizing k S with
  | start => exact ⟨k,S,by omega,run,sub⟩
  | @two p bank a b d h ha hb ih =>
    rw [List.map_cons,List.map_cons,table_prime] at sub
    have rep := prime_rep d (available_rep ha) (available_rep hb)
    obtain ⟨k',S',hk,run',sub'⟩ := pull_gate (c:=1) run (rep.imp id (fun h => ⟨rfl,h⟩))
      (fun a hm => by simpa [or_comm] using sub a hm)
    obtain ⟨l,V,hl,hr,hs⟩ := ih run' sub'
    exact ⟨l,V,by omega,hr,hs⟩

def plainWord (a : Sig) : Bool := !(bit 0 a)
theorem nrm_map {u} {w : List Sig} (h : w.all plainWord=true) : w.map (nrm u)=w := by
  have e : w.map (nrm u) = w.map id := by
    apply List.map_congr_left
    intro a ha
    exact nrm_id (by simpa [plainWord] using List.all_eq_true.mp h a ha)
  rw [e,List.map_id]
theorem reach_live {u} {roots : List Sig} {p bank T} (hp : proper T) (nT : plainWord T=true) (nR : roots.all plainWord=true)
    (h : Reach u (roots.map observe) p bank) (hit : Available u bank (observe T)) :
    ∃ k S, k ≤ p ∧ Live u T k S ∧ ∀ a ∈ S, a ∈ roots := by
  have hm := available_rep hit
  rw [table_observe] at hm
  unfold Repr at hm
  rw [nrm_id (by simpa [plainWord] using nT)] at hm
  have mem := hm.resolve_right (fun hn => hn hp)
  obtain ⟨l,V,hl,hr,hs⟩ := reach_live_sub h (Live.stop hp) (by simpa using mem)
  refine ⟨l,V,by omega,hr,?_⟩
  have e : (roots.map observe).map table = roots := by simp [List.map_map,Function.comp_def,table_observe]
  rw [e,nrm_map nR] at hs
  exact hs

theorem live_row_difference {u T k S} (h : Live u T k S) {r s : Row}
    (diff : bit r T ≠ bit s T) : ∃ a ∈ S, bit r a ≠ bit s a := by
  induction h using Live.ind with
  | stop hp => exact ⟨_,by simp,diff⟩
  | @binary k U a b d hd ha hb hab hf _ ih =>
    obtain ⟨v,hv,hd⟩ := ih
    rcases Finset.mem_insert.mp hv with rfl | hu
    · by_cases aeq : bit r a = bit s a
      · refine ⟨b,by simp,?_⟩
        intro beq
        exact hd (by rw [bit_bin,bit_bin,aeq,beq])
      · exact ⟨a,by simp,aeq⟩
    · exact ⟨v,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu),hd⟩

theorem raw_required {u T k S} (h : Live u T k S) (roots : List Sig) (a : Sig)
    (sub : ∀ v ∈ S, v ∈ roots) (r s : Row) (diff : bit r T ≠ bit s T)
    (isolated : ∀ v ∈ roots, v ≠ a → bit r v = bit s v) : a ∈ S := by
  obtain ⟨v,hv,hd⟩ := live_row_difference h diff
  by_cases veq : v=a
  · simpa [veq] using hv
  · exact False.elim (hd (isolated v (sub v hv) veq))

def rename (f : Row → Row) (a : Sig) := table fun r => bit (f r) a
theorem bit_rename (f : Row → Row) (a : Sig) (r : Row) :
    bit r (rename f a) = bit (f r) a := bit_table _ _
theorem observe_rename (f : Row → Row) (a : Sig) :
    observe (rename f a) = restrictRows f (observe a) := by funext r; exact bit_rename f a r

def Lower (u : Bool) (roots : List Sig) (T : Sig) (L : Nat) : Prop :=
  ∀ p bank, Reach u (roots.map observe) p bank → Available u bank (observe T) → L ≤ p

def Impossible (u : Bool) (T : Sig) (cap : Nat) (S : Finset Sig) : Prop :=
  ∀ k, k ≤ cap → ¬Live u T k S

def Essential (T : Sig) (roots : List Sig) (a : Sig) : Prop :=
  ∃ r s : Row, bit r T ≠ bit s T ∧ ∀ v ∈ roots, v ≠ a → bit r v = bit s v

theorem lower_impossible {u roots T L} (hp : proper T) (nT : plainWord T=true) (nR : roots.all plainWord=true)
    (essential : ∀ a ∈ roots, Essential T roots a)
    (noRun : Impossible u T L roots.toFinset) : Lower u roots T (L+1) := by
  intro p bank h ha
  obtain ⟨k,S,hk,run,hs⟩ := reach_live hp nT nR h ha
  have he : roots.toFinset = S := by
    ext a
    rw [List.mem_toFinset]
    refine ⟨fun hm => ?_,hs a⟩
    obtain ⟨r,s,hd,iso⟩ := essential _ hm
    exact raw_required run roots a hs r s hd iso
  by_contra! small
  exact noRun k (by omega) (he.symm ▸ run)

theorem observe_proper {v : Sig} (hv : proper v) : ¬Constant (observe v) := by
  rintro ⟨b,h⟩
  have hr : Repr false [] v := by
    apply repr_const
    cases b
    · exact Or.inl (bit_ext fun i => (congrFun h i).trans (bit_zero i).symm)
    · exact Or.inr (bit_ext fun i => (congrFun h i).trans (bit_one i).symm)
  have hr' : represented [] v := hr
  exact (hr'.resolve_left (by simp)) hv

theorem mass_append {R} (a b : List (Wire R)) : mass (a++b) = mass a + mass b := by
  simp [mass]
theorem mass_constants {R} (xs : List (Wire R)) (hc : ∀ x ∈ xs, Constant x) :
    mass xs = xs.length := by
  induction xs with
  | nil => simp [mass]
  | cons a xs ih =>
    have ha := hc a (by simp)
    simp only [mass_cons,List.length_cons,cost,if_pos ha,ih (fun x hx => hc x (by simp [hx]))]
    omega

theorem lower_slice {u} {roots other : List Sig} {T G : Sig} (pT : proper T) (nT : plainWord T=true) (nR : roots.all plainWord=true) (pG : proper G)
    (r : Row → Row) (eq : rename r T = G)
    (covered : ∀ a ∈ roots, Available u (other.map observe) (observe (rename r a)))
    (singles : Finset Sig) (necessary : ∀ a ∈ singles, Essential T roots a)
    (constant : ∀ a ∈ singles, Constant (observe (rename r a)))
    (L : Nat) (prior : Lower u other G L) : Lower u roots T (L + singles.card) := by
  classical
  intro p bank hh ha
  obtain ⟨k,S,hk,run,sub⟩ := reach_live pT nT nR hh ha
  have subS : singles ⊆ S := by
    intro a hs
    obtain ⟨i,j,hd,hiso⟩ := necessary a hs
    exact raw_required run roots a sub i j hd hiso
  let front := singles.toList ++ (S \ singles).toList
  have nd : front.Nodup := by
    simp only [front,List.nodup_append]
    refine ⟨Finset.nodup_toList _,Finset.nodup_toList _,?_⟩
    intro a ha b hb he
    subst b
    exact (Finset.mem_sdiff.mp (Finset.mem_toList.mp hb)).2 (Finset.mem_toList.mp ha)
  have fe : front.toFinset=S := by ext a; simp [front,Finset.union_sdiff_of_subset subS]
  have run' := list_run run front nd fe
  have gc : restrictRows r (observe T) = observe G := (observe_rename _ _).symm.trans (congrArg observe eq)
  have supp : supply u (other.map observe) ((front.map observe).map (restrictRows r)) := by
    intro v hv
    obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
    obtain ⟨a,hmem,rfl⟩ := List.mem_map.mp hm
    rw [←observe_rename]
    exact covered a (sub _ (fe ▸ List.mem_toFinset.mpr hmem))
  have bound := projected_bound r run' (gc ▸ observe_proper pG) Reach.start supp
    (L:=L) (gc ▸ prior)
  have massLo : singles.card ≤ mass ((front.map observe).map (restrictRows r)) := by
    simp only [front,List.map_append,mass_append]
    let xs := (singles.toList.map observe).map (restrictRows r)
    have only : ∀ v ∈ xs, Constant v := by
      intro v hv
      obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
      obtain ⟨a,hmem,rfl⟩ := List.mem_map.mp hm
      rw [←observe_rename]
      exact constant _ (Finset.mem_toList.mp hmem)
    have sz := mass_constants xs only
    simp only [xs,List.length_map,Finset.length_toList] at sz
    change singles.card ≤ mass xs + _
    rw [sz]
    omega
  omega



def childTwo (ws : List Sig) (a b : Sig) (d : Nat) (ka kb : Bool) : List Sig :=
  bin d a b :: kept ka a (kept kb b ((ws.erase a).erase b))

theorem erase_fin {l : List Sig} (h : l.Nodup) (a : Sig) : (l.erase a).toFinset = l.toFinset.erase a := by
  ext x
  simp [h.mem_erase_iff]

theorem enum_step {u} {T : Sig} {cap : Nat} {ws : List Sig} (hn : ws.Nodup) (out : T ∉ ws)
    (twoStep : ∀ a ∈ ws, ∀ b ∈ ws, ∀ d, allowed u d → ∀ ka kb, a ≠ b → bin d a b ∉ ws →
      proper (bin d a b) → (childTwo ws a b d ka kb).length ≤ cap →
      Impossible u T (cap-1) (childTwo ws a b d ka kb).toFinset) :
    Impossible u T cap ws.toFinset := by
  classical
  intro k hk h
  generalize he : ws.toFinset = S at h
  induction h using Live.ind with
  | stop hp =>
    have mem : T ∈ ws.toFinset := he.symm ▸ Finset.mem_singleton_self _
    exact out (List.mem_toFinset.mp mem)
  | @binary k U a b d hd ha hb hab hf tail _ =>
    have am : a ∈ ws := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
    have bm : b ∈ ws := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    have fresh : bin d a b ∉ ws := fun h => hf (he ▸ List.mem_toFinset.mpr h)
    have hz := live_proper tail _ (Finset.mem_insert_self _ _)
    let ka := decide (a ∈ U)
    let kb := decide (b ∈ U)
    let rest := (ws.erase a).erase b
    have er : rest.toFinset = (ws.toFinset.erase a).erase b := by
      rw [show rest=(ws.erase a).erase b by rfl,erase_fin (hn.erase _) b,
        erase_fin hn a]
    have ke : (kept ka a (kept kb b rest)).toFinset = U := by
      rw [kept_fin,kept_fin,er,he]
      ext j
      by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> by_cases ja : j=a <;>
        by_cases jb : j=b <;> simp_all [ka,kb]
    have rn : rest.Nodup := (hn.erase _).erase _
    have ar : a ∉ rest := fun h => (hn.not_mem_erase) (List.mem_of_mem_erase h)
    have br : b ∉ rest := (hn.erase a).not_mem_erase
    have nk := kept_nd kb b rest rn br
    have ax : a ∉ kept kb b rest := by cases kb <;> simp [kept,ar,hab]
    have nd : (childTwo ws a b d ka kb).Nodup := by
      refine List.nodup_cons.mpr ⟨?_,kept_nd ka a _ nk ax⟩
      intro h
      exact hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (ke ▸ List.mem_toFinset.mpr h)))
    have eq : (childTwo ws a b d ka kb).toFinset = insert (bin d a b) U := by
      change (bin d a b::kept ka a (kept kb b rest)).toFinset = _
      simp [ke]
    have sc := live_size tail
    have len : (childTwo ws a b d ka kb).length ≤ cap := by
      rw [←List.toFinset_card_of_nodup nd,eq]
      omega
    exact twoStep a am b bm d hd ka kb hab fresh hz len k (by omega) (eq.symm ▸ tail)

def Slice (u : Bool) (raw : List Sig) (T d : Sig) (L : Nat) : Prop :=
  ∃ (f : Row → Row) (roots : List Sig), (∀ r, bit (f r) d = true) ∧
    (∀ a ∈ raw, Available u (roots.map observe) (restrictRows f (observe a))) ∧
    ¬Constant (restrictRows f (observe T)) ∧
    ∀ p bank, Reach u (roots.map observe) p bank → Available u bank (restrictRows f (observe T)) → L ≤ p

def masked (d a : Sig) := a &&& d
def availableB (u : Bool) (d : Sig) (pool : List Sig) (a : Sig) :=
  let m := masked d a
  m == zero || m == d || (pool.map (masked d)).any (fun v => v==m) ||
    (u && (let c := masked d (neg a); (pool.map (masked d)).any (fun v => v==c)))

theorem masked_eq {f : Row → Row} {d a b : Sig} (dom : ∀ r, bit (f r) d = true)
    (eq : masked d a = masked d b) :
    restrictRows f (observe a) = restrictRows f (observe b) := by
  funext r
  have h := congrArg (bit (f r)) eq
  change bit (f r) a = bit (f r) b
  simpa only [bit,masked,BitVec.getLsbD_and,show d.getLsbD (f r).val = true from dom r,
    Bool.and_true] using h

theorem masked_zero {f : Row → Row} {d a : Sig} (dom : ∀ r, bit (f r) d = true)
    (eq : masked d a = zero) : restrictRows f (observe a) = fun _ => false := by
  funext r
  have he := congrArg (bit (f r)) eq
  change bit (f r) a = false
  rw [bit_zero] at he
  simpa only [bit,masked,BitVec.getLsbD_and,show d.getLsbD (f r).val = true from dom r,
    Bool.and_true] using he

theorem masked_one {f : Row → Row} {d a : Sig} (dom : ∀ r, bit (f r) d = true)
    (eq : masked d a = d) : restrictRows f (observe a) = fun _ => true := by
  funext r
  have he := congrArg (bit (f r)) eq
  change bit (f r) a = true
  rw [dom r] at he
  simpa only [bit,masked,BitVec.getLsbD_and,show d.getLsbD (f r).val = true from dom r,
    Bool.and_true] using he

def poolSupply (u : Bool) (f : Row → Row) (bank : List (Wire Row)) (pool : List Sig) :=
  ∀ a ∈ pool, Available u bank (restrictRows f (observe a))

theorem availableB_sound {u} {f : Row → Row} {d a : Sig} {bank pool}
    (dom : ∀ r, bit (f r) d = true) (supplyB : poolSupply u f bank pool)
    (check : availableB u d pool a = true) : Available u bank (restrictRows f (observe a)) := by
  simp only [availableB,List.any_map,Function.comp_def,Bool.or_eq_true,Bool.and_eq_true,beq_iff_eq,List.any_eq_true] at check
  rcases check with ((hz | ho) | ⟨v,hv,he⟩) | ⟨hu,v,hv,he⟩
  · exact Or.inr (Or.inl ⟨false,masked_zero dom hz⟩)
  · exact Or.inr (Or.inl ⟨true,masked_one dom ho⟩)
  · exact masked_eq dom he ▸ supplyB v hv
  · have h := avail_inv hu (masked_eq dom he ▸ supplyB v hv)
    rw [obs_neg] at h
    have e : inv (restrictRows f (inv (observe a))) = restrictRows f (observe a) := by
      funext r
      simp [inv,restrictRows]
    rwa [e] at h

abbrev Choice := Nat × Sig × Sig
def choiceVal (c : Choice) := bin c.1 c.2.1 c.2.2
def allowedB (u : Bool) (d : Nat) := decide (d<2) || (u && decide (d<4))
theorem allowedB_ok {u d} (h : allowedB u d=true) : allowed u d := by
  simpa [allowedB,allowed] using h
def choiceOK (u : Bool) (d : Sig) (pool : List Sig) (c : Choice) :=
  allowedB u c.1 && (availableB u d pool c.2.1 && availableB u d pool c.2.2)

theorem pay_choice {u} {f : Row → Row} {d : Sig} {roots bank pool q}
    (dom : ∀ r, bit (f r) d = true) (hp : Reach u roots q bank) (hs : poolSupply u f bank pool)
    (c : Choice) (valid : choiceOK u d pool c = true) :
    ∃ next, Reach u roots (q+1) next ∧ poolSupply u f next (choiceVal c :: pool) := by
  simp only [choiceOK,Bool.and_eq_true] at valid
  obtain ⟨op,x,y,e,hx,hy,_,_⟩ := comb_prime (allowedB_ok valid.1) (availableB_sound dom hs valid.2.1)
    (availableB_sound dom hs valid.2.2)
  refine ⟨_,Reach.two op hp hx hy,?_⟩
  intro a hm
  rcases List.mem_cons.mp hm with rfl | hm
  · rw [choiceVal,obs_bin,restrict_comb,e]
    exact Or.inl (by simp)
  · exact available_cons _ (hs _ hm)

def makePool (u : Bool) (d : Sig) (pool : List Sig) : List Choice → Option (List Sig)
  | [] => some pool
  | c::cs => if choiceOK u d pool c then makePool u d (choiceVal c::pool) cs else none

theorem makePool_sound {u} {d : Sig} {f : Row → Row} (dom : ∀ r, bit (f r) d = true)
    {roots bank q pool} (hp : Reach u roots q bank) (hs : poolSupply u f bank pool)
    (cs : List Choice) {result} (ok : makePool u d pool cs = some result) :
    ∃ next, Reach u roots (q+cs.length) next ∧ poolSupply u f next result := by
  induction cs generalizing bank q pool with
  | nil => cases ok; exact ⟨_,hp,hs⟩
  | cons c cs ih =>
    simp only [makePool] at ok
    split at ok
    next h =>
      obtain ⟨next,hr,sh⟩ := pay_choice dom hp hs c h
      obtain ⟨out,hr',sh'⟩ := ih hr sh ok
      exact ⟨out,by simpa [Nat.add_assoc,Nat.add_comm 1] using hr',sh'⟩
    next => contradiction

def isMaskedConstant (d a : Sig) := masked d a == zero || masked d a == d
theorem count_constants {d : Sig} {f : Row → Row} (dom : ∀ r, bit (f r) d = true)
    (ws : List Sig) : ws.countP (isMaskedConstant d) ≤ mass ((ws.map observe).map (restrictRows f)) := by
  classical
  induction ws with
  | nil => simp [mass]
  | cons a ws ih =>
    simp only [List.countP_cons,List.map_cons,mass_cons]
    cases h : isMaskedConstant d a
    · simpa using (Nat.le_add_left _ _ |> ih.trans)
    · have hc : Constant (restrictRows f (observe a)) := by
        have hh : masked d a = zero ∨ masked d a = d := by simpa only [isMaskedConstant,Bool.or_eq_true,beq_iff_eq] using h
        rcases hh with hz | ho
        · exact ⟨false,masked_zero dom hz⟩
        · exact ⟨true,masked_one dom ho⟩
      simpa [cost,hc,Nat.add_comm] using Nat.succ_le_succ ih

def poolCut (u : Bool) (d : Sig) (L k p : Nat) (pool ws : List Sig) :=
  decide (k+p < L+ws.countP (isMaskedConstant d)) && ws.all (availableB u d pool)

theorem poolCut_sound {u raw T d L} (slice : Slice u raw T d L) (cs : List Choice)
    {pool ws cap} (built : makePool u d raw cs = some pool)
    (nd : ws.Nodup) (cut : poolCut u d L cap cs.length pool ws = true) :
    Impossible u T cap ws.toFinset := by
  intro k hk h
  obtain ⟨f,roots,dom,base,nc,lo⟩ := slice
  obtain ⟨bank,hr,hs⟩ := makePool_sound dom (Reach.start (roots:=roots.map observe)) base cs built
  simp only [poolCut,Bool.and_eq_true,decide_eq_true_eq] at cut
  obtain ⟨ineq,all⟩ := cut
  have coveredS : supply u bank ((ws.map observe).map (restrictRows f)) := by
    intro v hv
    obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hm
    exact availableB_sound dom hs (List.all_eq_true.mp all a ha)
  have b := projected_bound f (list_run h ws nd rfl) nc hr coveredS lo
  have massLo := count_constants dom ws
  have hu := ineq
  simp only [Nat.zero_add] at b
  omega



abbrev Move := Sig × Sig × Row
def shifted (d r : Row) : Row :=
  if h : r.val < 256-d.val then ⟨d.val+r.val,by omega⟩ else ⟨r.val-(256-d.val),by omega⟩
def backwards (d : Row) : Row := Fin.ofNat 256 (256-d.val)
def rowMove (m : Move) (r : Row) : Row :=
  if bit r m.1 then shifted m.2.2 r else if bit r m.2.1 then shifted (backwards m.2.2) r else r
def mux (m a b : Sig) := (m &&& a) ||| (~~~m &&& b)
def wordMove (m : Move) (a : Sig) :=
  mux m.1 (a.rotateRight m.2.2.val) (mux m.2.1 (a.rotateRight (backwards m.2.2).val) a)

theorem bit_shift (d r : Row) (a : Sig) : bit r (a.rotateRight d.val) = bit (shifted d r) a := by
  unfold bit
  rw [BitVec.getLsbD_rotateRight_of_lt d.isLt]
  by_cases h : r.val < 256-d.val <;> simp [shifted,h,r.isLt]

theorem bool_mux (p x y : Bool) : (p && x || !p && y) = (if p then x else y) := by cases p <;> simp

theorem bit_mux (r : Row) (m a b : Sig) :
    bit r (mux m a b) = if bit r m then bit r a else bit r b := by
  simp only [bit,mux,BitVec.getLsbD_and,BitVec.getLsbD_or,BitVec.getLsbD_not,r.isLt,
    decide_true,Bool.true_and]
  exact bool_mux _ _ _

theorem bit_move (r : Row) (m : Move) (a : Sig) : bit r (wordMove m a) = bit (rowMove m r) a := by
  simp only [wordMove,bit_mux,bit_shift,rowMove]
  cases bit r m.1 <;> cases bit r m.2.1 <;> rfl

def movedRow (ms : List Move) (r : Row) := ms.foldl (fun j m => rowMove m j) r
def movedWord (ms : List Move) (a : Sig) := ms.foldr wordMove a
theorem bit_moved (ms : List Move) (a : Sig) (r : Row) :
    bit r (movedWord ms a) = bit (movedRow ms r) a := by
  induction ms generalizing r with
  | nil => rfl
  | cons m ms ih => exact (bit_move r m _).trans (ih _)
theorem moved_eq_rename (ms : List Move) (a : Sig) : movedWord ms a = rename (movedRow ms) a := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  exact (bit_moved ms a ⟨j,hj⟩).trans (bit_rename _ _ ⟨j,hj⟩).symm

def freeWord (roots : List Sig) (w : Sig) := w==zero || w==one || roots.contains w
theorem freeWord_ok {u roots w} (ok : freeWord roots w = true) :
    Available u (roots.map observe) (observe w) := by
  simp only [freeWord,Bool.or_eq_true,beq_iff_eq,List.contains_eq_mem,decide_eq_true_eq] at ok
  rcases ok with (rfl | rfl) | hm
  · exact Or.inr (Or.inl ⟨false,funext bit_zero⟩)
  · exact Or.inr (Or.inl ⟨true,funext bit_one⟩)
  · exact Or.inl (List.mem_map_of_mem hm)

def checkMap (ms : List Move) (raw : List Sig) (T : Sig) (base : List Sig) (G : Sig) :=
  movedWord ms T == G && raw.all (fun a => freeWord base (movedWord ms a))

theorem map_correct {u ms raw T base G} (ok : checkMap ms raw T base G = true) :
    rename (movedRow ms) T = G ∧
    ∀ a ∈ raw, Available u (base.map observe) (observe (rename (movedRow ms) a)) := by
  simp only [checkMap,Bool.and_eq_true,beq_iff_eq,List.all_eq_true,moved_eq_rename] at ok
  exact ⟨ok.1,fun a ha => freeWord_ok (ok.2 a ha)⟩

theorem slice_correct {u ms raw T base G L d} (ok : checkMap ms raw T base G = true)
    (all : movedWord ms d = one) (properG : proper G) (hL : Lower u base G L) :
    Slice u raw T d L := by
  obtain ⟨eq,supp⟩ := map_correct ok
  have obs : restrictRows (movedRow ms) (observe T) = observe G :=
    (observe_rename _ _).symm.trans (congrArg observe eq)
  refine ⟨movedRow ms,base,?_,?_,?_,?_⟩
  · intro r
    rw [←bit_moved,all,bit_one]
  · intro a ha
    rw [←observe_rename]
    exact supp a ha
  · rw [obs]
    exact observe_proper properG
  · rw [obs]
    exact hL

def witnessB (T : Sig) (roots : List Sig) (a : Sig) (rs : Row × Row) :=
  (bit rs.1 T != bit rs.2 T) &&
  roots.all (fun w => w == a || bit rs.1 w == bit rs.2 w)
theorem witnessB_sound {T roots a rs} (ok : witnessB T roots a rs = true) : Essential T roots a := by
  simp only [witnessB,Bool.and_eq_true,bne_iff_ne,List.all_eq_true,Bool.or_eq_true,beq_iff_eq] at ok
  exact ⟨rs.1,rs.2,ok.1,fun w hw hne => (ok.2 w hw).resolve_left hne⟩

def checkEssential (T : Sig) (raw : List Sig) (xs : List (Sig × Row × Row)) :=
  plainWord T && raw.all plainWord && xs.all (fun a => witnessB T raw a.1 a.2)
theorem essential_ok {T raw xs} (ok : checkEssential T raw xs = true) :
    ∀ a ∈ (xs.map Prod.fst).toFinset, Essential T raw a := by
  simp only [checkEssential,Bool.and_eq_true] at ok
  intro a ha
  obtain ⟨⟨a,r,s⟩,hm,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
  exact witnessB_sound (List.all_eq_true.mp ok.2 _ hm)

theorem essential_plain {T raw xs} (ok : checkEssential T raw xs = true) :
    plainWord T=true ∧ raw.all plainWord=true := by
  simp only [checkEssential,Bool.and_eq_true] at ok
  exact ok.1
theorem lower_count {u raw T} (properT : proper T) (xs : List (Sig × Row × Row))
    (ok : checkEssential T raw xs = true) :
    Lower u raw T ((xs.map Prod.fst).toFinset.card-1) := by
  intro p bank hr hit
  obtain ⟨k,S,hk,run,sub⟩ := reach_live properT (essential_plain ok).1 (essential_plain ok).2 hr hit
  have le : (xs.map Prod.fst).toFinset.card ≤ S.card := by
    apply Finset.card_le_card
    intro a ha
    obtain ⟨r,s,hd,iso⟩ := essential_ok ok a ha
    exact raw_required run raw a sub r s hd iso
  have bound := live_size run
  omega

def checkLift (ms : List Move) (T : Sig) (raw : List Sig) (base : List Sig) (G : Sig)
    (xs : List (Sig × Row × Row)) :=
  checkMap ms raw T base G && checkEssential T raw xs &&
    xs.all (fun a => movedWord ms a.1 == zero || movedWord ms a.1 == one)

theorem lift_ok {u ms T raw base G xs L} (ok : checkLift ms T raw base G xs = true)
    (properT : proper T) (properG : proper G) (low : Lower u base G L) :
    Lower u raw T (L+(xs.map Prod.fst).toFinset.card) := by
  simp only [checkLift,Bool.and_eq_true] at ok
  obtain ⟨eq,supp⟩ := map_correct ok.1.1
  apply lower_slice properT (essential_plain ok.1.2).1 (essential_plain ok.1.2).2 properG _ eq supp _ (essential_ok ok.1.2) _ L low
  intro a ha
  obtain ⟨⟨v,r,s⟩,hm,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
  have hh := List.all_eq_true.mp ok.2 _ hm
  simp only [Bool.or_eq_true,beq_iff_eq,moved_eq_rename] at hh
  rcases hh with h | h
  · rw [h]
    exact ⟨false,funext bit_zero⟩
  · rw [h]
    exact ⟨true,funext bit_one⟩

abbrev Cut := Sig × Nat × List Sig

def cutTest (c : Cut) (k : Nat) (ws : List Sig) : Bool :=
  decide (k < c.2.1 + ws.countP (isMaskedConstant c.1)) &&
    ws.all fun w => masked c.1 w == zero || c.2.2.contains (masked c.1 w)

def CutGood (T : Sig) (c : Cut) : Prop :=
  ∀ k ws, ws.Nodup → cutTest c k ws = true → Impossible true T k ws.toFinset

theorem cut_good {T d raw L} (s : Slice true raw T d L) (cs : List Choice)
    {pool} (hp : makePool true d raw cs = some pool) (afford : cs.length ≤ L) :
    CutGood T (d,L-cs.length,pool.map (masked d)) := by
  intro k ws nd checked
  simp only [cutTest,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true] at checked
  apply poolCut_sound s cs hp nd
  apply Bool.and_eq_true_iff.mpr
  refine ⟨decide_eq_true (by omega),List.all_eq_true.mpr ?_⟩
  intro w hw
  rcases Bool.or_eq_true_iff.mp (checked.2 w hw) with hz | hm
  · simp [availableB,hz]
  · have mem := List.contains_iff_mem.mp hm
    obtain ⟨v,hv,eq⟩ := List.mem_map.mp mem
    have yes : ((pool.map (masked d)).any fun z => z == masked d w) = true :=
      List.any_eq_true.mpr ⟨masked d v,List.mem_map_of_mem hv,beq_iff_eq.mpr eq⟩
    simp [availableB,yes]

def properB (w : Sig) := w != zero && w != one
theorem proper_of (w : Sig) (h : properB w = true) : proper w := by
  simpa only [properB,proper,Bool.and_eq_true,bne_iff_ne] using h

def bothFlags : List Bool := [false,true]
theorem has_flag (b : Bool) : b ∈ bothFlags := by cases b <;> decide

def moves (ws : List Sig) (k : Nat) (a b : Sig) : List (List Sig) :=
  ([0,1,2,3] : List Nat).flatMap fun d =>
    let z := bin d a b
    if properB z && !ws.contains z then
      bothFlags.flatMap fun ka =>
        (bothFlags.map fun kb => childTwo ws a b d ka kb).filter fun v => decide (v.length ≤ k)
    else []

def children (ws : List Sig) (k : Nat) : List (List Sig) :=
  ws.flatMap fun a => ws.flatMap fun b => if a < b then moves ws k a b else []

theorem listed {ws : List Sig} {k a b d ka kb} (ha : a ∈ ws) (hb : b ∈ ws)
    (ab : a < b) (legal : allowed true d) (fresh : bin d a b ∉ ws) (pr : proper (bin d a b))
    (short : (childTwo ws a b d ka kb).length ≤ k) : childTwo ws a b d ka kb ∈ children ws k := by
  apply List.mem_flatMap.mpr
  refine ⟨a,ha,List.mem_flatMap.mpr ⟨b,hb,?_⟩⟩
  rw [if_pos ab]
  have dm : d ∈ ([0,1,2,3] : List Nat) := by
    rcases allowed_four legal with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩ <;> decide
  apply List.mem_flatMap.mpr
  refine ⟨d,dm,?_⟩
  have ready : (properB (bin d a b) && !ws.contains (bin d a b)) = true := by
    simp [properB,pr.1,pr.2,fresh]
  dsimp only
  rw [if_pos ready]
  exact List.mem_flatMap.mpr ⟨ka,has_flag ka,List.mem_filter.mpr
    ⟨List.mem_map_of_mem (f:=fun kb => childTwo ws a b d ka kb) (has_flag kb),decide_eq_true short⟩⟩

theorem swapped {ws : List Sig} {a b d} (h : allowed true d) (ka kb : Bool) :
    (childTwo ws a b d ka kb).Perm (childTwo ws b a (flipOp d) kb ka) := by
  unfold childTwo
  rw [bin_flip h a b,List.erase_comm a b]
  apply List.Perm.cons
  cases ka <;> cases kb <;> simp [kept,List.Perm.swap]

theorem by_children {T k ws} (nd : ws.Nodup) (absent : T ∉ ws)
    (h : ∀ w ∈ children ws k, Impossible true T (k-1) w.toFinset) : Impossible true T k ws.toFinset := by
  apply enum_step nd absent
  intro a ha b hb d leg ka kb ne fresh pr short
  rcases lt_or_gt_of_ne (show a.toNat ≠ b.toNat from fun e => ne (BitVec.eq_of_toNat_eq e)) with ab | ba
  · exact h _ (listed ha hb ab leg fresh pr short)
  · have p := swapped leg (ws:=ws) (a:=a) (b:=b) ka kb
    have e := bin_flip leg a b
    have other := listed hb ha ba (flip_flip leg).1 (e ▸ fresh) (e ▸ pr)
      (ka:=kb) (kb:=ka) (p.length_eq ▸ short)
    have eq : (childTwo ws a b d ka kb).toFinset = (childTwo ws b a (flipOp d) kb ka).toFinset := by
      ext w
      simpa only [List.mem_toFinset] using (p.mem_iff (a:=w))
    rw [eq]
    exact h _ other

def sameWires (ws vs : List Sig) := ws.all vs.contains && vs.all ws.contains
theorem same_wires {ws vs} (ok : sameWires ws vs = true) : ws.toFinset = vs.toFinset := by
  obtain ⟨l,r⟩ := Bool.and_eq_true_iff.mp ok
  ext a
  simp only [List.mem_toFinset]
  exact ⟨fun ha => List.contains_iff_mem.mp (List.all_eq_true.mp l _ ha),
    fun ha => List.contains_iff_mem.mp (List.all_eq_true.mp r _ ha)⟩

abbrev Cuts (T : Sig) := List {c : Cut // CutGood T c}
abbrev Links (T : Sig) (k : Nat) := List {ws : List Sig // Impossible true T k ws.toFinset}

def closeCase (T : Sig) (k : Nat) (cuts : Cuts T) (links : Links T k) (ws : List Sig) (code : Nat) :=
  if code < 65536 then
    let r := Fin.ofNat 256 (code % 256)
    let s := Fin.ofNat 256 (code / 256)
    (bit r T != bit s T) && ws.all (fun w => bit r w == bit s w)
  else if code < 131072 then
    match cuts[code-65536]? with
    | none => false
    | some c => decide ws.Nodup && cutTest c.val k ws
  else
    match links[code-131072]? with
    | none => false
    | some v => sameWires ws v.val

theorem close_ok {T k cuts links ws code} (ok : closeCase T k cuts links ws code = true) :
    Impossible true T k ws.toFinset := by
  unfold closeCase at ok
  split at ok
  · simp only [Bool.and_eq_true,bne_iff_ne,List.all_eq_true,beq_iff_eq] at ok
    intro n _ run
    obtain ⟨w,hw,ne⟩ := live_row_difference run ok.1
    exact ne (ok.2 w (List.mem_toFinset.mp hw))
  · split at ok
    · split at ok
      · contradiction
      · rename_i c _
        obtain ⟨nd,good⟩ := Bool.and_eq_true_iff.mp ok
        exact c.property k ws (of_decide_eq_true nd) good
    · split at ok
      · contradiction
      · rename_i v _
        rw [same_wires ok]
        exact v.property

def checkMoves (T : Sig) (k : Nat) (cuts : Cuts T) (links : Links T k) :
    List (List Sig) → Nat → Bool
  | [],_ => true
  | ws::rest,data => closeCase T k cuts links ws (data % 262144) &&
      checkMoves T k cuts links rest (data / 262144)

theorem moves_ok {T k cuts links vs data} (ok : checkMoves T k cuts links vs data = true) :
    ∀ w ∈ vs, Impossible true T k w.toFinset := by
  induction vs generalizing data with
  | nil => simp
  | cons v vs ih =>
    obtain ⟨closed,tail⟩ := Bool.and_eq_true_iff.mp ok
    intro w hw
    rcases List.mem_cons.mp hw with rfl | hm
    · exact close_ok closed
    · exact ih tail _ hm

def checkNode (T : Sig) (k : Nat) (ws : List Sig) (cuts : Cuts T) (links : Links T (k-1)) (data : Nat) :=
  (decide ws.Nodup && !ws.contains T) && checkMoves T (k-1) cuts links (children ws k) data

theorem node_ok {T k ws} (cuts : Cuts T) (links : Links T (k-1)) (data : Nat)
    (ok : checkNode T k ws cuts links data = true) : Impossible true T k ws.toFinset := by
  obtain ⟨head,tail⟩ := Bool.and_eq_true_iff.mp ok
  obtain ⟨hn,hm⟩ := Bool.and_eq_true_iff.mp head
  exact by_children (of_decide_eq_true hn) (by simpa using hm) (moves_ok tail)

def inputs : List Sig := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc, 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00, 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000, 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000, 0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000, 0xffffffffffffffffffffffffffffffff00000000000000000000000000000000]
def input (i : Nat) := inputs.getD i zero
def selected (m : Nat) := (List.range 8).filter (fun i => m.testBit i)
def roots (m : Nat) := (selected m).map input


def goalAt (m : Nat) : Sig :=
  let x := fun i => if m.testBit i then input i else zero
  (x 0 &&& x 4) ||| (x 1 &&& x 4) ||| (x 0 &&& x 5) ||| (x 2 &&& x 5) ||| (x 3 &&& x 5) ||| (x 0 &&& x 6) ||| (x 1 &&& x 6) ||| (x 2 &&& x 6) ||| (x 3 &&& x 6) ||| (x 1 &&& x 7) ||| (x 2 &&& x 7) ||| (x 4 &&& x 7) ||| (x 5 &&& x 7) ||| (x 6 &&& x 7)


def fixes (q : Nat) : List Move :=
  ((List.range 8).filter fun i => !(q.testBit i)).map fun i =>
    (zero,input i,Fin.ofNat 256 (1 <<< i))

def domain (q : Nat) : Sig :=
  ((List.range 8).filter fun i => !(q.testBit i)).foldl (fun d i => d &&& neg (input i)) one

def tests (m hints : Nat) : List (Sig × Row × Row) :=
  (selected m).map fun i =>
    let r := 1 <<< ((hints >>> (4*i)) % 16)
    (input i,Fin.ofNat 256 r,Fin.ofNat 256 (r ||| (1 <<< i)))

def Claim (m L : Nat) : Prop := Lower true (roots m) (goalAt m) L

def essTest (m hints : Nat) :=
  (properB (goalAt m) && checkEssential (goalAt m) (roots m) (tests m hints)) &&
    ((tests m hints).map Prod.fst == roots m)

theorem fromSearch {m k} (hints : Nat) (checked : essTest m hints = true)
    (no : Impossible true (goalAt m) k (roots m).toFinset) : Claim m (k+1) := by
  simp only [essTest,Bool.and_eq_true,beq_iff_eq] at checked
  have ok := checked.1.2
  apply lower_impossible (proper_of _ checked.1.1) (essential_plain ok).1 (essential_plain ok).2 _ no
  intro w hw
  apply essential_ok ok w
  rw [checked.2]
  exact List.mem_toFinset.mpr hw

def liftTest (m q a b e hints : Nat) :=
  ((checkLift (fixes q) (goalAt m) (roots m) (roots q) (goalAt q) (tests e hints) &&
    properB (goalAt m)) && properB (goalAt q)) &&
      decide (b ≤ a+((tests e hints).map Prod.fst).toFinset.card)

theorem fromLift {m q a} (b e hints : Nat) (lower : Claim q a)
    (ok : liftTest m q a b e hints = true) : Claim m b := by
  simp only [liftTest,Bool.and_eq_true,decide_eq_true_eq] at ok
  have lb := lift_ok ok.1.1.1 (proper_of _ ok.1.1.2) (proper_of _ ok.1.2) lower
  exact fun p bank hr ha => ok.2.trans (lb p bank hr ha)

def poolFor (q : Nat) (extra : Option Choice) : List Sig :=
  match extra with
  | none => roots q
  | some c => choiceVal c :: roots q

def ruleTest (m q L : Nat) (e : Option Choice) : Bool :=
  (((checkMap (fixes q) (roots q) (goalAt m) (roots q) (goalAt q) &&
    (movedWord (fixes q) (domain q) == one)) && properB (goalAt q)) &&
    (makePool true (domain q) (roots q) e.toList == some (poolFor q e))) &&
    decide (e.toList.length ≤ L)

def ruleFor (m : Nat) {q L} (lo : Claim q L) (e : Option Choice)
    (ok : ruleTest m q L e = true) : {c : Cut // CutGood (goalAt m) c} := by
  refine ⟨(domain q,L-e.toList.length,(poolFor q e).map (masked (domain q))),?_⟩
  simp only [ruleTest,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] at ok
  exact cut_good (slice_correct ok.1.1.1.1 ok.1.1.1.2 (proper_of _ ok.1.1.2) lo)
    e.toList ok.1.2 ok.2




def cuts146 : Cuts (goalAt 146) := []

def state146_0 : List Sig := roots 146
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude146_0 : Impossible true (goalAt 146) 3 state146_0.toFinset :=
  node_ok cuts146 [] 0x24040120224040820224200908024040908024200820204808120220808121004840901020a00828020808828020a00901004840121004808828020a00908004840908004808121004840908020a008280 (by decide +kernel)

theorem lower146 : Claim 146 4 :=
  fromSearch 268501056 (by decide +kernel) exclude146_0

theorem lower178 : Claim 178 5 :=
  fromLift 5 32 275841088 lower146 (by decide +kernel)

def cuts164 : Cuts (goalAt 164) := []

def state164_0 : List Sig := roots 164
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude164_0 : Impossible true (goalAt 164) 3 state164_0.toFinset :=
  node_ok cuts164 [] 0x28080240428080840428200a08028080a08028200840409010240421010242009080a02021200848021010848021200a02009080242009010848021200a08009080a08009010242009080a080212008480 (by decide +kernel)

theorem lower164 : Claim 164 4 :=
  fromSearch 538969344 (by decide +kernel) exclude164_0

theorem lower166 : Claim 166 5 :=
  fromLift 5 2 270534000 lower164 (by decide +kernel)

theorem lower150 : Claim 150 5 :=
  fromLift 5 4 268502848 lower146 (by decide +kernel)

theorem lower180 : Claim 180 5 :=
  fromLift 5 16 539428096 lower164 (by decide +kernel)

def rule182_0 : {c : Cut // CutGood (goalAt 182) c} :=
  ruleFor 182 lower178 none (by decide +kernel)

def rule182_1 : {c : Cut // CutGood (goalAt 182) c} :=
  ruleFor 182 lower166 none (by decide +kernel)

def rule182_2 : {c : Cut // CutGood (goalAt 182) c} :=
  ruleFor 182 lower150 none (by decide +kernel)

def rule182_3 : {c : Cut // CutGood (goalAt 182) c} :=
  ruleFor 182 lower180 none (by decide +kernel)

def cuts182 : Cuts (goalAt 182) := [rule182_0,rule182_1,rule182_2,rule182_3]

def state182_0 : List Sig := roots 182
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude182_0 : Impossible true (goalAt 182) 6 state182_0.toFinset :=
  node_ok cuts182 [] 0x40008b0300d050b03040008941428200a08040008b03028200a0804000894140d050903040004b0300c888b03040004a22224200908040004b03024200908040004a2220c888a03040004341424200908040004a0800c888a0804000434140c888322240004a0802420090804000094140d0c0343040000b03021200848040000941421200848040000b0300d0c0343040000341421200848040000a0800d0c0a0804000034140d0c0343040000a0802120084804000016062120084804000090800d0c090804000016060d0c034304000090802120084804000ca2220c8c032304000cb03020a0082804000ca22220a0082804000cb0300c8c0323040008260620a00828040008a0800c8c0a0804000826060c8c0323040008a08020a00828040004322220a0082804000490800c8c090804000432220c8c0323040004908020a00828040000262220a00828040000848005850848040000262205850242240000848020a008280 (by decide +kernel)

theorem lower182 : Claim 182 7 :=
  fromSearch 270599488 (by decide +kernel) exclude182_0

theorem lower181 : Claim 181 6 :=
  fromLift 6 1 536872196 lower180 (by decide +kernel)

theorem lower179 : Claim 179 6 :=
  fromLift 6 1 268435524 lower178 (by decide +kernel)

theorem lower165 : Claim 165 5 :=
  fromLift 5 1 536872197 lower164 (by decide +kernel)

theorem lower167 : Claim 167 6 :=
  fromLift 6 1 268436853 lower166 (by decide +kernel)

theorem lower151 : Claim 151 6 :=
  fromLift 6 1 268437316 lower150 (by decide +kernel)

theorem lower147 : Claim 147 5 :=
  fromLift 5 1 268435524 lower146 (by decide +kernel)

def cuts53 : Cuts (goalAt 53) := []

def state53_0 : List Sig := roots 53
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude53_0 : Impossible true (goalAt 53) 3 state53_0.toFinset :=
  node_ok cuts53 [] 0xd05025050905024140d05034300d0c021050908034300d0c024300545031300c4c015140848031300c4c021300c4c03430054503130 (by decide +kernel)

theorem lower53 : Claim 53 4 :=
  fromSearch 1284 (by decide +kernel) exclude53_0

theorem lower55 : Claim 55 5 :=
  fromLift 5 2 1348 lower53 (by decide +kernel)

def cuts51 : Cuts (goalAt 51) := []

def state51_0 : List Sig := roots 51
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude51_0 : Impossible true (goalAt 51) 3 state51_0.toFinset :=
  node_ok cuts51 [] 0x4c0c32220c88812220484032300c8c012300c88832300c8c011030444031300c4c0113008c8831300c4c023220c4c0323008c883130 (by decide +kernel)

theorem lower51 : Claim 51 4 :=
  fromSearch 68 (by decide +kernel) exclude51_0

def cuts149 : Cuts (goalAt 149) := []

def state149_0 : List Sig := roots 149
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude149_0 : Impossible true (goalAt 149) 3 state149_0.toFinset :=
  node_ok cuts149 [] 0x250509181246048414250508581216049014216049181044148581054509414210141514246049080242049081216048480212048481 (by decide +kernel)

theorem lower149 : Claim 149 4 :=
  fromSearch 536872708 (by decide +kernel) exclude149_0

def cuts163 : Cuts (goalAt 163) := []

def state163_0 : List Sig := roots 163
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude163_0 : Impossible true (goalAt 163) 3 state163_0.toFinset :=
  node_ok cuts163 [] 0x28888a18128604822228888838120e04a02220e04a1810840c838108c88a2222080c232228604a08028204a08120e04828020a048281 (by decide +kernel)

theorem lower163 : Claim 163 4 :=
  fromSearch 268435573 (by decide +kernel) exclude163_0

def rule183_0 : {c : Cut // CutGood (goalAt 183) c} :=
  ruleFor 183 lower182 none (by decide +kernel)

def rule183_1 : {c : Cut // CutGood (goalAt 183) c} :=
  ruleFor 183 lower181 none (by decide +kernel)

def rule183_2 : {c : Cut // CutGood (goalAt 183) c} :=
  ruleFor 183 lower179 none (by decide +kernel)

def rule183_3 : {c : Cut // CutGood (goalAt 183) c} :=
  ruleFor 183 lower165 none (by decide +kernel)

def rule183_4 : {c : Cut // CutGood (goalAt 183) c} :=
  ruleFor 183 lower167 none (by decide +kernel)

def rule183_5 : {c : Cut // CutGood (goalAt 183) c} :=
  ruleFor 183 lower151 none (by decide +kernel)

def rule183_6 : {c : Cut // CutGood (goalAt 183) c} :=
  ruleFor 183 lower147 none (by decide +kernel)

def rule183_7 : {c : Cut // CutGood (goalAt 183) c} :=
  ruleFor 183 lower180 none (by decide +kernel)

def rule183_8 : {c : Cut // CutGood (goalAt 183) c} :=
  ruleFor 183 lower55 none (by decide +kernel)

def rule183_9 : {c : Cut // CutGood (goalAt 183) c} :=
  ruleFor 183 lower53 none (by decide +kernel)

def rule183_10 : {c : Cut // CutGood (goalAt 183) c} :=
  ruleFor 183 lower178 none (by decide +kernel)

def rule183_11 : {c : Cut // CutGood (goalAt 183) c} :=
  ruleFor 183 lower166 none (by decide +kernel)

def rule183_12 : {c : Cut // CutGood (goalAt 183) c} :=
  ruleFor 183 lower164 none (by decide +kernel)

def rule183_13 : {c : Cut // CutGood (goalAt 183) c} :=
  ruleFor 183 lower150 none (by decide +kernel)

def rule183_14 : {c : Cut // CutGood (goalAt 183) c} :=
  ruleFor 183 lower51 none (by decide +kernel)

def rule183_15 : {c : Cut // CutGood (goalAt 183) c} :=
  ruleFor 183 lower146 none (by decide +kernel)

def rule183_16 : {c : Cut // CutGood (goalAt 183) c} :=
  ruleFor 183 lower149 none (by decide +kernel)

def rule183_17 : {c : Cut // CutGood (goalAt 183) c} :=
  ruleFor 183 lower163 none (by decide +kernel)

def cuts183 : Cuts (goalAt 183) := [rule183_0,rule183_1,rule183_2,rule183_3,rule183_4,rule183_5,rule183_6,rule183_7,rule183_8,rule183_9,rule183_10,rule183_11,rule183_12,rule183_13,rule183_14,rule183_15,rule183_16,rule183_17]

def state183_0 : List Sig := [0xffff0000ffff0000ffff0000ffff0000aaaa0000aaaa0000aaaa0000aaaa,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000,input 1,input 2,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_0 : Impossible true (goalAt 183) 5 state183_0.toFinset :=
  node_ok cuts183 [] 0x322228204a08108600313028204a081240c08481282043430212042622212048481090c034302120484810c4c0828128204323020a04828121204242220a04322220a0482812101c323020a0482810c4c033220c4c031300c88890810d050a0812420484810d0c084812420482810c8c082812420486072420490810c888a030 (by decide +kernel)

def state183_1 : List Sig := [0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 5,0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_1 : Impossible true (goalAt 183) 5 state183_1.toFinset :=
  node_ok cuts183 [] 0x34302120484810c4c02622212048481090c084810d0c0343021204848124204343021204828121204242220a04323020a0482810c4c0322220a0482812101c82810c8c0323020a04828124204323020a0423220c4c0313008c883130054503130240c032220d050322209050a0810c4c090812420484140c8889081242048607 (by decide +kernel)

def state183_2 : List Sig := [0x3333333333333333333333333333333333330000333300003333000033330000,0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000,input 4,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 2,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_2 : Impossible true (goalAt 183) 5 state183_2.toFinset :=
  node_ok cuts183 [] 0xc4c0a0812820490300941ca08128204250721204a0810d0c084810d0c084812120431302120490810d0c0848109088848121204242208c8831300c4c0232224204a0810d05090810c4c0908124204a0300c88882810c8c0a08120a04828109088848120a04313020a0482810c8c082810c8c0908120a048407 (by decide +kernel)

def state183_3 : List Sig := [0xfffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0,input 2,0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 1,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_3 : Impossible true (goalAt 183) 5 state183_3.toFinset :=
  node_ok cuts183 [] 0x313028204a081240c0270728204a08108600828128204323020a04323020a0482810c4c0170720a0482810541c82810d0c0161420a04828124204323020a0423220c4c0313008c8834142820434302820434300c4c015140c4c017070d0c03430090c0848124204a0810d05090810c4c0908124204a0300c8889081242048203 (by decide +kernel)

def state183_4 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffff0000ffffffffffff0000,input 5,input 4,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_4 : Impossible true (goalAt 183) 5 state183_4.toFinset :=
  node_ok cuts183 [] 0xd0c084812120431302120490810d0c0848121204a0810d0c084812181c848121204820720a0484810908882810c8c0828120a04313020a0490810c8c0828120a04a0810c8c082812181c828120a0484072181c31300c4c100000c4c0908124204a03024204a0810c888908105c1c313028204a081240c02707 (by decide +kernel)

def state183_5 : List Sig := [0xffffffff00000000ffffffff00000000ffff000000000000ffff0000,input 5,input 4,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_5 : Impossible true (goalAt 183) 5 state183_5.toFinset :=
  node_ok cuts183 [] 0x34302120484810c4c084812420434302120484810d0c0343021204828121204242220a04323020a0482810c4c0828124204323020a0482810c8c0323020a043130242049081280c090810c88832222420431300545031300545084810d0c084810d0c082810c8c082810c8c015140c4c015140c4c090810c88890810c888a081 (by decide +kernel)

def state183_6 : List Sig := [0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000,input 4,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 1,input 2,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_6 : Impossible true (goalAt 183) 6 state183_6.toFinset :=
  node_ok cuts183 [⟨state183_0,exclude183_0⟩,⟨state183_1,exclude183_1⟩,⟨state183_2,exclude183_2⟩,⟨state183_3,exclude183_3⟩,⟨state183_4,exclude183_4⟩,⟨state183_5,exclude183_5⟩] 0x31300d050313005450a08128204313028204a081054503414240c2000509c1c27072181ca08128206000428204a0812181c27070860034142120484812820434302820434140d0c034302820484812120415140d0c034300c4c084812120415142120484810c4c034300c4c1000b2120484812420434302420600030d0c034302420484812120486070988826222080c84812120486072120484812080c262209888270720a0482812820432302820427070c8c0323028204828120a04262220a04828121204161421204262205850242221204828120a0423220c8c032300c4c0828120a04232220a0482810c4c032300c4c1000b20a04828124204323024205000c0c8c0323024204828120a04860780008860721014828120a04860720a04828121015000c2101c860708c8823224000031300c4c086070c4c0313040000232208c88341424204908128205000b28204341480004341428204908124204313080000313008c88908124204313024204908108c89000b280c10008400203222 (by decide +kernel)

def state183_7 : List Sig := [0xffff0000ffffffffffff0000ffffffffffff0000ffff0000ffff0000ffff0000,input 4,input 5,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_7 : Impossible true (goalAt 183) 5 state183_7.toFinset :=
  node_ok cuts183 [] 0x34302120484810c4c084810d0c0343021204848124204343021204262221204848109888828121204242220a04323020a0482810c4c082810c8c0323020a04828124204323020a04860720a0482812101c3130054503130240c0313024204908108c8890812c20434142420432220c4c023220c4c023220d050270728204a081 (by decide +kernel)

def state183_8 : List Sig := [0xffffffff00000000ffffffff00000000000000000000000000000000,input 5,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 1,input 2,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_8 : Impossible true (goalAt 183) 6 state183_8.toFinset :=
  node_ok cuts183 [⟨state183_7,exclude183_7⟩] 0xc4c032220c4c023222420490810c4c090812420423220c888a0300d05090812420427070c88832220d05032220c888270724204908105c1c84812120490810d0c0908105c1c34300d0c090812120484810545034300d0c031302120484810545084812120431300d0c031300d05084812120423030d0c034300d05034300d0c023032120484810c888828120a0490810c8c090810c88832300c8c0908120a04828109888828120a04848105850848109888161409088848120a04828108c8832300c8c0313020a04828108c88828120a0431300c8c0313009c1c828120a0434140c8c0323009c1c32300c8c0341420a0482810c4c034140c4c0151409c1c15140c4c027070c4c015140d05015142420486072420432224002032222420600002420432222181c32222120482032120434302181c34302120486072120434302080c343020a04840520a0432302181c323020a04860720a04323021014323040021000d25051000840034a081 (by decide +kernel)

def state183_9 : List Sig := [0xffffffff00000000ffffffff00000000aaaaaaaa00000000aaaaaaaa,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 1,input 2,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_9 : Impossible true (goalAt 183) 5 state183_9.toFinset :=
  node_ok cuts183 [] 0x3414242049081090503130242049081280c084812420434302120434142120484812081c34302120484810c4c0828124204323020a04828121204242220a04161420a04828105850323020a0482810c4c035140c4c031300d05090810c88890812820484810d0c084812820482810c8c0828128204860728204a0810d0509030 (by decide +kernel)

def state183_10 : List Sig := [0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc,input 1,0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 2,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_10 : Impossible true (goalAt 183) 5 state183_10.toFinset :=
  node_ok cuts183 [] 0x3130242049081280c017072420490810488890812820432222420484812420434302120434302120484810c4c0270721204848108c1c84812820434302120415140c4c031300545032222420432302420432302120424222120432300c4c023220c4c027070c8c03230048c082810c4c0a0812820490300d050a081282048405 (by decide +kernel)

def state183_11 : List Sig := [0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000000000f0f0f0f00000000,0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 5,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 1,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_11 : Impossible true (goalAt 183) 5 state183_11.toFinset :=
  node_ok cuts183 [] 0xc4c0908124204a03024204a0810c888908104c1c908124204130720a0490810c8c082810c8c0828120a04313020a04a0810c8c0828105850828120a0416140545031300c4c015140c4c0a0812820490300d05084810d0c090812120482810908882812120431302120484810d0c084810d0c0a081212048207 (by decide +kernel)

def state183_12 : List Sig := [0xffff0000ffff0000ffff0000ffff0000ffff000000000000ffff00000000,input 4,input 5,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_12 : Impossible true (goalAt 183) 5 state183_12.toFinset :=
  node_ok cuts183 [] 0x34302120484810c4c084812820434302120484810d0c0343021204828121204242220a04323020a0482810c4c0828128204323020a0482810c8c0323020a04313028204a081240c0313008c88313008c8834142820434142820484810d0c084810d0c082810c8c082810c8c023220c4c023220c4c0a0810d050a0810d0509081 (by decide +kernel)

def state183_13 : List Sig := [0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 4,0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_13 : Impossible true (goalAt 183) 5 state183_13.toFinset :=
  node_ok cuts183 [] 0x34302120484810c4c034142120484812081c84810d0c0343021204848128204343021204828121204242220a04323020a0482810c4c0161420a0482810585082810c8c0323020a04828128204323020a0415140c4c0313005450313008c883130280c034140c88832220905090810c4c0a0812820482220d050a081282048607 (by decide +kernel)

def state183_14 : List Sig := [0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 5,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 1,input 2,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_14 : Impossible true (goalAt 183) 6 state183_14.toFinset :=
  node_ok cuts183 [⟨state183_4,exclude183_4⟩,⟨state183_9,exclude183_9⟩,⟨state183_10,exclude183_10⟩,⟨state183_11,exclude183_11⟩,⟨state183_12,exclude183_12⟩,⟨state183_13,exclude183_13⟩] 0x31300c888313008c88908124204313024204908108c883222280c1000d2420490812820432222820600050c888322228204908124206000405c1c17072181c90812420600002420490812181c17070460017072120484812420434302420417070d0c034302420484812120415140d0c034300c4c084812120415142120484810c4c034300c4c1000d21204848128204343028205000f0d0c034302820484812120486078000c86072080c84812120486072120484812080d000f2081c322220a0482812420432302420432220c8c0323024204828120a04262220a04828121204161421204262205850242221204828120a0423220c8c032300c4c0828120a04232220a0482810c4c032300c4c1000d20a0482812820432302820600020c8c0323028204828120a04860705850161421014828120a04860720a0482812101416140585086070545015144000031300c4c086070c4c0313040000151405450313080004313005450a08128204313028204a08105451000d240c10008400203414 (by decide +kernel)

def state183_15 : List Sig := [0xffffffff0000ffffffffffff0000ffffffffffff00000000ffffffff00000000,input 5,input 4,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_15 : Impossible true (goalAt 183) 5 state183_15.toFinset :=
  node_ok cuts183 [] 0x34302120484810c4c084810d0c034302120484812820434302120486072120484812081c828121204242220a04323020a0482810c4c082810c8c0323020a04828128204323020a04161420a04828105850313008c883130280c0b0812820432222820417070c888908124204313028204a0812088834140c4c015140c4c01514 (by decide +kernel)

def state183_16 : List Sig := [0xffff0000ffff0000ffff0000ffff00000000000000000000000000000000,input 4,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 1,input 2,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_16 : Impossible true (goalAt 183) 6 state183_16.toFinset :=
  node_ok cuts183 [⟨state183_15,exclude183_15⟩] 0xc4c034140c4c0151428204a0810c4c0a0812820415140d05090300d050848121204a0810d0c0a0810d05034300d0c0a0812120484810545034300d0c031302120484810545084812120431300d0c0313005c1c84812120432220d0c0343005c1c34300d0c0322221204848109c1c828120a04a0810c8c0a08109c1c32300c8c0a08120a04828109888828120a04848105850848109888161409088848120a04828108c8832300c8c0313020a04828108c88828120a0431300c8c031300c888828120a0415050c8c032300c88832300c8c0150520a0482810d05017070d050a0810c888a0810d05032220c888a08105c1ca0810c4c032220c4c0232205c1c23220c4c017070c4c023220c88823222820486072820434144002034142820600002820434142181c21802120482032120434302181c34302120486072120434302080c343020a04840520a0432302181c323020a04860720a04323021014323040021000b2888900084002c9081 (by decide +kernel)

def state183_17 : List Sig := [0xffffffff00000000ffffffff00000000fafafafa00000000fafafafa,input 2,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 7,input 1,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_17 : Impossible true (goalAt 183) 5 state183_17.toFinset :=
  node_ok cuts183 [] 0x32222420490810c888313024204908108c88828124204323020a04323020a0482810c8c0323020a0482810c4c0828121204242220a04b0302120490810d0c084810d0c084812120434300d0c0848121204313024204322224204a08120a04323020a04a08108600a08128204341405450a08128204313021204343021204a081 (by decide +kernel)

def state183_18 : List Sig := [0xfffffffffffffffffffffffffffffffffafafafafafafafafafafafafafafafa,input 2,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 7,input 1,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_18 : Impossible true (goalAt 183) 6 state183_18.toFinset :=
  node_ok cuts183 [⟨state183_17,exclude183_17⟩] 0x341428204a08108600341428204a08105452000028204a0814003490812820432222420432222420490810c88832222420490810c88832222420490810c888828128204323020a04828124204323020a04323020a0482810c8c0323020a0482810c8c0828121204161420a04323020a0482810c8c0941440028313021204a0810d050848121204908104c1c84812181c8481212048207054508481044503430 (by decide +kernel)

def state183_19 : List Sig := [0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,input 2,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 7,input 1,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_19 : Impossible true (goalAt 183) 6 state183_19.toFinset :=
  node_ok cuts183 [] 0xd050a0812820421800d050a08128204151424204a0810c88890810c88890812420432220c888908124204322220a04a0810c8c0828120a0490810c8c082810c8c0828120a0432300c8c0828120a04323020a0434300908882812505034142820434302820426222420434302420434302080c86070d0c0353005450343028204341428204341424204322224204322220a04323020a0432302080c86072080c86070c4c08481 (by decide +kernel)

def state183_20 : List Sig := [0xfffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0,input 2,input 4,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 7,input 1,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_20 : Impossible true (goalAt 183) 6 state183_20.toFinset :=
  node_ok cuts183 [⟨state183_3,exclude183_3⟩] 0xd050a0812820421800c4c0a08128204151420a04a0810c8c082810c8c0828120a0432300c8c0828120a04313020a0432300c8c0828120a04343005850828120a0432300c8c082812c0c034142820424142820417072181e000005c1c313008c88313008c8890810d050a0810d0c0a0810d0c082032181c34300d0c0313005450313005c1c3430090c084810d050a0810d050a0812181c82032181c82030c4c023220c4c02322 (by decide +kernel)

def state183_21 : List Sig := [0x3333333333333333333333333333333333332222333322223333222233332222,input 4,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 7,input 2,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_21 : Impossible true (goalAt 183) 5 state183_21.toFinset :=
  node_ok cuts183 [] 0x341428204a08108600313028204a0810545084812820434302120434302120484810d0c034302120484810c4c0848124204343021204b03024204a0810c88890810c88890812420432220c4c0908124204232220a04323028204828120a0424222120482810c8c0828120a0432300c4c0828120a04323020a043230242048281 (by decide +kernel)

def state183_22 : List Sig := [0xffffffffffffffffffffffffffffffffffffaaaaffffaaaaffffaaaaffffaaaa,input 4,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 7,input 1,input 2,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_22 : Impossible true (goalAt 183) 6 state183_22.toFinset :=
  node_ok cuts183 [⟨state183_21,exclude183_21⟩] 0x341428204a08108600313028204a08105450260628204a0810981884812820434302120434302120484810d0c034302120484810c4c0848124204343021204262221204848109888828128204323020a04828121204242220a04323020a0482810c8c0323020a0482810c4c0828124204323020a06000020a0482814001cb0304002c232224204a0810d050908105c1c90812420411800c4c09081084c03222 (by decide +kernel)

def state183_23 : List Sig := [0xffff0000ffff0000ffff0000ffff0000aaaa0000aaaa0000aaaa0000aaaa,input 4,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 7,input 1,input 2,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_23 : Impossible true (goalAt 183) 6 state183_23.toFinset :=
  node_ok cuts183 [⟨state183_0,exclude183_0⟩] 0xd050a0812820421800c4c0a08128204151421204a0810d0c084810d0c084812120434300d0c084812120431302120434300d0c0848120a04a0810c8c0828120a0484810908882810c8c0828120a0432300c8c0828120a04313020a0432300c8c082812c0c034142820432222820432222181e00000c88833220c4c0322228204341428204341421204343021204343020a04323020a0432302181d00002181d000808c889081 (by decide +kernel)

def state183_24 : List Sig := [0xffff0000ffff0000ffff0000ffff0000eeee0000eeee0000eeee0000eeee,input 1,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 7,input 2,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_24 : Impossible true (goalAt 183) 5 state183_24.toFinset :=
  node_ok cuts183 [] 0x241428204a08108600313028204a0810545084812820434302120434302120484810d0c034302120484810c4c0b03020a04a0810c8c0828120a0484810988882810c8c0828120a0432300c8c0828120a0431302420432222820490812120434302120490810c888908124204322208c88908124204313020a04323020a049081 (by decide +kernel)

def state183_25 : List Sig := [0xffffffffffffffffffffffffffffffffeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,input 1,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 7,input 2,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_25 : Impossible true (goalAt 183) 6 state183_25.toFinset :=
  node_ok cuts183 [⟨state183_24,exclude183_24⟩] 0x341428204a08108600232228204a0810d050341428204a0810d05090812820432222420432222420490810c888322224204908108c8a00002420490814002c84812820434302120484812420434302120434302120484810d0c034302120484810d0c034302120484810d0c0a2224001c313020a04a0810941c828120a0490810c888828120a0484810988882812181c828120a04840708c888281084883230 (by decide +kernel)

def state183_26 : List Sig := [0x3333333333333333333333333333333333330000333300003333000033330000,input 4,input 7,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 2,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_26 : Impossible true (goalAt 183) 5 state183_26.toFinset :=
  node_ok cuts183 [] 0x313028204a08105450341428204a0810d05084812820434302120434302120484810c4c034302120484810d0c0848124204343021204b03024204a0810c88890810c4c090812420423220c888908124204322220a04323028204828120a0424222120482810c4c0828120a0432300c8c0828120a04323020a043230242048281 (by decide +kernel)

def state183_27 : List Sig := [0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000,input 4,input 7,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 1,input 2,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_27 : Impossible true (goalAt 183) 6 state183_27.toFinset :=
  node_ok cuts183 [⟨state183_26,exclude183_26⟩] 0xc4c0a0812820415140d050a08128204341409c1ca08128204270721204a0810d0c084810d0c084812120431300d0c084812120434302120490810d0c0848109888848121204262220a04a0810c8c0828120a0484810908882810c8c0828120a0431300c8c0828120a04323020a0490810c8c0828180000828120a05000708c8831300c4c023222c0c0860724204a0810d05090810c4c09081242042322400209081046003222 (by decide +kernel)

def state183_28 : List Sig := [0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc,input 1,input 5,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 7,input 2,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_28 : Impossible true (goalAt 183) 6 state183_28.toFinset :=
  node_ok cuts183 [⟨state183_10,exclude183_10⟩] 0xc88890812420432220c4c090812420423222420432220c88890812420432220c88890812120490810d0c084810d0c084812120434300d0c084812120431302120434300d0c084812120434300d0c084812c0c027072181e000009c1c313005450313005450a0810c88890810c8c090810c8c084810908884810c8c084052181c32300c8c0313008c88313009c1c3230048c082812181c84052181c84050c4c015140c4c01514 (by decide +kernel)

def state183_29 : List Sig := [0xffffffffffff0000ffffffffffff0000aaaaaaaaaaaa0000aaaaaaaaaaaa0000,input 4,input 5,input 7,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_29 : Impossible true (goalAt 183) 5 state183_29.toFinset :=
  node_ok cuts183 [] 0xd0c084812120434302120434300d0c084812120434300d0c0848121204313005450848120a0484810908882810c8c0828120a04323020a0432300c8c0828120a0432300c8c0828120a04313008c8882810d050860720888822228204a0810c4c015140c88886072105032220d05032220c88824142420490810c4c023220c4c0b030400003130 (by decide +kernel)

def state183_30 : List Sig := [0x55555555555500005555555555550000,input 4,input 5,input 7,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_30 : Impossible true (goalAt 183) 5 state183_30.toFinset :=
  node_ok cuts183 [] 0x34302120484810d0c0848128204343021204848124204343021204828121204242220a04323020a0482810c8c0828128204323020a04828124204323020a04341428204a0810860032222420490810c888908128204322224204313021204343021204313020a04323020a04b03005450a0810c4c0a08108c8890810c4c09081 (by decide +kernel)

def state183_31 : List Sig := [0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 4,input 5,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 7,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_31 : Impossible true (goalAt 183) 6 state183_31.toFinset :=
  node_ok cuts183 [⟨state183_4,exclude183_4⟩,⟨state183_1,exclude183_1⟩,⟨state183_13,exclude183_13⟩,⟨state183_29,exclude183_29⟩,⟨state183_30,exclude183_30⟩] 0xd0c084812120434300d0c084812120431302120434300d0c084812120434300d0c084812120434300d0c0848120a0484810908882810c8c0828120a0432300c8c0828120a04313020a0432300c8c0828120a0432300c8c0828120a0432300c8c082812c0c034142181e00020d050313005450313005450a0810c88886078000432220c4c023220c4c023220d05032220905090814002086078000086070c4c200040c4c20003 (by decide +kernel)

def state183_32 : List Sig := [0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0a0a0a0a0f0f0f0f0a0a0a0a,input 5,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 7,input 1,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_32 : Impossible true (goalAt 183) 5 state183_32.toFinset :=
  node_ok cuts183 [] 0x32222420490810c888313024204908108c88908128204322224204828124204323020a04323020a0482810c8c0323020a0482810c4c0828128204323020a04b0300d050a0812820421800c4c0a08128204151421204343024204848120a04242220a0484810d0c084812120434300c4c08481212043430212043430282048481 (by decide +kernel)

def state183_33 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffaaaaaaaaffffffffaaaaaaaa,input 5,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 7,input 1,input 2,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_33 : Impossible true (goalAt 183) 6 state183_33.toFinset :=
  node_ok cuts183 [⟨state183_32,exclude183_32⟩] 0x32222420490810c888313024204908108c8890812820432222420416062420490810581884812420434302120434302120484810d0c034302120484810c4c0848128204343021206000021204848140028828124204323020a04828121204242220a04323020a0482810c8c0323020a0482810c4c0828128204323020a04161420a04828105850b03040034151409c1ca0812820421800c4c0a081044c03414 (by decide +kernel)

def state183_34 : List Sig := [0xffffffff00000000ffffffff00000000aaaaaaaa00000000aaaaaaaa,input 5,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 7,input 1,input 2,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_34 : Impossible true (goalAt 183) 6 state183_34.toFinset :=
  node_ok cuts183 [⟨state183_9,exclude183_9⟩] 0xc88890812420432220c4c090812420423222420432220c88890812120490810d0c084810d0c084812120434300d0c084812120431302120434300d0c0848120a0490810c8c0828120a0484810908882810c8c0828120a0432300c8c0828120a04313020a0432300c8c082812c0c034142181e00000d05035140c4c0341424204322224204322221204343021204343020a04323020a0432302181d00002181d000805450a081 (by decide +kernel)

def state183_35 : List Sig := [0xfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfc,input 1,input 2,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_35 : Impossible true (goalAt 183) 5 state183_35.toFinset :=
  node_ok cuts183 [] 0xc4c0a08128204903024204a0810c88890810c4c0908124204a03021204a08109888848121204908104c1c84812d0c0848121204313020a04a0810941c828120a0490810c88882812c8c0828120a04313020a0484810908882810d050a0810d050a0810c88890810c888908108c88313008c8831300d0c084810988884810c8c08281058508281 (by decide +kernel)

def state183_36 : List Sig := [0xfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfc,input 1,input 2,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 7,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_36 : Impossible true (goalAt 183) 6 state183_36.toFinset :=
  node_ok cuts183 [⟨state183_35,exclude183_35⟩] 0xd050a0812820421800c4c0a08128204151424204a0810c88890810c88890812420432220c4c090812420423222c0c034142820426222820426222420413072420426222080c82070988826220c4c015140c4c0848105850a0810941ca0810c88890810c88890810585084052101c161408c88313008c8831300988816140908882810d050a0810d050a0810c88890810c88890812181e00002181d000808c88313008c883130 (by decide +kernel)

def state183_37 : List Sig := [0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000000000f0f0f0f00000000,input 5,input 7,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 1,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_37 : Impossible true (goalAt 183) 5 state183_37.toFinset :=
  node_ok cuts183 [] 0x313024204908108c8832222420490810c888908128204322224204828124204323020a04323020a0482810c4c0323020a0482810c8c0828128204323020a04b0300c4c0a0812820415140d050a08128204218021204343024204848120a04242220a0484810c4c084812120434300d0c08481212043430212043430282048481 (by decide +kernel)

def state183_38 : List Sig := [0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 5,input 7,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 1,input 2,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_38 : Impossible true (goalAt 183) 6 state183_38.toFinset :=
  node_ok cuts183 [⟨state183_37,exclude183_37⟩] 0xc4c090812420423220c888908124204322224204a0810c888908105c1c90812420417072120490810d0c084810d0c084812120431300d0c0848121204343021204a0810d0c0848180000848121205000a20a0490810c8c0828120a0484810908882810c8c0828120a0431300c8c0828120a04323020a04a0810c8c0828105850828120a0416140545031300c4c015142c0c086070c4c0a08128204151440020a081086003414 (by decide +kernel)

def state183_39 : List Sig := [0x3333333333333333333333333333333322222222222222222222222222222222,input 1,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 7,input 2,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_39 : Impossible true (goalAt 183) 6 state183_39.toFinset :=
  node_ok cuts183 [] 0xd050a08128204218008c88a08128204341424204a0810c88890810c88890812420432220c888908124204232221204a0810d0c084812120490810d0c084810d0c084812120434300d0c084812120434302888816142820432302820432222420432302420432302120424222120432302101486070c8c0333008c8832302820434142820434142420432222420432222120434302120434302101486072101486070c4c08281 (by decide +kernel)

def state183_40 : List Sig := [0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 7,input 1,input 2,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_40 : Impossible true (goalAt 183) 7 state183_40.toFinset :=
  node_ok cuts183 [⟨state183_6,exclude183_6⟩,⟨state183_8,exclude183_8⟩,⟨state183_14,exclude183_14⟩,⟨state183_16,exclude183_16⟩,⟨state183_18,exclude183_18⟩,⟨state183_19,exclude183_19⟩,⟨state183_20,exclude183_20⟩,⟨state183_22,exclude183_22⟩,⟨state183_23,exclude183_23⟩,⟨state183_25,exclude183_25⟩,⟨state183_27,exclude183_27⟩,⟨state183_28,exclude183_28⟩,⟨state183_31,exclude183_31⟩,⟨state183_33,exclude183_33⟩,⟨state183_34,exclude183_34⟩,⟨state183_36,exclude183_36⟩,⟨state183_38,exclude183_38⟩,⟨state183_39,exclude183_39⟩] 0x4002200010d050341440034860728204a08180042000228204a0814002086070d05021808003831300d050313040034151428204a08180034313028204a0814003415140d05015144003434142420490814002ca0810c888a0818003034140c888322240034a0812420490814002200030c88832224002c86072420490818002a00002420490814002086070c88832228002031300c88831304002c23222420490818001c31302420490814002c23220c888232240034341421204848140028a0810d0c0a0814003c34140d0c0343040034a0812120484814002c17072120484814002890810d0c090818001817070d0c034304002c90812120484814002086070d0c034304002882032120484814003886072120484814002082030d0c034308001415140d0c034304002831302120484818001015142120484814002831300d0c0313040034270720a0482814001ca0810c8c0a0818002c27070c8c0323040034a08120a0482814002c322220a0482814001c90810c8c090814003032220c8c032304002c908120a04828140028262220a0482814001c84810585084818003c262205850242240028848120a0482814002086070c8c032304001c840520a04828140024860720a0482814002084050c8c032308004423220c8c032304001c313020a04828180024232220a0482814001c31300c8c0313040001000040000b030 (by decide +kernel)

def state183_41 : List Sig := [0xfffffffffffffffffffffffffffffffffcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfc,input 7,input 1,input 2,input 0,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_41 : Impossible true (goalAt 183) 6 state183_41.toFinset :=
  node_ok cuts183 [] 0xa22228604a18120888210128604a1810840491812860432222460432222460491810c888110124604918104404a18128200a08128204918124200908124204858121200848121204838120a00828120a0431302888886070c4c0313008c8823220c4c0858128604262221604858124604130721604262221604858109888343020e04a1810941c838120e0491810c888838120e04858109088838128888838120e04a0220c8c0b030 (by decide +kernel)

def state183_42 : List Sig := [0xfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfc,input 7,input 1,input 2,input 0,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_42 : Impossible true (goalAt 183) 6 state183_42.toFinset :=
  node_ok cuts183 [⟨state183_35,exclude183_35⟩] 0xb03028604a181240c0918128604322224604b030246049181280c0a18128200a08128204918124200908124204858121200848121204838120a00828120a0431302c0c200000c4c0858128604262221604858124604130721604b4302160485812c0c0838128604250720e04838124604322220e04838121604242220e04b23020e0483812c0c034142860434142860432222460432222460423220c4c023220c4c0343021604262221604323020e04161420e04a222 (by decide +kernel)

def state183_43 : List Sig := [0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc,input 7,0xfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfc,input 2,input 0,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_43 : Impossible true (goalAt 183) 6 state183_43.toFinset :=
  node_ok cuts183 [] 0x28888a1812860482220d050a18128604161424604a1810c88891810c888918124604322205850918124604150728604a08028204a0812460490802420490810c4c0262205450313020e04828020a0482810c4c0a2222101c31300c4c0232208c8831300d050a18109888a18109888918104c1c918121604262228888830709888161409888242209088838128604341420e04838124604322220e04a22220e04838128088323020e04838140008b030 (by decide +kernel)

def state183_44 : List Sig := [0xfffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,input 7,0xfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfc,input 1,input 0,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_44 : Impossible true (goalAt 183) 6 state183_44.toFinset :=
  node_ok cuts183 [] 0xd050a18128604341409888a18128604230724604a1810c88891810c88891812460432220c888918124604262228604a08028204a0812460490802420490810c4c0232208c8831302160484802120484810c4c094142081c31300c4c0262205450313005850a1810941ca1810c88891810c888918120e04161424850830705850262205850242209088858128604341421604858124604322221604941421604858124050343021604858140004b030 (by decide +kernel)

def state183_45 : List Sig := [0xfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfc,input 1,input 2,input 0,input 4,input 5,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_45 : Impossible true (goalAt 183) 7 state183_45.toFinset :=
  node_ok cuts183 [⟨state183_36,exclude183_36⟩,⟨state183_41,exclude183_41⟩,⟨state183_42,exclude183_42⟩,⟨state183_43,exclude183_43⟩,⟨state183_44,exclude183_44⟩] 0xb0300d050b03025050a18128604b03028604a181250503414240c0b0300c888b03028888918124604b030246049181288883222280c034142460491812860432222860434140c88832222860491812460487070c4c031302c0c1000a2c0c087078000086072c0c031300c4c0a18105450a18128200313028200a1810c4c0a08128200151428204918108c8891812420031302420091810c4c090812420023222420500020c4c0313009888151409889000a0545015140988831300c4c100010c4c0313005850232208c89000a08c8823220585031300c4c1000a0c4c0313040000232208c89000a08c8823224000031300c4c094140988826222c0c100022c0c094148001094142c0c026222c0c034144001834142860426222860434140988826222860500022860417070988826222460500022460417074000c130724604262224605000140004858128888161428888b03040004b0302888a000328888b03005850b03009c1c161405850a18140004a18109c1d00060941ca18105850a1810c88900030c88891810585091810c88816140c888918140004918109889000209889000105850161440005000109089000140008838128889000828888b03080008b0302888a000128888b03040020b0300d05100050d050a18140018a1810d05100060d050a18140014a1810c88900040c88891814000c91810c88900030c8889181400109181 (by decide +kernel)

def state183_46 : List Sig := [0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0c0c0c0c0f0f0f0f0c0c0c0c,input 7,input 1,input 5,input 0,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_46 : Impossible true (goalAt 183) 5 state183_46.toFinset :=
  node_ok cuts183 [] 0x24604a1810c88891812c0c0918124604a03024604908024204908128604a08028204a08120e04828020a0482810c4c0b0302181c31302c0c0a18128604903020e0491810c8c0838120e04a1810c8c083810c8c0838120e04323021604343024604858121204848121604848021604343028604858120e04242220e0485810d0c08581216043430 (by decide +kernel)

def state183_47 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffccccccccffffffffcccccccc,input 7,input 1,input 5,input 0,input 2,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_47 : Impossible true (goalAt 183) 6 state183_47.toFinset :=
  node_ok cuts183 [⟨state183_46,exclude183_46⟩] 0x918128604322224604b030246049181280c015052460491810541485812460434302160485812860434302160434302160485810d0c2000021604858140008918124200908124204858121200848121204a18128200a08128204838120a00828120a0431302c0c086070c4c015140c4c0313005450b03028604a181240c0341420e0491810c8c0838120e04858109088838120e04a1810c8c083810c8c0838120e043230058509414 (by decide +kernel)

def state183_48 : List Sig := [0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc,input 7,0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc,input 5,input 0,input 2,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_48 : Impossible true (goalAt 183) 6 state183_48.toFinset :=
  node_ok cuts183 [] 0x2460432220c88891812460483810c88883810c88891812460432220c8c091812460415052160491810d0c085812160434300d0c085812160483810d0c083810d0c085812160434300d0c085812160432302460490802420490812160484802120484810545031300c4c0151420e04828020a0482810c4c0a0222181c31300c4c0323008c88313028604a02221c1c822220888323009c1c3230048c0a02220e0483812141c323020e04838140014b030 (by decide +kernel)

def state183_49 : List Sig := [0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 7,0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc,input 1,input 0,input 2,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_49 : Impossible true (goalAt 183) 6 state183_49.toFinset :=
  node_ok cuts183 [⟨state183_10,exclude183_10⟩] 0x24604a1810c88891812c0c0918124604a03005c1c91812460412222160491810d0c0858121604a1810d0c085810d0c0858121604343009c1c85812160423072460490802420490812160484802120484810c4c0323008c88313028604a08028204a0810c4c0b0308000031300545031300c4c015140c88891810c8c091810c8c0858109088858120e043230248c082220c8c027070c8c03230048c0b03028604a181240c0341428604a181400049414 (by decide +kernel)

def state183_50 : List Sig := [0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc,input 1,input 5,input 0,input 2,input 4,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_50 : Impossible true (goalAt 183) 7 state183_50.toFinset :=
  node_ok cuts183 [⟨state183_28,exclude183_28⟩,⟨state183_47,exclude183_47⟩,⟨state183_48,exclude183_48⟩,⟨state183_49,exclude183_49⟩] 0xb0300c888b03028888918124604b030246049181288883222280c1000524604918109c1c32220c88900030c888322209c1c91812460500032460491814001032220c88900030c88832224001091812460494140d0c034302c0c085812160494142160485812c0c034300d0c017072160485812460434302460417070d0c0343024604858121604270721604858108c0c34300d0c027070d0c0343008c0c85812160500062160485814000834300d0c100060d0c034304000885812160487070c4c031302c0c1000d2c0c087078000086072c0c031300c4c0918108c8891812420031302420091810c4c090812420023222420485810c4c085812120015142120085810545084812120031302120427070545015140981831300c4c027070c4c031300981815140545100010c4c031300c8c023220c8c1000d08c8823220c8c031300c4c1000d0545015144000031300c4c1000d0c4c0313040000151405450b03009c1cb03025051000525050b0308000cb03025050270720889000140004a1812888832300c8c0b03040004b0302888a000228088b0300c8c032300c88900030c88891810c8c091810c88832300c8c091814000491810988832300c8c085814000485810988900060908885810c8c0858109c1d000509c1d00010c8c03230400050001048c100014001483812c0c100082c0c094144004094142c0c200012c0c09414400209414 (by decide +kernel)

def state183_51 : List Sig := [0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc,input 1,input 7,input 0,input 2,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_51 : Impossible true (goalAt 183) 7 state183_51.toFinset :=
  node_ok cuts183 [⟨state183_43,exclude183_43⟩,⟨state183_48,exclude183_48⟩,⟨state183_41,exclude183_41⟩,⟨state183_47,exclude183_47⟩] 0xa2220d050a22221c1ca18128604a22228604a18121c1c34142088900090d050341440014a18128606000328604a1814001434140d05034142460491812860432222860434140c88832222860491812460500030c88832222888891812460500032460491812888832220c88900030541415054001091812460500032460491814001015050541434142160485812860434302860434140d0c034302860485812160417072160485812460434302460417070d0c034302460485812160487070d0c034302888885812160487072160485812888834300d0c100090d0c034304000885812160600022160485814000834300d0c0a18105450a18128200313028200a1810c4c0a08128200151428204918108c8891812420031302420091810c4c090812420023222420485810c4c085812120015142120085810545084812120031302120487070c4c031302888900072888887074002486072888831300c4c083810c4c0838120a00232220a00838108c88828120a00313020a0500070c4c0313040000232208c89000708c8823224000031300c4c1000140004b03009c1c838120e04a18140004a18109c1e000109c1ca18120e0483810c888838120e0491814000491810c88900030c888918120e04838109888838120e0485814000485810988a000009888858120e04838128889000828889000120e048381400050001280890001400203230 (by decide +kernel)

def state183_52 : List Sig := [0xbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 1,input 7,input 2,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_52 : Impossible true (goalAt 183) 6 state183_52.toFinset :=
  node_ok cuts183 [] 0x28888341428888870728204a08128888a0812820487070d05082220d050908124204a0810c888a0810d05032220c888a0812420490814002032220c888a22224204908140030908124204a2220c88832220d050848121204a0810d0c0a0810d05034300d0c0a08121204848105c1c84812120490810d0c0908105c1c34300d0c0908121204848121c1c34300d0c0a22221204848121c1c848121204a2220d0c0343009c1c838120e04a0810c8c0a08109c1c32300c8c0a08120e0483810c888838120e0490810c8c090810c88832300c8c0908120e04838109888838120e04848105850848109888161409088848120e0483812888832300c8c0840520e04838128888838120e0484050c8c032302820415142820434140c4c031302820431302820434140545015142420423222420432220c4c0313024204313024204322208c8823222120431302120434300545034302120415142120434300c4c0313021c1c31300c4c0a22240000b03021c1d00002181ca2220c4c0313020e04313020e04323008c88323020e04232220a0432300c4c08281 (by decide +kernel)

def state183_53 : List Sig := [0xf0f0f0f030303030f0f0f0f030303030f0f0f0f000000000f0f0f0f00000000,input 5,input 1,input 7,input 0,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_53 : Impossible true (goalAt 183) 5 state183_53.toFinset :=
  node_ok cuts183 [] 0x2c0c0918124604a03024604a1810c88891812460490802420490810c4c0b0302081c31300c4c0323008c88313028604a08028204a0810c88891810c8c091810c8c0b03028088323028e04a1810c8c0a1812c0c0a1812860490302160434302460485812120484812160484800d0c0858121604343021604242220e048381216043430286048581 (by decide +kernel)

def state183_54 : List Sig := [0xffffffff33333333ffffffff33333333ffffffff00000000ffffffff00000000,input 5,input 1,input 7,input 0,input 2,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_54 : Impossible true (goalAt 183) 6 state183_54.toFinset :=
  node_ok cuts183 [⟨state183_53,exclude183_53⟩] 0xb030246049181280c0918128604322224604170724604918105c1c85812460434302160434302160485810d0c085812860434302160600002160485814000891812420090812420485812120084812120431302c0c086070c4c031300c8c023220c4c0a18128200a0812820415140c4c031300545032222460432302460432302160424222160432302c0c0a0220c8c0a3812860432302860416140c8c0838120e04b03028604a181240c034142c0c094142c0c08707 (by decide +kernel)

def state183_55 : List Sig := [0x3333333333333333333333333333333300000000000000000000000000000000,input 1,input 7,input 0,input 2,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_55 : Impossible true (goalAt 183) 7 state183_55.toFinset :=
  node_ok cuts183 [⟨state183_52,exclude183_52⟩,⟨state183_54,exclude183_54⟩] 0xa2220d050a22221c1ca18128604a22228604a18121c1c34142088834142460491812860432222860434140c88832222860491812460500080c88832222888891812460500032460491812888832220c88834142160485812860434302860434140d0c034302860485812160417072160485812460434302460417070d0c034302460485812160487070d0c034302888885812160487072160485812888834300d0c0a18105450a18128200313028200a1810c4c0a08128200151428204918108c8891812420031302420091810c4c090812420023222420485810c4c085812120015142120085810545084812120031302120487070c4c031302888900082888887074002086072888831300c4c100010c4c031300c8c023220c8c1000708c8823220c8c031300c4c027070585016142860432302860427070c8c032302860416142860432224000c32222460432302460432220c8c032302460500012460426220c8c0323021604161421604262205850242221604323021605000140004b2302888900082888900010c8c0323028605000528604341440020341428606000128604341440014341424605000424604322240020322224605000324604322240010322221605000221604343040020343021605000e2160434304000834304002100004000031304002031304002100078000031304000031304000500012c0c10008400048381 (by decide +kernel)

def state183_56 : List Sig := [0x3333333333333333333333333333333333333030333330303333303033333030,input 7,input 2,input 4,input 0,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_56 : Impossible true (goalAt 183) 5 state183_56.toFinset :=
  node_ok cuts183 [] 0x2c0c0a18128604903028604a08028204a0812460490802420490812160484802120484810c4c0b0302181c313024604a1810c88891812c0c0918124604a03021604a1810d0c085812160491810d0c085810d0c0858121604343020e04323028604838120a04828120e04828020e04323024604838120e0424222160483810c8c0838120e043230 (by decide +kernel)

def state183_57 : List Sig := [0xfffffffffffffffffffffffffffffffffffff0f0fffff0f0fffff0f0fffff0f0,input 7,input 2,input 4,input 0,input 1,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_57 : Impossible true (goalAt 183) 6 state183_57.toFinset :=
  node_ok cuts183 [⟨state183_56,exclude183_56⟩] 0xb03028604a181240c0230328604a18108c0c838128604323020e04838124604323020e04838121604161420e04323020e0483810c8c2000020e04838140004a18128200a08128204838120a00828120a0491812420090812420485812120084812120431302c0c086070c4c023220c4c0313008c88918128604241424604b030246049181280c0322221604a1810d0c085812160491810d0c085810d0c0858121604343009888a222 (by decide +kernel)

def state183_58 : List Sig := [0xfffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,input 7,0xfffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0,input 4,input 0,input 1,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_58 : Impossible true (goalAt 183) 6 state183_58.toFinset :=
  node_ok cuts183 [] 0xd050a1812860434140d0c0a18128604230320e04a1810c8c0838120e0432300c8c0838120e0485810c8c083810c8c0838120e0432300c8c0838120e04323028604a08028204a08120e04828020a04828108c8831300c4c023222160484802120484810c4c090142181c31300c4c034300545031300d050a18109050a18124604901421c1c841421050343005c1c3430090c0858128604341421604901421604858120c1c343021604858140010b030 (by decide +kernel)

def state183_59 : List Sig := [0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000,input 7,0xfffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0,input 2,input 0,input 1,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_59 : Impossible true (goalAt 183) 6 state183_59.toFinset :=
  node_ok cuts183 [⟨state183_3,exclude183_3⟩] 0x2c0c0a18128604903009c1ca18128604241420e04a1810c8c0838120e04343005850838120e0491810c8c083810c8c0838120e04323005c1c838120e04150728604a08028204a08120e04828020a0482810c4c034300545031302460490802420490810c4c0b03080000313008c8831300c4c023220d050a1810d0c0a181216043430290c084140d0c017070d0c03430090c0918128604341424604b030246049181280c0322224604918140008a222 (by decide +kernel)

def state183_60 : List Sig := [0xfffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0,input 2,input 4,input 0,input 1,input 5,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_60 : Impossible true (goalAt 183) 7 state183_60.toFinset :=
  node_ok cuts183 [⟨state183_20,exclude183_20⟩,⟨state183_57,exclude183_57⟩,⟨state183_58,exclude183_58⟩,⟨state183_59,exclude183_59⟩] 0xb0300d050b03025050a18128604b03028604a181250503414240c0a2220c8c032302c0c0838120e04a22220e0483812c0c032300c8c0270720e0483812860432302860427070c8c0323028604838120e04170720e0483810541432300c8c017070c8c0323005414838120e05000220e0483810d0c016140d0c100030585016140d0c0838120e05000320e0483814000432300c8c100030c8c0323040004838120e0487070c4c031302c0c1000b2c0c087078000086072c0c031300c4c0a18105450a18128200313028200a1810c4c0a0812820015142820483810c4c0838120a00232220a00838108c88828120a00313020a04170708c8823220581831300c4c017070c4c0313005818232208c8900020c4c031300d0c015140d0c1000b0545015140d0c031300c4c1000b08c8823224000031300c4c1000b0c4c0313040000232208c88b03005c1cb03028889000428888b0308000cb03028888170728888341405c1c34142860500042860434144001824142860417072860500024000891812505034300d0c0b03040008b03025052000224050b0300d0c034300d05100060d050a1810d0c0a1810d05034300d0c0a18140008a18105c1d000405c1d00020d0c03430400090002090c100024001085812c0c100082c0c0a22240044a2222c0c200012c0c0a22240020a2220d05100050d050a18140018a1810d05100060d050a18140014a181 (by decide +kernel)

def state183_61 : List Sig := [0xfffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,input 2,input 7,input 0,input 1,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_61 : Impossible true (goalAt 183) 7 state183_61.toFinset :=
  node_ok cuts183 [⟨state183_58,exclude183_58⟩,⟨state183_41,exclude183_41⟩,⟨state183_44,exclude183_44⟩,⟨state183_57,exclude183_57⟩] 0x100060d050341425050a18128605000628604a1812505034140d051000608c0c230340014a18128605000628604a18140014230308c0c34142460491812860432222860434140c88832222860491812460494140c888322221c1c918124604941424604918121c1c32220c889000e0c88832224001091812460600032460491814001032220c888270720e0483812860432302860427070c8c0323028604838120e04322220e0483812460432302460432220c8c0323024604838120e0487070c8c0323025050838120e04870720e0483812505032300c8c1000220e04838121604161421606000205850161421604838120e05000e0c8c0323040004838120e06000120e0483814000432300c8c0a18105450a18128200313028200a1810c4c0a08128200151428204918108c8891812420031302420091810c4c090812420023222420483810c4c0838120a00232220a00838108c88828120a00313020a0487070c4c0313025051000a2505087074003886072505031300c4c085810c4c0858121200151421200858105450848121200313021205000a0c4c0313040000151405451000a0545015144000031300c4c1000240008b0300d050858121604a18140008a1810d05100060d050a18121604858105c1c858121604918140008918105c1e000005c1c9181216048581250510008250510002216048581400090002240510002400203430 (by decide +kernel)

def state183_62 : List Sig := [0xafafafafafafafafafafafafafafafafaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 2,input 7,input 1,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_62 : Impossible true (goalAt 183) 6 state183_62.toFinset :=
  node_ok cuts183 [] 0x4002034140d050941428204a0814003ca0812820494140d05021800d050908124204a0810c888a0810d05032220c888a0812420490812505032220c88887072420490812505090812420487070c888322209c1c828120a04a0810c8c0a08109c1c32300c8c0a08120a0482810c888828120a0490810c8c090810c88832300c8c0908120a04828121c1c32300c8c0941420a04828121c1c828120a0494140c8c0323009888828120a04858105850858109888161409088858120a0482810d050858121604a0810d0c0a0810d05034300d0c0a08121604858105c1c85812160490810d0c0908105c1c34300d0c090812160485812505034300d0c082032160485812505085812160482030d0c034302820415142820434140c4c031302820431302820434140545015142420423222420432220c4c0313024204313024204322208c88232220a04313020a04323008c88323020a04232220a0432300c4c0313021c1c31300c4c0941440000b03021c1d00002181c94140c4c031302160431302160434300545034302160415142120434300c4c08481 (by decide +kernel)

def state183_63 : List Sig := [0x3333030333330303333303033333030333330000333300003333000033330000,input 4,input 2,input 7,input 0,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_63 : Impossible true (goalAt 183) 5 state183_63.toFinset :=
  node_ok cuts183 [] 0x2c0c0a18128604903028604a08028204a0810c4c0b0302101c31300c4c034300545031302460490802420490810d050a1810d0c0a1810d0c0b0302405034302560491810d0c0918124604a1810c88891812c0c0918124604a03020e04323028604838120a04828120e0482800c8c0838120e04323020e04242221604838120e043230246048381 (by decide +kernel)

def state183_64 : List Sig := [0xffff0f0fffff0f0fffff0f0fffff0f0fffff0000ffff0000ffff0000ffff0000,input 4,input 2,input 7,input 0,input 1,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_64 : Impossible true (goalAt 183) 6 state183_64.toFinset :=
  node_ok cuts183 [⟨state183_63,exclude183_63⟩] 0xb03028604a181240c0838128604323020e04323020e0483810c8c083810d0c0242220e04838124604323020e06000020e04838140004a18128200a08128204838120a00828120a0431302c0c086070c4c031300d0c015140c4c091812420090812420423220c4c0313008c8834142860434302860434302c0c090140d0c095812460434302460426220d0c0858121604918128604341424604b030246049181280c032222860427072860427072c0c0a2222c0c08707 (by decide +kernel)

def state183_65 : List Sig := [0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000000000000000000000000000000,input 2,input 7,input 0,input 1,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_65 : Impossible true (goalAt 183) 7 state183_65.toFinset :=
  node_ok cuts183 [⟨state183_62,exclude183_62⟩,⟨state183_64,exclude183_64⟩] 0x100080d050341425050a18128605000628604a1812505034140d05034142460491812860432222860434140c88832222860491812460494140c888322221c1c918124604941424604918121c1c32220c888270720e0483812860432302860427070c8c0323028604838120e04322220e0483812460432302460432220c8c0323024604838120e0487070c8c0323025050838120e04870720e0483812505032300c8c0262220e0483810d0c016140d0c026220585024220d0c0838120e04a18105450a18128200313028200a1810c4c0a08128200151428204918108c8891812420031302420091810c4c090812420023222420483810c4c0838120a00232220a00838108c88828120a00313020a0487070c4c031302505100082505087074002086072505031300c4c100020c4c031300d0c015140d0c1000a0545015140d0c031300c4c034144001834142860434302860434140d0c034302860500022860417070988826222460434302460417070d0c0343024604262224605000240008b4302505100082505100020d0c0343028605000528604341440020341428605000628604341440014341424605000424604322240020322224606000124604322240010322220e05000120e04323040020323020e05000920e04323040004323040021000040000313040020313040021000a8000031304000031304000900022c0c10008400088581 (by decide +kernel)

def state183_66 : List Sig := [0xffffffffffffffffffffffffffffffff55555555555500005555555555550000,input 7,input 4,input 5,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_66 : Impossible true (goalAt 183) 5 state183_66.toFinset :=
  node_ok cuts183 [] 0x84812820434302120484812420434302120434302120484810d0c015142120484810c4c0828121204242220a04828128204323020a04828124204323020a04323020a0482810c8c0232220a0482810c4c0b03028204a081240c0313028204a08105450908128204322224204b030242049081280c0313024204908108c888607 (by decide +kernel)

def state183_67 : List Sig := [0x5555555555550000555555555555000055555555555500005555555555550000,input 4,input 5,input 1,input 2,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_67 : Impossible true (goalAt 183) 6 state183_67.toFinset :=
  node_ok cuts183 [⟨state183_30,exclude183_30⟩,⟨state183_66,exclude183_66⟩] 0x2505034300d0c0b03021204848125050848121204b0300d0c034300d050848121204a1810d0c0a1810d05034300d0c0a18121204848105c1c84812120491810d0c0918105c1c34300d0c091812120484812888832300c8c0b03020a04828128888828120a04b0300c8c0323009888828120a04848105850848109888161409088848120a04828109c1c828120a04a1810c8c0a18109c1c32300c8c0a18120a0482810c888828120a0491810c8c091810c88832300c8c0918120a0482812c0c034142c0c0941428604a1812c0c0a1812860494140d05090302c0c032222c0c0a2222460491812c0c0918124604a2220c888a0300d050918124604a1810c888a1810d05032220c888a1812460491812c0c031300c4c086078000086072c0c200012c0c086070c4c031300d0c031300c4c084810545084810d0c015140d0c084810c4c084810c8c031300c4c0828108c8882810c8c023220c8c082810c4c082810d050151428204a1810c4c0a0810d05031300c4c0a18105450a1810c88823222420491810c4c090810c88831300c4c0918108c889181 (by decide +kernel)

def state183_68 : List Sig := [0x5555555555555555555555555555555555555555555500005555555555550000,input 7,input 4,input 5,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_68 : Impossible true (goalAt 183) 5 state183_68.toFinset :=
  node_ok cuts183 [] 0x21604a1810d0c085812160491810d0c085810d0c0858121604343020e04858109088838120e04a1810c8c0838120e0491810c8c083810c8c0838120e0432302c0c0a18128604903024604a1810c88891812c0c0918124604a03021204848121200858120a04828120a00838128204a08128200a1812420490812420091810c4c086072c0c03130 (by decide +kernel)

def state183_69 : List Sig := [0x3333333333333333333333333333333333333333333300003333333333330000,input 7,input 4,input 5,input 0,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_69 : Impossible true (goalAt 183) 5 state183_69.toFinset :=
  node_ok cuts183 [] 0x21604a1810d0c085812160491810d0c085810d0c0858121604343021604848021204848128604a08028204a0812460490802420490810c4c0b0302181c31302c0c0a18128604903024604a1810c88891812c0c0918124604a03020e04242221604838120a04828120e04828020e04323028604838120e0432302460483810c8c0838120e043230 (by decide +kernel)

def state183_70 : List Sig := [0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000f0f0f0f0f0f0000,input 7,input 4,input 5,input 0,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_70 : Impossible true (goalAt 183) 5 state183_70.toFinset :=
  node_ok cuts183 [] 0x20e04a1810c8c0838120e0491810c8c083810c8c0838120e04323020e04828020a04828128604a08028204a0812460490802420490810c4c0b0302181c31302c0c0a18128604903024604a1810c88891812c0c0918124604a03020e04242220e0485812120484812160484802160434302860485812160434302460485810d0c08581216043430 (by decide +kernel)

def state183_71 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffff0000ffffffffffff0000,input 7,input 4,input 5,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_71 : Impossible true (goalAt 183) 6 state183_71.toFinset :=
  node_ok cuts183 [⟨state183_4,exclude183_4⟩,⟨state183_68,exclude183_68⟩,⟨state183_69,exclude183_69⟩,⟨state183_70,exclude183_70⟩] 0x85812860434302160485812460434302160434302160485810d0c2000321604858140008838121604242220e04838128604323020e04838124604323020e04323020e0483810c8c2000220e04838140004858121200848121204838120a00828120a04a18128200a0812820491812420090812420431302c0c200000c4c200010c4c0313040000b03028604a181240c0270724604a1810c88891812c0c0918124604a03005c1c8707 (by decide +kernel)

def state183_72 : List Sig := [0xffffffffffff0000ffffffffffff0000,input 7,input 4,input 5,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_72 : Impossible true (goalAt 183) 6 state183_72.toFinset :=
  node_ok cuts183 [⟨state183_30,exclude183_30⟩] 0x85812860434302160485812460434302160434302160485810d0c0838121604242220e04838128604323020e04838124604323020e04323020e0483810c8c0858121200848121204838120a00828120a04a18128200a0812820491812420090812420431302181886070c4c0341428604a1810d05091812860432222460432222460491810c888343021604343021604323020e04323020e04313080000313040000341428604341428604322224604322224604b030 (by decide +kernel)

def state183_73 : List Sig := [0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000,input 7,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 5,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_73 : Impossible true (goalAt 183) 6 state183_73.toFinset :=
  node_ok cuts183 [⟨state183_1,exclude183_1⟩] 0x2160434300d0c085812160491810d0c085810d0c0858121604343009888858121604243020e04858109088838120e0432300c8c0838120e0491810c8c083810c8c0838120e0432300c888838120e05000321604848021204848120e04828020a0482810545031300c4c015142460490802420490810c4c0a03080000313008c8831300c4c0232228604a030250509030240c032220d050322209050a03024604918121050322224604918140014a222 (by decide +kernel)

def state183_74 : List Sig := [0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 7,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 4,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_74 : Impossible true (goalAt 183) 6 state183_74.toFinset :=
  node_ok cuts183 [⟨state183_13,exclude183_13⟩] 0x2160434300d0c0858121604a1810d0c085810d0c085812160434300d050858121605000620e04858109088838120e0432300c8c0838120e04a1810c8c083810c8c0838120e04323005850838120e04161421604848021204848120e04828020a04828108c8831300c4c0232228604a08028204a0810c4c090308000031300545031300c4c01514246049030248889030280c034140c888322209050903028604a18120888341428604a181400109414 (by decide +kernel)

def state183_75 : List Sig := [0x5555555555550000555555555555000055555555555500005555555555550000,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 4,input 5,input 1,input 2,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_75 : Impossible true (goalAt 183) 6 state183_75.toFinset :=
  node_ok cuts183 [] 0xd0c084812120434302120434300d0c084812120434300d0c084812120434300d0c084810c8c0828120a04323020a04848109088828120a0432300c8c0828120a0432300c8c0828120a0432300c8c082812c0c09414240c0903028604b03028888a030280c034140c888241424604b0302181cb0302181c31302181cb0300c4c0313021204343021204313020a04323020a0415140c4c031300545023220c4c0313008c890000 (by decide +kernel)

def state183_76 : List Sig := [0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 4,input 5,input 0,input 1,input 2,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_76 : Impossible true (goalAt 183) 7 state183_76.toFinset :=
  node_ok cuts183 [⟨state183_31,exclude183_31⟩,⟨state183_67,exclude183_67⟩,⟨state183_71,exclude183_71⟩,⟨state183_72,exclude183_72⟩,⟨state183_73,exclude183_73⟩,⟨state183_74,exclude183_74⟩,⟨state183_75,exclude183_75⟩] 0x94140d0c034302c0c085812160494142160485812c0c034300d0c034142160485814001834300d0c034140d0c034304001485812160500042160485810c88834300d0c100060d0c034300c88885812160500062160485814000834300d0c100060d0c0343040008858121604a2220c8c032302c0c0838120e04a22220e0483812c0c032300c8c0262220e04838121604161421604262205850242221604838120e05000520e0483810d05032300c8c100030c8c032300d050838120e04322220e0483814000c32300c8c032220c8c0323040010838120e05000320e0483814000432300c8c100030c8c0323040004838120e0487070c4c031302c0c1000d2c0c087078000086072c0c031300c4c085810c4c085812120015142120085810545084812120031302120483810c4c0838120a00232220a00838108c88828120a00313020a0500050545015140d05031300c4c1000d0c4c031300d050151405451000408c8823220c88831300c4c1000d0c4c031300c888232208c89000d8001a00014000031300c4c1000d0c4c0313040001000d40000b0300d050b03025051000525050b030800149030250503414240c1000540010a1812c0c032222c0c0a22240010a2222c0c20004280c0a2220c888a0300d05100050d05100040c88832224001500050905100054001491812c0c100082c0c087078000c87072c0c200022c0c08707400208707 (by decide +kernel)

def state183_77 : List Sig := [0x3333333333333333333333333333333333330000333300003333000033330000,input 4,input 7,input 0,input 2,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_77 : Impossible true (goalAt 183) 6 state183_77.toFinset :=
  node_ok cuts183 [⟨state183_26,exclude183_26⟩] 0x2c0c034142c0c0941428604a1812c0c0a1812860494140d05090300d050858121604a1810d0c0a1810d05034300d0c0a1812160485812505034300d0c0b03021604858125050858121604b0300d0c0343005c1c85812160491810d0c0918105c1c34300d0c0918121604858128604151428604a0800c4c0a08028604313028204a08005450a0812160431302160484800545084802160415142120484800c4c0848121c1c31300c4c0b03040030b03021c1e00002181cb0300c4c031302460423222460490800c4c0908024604313024204908008c8890810d050918124604a1810c888a1810d05032220c888a1812460491812c0c032222c0c0a2222460491812c0c0918124604a2220c888a03028604838120e0425070c8c0323028604323028604250720e04838121604838120e04242205850242221604161421604242220e0483810c4c0828020a04232220e0482810c4c0838120e04232220a0082802c0c032300c8c0a22220e0483812c0c0838120e04a2220c8c0323024604838120e0432220c8c0323024604323024604322220e048381 (by decide +kernel)

def state183_78 : List Sig := [0x3333333333333333333333333333333333330000333300003333000033330000,0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000,input 4,input 7,input 0,input 2,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_78 : Impossible true (goalAt 183) 6 state183_78.toFinset :=
  node_ok cuts183 [⟨state183_2,exclude183_2⟩] 0x2c0c0a1812860490300941ca18128604250721604a1810d0c085810d0c085812160434302160491810d0c0858109088858121604242228604a08028204a0812160484802120484810c4c0b03080000313024604908024204908108c8831300c4c0232228888918128604341424604b03024604a0300c88883810c8c0a18120e04838109088858120e04828120a04838120a00323020e0483810c8c083810c8c0918120e050001 (by decide +kernel)

def state183_79 : List Sig := [0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000f0f00000f0f00000f0f0000,input 2,input 4,input 7,input 0,input 1,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_79 : Impossible true (goalAt 183) 6 state183_79.toFinset :=
  node_ok cuts183 [] 0xb03028604a181240c0838128604323020e04323020e0483810c8c0838124604323020e04838109080242220e04a18128200a08128204838120a00828120a0431302c0c086070c4c091812420090812420431300988815140c4c0918128604241424604b030246049181280c034142860426222860426222c0c094142c0c0262224604170724604a1810d050a1810d050838105850838105850313008c88313008c88b03028888b0302505091810c888918105c1c8581 (by decide +kernel)

def state183_80 : List Sig := [0xffffffff00000000ffffffff00000000ffff000000000000ffff0000,input 5,input 4,input 7,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_80 : Impossible true (goalAt 183) 6 state183_80.toFinset :=
  node_ok cuts183 [⟨state183_5,exclude183_5⟩] 0x34302160485810d0c085812460434302160485810d0c0343021604838121604242220e04323020e0483810c8c0838124604323020e0483810c8c0323020e04858121200848121204838120a00828120a0431302c0c200000c4c091812420090812420415140c4c0313005450b030246049181280c091810c888322224604b03025050b0302505085810d0c085810d0c083810c8c083810c8c015140c4c015140c4c094142c0c094142c0c091810c88891810c888a181 (by decide +kernel)

def state183_81 : List Sig := [0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000,input 4,input 7,input 0,input 1,input 2,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_81 : Impossible true (goalAt 183) 7 state183_81.toFinset :=
  node_ok cuts183 [⟨state183_73,exclude183_73⟩,⟨state183_6,exclude183_6⟩,⟨state183_27,exclude183_27⟩,⟨state183_57,exclude183_57⟩,⟨state183_59,exclude183_59⟩,⟨state183_71,exclude183_71⟩,⟨state183_77,exclude183_77⟩,⟨state183_78,exclude183_78⟩,⟨state183_79,exclude183_79⟩,⟨state183_80,exclude183_80⟩] 0xb0300d050b03025050a18128604b03028604a181250503414240c2000909c1c270740014a18128606000528604a18140014270709c1c34142160485812860434302860434140d0c034302860485812160494140d0c034302c0c085812160494142160485812c0c034300d0c100042160485812460434302460600040d0c0343024604858121606000809888262240008858121606000321604858140008262209888270720e0483812860432302860427070c8c0323028604838120e04262220e04838121604161421604262205850242221604838120e0500030c8c032302c0c0838120e05000320e0483812c0c032300c8c1000420e0483812460432302460500030c8c0323024604838120e0500038001e000640004838120e05000320e04838140005000340004a18105450a18128200313028200a1810c4c0a0812820015142820485810c4c085812120015142120085810545084812120031302120483810c4c0838120a00232220a00838108c88828120a00313020a05000b0c4c031302c0c1000b2c0c1000b8000a00012c0c031300c4c0918108c8891812420031302420091810c4c0908124200232224205000b08c8823224000031300c4c1000b0c4c0313040000232208c89000440010a2220d050918124604a18140010a1810d05200000d050a1812460491812c0c100082c0c10004246049181400110004280c10004400203222 (by decide +kernel)

def state183_82 : List Sig := [0xaaaaffffaaaaffffaaaaffffaaaaffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 4,input 7,input 1,input 2,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_82 : Impossible true (goalAt 183) 6 state183_82.toFinset :=
  node_ok cuts183 [] 0x2c0c034142c0c0941428204a0812c0c0a0812820494140d05090300d050848121204a0810d0c0a0810d05034300d0c0a0812120484812505034300d0c0b03021204848125050848121204b0300d0c0343005c1c84812120491810d0c0918105c1c34300d0c0918121204848109c1c828120a04a0810c8c0a08109c1c32300c8c0a08120a04828109888828120a04848105850848109888161409088848120a0482812181c32300c8c0b03020a0482812181c828120a04b0300c8c032300c888828120a0491810c8c091810c88832300c8c0918120a0482810d050918124604a0810c888a0810d05032220c888a0812460491812c0c032222c0c086072460491812c0c091812460486070c88832222820415142820434140c4c031302820431302820434140545015142120431302120434300545034302120415142120434300c4c0313020a04313020a04323008c88323020a04232220a0432300c4c031302181c31300c4c0b03040000b0302181d00002181cb0300c4c031302460423222460432220c4c0313024604313024204322208c889081 (by decide +kernel)

def state183_83 : List Sig := [0xf0f0f0f00000f0f0f0f0f0f00000f0f0f0f0f0f000000000f0f0f0f00000000,input 5,input 4,input 7,input 0,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_83 : Impossible true (goalAt 183) 5 state183_83.toFinset :=
  node_ok cuts183 [] 0xc8c0838120e04323020e0432300c8c0838120e04a1810c8c0838120e04828020a0482810c4c0b0302181c313008c8831300c4c0232228604a08028204a0812c0c0a222280c0a0302c604a1810c888a1812c0c0a18128604822220e04242220e0485812120484812160484800d0c08581216043430216043430246048581216043430286048581 (by decide +kernel)

def state183_84 : List Sig := [0xffffffff0000ffffffffffff0000ffffffffffff00000000ffffffff00000000,input 5,input 4,input 7,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_84 : Impossible true (goalAt 183) 6 state183_84.toFinset :=
  node_ok cuts183 [⟨state183_15,exclude183_15⟩,⟨state183_83,exclude183_83⟩] 0x34302160485810d0c085810d0c0343021604858128604343021606000121604858140008838121604242220e04323020e0483810c8c083810c8c0323020e04838128604323020e04161420e04838105850858121200848121204838120a00828120a0431302c0c200000c4c023220c4c0313008c88a18128200a0812820415140c4c0313005450b03028888a030280c0b1812860432222860417070c888918124604b03028604a1812088834142c0c094142c0c09414 (by decide +kernel)

def state183_85 : List Sig := [0xffff0000ffff0000ffff0000ffff00000000000000000000000000000000,input 4,input 7,input 0,input 1,input 2,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_85 : Impossible true (goalAt 183) 7 state183_85.toFinset :=
  node_ok cuts183 [⟨state183_16,exclude183_16⟩,⟨state183_82,exclude183_82⟩,⟨state183_84,exclude183_84⟩] 0xb0300d050b03025050a18128604b03028604a181250503414240c034142160485812860434302860434140d0c034302860485812160494140d0c034302c0c085812160494142160485812c0c034300d0c017072160485810c88834300d0c017070d0c034300c888858121604270720e0483812860432302860427070c8c0323028604838120e04262220e04838121604161421604262205850242221604838120e0500080c8c032302c0c0838120e05000320e0483812c0c032300c8c0322220e0483810541432300c8c032220c8c0323005414838120e04a18105450a18128200313028200a1810c4c0a0812820015142820485810c4c085812120015142120085810545084812120031302120483810c4c0838120a00232220a00838108c88828120a00313020a0500080c4c031302c0c100082c0c1000b4002200002c0c031300c4c0170708c8823220c88831300c4c017070c4c031300c888232208c88341405c1c34142860432222860434140c888322228604170728605000440010b2222c0c100082c0c100040c888322228605000528604341440020341428606000228604341440014341421605000221604343040020343021605000e21604343040008343020e05000120e04323040020323020e05000320e04323040004323040021000040000313040020313040021000b800043130400003130400110004288890008400109181 (by decide +kernel)

def state183_86 : List Sig := [0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000000000f0f0f0f00000000,input 5,input 7,input 0,input 1,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_86 : Impossible true (goalAt 183) 6 state183_86.toFinset :=
  node_ok cuts183 [⟨state183_37,exclude183_37⟩] 0x2c0c032222c0c0a2222460491812c0c0918124604a2220c888a0300d050918124604a1810c888a1810d05032220c888a1812460491810c888838120e0491810c8c091810c88832300c8c0918120e0483812888832300c8c0b03020e04838128888838120e04b0300c8c0323009c1c838120e04a1810c8c0a18109c1c32300c8c0a18120e0483812460423222460490800c4c0908024604313024204908008c88908120e04313020e04828008c88828020e04232220a0482800c4c0828121c1c31300c4c0b0304003cb03021c1e00002181cb0300c4c0313028604151428604a0800c4c0a08028604313028204a08005450a0812c0c034142c0c0941428604a1812c0c0a1812860494140d05090302460485812160413070d0c0343024604343024604130721604858120e04858120e04161409888242220e04262220e0416142160485810c4c084802120415142160484810c4c085812160415142120084802c0c034300d0c094142160485812c0c085812160494140d0c034302860485812160434140d0c03430286043430286043414216048581 (by decide +kernel)

def state183_87 : List Sig := [0x3333333333333333333333333333333333333333000000003333333300000000,input 1,input 5,input 7,input 0,input 2,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_87 : Impossible true (goalAt 183) 6 state183_87.toFinset :=
  node_ok cuts183 [] 0xb030246049181280c091812860432222460485812460434302160434302160485810d0c085812860434302160491812420090812420485812120084812120431302c0c086070c4c0a18128200a08128204313008c8823220c4c0b03028604a181240c0322224604322224604262221604262221604a2222c0c0a2222c0c016142860427072860491810c88891810c888858109888858109888313008c88313008c88b03028888b03028888a1810d050a18109c1c8381 (by decide +kernel)

def state183_88 : List Sig := [0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000000000f0f0f0f00000000,0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 5,input 7,input 0,input 1,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_88 : Impossible true (goalAt 183) 6 state183_88.toFinset :=
  node_ok cuts183 [⟨state183_11,exclude183_11⟩] 0x2c0c0918124604a03024604a1810c888918104c1c918124604130720e0491810c8c083810c8c0838120e04323020e04a1810c8c0838105850838120e04161424604908024204908120e04828020a0482810c4c0b03080000313028604a08028204a0810545031300c4c0151425050b0302860490300d05085810d0c091812160483810908883812160484812120485812120034302160485810d0c085810d0c0a181216050002 (by decide +kernel)

def state183_89 : List Sig := [0xffff0000ffff0000ffff0000ffff0000ffff000000000000ffff00000000,input 4,input 5,input 7,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_89 : Impossible true (goalAt 183) 6 state183_89.toFinset :=
  node_ok cuts183 [⟨state183_12,exclude183_12⟩] 0x34302160485810d0c085812860434302160485810d0c0343021604838121604242220e04323020e0483810c8c0838128604323020e0483810c8c0323020e04858121200848121204838120a00828120a0431302c0c200000c4c0a18128200a0812820423220c4c0313008c88b03028604a181240c0b03028888b0302888834142860434142860485810d0c085810d0c083810c8c083810c8c023220c4c023220c4c0a2222c0c0a2222c0c0a1810d050a1810d0509181 (by decide +kernel)

def state183_90 : List Sig := [0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 5,input 7,input 0,input 1,input 2,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_90 : Impossible true (goalAt 183) 7 state183_90.toFinset :=
  node_ok cuts183 [⟨state183_14,exclude183_14⟩,⟨state183_38,exclude183_38⟩,⟨state183_47,exclude183_47⟩,⟨state183_49,exclude183_49⟩,⟨state183_71,exclude183_71⟩,⟨state183_74,exclude183_74⟩,⟨state183_86,exclude183_86⟩,⟨state183_87,exclude183_87⟩,⟨state183_88,exclude183_88⟩,⟨state183_89,exclude183_89⟩] 0xb0300c888b03028888918124604b030246049181288883222280c100052460491812860432222860600050c888322228604918124606000905c1c170740010918124606000424604918140010170705c1c17072160485812460434302460417070d0c034302460485812160500060d0c034302c0c085812160500062160485812c0c034300d0c100052160485812860434302860500060d0c0343028604858121605000680022000640008858121605000621604858140009000640008322220e0483812460432302460432220c8c0323024604838120e04262220e04838121604161421604262205850242221604838120e04a2220c8c032302c0c0838120e04a22220e0483812c0c032300c8c1000520e0483812860432302860600030c8c0323028604838120e06000705850161440004838120e06000220e04838140004161405850918108c8891812420031302420091810c4c090812420023222420485810c4c085812120015142120085810545084812120031302120483810c4c0838120a00232220a00838108c88828120a00313020a05000d0c4c031302c0c1000d2c0c1000d8000600002c0c031300c4c0a18105450a18128200313028200a1810c4c0a08128200151428205000d0545015144000031300c4c1000d0c4c031304000015140545100054001494142c0c100082c0c1000528604a181400150005240c10005400203414 (by decide +kernel)

def state183_91 : List Sig := [0xaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 5,input 7,input 1,input 2,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_91 : Impossible true (goalAt 183) 6 state183_91.toFinset :=
  node_ok cuts183 [] 0x2c0c032222c0c0a2222420490812c0c0908124204a2220c888a0300d050908124204a1810c888a1810d05032220c888a18124204908105c1c84812120490810d0c0908105c1c34300d0c090812120484812181c34300d0c0b0302120484812181c848121204b0300d0c034300d050848121204a1810d0c0a1810d05034300d0c0a1812120484810c888828120a0490810c8c090810c88832300c8c0908120a04828109888828120a04848105850848109888161409088848120a0482812888832300c8c0b03020a04828128888828120a04b0300c8c0323009c1c828120a04a1810c8c0a18109c1c32300c8c0a18120a0482812c0c034142c0c0860728604a1812c0c0a1812860486070d05021802420423222420432220c4c0313024204313024204322208c8823222120431302120434300545034302120415142120434300c4c0313020a04313020a04323008c88323020a04232220a0432300c4c031302181c31300c4c0b03040000b0302181d00002181cb0300c4c031302860415142860434140c4c0313028604313028204341405450a081 (by decide +kernel)

def state183_92 : List Sig := [0x3333000033333333333300003333333333330000333300003333000033330000,input 4,input 5,input 7,input 0,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_92 : Impossible true (goalAt 183) 5 state183_92.toFinset :=
  node_ok cuts183 [] 0xd0c085812160434302160434300d0c085812160491810d0c085812160484802120484810c4c0b0302181c31300545031300c4c015142460490802420490812c0c09414240c090302c0c0918124604322224604b1810c888918120e04242221604838120a04828120e0482800c8c0838120e04323020e04323028604838120e043230246048381 (by decide +kernel)

def state183_93 : List Sig := [0xffff0000ffffffffffff0000ffffffffffff0000ffff0000ffff0000ffff0000,input 4,input 5,input 7,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_93 : Impossible true (goalAt 183) 6 state183_93.toFinset :=
  node_ok cuts183 [⟨state183_7,exclude183_7⟩,⟨state183_92,exclude183_92⟩] 0x34302160485810d0c085810d0c0343021604858124604343021604262221604858109888838121604242220e04323020e0483810c8c083810c8c0323020e04838124604323020e06000120e04838140004858121200848121204838120a00828120a0431302c0c200000c4c015140c4c031300545091812420090812420423220c4c0313008c88b030250509030240c0b0302460491812888891812c60434142460432222c0c0a2222c0c0a2220d050270728604a181 (by decide +kernel)

def state183_94 : List Sig := [0xffffffff00000000ffffffff00000000000000000000000000000000,input 5,input 7,input 0,input 1,input 2,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_94 : Impossible true (goalAt 183) 7 state183_94.toFinset :=
  node_ok cuts183 [⟨state183_8,exclude183_8⟩,⟨state183_91,exclude183_91⟩,⟨state183_93,exclude183_93⟩] 0xb0300c888b03028888918124604b030246049181288883222280c0341424604918109c1c32220c88834140c888322209c1c91812460417072160485812460434302460417070d0c034302460485812160500080d0c034302c0c085812160500062160485812c0c034300d0c0341421604858108c0c34300d0c034140d0c0343008c0c858121604322220e0483812460432302460432220c8c0323024604838120e04262220e04838121604161421604262205850242221604838120e04a2220c8c032302c0c0838120e04a22220e0483812c0c032300c8c0270720e0483810d05032300c8c027070c8c032300d050838120e04918108c8891812420031302420091810c4c090812420023222420485810c4c085812120015142120085810545084812120031302120483810c4c0838120a00232220a00838108c88828120a00313020a0500080c4c031302c0c100082c0c1000d4002200002c0c031300c4c027070545015140d05031300c4c027070c4c031300d050151405451000540014b4142c0c100082c0c100050d050341424605000424604322240020322224606000224604322240010322221605000221604343040020343021605000621604343040008343020e05000120e04323040020323020e05000920e04323040004323040021000040000313040020313040021000d80004313040000313040015000525051000840014a181 (by decide +kernel)

def state183_95 : List Sig := roots 183
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_95 : Impossible true (goalAt 183) 8 state183_95.toFinset :=
  node_ok cuts183 [⟨state183_40,exclude183_40⟩,⟨state183_45,exclude183_45⟩,⟨state183_50,exclude183_50⟩,⟨state183_51,exclude183_51⟩,⟨state183_55,exclude183_55⟩,⟨state183_60,exclude183_60⟩,⟨state183_61,exclude183_61⟩,⟨state183_65,exclude183_65⟩,⟨state183_76,exclude183_76⟩,⟨state183_81,exclude183_81⟩,⟨state183_85,exclude183_85⟩,⟨state183_90,exclude183_90⟩,⟨state183_94,exclude183_94⟩] 0x80030b0300d050b03040014941428604a1818002cb03028604a1814001494140d050903080028b0300c888b03040010a22224604918180024b03024604918140010a2220c888a03040014341424604918140010a1810c888a1818002034140c888322240014a1812460491818001c94140d0c0343040008b03021604858180018941421604858140008b0300d0c0343040014341421604858140008a1810d0c0a1814001834140d0c0343040008a1812160485814001017072160485814000891810d0c091818001417070d0c0343040008918121604858180010a2220c8c0323040004b03020e0483818000ca22220e04838140004b0300c8c0323040014270720e04838140004a1810c8c0a1818000827070c8c0323040004a18120e04838140010322220e0483814000491810c8c091814000c32220c8c0323040004918120e04838140008262220e04838140004858105850858180004262205850242240004858120e0483814000087070c4c0313040000b03040000b03040000870780000860740000b0300c4c0313040000a18105450a18140000a0800c4c0a08040000a1810c4c0a08140000a08005450a08140000918108c8891814000090800c4c090804000091810c4c0908140000908008c8890814000085810c4c085814000084800545084804000085810545084814000084800c4c084814000083810c4c0838140000828008c88828040000838108c8882814000082800c4c08281 (by decide +kernel)

theorem lower183 : Claim 183 9 :=
  fromSearch 268436804 (by decide +kernel) exclude183_95


open PEqualNP.CircuitLowerBounds

def graph : Sig := goalAt 255
theorem graph_proper : proper graph := by unfold proper; decide +kernel

def edgeList : List Nat := [0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7]
def target (x : Fin 8 → Bool) : Bool :=
  decide (∃ i < edgeList.length / 2,
    (List.ofFn x).getD (edgeList.getD (2*i) 0) false = true ∧
    (List.ofFn x).getD (edgeList.getD (2*i+1) 0) false = true)

def smallCircuit : Circuit := ⟨[⟨.or, [0, 7]⟩, ⟨.or, [5, 6]⟩, ⟨.or, [2, 3]⟩, ⟨.or, [8, 10]⟩, ⟨.or, [1, 2]⟩, ⟨.or, [6, 7]⟩, ⟨.or, [1, 8]⟩, ⟨.and, [9, 11]⟩, ⟨.and, [12, 13]⟩, ⟨.and, [4, 14]⟩, ⟨.or, [15, 16]⟩, ⟨.or, [18, 17]⟩], 19⟩

theorem witnessMonotone : ∀ g ∈ smallCircuit.gates,
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [smallCircuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact ⟨Or.inl rfl, by decide⟩ | exact ⟨Or.inr rfl, by decide⟩

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem witnessCorrect : ∀ x : Fin 8 → Bool, smallCircuit.eval (List.ofFn x) = target x := by
  decide +kernel

theorem witnessSize : smallCircuit.gates.length = 12 := rfl

theorem noNotReuse {gates : List Gate} (fit : ∀ g ∈ gates,
    (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (h : ∀ g ∈ gates, g.op ≠ GateOp.not) :
    ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  obtain ⟨ops,arity⟩ := fit g hg
  refine ⟨?_,arity⟩
  rcases ops with a | b | c
  · exact Or.inl a
  · exact Or.inr b
  · exact (h g hg c).elim


def eightInputs : List Sig := roots 255
def sampleEight (r : Row) (i : Fin 8) : Bool := bit r (eightInputs.getD i.val zero)
theorem eightList : List.ofFn (fun i : Fin 8 => eightInputs.getD i.val zero) = eightInputs := rfl
theorem eightSampled (r : Row) : List.ofFn (sampleEight r) = eightInputs.map (bit r) := by
  rw [←eightList,List.map_ofFn]
  rfl

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem eightTable : ∀ r : Row, bit r graph = target (sampleEight r) := by decide +kernel

theorem eightEval (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C)
    (i : Nat) (r : Row) : bit r ((execute C.gates eightInputs).getD i zero) =
      (C.wires (List.ofFn (sampleEight r))).getD i false := by
  rw [←b_read,execute_bits _ _ _ (fun g hg => (h g hg).1),eightSampled]
  rfl


def lowRow (i : Fin 8) : Row := Fin.ofNat 256 (1 <<< ([4, 4, 5, 5, 0, 0, 0, 1] : List Nat).getD i.val 0)
def highRow (i : Fin 8) : Row := Fin.ofNat 256 ((1 <<< i.val) ||| (1 <<< ([4, 4, 5, 5, 0, 0, 0, 1] : List Nat).getD i.val 0))

set_option maxHeartbeats 1000000 in
theorem allEightRequired :
    (∀ i : Fin 8, bit (lowRow i) graph ≠ bit (highRow i) graph) ∧
    (∀ i j : Fin 8, i ≠ j →
      bit (lowRow i) (eightInputs.getD j.val zero) =
      bit (highRow i) (eightInputs.getD j.val zero)) := by decide +kernel

theorem physicalSigned (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (computes : ∀ x : Fin 8 → Bool, C.eval (List.ofFn x)=target x) :
    ∃ k, k ≤ C.gates.countP (fun g => !isNot g) ∧ Live true graph k eightInputs.toFinset := by
  have goalEq : (execute C.gates eightInputs).getD C.output zero = graph := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j,hj⟩
    exact (eightEval C legal C.output r).trans ((computes (sampleEight r)).trans (eightTable r).symm)
  have out := get_rep (u:=true) (execute C.gates eightInputs) C.output
  rw [goalEq] at out
  unfold Repr at out
  have pg : bit 0 graph = false := by decide +kernel
  rw [nrm_id pg] at out
  obtain ⟨k,S,hk,run,sub⟩ := extract (u:=true) C.gates eightInputs legal (by simp) graph_proper
    (out.resolve_right (fun h => h graph_proper))
  have ns : eightInputs.all plainWord = true := by decide +kernel
  rw [nrm_map ns] at sub
  have idx (a : Sig) (ha : a ∈ eightInputs) : ∃ i : Fin 8, eightInputs.getD i.val zero = a := by
    rw [←eightList] at ha
    exact List.mem_ofFn.mp ha
  have eq : S = eightInputs.toFinset := by
    ext a
    constructor
    · exact fun h => List.mem_toFinset.mpr (sub a h)
    · intro ha
      obtain ⟨i,rfl⟩ := idx a (List.mem_toFinset.mp ha)
      apply raw_required run eightInputs (eightInputs.getD i.val zero) sub (lowRow i) (highRow i)
        (allEightRequired.1 i)
      intro v hv hn
      obtain ⟨j,rfl⟩ := idx v hv
      apply allEightRequired.2 i j
      rintro rfl
      exact hn rfl
  exact ⟨k,hk,eq ▸ run⟩


theorem replaceShort
    (lower : Impossible true graph 10 eightInputs.toFinset) (gates : List Gate) (o : Nat)
    (fit : ∀ g ∈ gates, (g.op=GateOp.and ∨ g.op=GateOp.or ∨ g.op=GateOp.not) ∧ g.inputs.length≤2)
    (correct : ∀ x : Fin 8 → Bool, (Circuit.mk gates o).eval (List.ofFn x)=target x) :
    ∃ (gs : List Gate) (out : Nat), (∀ g ∈ gs, (g.op=GateOp.and ∨ g.op=GateOp.or) ∧ g.inputs.length≤2) ∧
       gs.length≤gates.length ∧ ∀ x : Fin 8 → Bool, (Circuit.mk gs out).eval (List.ofFn x)=target x := by
  classical
  by_cases big : 12 ≤ gates.length
  · exact ⟨smallCircuit.gates, smallCircuit.output, witnessMonotone, (by simpa only [witnessSize] using big), witnessCorrect⟩
  by_cases mono : ∀ g ∈ gates, g.op ≠ GateOp.not
  · exact ⟨gates, o, noNotReuse fit mono, Nat.le_refl _, correct⟩
  push Not at mono
  obtain ⟨g, hg, hop⟩ := mono
  have lt : gates.countP (fun q => !isNot q) < gates.length := by
    rcases Nat.lt_or_ge (gates.countP (fun q => !isNot q)) gates.length with h | h
    · exact h
    · have eq := List.countP_eq_length.mp (Nat.le_antisymm List.countP_le_length h) g hg
      simp [isNot, hop] at eq
  have legal : PEqualNP.MetaComplexity.FanInTwo (Circuit.mk gates o) := by
    intro g hg
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using fit g hg
  obtain ⟨k, hk, run⟩ := physicalSigned (Circuit.mk gates o) legal correct
  change k ≤ gates.countP (fun q => !isNot q) at hk
  exact (lower k (by omega) run).elim

theorem lowerGraph : Impossible true graph 10 eightInputs.toFinset :=
  (ruleFor 255 lower183 none (by decide +kernel)).property 10 eightInputs
    (by decide +kernel) (by decide +kernel)

end PEqualNP.Outside.L_meta_31133_aux

open PEqualNP.Outside.L_meta_31133_aux in
theorem PEqualNP.Outside.L_meta_31133 : (∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true))  := by
  intro gates o fit _ correct
  exact replaceShort lowerGraph gates o fit correct
