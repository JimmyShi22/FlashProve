-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cm/SegAttIdn.lean: the identities of the attention segment as families (`Fam`) of
Cb/Req/ReqSpec.lean (Inst/Model/Att/Trace.lean: `idnVal`: at1, at2, at3).

Part of the arithmetisation of the model. The cells (the entries of one matrix for each segment)
must meet zero tests (identities) and table lookups (keys) at the vertices of Boolean cubes
(`SegSpec.Holds`, Cb/Req/ReqSpec.lean). A family has one value at each vertex B < 2^v of a cube; a
vertex beyond the index set is called dead.
Vertices: B = b · 2^13 + (h · 2^10 + i): the pair b (layer, number of the query head among those of
its key/value head: `AttSeg.Dim.nb`) in 5 bits (20 live), the key/value head h, the position i. At
a dead vertex all forms are 0, and so is the value.

Main names:
  `famAt1 k`: ib_k (ib_k - 1): one family for each of the 10 bits k of the index of the greatest
    score.
  `famAt2`: mx - Σ_(n, j) query_n × key_(j, n) × Π_k eq1(ib_k, bit_k(j)): a sum atom over 7 + 10
    further variables of a product of 12 forms; eq1(u, bit) is the form u or 1 - u.
  `famAt3`: den - Σ_j weight: a sum atom over the 10 bits of j (`AttSeg.rowSum_eq`).
  `AttIdnOK Φ g fs`: the property of a list fs of families: all vanish on their cubes if and only
    if all identities of Inst/Model/Att/Trace.lean with valid names (`AttSeg.Idn.Valid`) do, at the
    trace `tAtt g A`, over E, for all matrices A; each family is well-formed (`Fam.WF`) and reads
    only places of valid cells that the segment reads, own or borrowed (`IsAtt`). `attIdn_ok`:
    `attIdnFams g` (the ten `famAt1 k`, `famAt2`, `famAt3`) has it.
Terms: lean/GLOSSARY.md.
-/
import Cm.SegAttKeySum

set_option autoImplicit false
set_option linter.unusedSectionVars false

attribute [-instance] Inst.Model.Scl.ref

namespace Cm.Seg
open Cb Inst.Model Inst.Model.All Finset Ex
open Inst.Model.AttSeg (Raw Reg)

variable {X F E : Type} [Field F] [Field E] [Algebra F E]

/-- What the theorems on `attSpec` (Cm/TargetSegAtt.lean) require of the families of identities. -/
structure AttIdnOK (Φ : IdxFmt F) (g : ℕ) (fs : List (Cb.Fam X E)) : Prop where
  iff : ∀ (x₀ : X) (W : ℕ → ℕ → F) (A : ℕ → ℕ → ℕ → E),
    (∀ f ∈ fs, ∀ B < 2 ^ f.v, f.val Φ x₀ W A B = 0) ↔
    ∀ j : AttSeg.Idn, j.Valid DA → AttSeg.idnVal DA (tAtt g A) j = 0
  wf : ∀ f ∈ fs, f.WF Φ
  places : ∀ f ∈ fs, ∀ p ∈ f.places, IsAtt g p

/-! ## Tools -/

/-- a product of expressions -/
def exProd : ℕ → (ℕ → Ex0 X E) → Ex0 X E
  | 0, _ => Ex.con 1
  | n + 1, f => exProd n f * f n

theorem val0_exProd (Φ : IdxFmt F) (x : X) (W : ℕ → ℕ → F) (A : ℕ → ℕ → ℕ → E)
    (v b : ℕ) (f : ℕ → Ex0 X E) :
    ∀ n, Ex0.val Φ x W A (exProd n f) v b = ∏ k ∈ range n, Ex0.val Φ x W A (f k) v b
  | 0 => by simp [exProd]
  | n + 1 => by rw [exProd, val0_mul, val0_exProd Φ x W A v b f n, prod_range_succ]

theorem all_exProd {Q : Atom0 E → Prop} {f : ℕ → Ex0 X E} :
    ∀ n, (∀ k < n, Ex.All Q (f k)) → Ex.All Q (exProd n f)
  | 0, _ => All.con _
  | n + 1, h =>
    All.mul (all_exProd n fun k hk => h k (Nat.lt_succ_of_lt hk)) (h n (Nat.lt_succ_self n))

/-- the parts (h, i) of the inner index -/
def xH (y : ℕ) : ℕ := y / DA.T
def xI (y : ℕ) : ℕ := y % DA.T
theorem xI_lt (y : ℕ) : xI y < DA.T := Nat.mod_lt _ (by decide)
theorem xH_lt {y : ℕ} (hy : y < 2 ^ DA.lX) : xH y < DA.nG := Nat.div_lt_of_lt_mul (by
  have : (2 : ℕ) ^ DA.lX = DA.T * DA.nG := by decide
  omega)

theorem forall_hi (P : ℕ → ℕ → Prop) :
    (∀ y < 2 ^ DA.lX, P (xH y) (xI y)) ↔ ∀ h < DA.nG, ∀ i < DA.T, P h i := by
  constructor
  · intro H h hh i hi
    have h1 := AttSeg.Dim.div_step (a := h) (by decide : 0 < DA.T) hi
    have h2 := H (h * DA.T + i) (by
      have e : (2 : ℕ) ^ DA.lX = DA.nG * DA.T := by decide
      rw [e]
      nlinarith)
    unfold xH xI at h2
    rwa [h1.1, h1.2] at h2
  · exact fun H y hy => H _ (xH_lt hy) _ (xI_lt y)

theorem not_bOf_lt {l B : ℕ} (h : ¬ B < DA.nb * 2 ^ l) : ¬ bOf l B < DA.nb := fun hb =>
  h ((Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).1 hb)

/-- a form at a live vertex, 0 at a dead one -/
abbrev live0 (K : ℕ → ℕ → CForm E) : ℕ → CForm E := live DA.lX 0 K

variable (g : ℕ) (Φ : IdxFmt F)

/-! ## at1 -/

def famAt1 (k : ℕ) : Cb.Fam X E :=
  Ex1.fam (5 + DA.lX)
    (aff (live0 fun b y => cib g k b (xH y) (xI y)) *
      (aff (live0 fun b y => cib g k b (xH y) (xI y)) - Ex.con 1))

theorem val_at1 (k : ℕ) (x₀ : X) (W : ℕ → ℕ → F) (A : ℕ → ℕ → ℕ → E) (B : ℕ) :
    (famAt1 (X := X) g k).val Φ x₀ W A B =
      if bOf DA.lX B < DA.nb then
        AttSeg.idnVal DA (tAtt g A) (.at1 k (bOf DA.lX B) (xH (yOf DA.lX B)) (xI (yOf DA.lX B)))
      else 0 := by
  unfold famAt1
  rw [fam_val]
  simp only [val1_mul, val1_sub, val1_aff, val1_con, val_live]
  by_cases h : B < DA.nb * 2 ^ DA.lX
  · rw [if_pos h, if_pos (bOf_lt h), val_cib]
    rfl
  · rw [if_neg h, if_neg (not_bOf_lt h), zero_mul]

/-! ## at2 -/

/-- eq1(ib_k, bit_k(j)) as a form -/
def ceq (k b h i j : ℕ) : CForm E := if j.testBit k then cib g k b h i else cK 1 - cib g k b h i

theorem val_ceq (A : ℕ → ℕ → ℕ → E) (k b h i j : ℕ) :
    (ceq g k b h i j : CForm E).val A =
      AttSeg.eq1 (AttSeg.ibV (tAtt g A) k b h i) (AttSeg.bitR E k j) := by
  unfold ceq AttSeg.eq1 AttSeg.bitR
  by_cases hb : j.testBit k = true
  · rw [if_pos hb, if_pos hb, val_cib]
    ring
  · rw [if_neg hb, if_neg hb, val_sub, val_cK, val_cib]
    ring

/-- the summand of at2 at (n, j) -/
def F5 {R : Type} [CommRing R] (t : Raw → R) (b h i n j : ℕ) : R :=
  AttSeg.qryV t b h i n *
    (AttSeg.keyV t (DA.lamOf b) h j n *
      ∏ k ∈ range DA.lT, AttSeg.eq1 (AttSeg.ibV t k b h i) (AttSeg.bitR R k j))

theorem idn_at2_eq {R : Type} [CommRing R] (t : Raw → R) (b h i : ℕ) :
    AttSeg.idnVal DA t (.at2 b h i) =
      AttSeg.mxV t b h i - ∑ n ∈ range DA.ch, ∑ j ∈ range DA.T, F5 t b h i n j := by
  show AttSeg.mxV t b h i - ∑ n ∈ range DA.ch, AttSeg.qryV t b h i n * AttSeg.sel DA t b h i n = _
  unfold AttSeg.sel F5
  simp only [mul_sum]

/-- the factors at (vertex B, (n, j)) -/
def q5 (B J : ℕ) : CForm E :=
  if B < DA.nb * 2 ^ DA.lX then
    cqry g (bOf DA.lX B) (xH (yOf DA.lX B)) (xI (yOf DA.lX B)) (bOf DA.lT J)
  else cK 0
def k5 (B J : ℕ) : CForm E :=
  if B < DA.nb * 2 ^ DA.lX then
    ckey g (DA.lamOf (bOf DA.lX B)) (xH (yOf DA.lX B)) (yOf DA.lT J) (bOf DA.lT J)
  else cK 0
def e5 (k B J : ℕ) : CForm E :=
  if B < DA.nb * 2 ^ DA.lX then
    ceq g k (bOf DA.lX B) (xH (yOf DA.lX B)) (xI (yOf DA.lX B)) (yOf DA.lT J)
  else cK 0

def exAt2 : Ex1 X E :=
  aff (live0 fun b y => cmx g b (xH y) (xI y)) -
    sumA (5 + DA.lX) (DA.ln + DA.lT)
      (aff0 (fun B' => q5 g (bOf (DA.ln + DA.lT) B') (yOf (DA.ln + DA.lT) B')) *
        aff0 (fun B' => k5 g (bOf (DA.ln + DA.lT) B') (yOf (DA.ln + DA.lT) B')) *
        exProd DA.lT fun k =>
          aff0 fun B' => e5 g k (bOf (DA.ln + DA.lT) B') (yOf (DA.ln + DA.lT) B'))

def famAt2 : Cb.Fam X E := Ex1.fam (5 + DA.lX) (exAt2 g)

theorem val_at2 (x₀ : X) (W : ℕ → ℕ → F) (A : ℕ → ℕ → ℕ → E) (B : ℕ) :
    (famAt2 (X := X) g).val Φ x₀ W A B =
      if bOf DA.lX B < DA.nb then
        AttSeg.idnVal DA (tAtt g A) (.at2 (bOf DA.lX B) (xH (yOf DA.lX B)) (xI (yOf DA.lX B)))
      else 0 := by
  unfold famAt2
  rw [fam_val]
  unfold exAt2
  simp only [val1_sub, val1_aff, val1_sumA, val0_mul, val0_aff, val0_exProd, val_live]
  rw [sum_dec (DA.ln + DA.lT) B fun B J =>
      (q5 g B J).val A * (k5 g B J).val A * ∏ k ∈ range DA.lT, (e5 g k B J).val A]
  by_cases h : B < DA.nb * 2 ^ DA.lX
  · rw [if_pos h, if_pos (bOf_lt h), val_cmx]
    have e : ∀ J, (q5 g B J).val A * (k5 g B J).val A * ∏ k ∈ range DA.lT, (e5 g k B J).val A =
        F5 (tAtt g A) (bOf DA.lX B) (xH (yOf DA.lX B)) (xI (yOf DA.lX B))
          (bOf DA.lT J) (yOf DA.lT J) := fun J => by
      unfold q5 k5 e5 F5
      simp only [if_pos h, val_cqry, val_ckey, val_ceq]
      exact mul_assoc _ _ _
    have e2 : (2 : ℕ) ^ (DA.ln + DA.lT) = DA.ch * 2 ^ DA.lT := pow_add 2 _ _
    have hT : (2 : ℕ) ^ DA.lT = DA.T := by decide
    rw [sum_congr rfl fun J _ => e J, e2,
      sum_pair DA.lT (F5 (tAtt g A) (bOf DA.lX B) (xH (yOf DA.lX B)) (xI (yOf DA.lX B))) DA.ch,
      idn_at2_eq, hT]
  · rw [if_neg h, if_neg (not_bOf_lt h)]
    have e : ∀ J, (q5 g B J : CForm E).val A * (k5 g B J).val A *
          ∏ k ∈ range DA.lT, (e5 g k B J).val A = 0 := fun J => by
      unfold q5
      rw [if_neg h, val_cK, zero_mul, zero_mul]
    simp only [e, sum_const_zero, sub_zero]

/-! ## at3 -/

def w6 (B j : ℕ) : CForm E :=
  if B < DA.nb * 2 ^ DA.lX ∧ j < DA.B * (xI (yOf DA.lX B) / DA.B + 1) then
    cwtIJ g (bOf DA.lX B) (xH (yOf DA.lX B)) (xI (yOf DA.lX B)) j
  else cK 0

def famAt3 : Cb.Fam X E :=
  Ex1.fam (5 + DA.lX)
    (aff (live0 fun b y => cden g b (xH y) (xI y)) -
      sumA (5 + DA.lX) DA.lT (aff0 fun B' => w6 g (bOf DA.lT B') (yOf DA.lT B')))

theorem val_at3 (x₀ : X) (W : ℕ → ℕ → F) (A : ℕ → ℕ → ℕ → E) (B : ℕ) :
    (famAt3 (X := X) g).val Φ x₀ W A B =
      if bOf DA.lX B < DA.nb then
        AttSeg.idnVal DA (tAtt g A) (.at3 (bOf DA.lX B) (xH (yOf DA.lX B)) (xI (yOf DA.lX B)))
      else 0 := by
  unfold famAt3
  rw [fam_val]
  simp only [val1_sub, val1_aff, val1_sumA, val0_aff, val_live]
  rw [sum_dec DA.lT B fun B j => (w6 g B j).val A]
  by_cases h : B < DA.nb * 2 ^ DA.lX
  · rw [if_pos h, if_pos (bOf_lt h), val_cden]
    have e : ∀ j, (w6 g B j).val A =
        if j < DA.B * (xI (yOf DA.lX B) / DA.B + 1) then
          AttSeg.wtIJ DA (tAtt g A) (bOf DA.lX B) (xH (yOf DA.lX B)) (xI (yOf DA.lX B)) j * 1
        else 0 := fun j => by
      unfold w6
      by_cases hj : j < DA.B * (xI (yOf DA.lX B) / DA.B + 1)
      · rw [if_pos ⟨h, hj⟩, if_pos hj, val_cwtIJ, mul_one]
      · rw [if_neg fun hh => hj hh.2, if_neg hj, val_cK]
    simp only [e]
    have hle : DA.B * (xI (yOf DA.lX B) / DA.B + 1) ≤ 2 ^ DA.lT := by
      have h1 : xI (yOf DA.lX B) / DA.B < DA.nBlk :=
        Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact xI_lt _)
      have h2 : (2 : ℕ) ^ DA.lT = DA.B * DA.nBlk := by decide
      rw [h2]
      exact Nat.mul_le_mul_left _ h1
    rw [sum_range_ite hle]
    show _ = AttSeg.denV (tAtt g A) _ _ _ - AttSeg.rowSum DA (tAtt g A) (fun _ => 1) _ _ _
    rw [AttSeg.rowSum_eq DA (tAtt g A) _ _ _ (xI_lt _)]
  · rw [if_neg h, if_neg (not_bOf_lt h)]
    have e : ∀ j, (w6 g B j : CForm E).val A = 0 := fun j => by
      unfold w6
      rw [if_neg fun hh => h hh.1, val_cK]
    simp only [e, sum_const_zero, sub_zero]

/-! ## All identities -/

/-- The families of identities. -/
def attIdnFams : List (Cb.Fam X E) := (List.range DA.lT).map (famAt1 g) ++ [famAt2 g, famAt3 g]

/-- from a value lemma to the condition on the cube -/
theorem zero_iff (f : ℕ → E) (K : ℕ → ℕ → ℕ → E)
    (hf : ∀ B, f B =
      if bOf DA.lX B < DA.nb then K (bOf DA.lX B) (xH (yOf DA.lX B)) (xI (yOf DA.lX B)) else 0) :
    (∀ B < 2 ^ (5 + DA.lX), f B = 0) ↔ ∀ b < DA.nb, ∀ h < DA.nG, ∀ i < DA.T, K b h i = 0 := by
  have h1 := iff_of_val (a := 5) (l := DA.lX) (nb := DA.nb) (by decide) f
    (fun b y => K b (xH y) (xI y)) 0 hf {0} rfl
  simp only [Set.mem_singleton_iff] at h1
  rw [h1]
  exact forall_congr' fun b => forall_congr' fun _ => forall_hi fun h i => K b h i = 0

theorem attIdn_ok : AttIdnOK Φ g (attIdnFams (X := X) (E := E) g) where
  iff := fun x₀ W A => by
    have h1 := fun k =>
      zero_iff _ (fun b h i => AttSeg.idnVal DA (tAtt g A) (.at1 k b h i))
        (val_at1 (X := X) g Φ k x₀ W A)
    have h2 := zero_iff _ (fun b h i => AttSeg.idnVal DA (tAtt g A) (.at2 b h i))
      (val_at2 (X := X) g Φ x₀ W A)
    have h3 := zero_iff _ (fun b h i => AttSeg.idnVal DA (tAtt g A) (.at3 b h i))
      (val_at3 (X := X) g Φ x₀ W A)
    constructor
    · intro H j hj
      cases j with
      | at1 k b h i =>
        exact (h1 k).1 (H _ (List.mem_append_left _ (List.mem_map_of_mem (List.mem_range.2 hj.1))))
          b hj.2.1 h hj.2.2.1 i hj.2.2.2
      | at2 b h i =>
        exact h2.1 (H _ (List.mem_append_right _ (List.mem_cons_self))) b hj.1 h hj.2.1 i hj.2.2
      | at3 b h i =>
        exact h3.1 (H _ (List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self)))
          b hj.1 h hj.2.1 i hj.2.2
    · intro H f hf
      rcases List.mem_append.1 hf with hf | hf
      · obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hf
        exact (h1 k).2 fun b hb h hh i hi => H _ ⟨List.mem_range.1 hk, hb, hh, hi⟩
      · rcases List.mem_cons.1 hf with rfl | hf
        · exact h2.2 fun b hb h hh i hi => H _ ⟨hb, hh, hi⟩
        · obtain rfl := List.mem_singleton.1 hf
          exact h3.2 fun b hb h hh i hi => H _ ⟨hb, hh, hi⟩
  wf := fun f hf => by
    rcases List.mem_append.1 hf with hf | hf
    · obtain ⟨k, -, rfl⟩ := List.mem_map.1 hf
      exact fam_wf Φ (All.mul (WF1.aff Φ _ _) (All.sub (WF1.aff Φ _ _) (All.con _)))
    · rcases List.mem_cons.1 hf with rfl | hf
      · exact fam_wf Φ
          (All.sub (WF1.aff Φ _ _)
            (WF1.sumA Φ
              (All.mul (All.mul (WF0.aff Φ _ _) (WF0.aff Φ _ _))
                (all_exProd _ fun _ _ => WF0.aff Φ _ _))))
      · obtain rfl := List.mem_singleton.1 hf
        exact fam_wf Φ (All.sub (WF1.aff Φ _ _) (WF1.sumA Φ (WF0.aff Φ _ _)))
  places := fun f hf => by
    have hT : (2 : ℕ) ^ DA.lT = DA.T := by decide
    have hn : ∀ J, J < 2 ^ (DA.ln + DA.lT) → bOf DA.lT J < DA.ch := fun J hJ => Nat.div_lt_of_lt_mul (by
      have e : (2 : ℕ) ^ (DA.ln + DA.lT) = 2 ^ DA.lT * DA.ch := by rw [pow_add, Nat.mul_comm]; rfl
      omega)
    rcases List.mem_append.1 hf with hf | hf
    · obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hf
      have hib : ∀ B, InAtt g (live0 (fun b y => cib g k b (xH y) (xI y)) B : CForm E) := fun B =>
        pl_live (fun b hb y hy => inAtt_cib g (List.mem_range.1 hk) hb (xH_lt hy) (xI_lt y)) B
      exact fam_places
        (All.mul (Pl1.aff fun B _ => hib B) (All.sub (Pl1.aff fun B _ => hib B) (All.con _)))
    · rcases List.mem_cons.1 hf with rfl | hf
      · refine fam_places
          (All.sub
            (Pl1.aff fun B _ => pl_live (fun b hb y hy => inAtt_cmx g hb (xH_lt hy) (xI_lt y)) B)
            (Pl1.sumA (All.mul
                (All.mul (Pl0.aff fun B' _ =>
                    AllPl.ite (fun hh =>
                        inAtt_cqry g (bOf_lt hh) (xH_lt (yOf_lt _ _)) (xI_lt _) (hn _ (yOf_lt _ _)))
                      fun _ => AllPl.cK _)
                  (Pl0.aff fun B' _ =>
                    AllPl.ite (fun hh =>
                        inAtt_ckey g (lam_lt (bOf_lt hh)) (xH_lt (yOf_lt _ _))
                          (hT ▸ yOf_lt _ _) (hn _ (yOf_lt _ _)))
                      fun _ => AllPl.cK _))
                (all_exProd _ fun k hk =>
                  Pl0.aff fun B' _ =>
                    AllPl.ite (fun hh =>
                        AllPl.ite
                          (fun _ => inAtt_cib g hk (bOf_lt hh) (xH_lt (yOf_lt _ _)) (xI_lt _))
                          fun _ =>
                            (AllPl.cK _).sub
                              (inAtt_cib g hk (bOf_lt hh) (xH_lt (yOf_lt _ _)) (xI_lt _)))
                      fun _ => AllPl.cK _))))
      · obtain rfl := List.mem_singleton.1 hf
        exact fam_places
          (All.sub
            (Pl1.aff fun B _ => pl_live (fun b hb y hy => inAtt_cden g hb (xH_lt hy) (xI_lt y)) B)
            (Pl1.sumA (Pl0.aff fun B' _ =>
                AllPl.ite (fun hh => inAtt_cwtIJ g (bOf_lt hh.1) (xH_lt (yOf_lt _ _)) (xI_lt _))
                  fun _ => AllPl.cK _)))

end Cm.Seg
