-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Policy/Seg/HeadAsm.lean

From the values of the families of `segHeadPol s pol` at vertices to the statement
`Spec.headPol_holds_int` of Policy/Seg/Head.lean.

Theorems with their proofs, after Cm/TargetSegHeadAsm.lean and Cm/SegHeadAsm.lean, the plain head's
files. The values of the families are hypotheses here (the statements of Policy/Seg/HeadSteps.lean);
Policy/Seg/HeadProofs.lean puts their proofs in.
`SameMain t t'`: two families of cells agree at the names that this head reads. `keyM_same` to
`sB3_same`: the keys, the 17 identities and the ledger's four clauses read these names only.
`segKey_tab`: the segment's key is the image of an entry of the segment's table if and only if the
relation's key is the image of an entry of the relation's table; the two differ at HD0 alone.
`headPol_holds_of`: `Spec.headPol_holds` from the four statements on values.
`headPol_holds_int_of`: `Spec.headPol_holds_int` from `Spec.headPol_holds`.
A lemma with M before `_same` is this head's form of the plain head's lemma without the M.

Limits: nothing on the request's form, on bounds of cells, or on protocols.
-/
import Policy.Seg.HeadSteps
import Policy.Rel.LedgerHeadInt
import Cm.TargetSegHeadAsm

set_option autoImplicit false
set_option linter.unusedSectionVars false

attribute [-instance] Inst.Model.Scl.ref

namespace Policy
open Cb Inst.Model Finset Cm.Seg Cm.Seg.Ex

/-! ## 1. Keys, identities and clauses read the valid names only -/

section Same
variable {K : Type} [CommRing K]

/-- two families of cells agree at the names that the head with the ledger reads -/
structure SameMain (t t' : Head.Cells K) : Prop where
  hf : ∀ φ < Head.nFeat .hf, ∀ i < Head.nT, t.hf φ i = t'.hf φ i
  hd : ∀ φ < Head.nFeat .hd, ∀ i < Head.nT, t.hd φ i = t'.hd φ i
  hr : ∀ φ < Head.nFeat .hr, ∀ i < Head.nT, t.hr φ i = t'.hr φ i
  x : ∀ φ < Head.nFeat .x, ∀ i < Head.nT, t.x φ i = t'.x φ i

theorem b256M_same {D D' : ℕ → K} (hD : ∀ n < 120, D n = D' n) {a n : ℕ} (han : a + n ≤ 120) :
    Ledger.b256 D a n = Ledger.b256 D' a n :=
  sum_congr rfl fun l hl => by rw [hD (a + l) (by have := mem_range.1 hl; omega)]

variable {t t' : Head.Cells K} (h : SameMain t t')
include h

/-- Cells that agree at the names that this head reads agree at those that the plain head reads. -/
theorem SameMain.plain : Same t t' :=
  ⟨fun φ hφ => h.hf φ (lt_trans hφ (by show (626624 : ℕ) < 1232768; norm_num)), h.hd,
    fun φ hφ => h.hr φ (lt_trans hφ (by show (99 : ℕ) < 120; norm_num)), h.x⟩

theorem ex_same {v i : ℕ} (hv : v < Head.nV) (hi : i < Head.nT) :
    Head.ex t v i = Head.ex t' v i := by
  unfold Head.ex
  rw [rd_same (m := 3) fun l hl =>
    h.hf (Head.fEx l v) (by simp only [Head.fEx, Head.nFeat, Head.nV] at *; omega) i hi]

theorem DvM_same {n i : ℕ} (hn : n < 120) (hi : i < Head.nT) :
    Head.Dv t n i = Head.Dv t' n i := by
  unfold Head.Dv
  rw [h.hr n hn i hi]

theorem hid_same {i : ℕ} (hi : i < Head.nT) {a n : ℕ} (han : a + n ≤ 120) :
    Ledger.b256 (fun m => Head.Dv t m i) a n = Ledger.b256 (fun m => Head.Dv t' m i) a n :=
  b256M_same (fun _ hm => DvM_same h hm hi) han

theorem hidC_same {i : ℕ} (hi : i < Head.nT) : Head.hidC t i = Head.hidC t' i :=
  hid_same h hi (a := 99) (n := 5) (by norm_num)
theorem hidB_same {i : ℕ} (hi : i < Head.nT) : Head.hidB t i = Head.hidB t' i :=
  hid_same h hi (a := 104) (n := 1) (by norm_num)
theorem hidU_same {i : ℕ} (hi : i < Head.nT) : Head.hidU t i = Head.hidU t' i :=
  hid_same h hi (a := 105) (n := 5) (by norm_num)
theorem hidK_same {i : ℕ} (hi : i < Head.nT) : Head.hidK t i = Head.hidK t' i :=
  hid_same h hi (a := 110) (n := 5) (by norm_num)
theorem hidZ_same {i : ℕ} (hi : i < Head.nT) : Head.hidZ t i = Head.hidZ t' i :=
  hid_same h hi (a := 115) (n := 2) (by norm_num)
theorem hidS_same {i : ℕ} (hi : i < Head.nT) : Head.hidS t i = Head.hidS t' i :=
  hid_same h hi (a := 117) (n := 3) (by norm_num)

theorem K1_same (y : Head.Req) {v i : ℕ} (hv : v < Head.nV) (hi : i < Head.nT) :
    Head.K1 t y v i = Head.K1 t' y v i := by
  unfold Head.K1
  rw [d1_same h.plain hv hi]

theorem K2_same (y : Head.Req) {v i : ℕ} (hv : v < Head.nV) (hi : i < Head.nT) :
    Head.K2 t y v i = Head.K2 t' y v i := by
  unfold Head.K2
  rw [d2_same h.plain hv hi]

theorem mg_same (H : ℕ → ℕ → K) (y : Head.Req) (v : ℕ) {i : ℕ} (hi : i < Head.nT) :
    Head.mg t H y v i = Head.mg t' H y v i := by
  unfold Head.mg
  rw [lg_same h.plain H hi (y.win i), lg_same h.plain H hi v, hidC_same h hi, hidB_same h hi]

/-- the keys read the valid names only: if `SameMain t t'`, a < `Head.len f` and i < `Head.nT`, then
`LedgerHead.key` is the same at t and at t' -/
theorem keyM_same (np : NormPar) (H : ℕ → ℕ → K) (y : Head.Req) (f : Head.Fam) {a i : ℕ}
    (ha : a < Head.len f) (hi : i < Head.nT) :
    LedgerHead.key np t H y f a i = LedgerHead.key np t' H y f a i := by
  have hp : Same t t' := h.plain
  have hD : ∀ n < 99, Head.Dv t n i = Head.Dv t' n i := fun n hn => Dv_same hp hn hi
  cases f
  · show Head.xv t a i * Ledger.R (fun n => Head.Dv t n i) + 2 ^ (np.K - 1) -
        2 ^ np.K * Head.nw t a i - 2 ^ 16 * Head.rn t a i =
      Head.xv t' a i * Ledger.R (fun n => Head.Dv t' n i) + 2 ^ (np.K - 1) -
        2 ^ np.K * Head.nw t' a i - 2 ^ 16 * Head.rn t' a i
    rw [xv_same hp ha hi, R_same hD, nw_same hp ha hi, rn_same hp ha hi]
  · show _ * Head.rn t a i = _ * Head.rn t' a i
    rw [rn_same hp ha hi]
  · show Head.mg t H y a i - 2 ^ 8 * Head.K1 t y a i - Head.K2 t y a i =
      Head.mg t' H y a i - 2 ^ 8 * Head.K1 t' y a i - Head.K2 t' y a i
    rw [mg_same h H y a hi, K1_same h y ha hi, K2_same h y ha hi]
  · exact K1_same h y ha hi
  · show _ * Head.Dv t a i = _ * Head.Dv t' a i
    rw [DvM_same h ha hi]
  · exact K2_same h y ha hi
  · have hv : a < Head.nV := lt_trans ha (by show (131072 : ℕ) < 202048; norm_num)
    show Head.K1 t y a i + 2 ^ 16 * Head.ex t a i = Head.K1 t' y a i + 2 ^ 16 * Head.ex t' a i
    rw [K1_same h y hv hi, ex_same h hv hi]
  · have hv : 131072 + a < Head.nV := by
      have h1 : a < 70976 := ha
      show 131072 + a < 202048
      omega
    show Head.K1 t y (131072 + a) i + 2 ^ 16 * Head.ex t (131072 + a) i =
      Head.K1 t' y (131072 + a) i + 2 ^ 16 * Head.ex t' (131072 + a) i
    rw [K1_same h y hv hi, ex_same h hv hi]
  · show (Head.nw t a i + 2 ^ 15) + 2 ^ 28 * (Head.nrm t a i + 2 ^ 11) =
      (Head.nw t' a i + 2 ^ 15) + 2 ^ 28 * (Head.nrm t' a i + 2 ^ 11)
    rw [nw_same hp ha hi, nrm_same hp ha hi]

theorem idnM_same (np : NormPar) {i k : ℕ} (hi : i < Head.nT) (hk : k < 17) :
    Head.N.idn np t i k = Head.N.idn np t' i k :=
  idn_same h.plain np hi hk

theorem dB4_same (y : Head.Req) {i : ℕ} (hi : i < Head.nT) :
    Head.dB4 t y i = Head.dB4 t' y i := by
  unfold Head.dB4
  rw [hidC_same h hi, hidK_same h hi]

theorem dZ_same (y : Head.Req) {i : ℕ} (hi : i < Head.nT) : Head.dZ t y i = Head.dZ t' y i := by
  have e : ∑ v ∈ range Head.nV, Head.ex t v i = ∑ v ∈ range Head.nV, Head.ex t' v i :=
    sum_congr rfl fun v hv => ex_same h (mem_range.1 hv) hi
  unfold Head.dZ
  rw [hidS_same h hi, e]

theorem sB2_same (y : Head.Req) : Head.sB2 t y = Head.sB2 t' y := by
  have e : ∑ i ∈ range Head.nT,
        (y.rhoC i : K) * (Head.hidC t i + (y.pol.C : K) * Head.hidB t i + Head.hidU t i) =
      ∑ i ∈ range Head.nT,
        (y.rhoC i : K) * (Head.hidC t' i + (y.pol.C : K) * Head.hidB t' i + Head.hidU t' i) :=
    sum_congr rfl fun i hi => by
      rw [hidC_same h (mem_range.1 hi), hidB_same h (mem_range.1 hi), hidU_same h (mem_range.1 hi)]
  unfold Head.sB2
  rw [e]

theorem sB3_same (y : Head.Req) : Head.sB3 t y = Head.sB3 t' y := by
  have e : ∑ i ∈ range Head.nT, (y.rhoC i : K) * (Head.hidB t i + Head.hidZ t i) =
      ∑ i ∈ range Head.nT, (y.rhoC i : K) * (Head.hidB t' i + Head.hidZ t' i) :=
    sum_congr rfl fun i hi => by
      rw [hidB_same h (mem_range.1 hi), hidZ_same h (mem_range.1 hi)]
  unfold Head.sB3
  rw [e]

end Same

/-! ## 2. The segment's tables and the relation's -/

theorem two_ne_GlE : (2 : Gl.E) ≠ 0 := by
  simpa using Code.natCast_ne_zero_of_lt Gl.E Gl.p (n := 2) (by norm_num) (by decide +kernel)

theorem mem_allFamPol (f : Head.Fam) : f ∈ allFamPol := by cases f <;> simp [allFamPol]

theorem rowsPol_eq (f : Head.Fam) : (Head.tableOf f).rows = 2 ^ tabLogPol f := by cases f <;> rfl

theorem lenPol_le (f : Head.Fam) : Head.len f ≤ 2 ^ vxPol f := by cases f <;> decide

/-- The segment's key is the image of an entry of the segment's table if and only if the relation's
key is the image of an entry of the relation's table. -/
theorem segKey_tab (np : NormPar) (t : Head.Cells Gl.E) (H : ℕ → ℕ → Gl.E) (y : Head.Req)
    (f : Head.Fam) (a i : ℕ) :
    (∃ r < (Head.tableOf f).rows,
      segKey np t H y f a i = algebraMap Gl.F Gl.E (((Head.tableOf f).row r : ℤ) : Gl.F)) ↔
    ∃ r < (LedgerHead.tableOf f).rows,
      LedgerHead.key np t H y f a i =
        algebraMap Gl.F Gl.E (((LedgerHead.tableOf f).row r : ℤ) : Gl.F) := by
  cases f
  case HD0 =>
    show (∃ r : ℕ, r < 2 ^ 16 ∧
        ((2 : Gl.E) ^ 23)⁻¹ * LedgerHead.key np t H y .HD0 a i =
          algebraMap Gl.F Gl.E (((r : ℕ) : ℤ) : Gl.F)) ↔
      ∃ r : ℕ, r < 2 ^ 16 ∧
        LedgerHead.key np t H y .HD0 a i =
          algebraMap Gl.F Gl.E ((2 ^ 23 * ((r : ℕ) : ℤ) : ℤ) : Gl.F)
    refine exists_congr fun r => and_congr_right fun _ => ?_
    rw [inv_mul_eq_iff_eq_mul₀ (pow_ne_zero 23 two_ne_GlE), Int.cast_mul, map_mul, Int.cast_pow,
      Int.cast_ofNat, map_pow, map_ofNat]
  all_goals exact Iff.rfl

theorem mem_ledgerIdn_iff (pol : AcceptancePolicy) (f : Fam XI Gl.E) :
    f ∈ ledgerIdn pol ↔ f = jB4Fam pol ∨ f = jZFam ∨ f = sB2Fam pol ∨ f = sB3Fam pol := by
  simp [ledgerIdn]

/-! ## 3. The assembly -/

/-- `Spec.headPol_holds` is true if the four propositions on the families' values are true. -/
theorem headPol_holds_of (hl : Spec.headPol_key_live) (hd : Spec.headPol_key_dead)
    (hn : Spec.headPol_idn_val) (hL : Spec.headPol_led_val) : Spec.headPol_holds := by
  intro s pol x W A
  obtain ⟨vJ, v2, v3⟩ := hL pol x W A
  constructor
  · rintro ⟨hI, hK⟩
    have hI' : ∀ f ∈ ledgerIdn pol, ∀ b < 2 ^ f.v, f.val TS.fmtRef x W A b = 0 := fun f hf =>
      hI f (List.mem_append_right _ hf)
    refine ⟨fun f a i ha hi => ?_, fun i hi k hk => ?_, fun i hi => ⟨?_, ?_⟩, ?_, ?_⟩
    · obtain ⟨u, hu, e⟩ := hK (keyFamPol s.nf f, keyTabPol f)
        (List.mem_map.2 ⟨f, mem_allFamPol f, rfl⟩)
        (vOf a i) (vOf_lt (lt_of_lt_of_le ha (lenPol_le f)) hi)
      obtain ⟨r, hr, rfl⟩ := (mem_tabOf_iff (rowsPol_eq f) u).1 hu
      exact (segKey_tab s.nf _ _ _ f a i).1
        ⟨r, hr, (hl s.nf pol f x W A a i ha hi).symm.trans e⟩
    · rw [← hn s.nf k x W A i hi]
      exact hI (TS.idnFam s.nf k)
        (List.mem_append_left _ (List.mem_map.2 ⟨k, List.mem_range.2 hk, rfl⟩)) i hi
    · rw [← (vJ i hi).1]
      exact hI' _ ((mem_ledgerIdn_iff pol _).2 (Or.inl rfl)) i hi
    · rw [← (vJ i hi).2]
      exact hI' _ ((mem_ledgerIdn_iff pol _).2 (Or.inr (Or.inl rfl))) i hi
    · rw [← v2]
      exact hI' _ ((mem_ledgerIdn_iff pol _).2 (Or.inr (Or.inr (Or.inl rfl)))) 0 (Nat.two_pow_pos _)
    · rw [← v3]
      exact hI' _ ((mem_ledgerIdn_iff pol _).2 (Or.inr (Or.inr (Or.inr rfl)))) 0 (Nat.two_pow_pos _)
  · rintro ⟨hK, hI, hJ, h2, h3⟩
    refine ⟨fun f hf b hb => ?_, fun k hk b hb => ?_⟩
    · have hf' : f ∈ (List.range 17).map (TS.idnFam s.nf) ++ ledgerIdn pol := hf
      rcases List.mem_append.1 hf' with hf1 | hf1
      · obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hf1
        rw [hn s.nf k x W A b hb]
        exact hI b hb k (List.mem_range.1 hk)
      · rcases (mem_ledgerIdn_iff pol f).1 hf1 with rfl | rfl | rfl | rfl
        · rw [(vJ b hb).1]
          exact (hJ b hb).1
        · rw [(vJ b hb).2]
          exact (hJ b hb).2
        · obtain rfl : b = 0 := Nat.lt_one_iff.1 hb
          rw [v2]
          exact h2
        · obtain rfl : b = 0 := Nat.lt_one_iff.1 hb
          rw [v3]
          exact h3
    · obtain ⟨f, _, rfl⟩ := List.mem_map.1 hk
      have hb' : b < 2 ^ (vxPol f + 10) := hb
      by_cases hlv : va (vxPol f) b < Head.len f
      · obtain ⟨r, hr, e⟩ := (segKey_tab s.nf _ _ _ f _ _).2 (hK f _ _ hlv (vi_lt b))
        refine ⟨_, (mem_tabOf_iff (rowsPol_eq f) _).2 ⟨r, hr, rfl⟩, ?_⟩
        rw [← e, ← hl s.nf pol f x W A _ _ hlv (vi_lt b), vOf_va_vi hb']
      · exact hd s.nf f x W A b hb' (not_lt.1 hlv)

/-! ## 4. Integer matrices -/

/-- At integer matrices M that hold the integer cells t (`ReadsAtMain t M`), and an integer index
matrix, the segment's conditions are `HeadCl` at t, if `Spec.headPol_holds` is true. -/
theorem headPol_holds_int_of (hA : Spec.headPol_holds) : Spec.headPol_holds_int := by
  intro s pol x Wz M t hR
  have ι_inj : Function.Injective (algebraMap Gl.F Gl.E) := (algebraMap Gl.F Gl.E).injective
  have hS : SameMain ((t.cast Gl.F).map (algebraMap Gl.F Gl.E))
      (TS.tH (Partition.castM (E := Gl.E) M)) :=
    ⟨fun φ hφ i hi => by
        show algebraMap Gl.F Gl.E ((t.hf φ i : ℤ) : Gl.F) =
          ((at' M (Name.hf φ i).place : ℤ) : Gl.E)
        rw [hR.hf φ hφ i hi, map_intCast],
      fun φ hφ i hi => by
        show algebraMap Gl.F Gl.E ((t.hd φ i : ℤ) : Gl.F) =
          ((at' M (Name.hd φ i).place : ℤ) : Gl.E)
        rw [hR.hd φ hφ i hi, map_intCast],
      fun φ hφ i hi => by
        show algebraMap Gl.F Gl.E ((t.hr φ i : ℤ) : Gl.F) =
          ((at' M (Name.hr φ i).place : ℤ) : Gl.E)
        rw [hR.hr φ hφ i hi, map_intCast],
      fun φ hφ i hi => by
        show algebraMap Gl.F Gl.E ((t.x φ i : ℤ) : Gl.F) =
          ((at' M (ownX φ i).place : ℤ) : Gl.E)
        rw [hR.x φ hφ i hi, map_intCast]⟩
  have hH : TS.HW (fun y c => ((Wz y c : ℤ) : Gl.F)) =
      fun j v => algebraMap Gl.F Gl.E (Cm.TP.castH Gl.p Wz j v) := by
    funext j v
    show algebraMap Gl.F Gl.E _ = _
    congr 1
    exact TS.h_int Wz j v
  have eK : ∀ f a i, a < Head.len f → i < Head.nT →
      LedgerHead.key s.nf (TS.tH (Partition.castM (E := Gl.E) M))
          (TS.HW fun y c => ((Wz y c : ℤ) : Gl.F)) (Head.Req.of pol x) f a i =
        algebraMap Gl.F Gl.E
          (LedgerHead.key s.nf (t.cast Gl.F) (Cm.TP.castH Gl.p Wz) (Head.Req.of pol x)
            f a i) := fun f a i ha hi => by
    rw [LedgerHead.map_key (algebraMap Gl.F Gl.E) s.nf (t.cast Gl.F)
          (Cm.TP.castH Gl.p Wz) (Head.Req.of pol x) f a i, hH]
    exact (keyM_same hS s.nf _ _ f ha hi).symm
  have eI : ∀ i k, i < Head.nT → k < 17 →
      Head.N.idn s.nf (TS.tH (Partition.castM (E := Gl.E) M)) i k =
        algebraMap Gl.F Gl.E (Head.N.idn s.nf (t.cast Gl.F) i k) := fun i k hi hk => by
    rw [Head.N.map_idn' (algebraMap Gl.F Gl.E) s.nf (t.cast Gl.F) i k]
    exact (idnM_same hS s.nf hi hk).symm
  have e4 : ∀ i, i < Head.nT →
      Head.dB4 (TS.tH (Partition.castM (E := Gl.E) M)) (Head.Req.of pol x) i =
        algebraMap Gl.F Gl.E (Head.dB4 (t.cast Gl.F) (Head.Req.of pol x) i) := fun i hi => by
    rw [Head.map_dB4 (algebraMap Gl.F Gl.E) (t.cast Gl.F) (Head.Req.of pol x) i]
    exact (dB4_same hS _ hi).symm
  have eZ : ∀ i, i < Head.nT →
      Head.dZ (TS.tH (Partition.castM (E := Gl.E) M)) (Head.Req.of pol x) i =
        algebraMap Gl.F Gl.E (Head.dZ (t.cast Gl.F) (Head.Req.of pol x) i) := fun i hi => by
    rw [Head.map_dZ (algebraMap Gl.F Gl.E) (t.cast Gl.F) (Head.Req.of pol x) i]
    exact (dZ_same hS _ hi).symm
  have e2 : Head.sB2 (TS.tH (Partition.castM (E := Gl.E) M)) (Head.Req.of pol x) =
      algebraMap Gl.F Gl.E (Head.sB2 (t.cast Gl.F) (Head.Req.of pol x)) := by
    rw [Head.map_sB2 (algebraMap Gl.F Gl.E) (t.cast Gl.F) (Head.Req.of pol x)]
    exact (sB2_same hS _).symm
  have e3 : Head.sB3 (TS.tH (Partition.castM (E := Gl.E) M)) (Head.Req.of pol x) =
      algebraMap Gl.F Gl.E (Head.sB3 (t.cast Gl.F) (Head.Req.of pol x)) := by
    rw [Head.map_sB3 (algebraMap Gl.F Gl.E) (t.cast Gl.F) (Head.Req.of pol x)]
    exact (sB3_same hS _).symm
  rw [hA s pol x _ _]
  unfold HeadCl
  constructor
  · rintro ⟨hK, hI, hJ, h2, h3⟩
    refine ⟨fun f a i ha hi => ?_, fun i hi k hk => ?_, fun i hi => ⟨?_, ?_⟩, ?_, ?_⟩
    · obtain ⟨u, hu, e⟩ := hK f a i ha hi
      rw [eK f a i ha hi] at e
      exact ⟨u, hu, ι_inj e⟩
    · have e := hI i hi k hk
      rw [eI i k hi hk] at e
      exact (map_eq_zero _).1 e
    · have e := (hJ i hi).1
      rw [e4 i hi] at e
      exact (map_eq_zero _).1 e
    · have e := (hJ i hi).2
      rw [eZ i hi] at e
      exact (map_eq_zero _).1 e
    · rw [e2] at h2
      exact (map_eq_zero _).1 h2
    · rw [e3] at h3
      exact (map_eq_zero _).1 h3
  · rintro ⟨hK, hI, hJ, h2, h3⟩
    refine ⟨fun f a i ha hi => ?_, fun i hi k hk => ?_, fun i hi => ⟨?_, ?_⟩, ?_, ?_⟩
    · obtain ⟨u, hu, e⟩ := hK f a i ha hi
      exact ⟨u, hu, by rw [eK f a i ha hi, e]⟩
    · rw [eI i k hi hk, hI i hi k hk, map_zero]
    · rw [e4 i hi, (hJ i hi).1, map_zero]
    · rw [eZ i hi, (hJ i hi).2, map_zero]
    · rw [e2, h2, map_zero]
    · rw [e3, h3, map_zero]

end Policy
