-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cm/TargetSegAtt.lean: the attention segment of group g, assembled as a segment (`SegSpec`) of
Cb/Req/ReqSpec.lean over p = 2^64 - 2^32 + 1, and its conditions compared with those of
Cm/TargetPRel.lean (`TP.CondL` at `Cb.Gl.p`: `attKey`, `attIdn`).

The namespace is `Cm.Seg.TS`. What a segment is, and where its families come from: the head of
Cm/SegAtt.lean.

Main names:
  `attSpec g u0 tb`: the segment: 2^18 rows, 7,200 columns; keys: the seven families 1M, 1D, 2M, 2D,
    3W, 3X, 4 with the tables of their calls; identities: at1 (ten families), at2, at3. u0 is the
    number of live rows of the exponential (`DU`, Cm/SegAttKeyKit.lean); tb holds the table
    functions that the program reads (`Tables`, Inst/Model/Program.lean).
  `attSpec_holds_iff`: under the two hypotheses named under Limits, for integer matrices M and
    every integer trace that agrees with M at the owners' places (`ownAtt`, Cm/SegLayout.lean) of
    the valid names: the conditions of the segment `attSpec g u0 tb` hold at M if and only if, at
    that trace over `Cb.Gl.F`, the key vectors of Inst/Model/Att/Trace.lean hold entries of their
    tables at all indices in pieces and that file's identities with valid names are 0.
  `attSpec_iff_toMat`, `attSpec_iff_ofMat`: the same, of the segment at `SFK κ nf g`,
    `(κ (4 * g)).expRows.toNat` and `tbRef`, under the hypotheses of their statements, at the
    matrices of a trace (completeness; under `hh : h.OK`, with `Hd.OK` of Cm/SegLayout.lean) and at
    the trace of matrices (knowledge soundness), in the words of `TP.CondL`'s clauses `attKey`,
    `attIdn` at g.
  `attSpec_wf`, `attSpec_places`, `attSpec_reads`: the segment is well formed (`SegSpec.WF`); the
    places that it reads.

Why: both sides of the comparison are casts of one integer (`AttSeg.key_cast`, `AttSeg.idn_cast`).
Limits: taken as hypotheses (statements `Spec.keyVec_agree`, `Spec.idnVal_agree`, Cm/SegAtt.lean;
proofs: Cm/SegAttAgree.lean, Cm/SegAttOK.lean): keys and identities read valid names only (the
identities: those with valid names).
No hypothesis on the table of scales: at dead vertices the families have row 0 of their table. (Dead
vertices: B ≥ N in `AttKeyOK`, Cm/SegAttKey.lean.)
-/
import Cm.SegAtt
import Cm.TargetSegAll


set_option autoImplicit false
set_option linter.unusedSectionVars false

attribute [-instance] Inst.Model.Scl.ref

namespace Cm.Seg.TS
open Cb Inst.Model Inst.Model.All Finset
open Inst.Model.AttSeg (Raw Reg)

variable [scl : Scl] {X E : Type} [Field E] [Algebra Cb.Gl.F E]

/-- integer matrices, read as an integer trace of the attention segment of group g -/
def tMA (g : ℕ) (M : ℕ → ℕ → ℕ → ℤ) : Raw → ℤ := fun c => at' M (ownAtt g c).place

omit scl in
theorem tAtt_castM (g : ℕ) (M : ℕ → ℕ → ℕ → ℤ) :
    tAtt g (Partition.castM (E := E) M) = AttSeg.castT (tMA g M) := rfl

/-- the table of a call -/
def tabA (u0 : ℕ) (tb : Tables) (c : Fin 4) : Tab Cb.Gl.F := tabOf (AttSeg.lut (DU u0) tb c) 16

theorem rowsA (u0 : ℕ) (tb : Tables) (c : Fin 4) : (AttSeg.lut (DU u0) tb c).rows = 2 ^ 16 := by
  fin_cases c <;> rfl

/-- the images in E of the elements of the table of a call -/
def imgA (u0 : ℕ) (tb : Tables) (c : Fin 4) : Set E :=
  {e | ∃ u ∈ (tabA u0 tb c).set, e = algebraMap Cb.Gl.F E u}

theorem mem_imgA (u0 : ℕ) (tb : Tables) (c : Fin 4) (k : Cb.Gl.F) :
    algebraMap Cb.Gl.F E k ∈ (imgA u0 tb c : Set E) ↔
    k ∈ (AttSeg.lutSet (AttSeg.lut (DU u0) tb c) : Set Cb.Gl.F) := by
  constructor
  · rintro ⟨u, hu, h⟩
    rw [(algebraMap Cb.Gl.F E).injective h]
    exact (mem_tabOf_iff (rowsA u0 tb c) u).1 hu
  · exact fun h => ⟨k, (mem_tabOf_iff (rowsA u0 tb c) k).2 h, rfl⟩

theorem pad_imgA (u0 : ℕ) (tb : Tables) (c : Fin 4) :
    (padA u0 tb c : E) ∈ (imgA u0 tb c : Set E) := by
  have h := (mem_imgA (E := E) u0 tb c _).2 ⟨0, by rw [rowsA]; norm_num, rfl⟩
  rwa [map_intCast] at h

/-- From a family to its part of the key vector: under `AttKeyOK`, for a set S that has
`padA u0 tb c`, all values of the family on its cube are in S if and only if the N entries of the
key vector from `off` on are. -/
theorem AttKeyOK.cube_iff {Φ : IdxFmt Cb.Gl.F} {g u0 : ℕ} {tb : Tables} {c : Fin 4} {off N : ℕ}
    {f : Cb.Fam X E} (h : AttKeyOK Φ g u0 tb c off N f) (S : Set E) (hS : padA u0 tb c ∈ S) (x₀ : X)
    (W : ℕ → ℕ → Cb.Gl.F) (A : ℕ → ℕ → ℕ → E) :
    (∀ B < 2 ^ f.v, f.val Φ x₀ W A B ∈ S) ↔
    ∀ B < N, AttSeg.keyVec (DU u0) tb (tAtt g A) c (off + B) ∈ S := by
  constructor
  · intro H B hB
    have h1 := H B (lt_of_lt_of_le hB h.le)
    rwa [h.val, if_pos hB] at h1
  · intro H B _
    rw [h.val]
    split_ifs with hB
    · exact H B hB
    · exact hS

omit scl in
theorem split_iff (P : ℕ → Prop) (a b : ℕ) :
    ((∀ B < a, P (0 + B)) ∧ ∀ B < b, P (a + B)) ↔ ∀ Y < a + b, P Y := by
  constructor
  · rintro ⟨h1, h2⟩ Y hY
    by_cases h : Y < a
    · simpa using h1 Y h
    · have := h2 (Y - a) (by omega)
      rwa [Nat.add_sub_cancel' (Nat.le_of_not_lt h)] at this
  · exact fun H => ⟨fun B hB => H _ (by omega), fun B hB => H _ (by omega)⟩

variable (g u0 : ℕ) (tb : Tables)

/-- The attention segment of group g. -/
def attSpec : SegSpec X Cb.Gl.F E :=
  ⟨18, colsAtt, attIdnFams g,
    [(fam1 g u0 tb .M, tabA u0 tb 0), (fam1 g u0 tb .D, tabA u0 tb 0),
      (fam2M g u0 tb, tabA u0 tb 1), (fam2D g u0 tb, tabA u0 tb 1), (fam3W g u0 tb, tabA u0 tb 2),
      (fam3X g u0 tb, tabA u0 tb 2), (fam4 g u0 tb, tabA u0 tb 3)]⟩

variable {g u0 tb} (Φ : IdxFmt Cb.Gl.F)

theorem attSpec_wf : (attSpec (X := X) (E := E) g u0 tb).WF Φ := by
  refine ⟨(attIdn_ok g Φ).wf, fun k hk => ?_⟩
  simp only [attSpec, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [(fam1M_ok g u0 tb Φ).wf, (fam1D_ok g u0 tb Φ).wf,
    (fam2M_ok g u0 tb Φ).wf, (fam2D_ok g u0 tb Φ).wf, (fam3W_ok g u0 tb Φ).wf,
    (fam3X_ok g u0 tb Φ).wf, (fam4_ok g u0 tb Φ).wf]

include Φ in
theorem attSpec_places : ∀ p ∈ (attSpec (X := X) (E := E) g u0 tb).places, IsAtt g p := by
  rintro p (⟨f, hf, hp⟩ | ⟨k, hk, hp⟩)
  · exact (attIdn_ok g Φ).places f hf p hp
  · simp only [attSpec, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [(fam1M_ok g u0 tb Φ).places p hp,
      (fam1D_ok g u0 tb Φ).places p hp, (fam2M_ok g u0 tb Φ).places p hp,
      (fam2D_ok g u0 tb Φ).places p hp, (fam3W_ok g u0 tb Φ).places p hp,
      (fam3X_ok g u0 tb Φ).places p hp, (fam4_ok g u0 tb Φ).places p hp]

/-! ## The comparison -/

section Pass
variable (hK : Spec.keyVec_agree)
  (hI : Spec.idnVal_agree) (M : ℕ → ℕ → ℕ → ℤ) (tZ : Raw → ℤ) (ht : Agree (tMA g M) tZ)
include ht

include hK in
/-- Under `hK` and `ht`, the key vector over E at the matrices is the image of the key vector over
the prime field at the integer trace. -/
theorem keyVec_pass (c : Fin 4) (Y : ℕ) :
    AttSeg.keyVec (DU u0) tb (tAtt g (Partition.castM (E := E) M)) c Y =
      algebraMap Cb.Gl.F E (AttSeg.keyVec (DU u0) tb (AttSeg.castT tZ : Raw → Cb.Gl.F) c Y) := by
  rw [tAtt_castM, AttSeg.key_cast, AttSeg.key_cast, map_intCast, hK scl u0 tb _ _ ht c Y]

omit scl in
include hI in
theorem idnVal_pass {j : AttSeg.Idn} (hj : j.Valid DA) :
    AttSeg.idnVal DA (tAtt g (Partition.castM (E := E) M)) j =
      algebraMap Cb.Gl.F E (AttSeg.idnVal DA (AttSeg.castT tZ : Raw → Cb.Gl.F) j) := by
  rw [tAtt_castM, AttSeg.idn_cast, AttSeg.idn_cast, map_intCast, hI _ _ ht j hj]

include hK hI in
/-- Under `hK`, `hI` and `ht`, the conditions of the segment are those of
Inst/Model/Att/Trace.lean on keys and identities. -/
theorem attSpec_holds_iff (x₀ : X) (W : ℕ → ℕ → Cb.Gl.F) :
    (attSpec g u0 tb).Holds Φ x₀ W (Partition.castM (E := E) M) ↔
    (∀ (c : Fin 4) (Y : ℕ), Y < (DU u0).used c →
      AttSeg.keyVec (DU u0) tb (AttSeg.castT tZ : Raw → Cb.Gl.F) c Y ∈
        AttSeg.lutSet (AttSeg.lut (DU u0) tb c)) ∧
    ∀ j : AttSeg.Idn,
      j.Valid (DU u0) → AttSeg.idnVal (DU u0) (AttSeg.castT tZ : Raw → Cb.Gl.F) j = 0 := by
  -- one family
  have fam : ∀ {c : Fin 4} {off N : ℕ} {f : Cb.Fam X E}, AttKeyOK Φ g u0 tb c off N f →
      ((∀ B < 2 ^ f.v, ∃ u ∈ (tabA u0 tb c).set,
          f.val Φ x₀ W (Partition.castM (E := E) M) B = algebraMap Cb.Gl.F E u) ↔
        ∀ B < N, AttSeg.keyVec (DU u0) tb (AttSeg.castT tZ : Raw → Cb.Gl.F) c (off + B) ∈
          AttSeg.lutSet (AttSeg.lut (DU u0) tb c)) := fun {c off N f} h => by
    refine (AttKeyOK.cube_iff h (imgA u0 tb c) (pad_imgA u0 tb c) x₀ W _).trans
      (forall_congr' fun B => forall_congr' fun _ => ?_)
    rw [keyVec_pass hK M tZ ht c]
    exact mem_imgA u0 tb c _
  unfold SegSpec.Holds
  rw [and_comm]
  refine and_congr ?_ ?_
  · have e : (∀ k ∈ (attSpec (X := X) (E := E) g u0 tb).keys, ∀ b < 2 ^ k.1.v,
      ∃ u ∈ k.2.set, k.1.val Φ x₀ W (Partition.castM (E := E) M) b = algebraMap Cb.Gl.F E u) ↔
        ((∀ B < DA.nb * 2 ^ DA.lM,
            AttSeg.keyVec (DU u0) tb (AttSeg.castT tZ : Raw → Cb.Gl.F) 0 (0 + B) ∈
              AttSeg.lutSet (AttSeg.lut (DU u0) tb 0)) ∧
          ∀ B < DA.nb * 2 ^ DA.lD,
            AttSeg.keyVec (DU u0) tb (AttSeg.castT tZ : Raw → Cb.Gl.F) 0 (DA.nb * 2 ^ DA.lM + B) ∈
              AttSeg.lutSet (AttSeg.lut (DU u0) tb 0)) ∧
        ((∀ B < DA.nb * 2 ^ DA.lM,
            AttSeg.keyVec (DU u0) tb (AttSeg.castT tZ : Raw → Cb.Gl.F) 1 (0 + B) ∈
              AttSeg.lutSet (AttSeg.lut (DU u0) tb 1)) ∧
          ∀ B < DA.nb * 2 ^ DA.lD,
            AttSeg.keyVec (DU u0) tb (AttSeg.castT tZ : Raw → Cb.Gl.F) 1 (DA.nb * 2 ^ DA.lM + B) ∈
              AttSeg.lutSet (AttSeg.lut (DU u0) tb 1)) ∧
        ((∀ B < DA.nb * 2 ^ DA.lW,
            AttSeg.keyVec (DU u0) tb (AttSeg.castT tZ : Raw → Cb.Gl.F) 2 (0 + B) ∈
              AttSeg.lutSet (AttSeg.lut (DU u0) tb 2)) ∧
          ∀ B < DA.nb * 2 ^ DA.lX,
            AttSeg.keyVec (DU u0) tb (AttSeg.castT tZ : Raw → Cb.Gl.F) 2 (DA.nb * 2 ^ DA.lW + B) ∈
              AttSeg.lutSet (AttSeg.lut (DU u0) tb 2)) ∧
        ∀ B < DA.nb * 2 ^ DA.l4,
            AttSeg.keyVec (DU u0) tb (AttSeg.castT tZ : Raw → Cb.Gl.F) 3 (0 + B) ∈
              AttSeg.lutSet (AttSeg.lut (DU u0) tb 3) := by
      rw [← fam (fam1M_ok g u0 tb Φ), ← fam (fam1D_ok g u0 tb Φ),
        ← fam (fam2M_ok g u0 tb Φ), ← fam (fam2D_ok g u0 tb Φ), ← fam (fam3W_ok g u0 tb Φ),
        ← fam (fam3X_ok g u0 tb Φ), ← fam (fam4_ok g u0 tb Φ)]
      simp only [attSpec, List.forall_mem_cons, List.not_mem_nil, false_imp_iff,
        implies_true, and_true, and_assoc]
    rw [e]
    have s0 := split_iff
      (fun Y =>
        AttSeg.keyVec (DU u0) tb (AttSeg.castT tZ : Raw → Cb.Gl.F) 0 Y ∈
          AttSeg.lutSet (AttSeg.lut (DU u0) tb 0))
      (DA.nb * 2 ^ DA.lM) (DA.nb * 2 ^ DA.lD)
    have s1 := split_iff
      (fun Y =>
        AttSeg.keyVec (DU u0) tb (AttSeg.castT tZ : Raw → Cb.Gl.F) 1 Y ∈
          AttSeg.lutSet (AttSeg.lut (DU u0) tb 1))
      (DA.nb * 2 ^ DA.lM) (DA.nb * 2 ^ DA.lD)
    have s2 := split_iff
      (fun Y =>
        AttSeg.keyVec (DU u0) tb (AttSeg.castT tZ : Raw → Cb.Gl.F) 2 Y ∈
          AttSeg.lutSet (AttSeg.lut (DU u0) tb 2))
      (DA.nb * 2 ^ DA.lW) (DA.nb * 2 ^ DA.lX)
    constructor
    · rintro ⟨h0, h1, h2, h3⟩ c
      fin_cases c
      · exact s0.1 h0
      · exact s1.1 h1
      · exact s2.1 h2
      · exact fun Y hY => by simpa using h3 Y hY
    · exact fun H => ⟨s0.2 (H 0), s1.2 (H 1), s2.2 (H 2), fun B hB => by simpa using H 3 B hB⟩
  · refine ((attIdn_ok g Φ).iff x₀ W (Partition.castM (E := E) M)).trans
      (forall_congr' fun j => forall_congr' fun hj => ?_)
    rw [idnVal_pass hI M tZ ht hj]
    exact map_eq_zero_iff _ (algebraMap Cb.Gl.F E).injective

end Pass

/-! ## At the conditions of Cm/TargetPRel.lean (`Cm.TP.CondL` at `Cb.Gl.p`) -/

omit scl in
/-- `attSpec_holds_iff` for the matrices of a trace (completeness). -/
theorem attSpec_iff_toMat (hK : Spec.keyVec_agree) (hI : Spec.idnVal_agree) (κ : ℕ → LayerScale)
    (nf : NormPar) (h : Hd) (hh : h.OK) (hg : g < nGr) (x₀ : X) (T : Trace) (W : ℕ → ℕ → Cb.Gl.F) :
    (attSpec (scl := SFK κ nf g) g (κ (4 * g)).expRows.toNat tbRef).Holds
      Φ x₀ W (Partition.castM (E := E) (toMat h T)) ↔
    (∀ (c : Fin 4) (Y : ℕ), Y < (DAK κ g).used c →
      AttSeg.keyVec (scl := SFK κ nf g) (DAK κ g) tbRef
          (AttSeg.castT (T.vAtt g) : Raw → Cb.Gl.F) c Y ∈
        AttSeg.lutSet (AttSeg.lut (scl := SFK κ nf g) (DAK κ g) tbRef c)) ∧
    ∀ j : AttSeg.Idn,
      j.Valid (DAK κ g) → AttSeg.idnVal (DAK κ g) (AttSeg.castT (T.vAtt g) : Raw → Cb.Gl.F) j = 0 :=
  attSpec_holds_iff (scl := SFK κ nf g)
    Φ hK hI (toMat h T) (T.vAtt g) (fun c hc => ((lay_read_toMat h hh T).2.1 g hg c hc).symm) x₀ W

omit scl in
/-- `attSpec_holds_iff` for the trace of matrices (knowledge soundness). -/
theorem attSpec_iff_ofMat (hK : Spec.keyVec_agree) (hI : Spec.idnVal_agree) (κ : ℕ → LayerScale)
    (nf : NormPar) (h : Hd) (hg : g < nGr) (x₀ : X) (M : ℕ → ℕ → ℕ → ℤ) (W : ℕ → ℕ → Cb.Gl.F) :
    (attSpec (scl := SFK κ nf g) g (κ (4 * g)).expRows.toNat tbRef).Holds
      Φ x₀ W (Partition.castM (E := E) M) ↔
    (∀ (c : Fin 4) (Y : ℕ), Y < (DAK κ g).used c →
      AttSeg.keyVec (scl := SFK κ nf g) (DAK κ g) tbRef
          (AttSeg.castT ((ofMat h M).vAtt g) : Raw → Cb.Gl.F) c Y ∈
        AttSeg.lutSet (AttSeg.lut (scl := SFK κ nf g) (DAK κ g) tbRef c)) ∧
    ∀ j : AttSeg.Idn, j.Valid (DAK κ g) →
      AttSeg.idnVal (DAK κ g) (AttSeg.castT ((ofMat h M).vAtt g) : Raw → Cb.Gl.F) j = 0 :=
  attSpec_holds_iff (scl := SFK κ nf g)
    Φ hK hI M ((ofMat h M).vAtt g) (fun c hc => ((lay_read_ofMat h M).2.1 g hg c hc).symm) x₀ W

include Φ in
/-- For g < `nGr`, the places that the segment reads are among those of the layout (`reads`). -/
theorem attSpec_reads (h : Hd) (hg : g < nGr) :
    ∀ p ∈ (attSpec (X := X) (E := E) g u0 tb).places, p ∈ reads h (2 * g + 1) :=
  fun p hp => isAtt_reads g h hg (attSpec_places Φ p hp)

end Cm.Seg.TS
