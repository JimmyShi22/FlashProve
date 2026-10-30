-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cm/TargetSegHeadAsm.lean: the head's segment over p = 2^64 - 2^32 + 1 assembled: the statements
`head_wf`, `head_places`, `head_holds`, `head_holds_int` of Cm/TargetSegHead.lean, proved.
Cm/TargetSegHead.lean tells them in words: under Main names, and `head_holds_int` in its docstring.

The fields
are `Gl.F`, `Gl.E` (Cb/Gl/GlField.lean);
the format is `Cm.Seg.TS.fmtRef` (Cm/TargetSegAll.lean);
the head's keys and tables are those of the plain head with the scaled table (Cm/TargetPHead.lean).


Main names (statements and hypotheses: Cm/TargetSegHead.lean):
  `head_wf`: every family of `segHead np` well formed.
  `head_places`: every place read, within `reads Hd.plain 24` (Cm/SegLayout.lean).
  `head_holds`: the assembly: the segment's conditions ⇔ the plain head's keys in their tables,
    identities 0.
  `head_holds_int`: the segment's conditions at integer matrices M ⇔ `Cm.TP.Cond`'s clauses headKey,
    headIdn at integer cells t (`ReadsAt t M`).

The limits of the statements: the head of
Cm/TargetSegHead.lean.




Terms: lean/GLOSSARY.md.
-/
import Cm.SegHeadAsm
import Cm.TargetSegAll
import Cm.TargetSegHeadProofs
import Cm.TargetSegHead
import Cm.TargetSegIdxModel
import Cm.TargetSegIdxModelProofs
import Cm.TargetPHeadNoWrap


set_option autoImplicit false
set_option linter.unusedSectionVars false

attribute [-instance] Inst.Model.Scl.ref

namespace Cm.Seg.TS
open Cb Code Inst.Model Inst.Model.Head Inst.Model.Layout Finset Cm.Seg.Ex

/-! ## 1. Keys read the valid names only -/

section Same
variable {K : Type} [CommRing K]

variable {t t' : Head.Cells K} (h : Same t t')
include h

/-- the keys of the plain head read the valid names only: if `Same t t'` (Cm/SegHeadAsm.lean: t and
t' agree at the names that the plain head reads), a < `Plain.len f` and i < `nT`, then
`Plain.TP.key` is the same at t and at t' -/
theorem key_same (np : NormPar) (H : ℕ → ℕ → K) (y : Req) (f : Plain.Fam) {a i : ℕ}
    (ha : a < Plain.len f) (hi : i < nT) :
    Plain.TP.key np t H y f a i = Plain.TP.key np t' H y f a i := by
  have hD : ∀ n < 99, Dv t n i = Dv t' n i := fun n hn => Dv_same h hn hi
  cases f
  · show xv t a i * Ledger.R (fun n => Dv t n i) + 2 ^ (np.K - 1) -
        2 ^ np.K * Head.nw t a i - 2 ^ 16 * rn t a i =
      xv t' a i * Ledger.R (fun n => Dv t' n i) + 2 ^ (np.K - 1) -
        2 ^ np.K * Head.nw t' a i - 2 ^ 16 * rn t' a i
    rw [xv_same h ha hi, R_same hD, nw_same h ha hi, rn_same h ha hi]
  · show _ * rn t a i = _ * rn t' a i
    rw [rn_same h ha hi]
  · show Plain.mg t H y a i - 2 ^ 8 * K1 t y a i - K2 t y a i =
      Plain.mg t' H y a i - 2 ^ 8 * K1 t' y a i - K2 t' y a i
    unfold Plain.mg K1 K2
    rw [lg_same h H hi, lg_same h H hi, d1_same h ha hi, d2_same h ha hi]
  · show K1 t y a i = K1 t' y a i
    unfold K1
    rw [d1_same h ha hi]
  · show _ * Dv t a i = _ * Dv t' a i
    rw [hD a ha]
  · show K2 t y a i = K2 t' y a i
    unfold K2
    rw [d2_same h ha hi]
  · show (Head.nw t a i + 2 ^ 15) + 2 ^ 28 * (Head.nrm t a i + 2 ^ 11) =
      (Head.nw t' a i + 2 ^ 15) + 2 ^ 28 * (Head.nrm t' a i + 2 ^ 11)
    rw [nw_same h ha hi, nrm_same h ha hi]

end Same

/-! ## 2. Well-formedness -/

theorem wf_lgV : WF1 (X := XI) fmtRef 28 lgV :=
  WF1.sumA fmtRef
    (All.mul (WF0.aff fmtRef _ _)
      (WF0.idx fmtRef
        (tok_ok (28 + 13) _ _ (run_length 0 18) (by rw [run_length]; norm_num)
          (ok_run_run (by norm_num) (by norm_num))).2))

theorem wf_lgW : WF1 (X := XI) fmtRef 28 lgW :=
  WF1.sumA fmtRef
    (All.sc _ (All.mul (WF0.aff fmtRef _ _)
        (WF0.idx fmtRef
          (tok_ok (28 + 31) _ _ (run_length 28 18) (by rw [run_length]; norm_num)
            (ok_run_run (by norm_num) (by norm_num))).2)))

theorem wf_k1Ex (v : ℕ) : WF1 (X := XI) fmtRef v k1Ex :=
  All.add (WF1.aff fmtRef _ _) (All.smul _ (All.pub _))
theorem wf_k2Ex (v : ℕ) : WF1 (X := XI) fmtRef v k2Ex :=
  All.add (WF1.aff fmtRef _ _) (All.smul _ (All.pub _))
theorem wf_mgEx : WF1 (X := XI) fmtRef 28 mgEx :=
  All.sc _ (All.sub (All.sub wf_lgW wf_lgV) (All.pub _))

theorem wf_keyEx (np : NormPar) (f : Plain.Fam) : WF1 fmtRef (vxH f + 10) (keyEx np f) := by
  cases f
  · exact All.add (All.mul (WF1.aff fmtRef _ _) (WF1.aff fmtRef _ _)) (WF1.aff fmtRef _ _)
  · exact WF1.aff fmtRef _ _
  · exact All.sub (All.sub wf_mgEx (All.smul _ (wf_k1Ex 28))) (wf_k2Ex 28)
  · exact wf_k1Ex _
  · exact WF1.aff fmtRef _ _
  · exact wf_k2Ex _
  · exact WF1.aff fmtRef _ _

theorem head_wf : Spec.head_wf := fun np =>
  ⟨fun f hf => by
      obtain ⟨k, _, rfl⟩ := List.mem_map.1 hf
      exact fam_wf fmtRef (wf_ledEx fmtRef np _ k 10 fun s => wf_wsEx fmtRef 10 13 blIn s),
    fun k hk => by
      obtain ⟨f, _, rfl⟩ := List.mem_map.1 hk
      exact fam_wf fmtRef (wf_keyEx np f)⟩

/-! ## 3. Places -/

theorem pl_cHf {φ i : ℕ} (hφ : φ < Plain.nHf) (hi : i < nT) : AllPl IsHd (cHf φ i) :=
  AllPl.cAt (Or.inr (Or.inr ⟨rfl, Or.inl ⟨Name.hf φ i, ⟨hφ, hi⟩, rfl, rfl⟩⟩))
theorem pl_cHd {φ i : ℕ} (hφ : φ < nFeat .hd) (hi : i < nT) : AllPl IsHd (cHd φ i) :=
  AllPl.cAt (Or.inr (Or.inr ⟨rfl, Or.inl ⟨Name.hd φ i, ⟨hφ, hi⟩, rfl, rfl⟩⟩))
theorem pl_cHr {φ i : ℕ} (hφ : φ < Plain.nHr) (hi : i < nT) : AllPl IsHd (cHr φ i) :=
  AllPl.cAt (Or.inr (Or.inr ⟨rfl, Or.inl ⟨Name.hr φ i, ⟨hφ, hi⟩, rfl, rfl⟩⟩))
theorem pl_cX {φ i : ℕ} (hφ : φ < nFeat .x) (hi : i < nT) : AllPl IsHd (cX φ i) :=
  AllPl.cAt (Or.inr (Or.inr ⟨rfl, Or.inr ⟨φ, i, hφ, hi, rfl⟩⟩))
theorem pl_cRd {m : ℕ} {c : ℕ → CForm Cb.Gl.E} (h : ∀ l < m, AllPl IsHd (c l)) :
    AllPl IsHd (cRd m c) :=
  AllPl.cSum fun l hl => AllPl.smul _ (h l hl)
theorem pl_cBl {l j i : ℕ} (hl : l < 5) (hj : j < 5120) (hi : i < nT) : AllPl IsHd (cBl l j i) :=
  pl_cX (by simp only [fX, nFeat]; omega) hi
theorem pl_cXv {j i : ℕ} (hj : j < 5120) (hi : i < nT) : AllPl IsHd (cXv j i) :=
  pl_cRd fun _ hl => pl_cBl hl hj hi
theorem pl_cNw {j i : ℕ} (hj : j < 5120) (hi : i < nT) : AllPl IsHd (cNw j i) :=
  pl_cRd fun l hl => pl_cHf (by simp only [fNw, Plain.nHf]; omega) hi
theorem pl_cRn {j i : ℕ} (hj : j < 5120) (hi : i < nT) : AllPl IsHd (cRn j i) :=
  AllPl.add (AllPl.cK _) (pl_cRd fun l hl => pl_cHf (by simp only [fRn, Plain.nHf]; omega) hi)
theorem pl_cD1 {v i : ℕ} (hv : v < 202048) (hi : i < nT) : AllPl IsHd (cD1 v i) :=
  pl_cRd fun l hl => pl_cHf (by simp only [fD1, Plain.nHf]; omega) hi
theorem pl_cD2 {v i : ℕ} (hv : v < 202048) (hi : i < nT) : AllPl IsHd (cD2 v i) :=
  pl_cHf (by simp only [fD2, Plain.nHf]; omega) hi
theorem pl_cNrm {j i : ℕ} (hj : j < 5120) (hi : i < nT) : AllPl IsHd (cNrm j i) :=
  pl_cRd fun l hl => pl_cHd (by simp only [fNrm, nFeat]; omega) hi
theorem pl_cDv {n i : ℕ} (hn : n < 99) (hi : i < nT) : AllPl IsHd (cDv n i) :=
  AllPl.add (AllPl.cK _) (pl_cHr hn hi)

theorem pl_gd {vx len : ℕ} {f : ℕ → ℕ → CForm Cb.Gl.E}
    (h : ∀ a < len, ∀ i < nT, AllPl IsHd (f a i)) (b : ℕ) : AllPl IsHd (gd vx len f b) :=
  AllPl.ite (fun ha => h _ ha _ (vi_lt b)) fun _ => AllPl.cK _

theorem pl_nrmIn (o b : ℕ) : AllPl IsHd (nrmIn o b) :=
  AllPl.ite (fun h => pl_cNrm h (Nat.mod_lt _ (by norm_num))) fun _ => AllPl.cK _
theorem pl_blIn {l : ℕ} (hl : l < 5) (b : ℕ) : AllPl IsHd (blIn l b) :=
  AllPl.ite (fun h => pl_cBl hl h (Nat.mod_lt _ (by norm_num))) fun _ => AllPl.cK _

theorem pl_lgV : Pl1 (X := XI) IsHd 28 lgV :=
  Pl1.sumA (All.mul (Pl0.aff fun b _ => pl_nrmIn 13 b) (Pl0.idx _ _))
theorem pl_lgW : Pl1 (X := XI) IsHd 28 lgW :=
  Pl1.sumA (All.sc _ (All.mul (Pl0.aff fun b _ => pl_nrmIn 31 b) (Pl0.idx _ _)))
theorem pl_k1Ex (v : ℕ) : Pl1 (X := XI) IsHd v k1Ex :=
  All.add (Pl1.aff fun b _ => pl_gd (fun _ ha _ hi => pl_cD1 ha hi) b) (All.smul _ (All.pub _))
theorem pl_k2Ex (v : ℕ) : Pl1 (X := XI) IsHd v k2Ex :=
  All.add (Pl1.aff fun b _ => pl_gd (fun _ ha _ hi => pl_cD2 ha hi) b) (All.smul _ (All.pub _))
theorem pl_mgEx : Pl1 (X := XI) IsHd 28 mgEx :=
  All.sc _ (All.sub (All.sub pl_lgW pl_lgV) (All.pub _))

theorem pl_keyEx (np : NormPar) (f : Plain.Fam) : Pl1 IsHd (vxH f + 10) (keyEx np f) := by
  cases f
  · exact All.add
      (All.mul (Pl1.aff fun b _ => pl_gd (fun _ ha _ hi => pl_cXv ha hi) b)
        (Pl1.aff fun b _ => pl_lR fun n hn => pl_cDv hn (vi_lt b)))
      (Pl1.aff fun b _ =>
        pl_gd (fun _ ha _ hi =>
            AllPl.sub (AllPl.sub (AllPl.cK _) (AllPl.smul _ (pl_cNw ha hi)))
              (AllPl.smul _ (pl_cRn ha hi))) b)
  · exact Pl1.aff fun b _ => pl_gd (fun _ ha _ hi => AllPl.smul _ (pl_cRn ha hi)) b
  · exact All.sub (All.sub pl_mgEx (All.smul _ (pl_k1Ex 28))) (pl_k2Ex 28)
  · exact pl_k1Ex _
  · exact Pl1.aff fun b _ => pl_gd (fun _ ha _ hi => AllPl.smul _ (pl_cDv ha hi)) b
  · exact pl_k2Ex _
  · exact Pl1.aff fun b _ =>
      AllPl.ite (fun ha =>
          AllPl.add (AllPl.add (pl_cNw ha (vi_lt b)) (AllPl.cK _))
            (AllPl.smul _ (AllPl.add (pl_cNrm ha (vi_lt b)) (AllPl.cK _))))
        fun _ => AllPl.cK _

theorem head_places : Spec.head_places := by
  rintro np p (⟨f, hf, hp⟩ | ⟨k, hk, hp⟩)
  · obtain ⟨k, _, rfl⟩ := List.mem_map.1 hf
    exact fam_places (P := IsHd)
      (pl_ledEx np (fun s => pl_wsEx s fun l hl b _ => pl_blIn hl b) fun b _ n hn =>
        pl_cDv hn (vi_lt b))
      p hp
  · obtain ⟨f, _, rfl⟩ := List.mem_map.1 hk
    exact fam_places (P := IsHd) (pl_keyEx np f) p hp

/-! ## 4. The assembly -/

theorem rowsH_eq (f : Plain.Fam) : (Plain.TP.tableOf f).rows = 2 ^ tabLog f := by cases f <;> rfl

theorem head_holds : Spec.head_holds := by
  intro np x W A
  constructor
  · rintro ⟨hI, hK⟩
    refine ⟨fun f a i ha hi => ?_, fun i hi k hk => ?_⟩
    · obtain ⟨u, hu, e⟩ := hK (keyFam np f, keyTab f) (List.mem_map.2 ⟨f, mem_allFam f, rfl⟩)
        (vOf a i) (vOf_lt (lt_of_lt_of_le ha (lenH_le f)) hi)
      obtain ⟨r, hr, rfl⟩ := (mem_tabOf_iff (rowsH_eq f) u).1 hu
      exact ⟨r, hr, (head_key_live np f x W A a i ha hi).symm.trans e⟩
    · rw [← head_idn_val np k x W A i hi]
      exact hI (idnFam np k) (List.mem_map.2 ⟨k, List.mem_range.2 hk, rfl⟩) i hi
  · rintro ⟨hK, hI⟩
    refine ⟨fun f hf b hb => ?_, fun k hk b hb => ?_⟩
    · obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hf
      rw [head_idn_val np k x W A b hb]
      exact hI b hb k (List.mem_range.1 hk)
    · obtain ⟨f, _, rfl⟩ := List.mem_map.1 hk
      have hb' : b < 2 ^ (vxH f + 10) := hb
      by_cases hl : va (vxH f) b < Plain.len f
      · obtain ⟨r, hr, e⟩ := hK f _ _ hl (vi_lt b)
        refine ⟨_, (mem_tabOf_iff (rowsH_eq f) _).2 ⟨r, hr, rfl⟩, ?_⟩
        rw [← e, ← head_key_live np f x W A _ _ hl (vi_lt b), vOf_va_vi hb']
      · exact head_key_dead np f x W A b hb' (not_lt.1 hl)

/-! ## 5. Integer matrices -/

theorem head_holds_int : Spec.head_holds_int := by
  intro np x Wz M t hR
  have ι_inj : Function.Injective (algebraMap Cb.Gl.F Cb.Gl.E) :=
    (algebraMap Cb.Gl.F Cb.Gl.E).injective
  have hS : Same ((t.cast Cb.Gl.F).map (algebraMap Cb.Gl.F Cb.Gl.E))
      (tH (Partition.castM (E := Cb.Gl.E) M)) :=
    ⟨fun φ hφ i hi => by
        show algebraMap Cb.Gl.F Cb.Gl.E ((t.hf φ i : ℤ) : Cb.Gl.F) =
          ((at' M (Name.hf φ i).place : ℤ) : Cb.Gl.E)
        rw [hR.hf φ hφ i hi, map_intCast],
      fun φ hφ i hi => by
        show algebraMap Cb.Gl.F Cb.Gl.E ((t.hd φ i : ℤ) : Cb.Gl.F) =
          ((at' M (Name.hd φ i).place : ℤ) : Cb.Gl.E)
        rw [hR.hd φ hφ i hi, map_intCast],
      fun φ hφ i hi => by
        show algebraMap Cb.Gl.F Cb.Gl.E ((t.hr φ i : ℤ) : Cb.Gl.F) =
          ((at' M (Name.hr φ i).place : ℤ) : Cb.Gl.E)
        rw [hR.hr φ hφ i hi, map_intCast],
      fun φ hφ i hi => by
        show algebraMap Cb.Gl.F Cb.Gl.E ((t.x φ i : ℤ) : Cb.Gl.F) =
          ((at' M (ownX φ i).place : ℤ) : Cb.Gl.E)
        rw [hR.x φ hφ i hi, map_intCast]⟩
  have hH : HW (fun y c => ((Wz y c : ℤ) : Cb.Gl.F)) =
      fun j v => algebraMap Cb.Gl.F Cb.Gl.E (TP.castH Cb.Gl.p Wz j v) := by
    funext j v
    show algebraMap Cb.Gl.F Cb.Gl.E _ = _
    congr 1
    exact h_int Wz j v
  have eK : ∀ f a i, a < Plain.len f → i < nT →
      Plain.TP.key np (tH (Partition.castM (E := Cb.Gl.E) M))
          (HW fun y c => ((Wz y c : ℤ) : Cb.Gl.F)) (reqOf x) f a i =
        algebraMap Cb.Gl.F Cb.Gl.E
          (Plain.TP.key np (t.cast Cb.Gl.F) (TP.castH Cb.Gl.p Wz) (reqOf x)
            f a i) := fun f a i ha hi => by
    rw [Plain.TP.map_key (algebraMap Cb.Gl.F Cb.Gl.E) np (t.cast Cb.Gl.F)
          (TP.castH Cb.Gl.p Wz) (reqOf x) f a i, hH]
    exact (key_same hS np _ _ f ha hi).symm
  have eI : ∀ i k, i < nT → k < 17 →
      Plain.idn np (tH (Partition.castM (E := Cb.Gl.E) M)) i k =
        algebraMap Cb.Gl.F Cb.Gl.E (Plain.idn np (t.cast Cb.Gl.F) i k) := fun i k hi hk => by
    rw [Plain.map_idn' (algebraMap Cb.Gl.F Cb.Gl.E) np (t.cast Cb.Gl.F) i k]
    exact (idn_same hS np hi hk).symm
  rw [head_holds np x _ _]
  constructor
  · rintro ⟨hK, hI⟩
    refine ⟨fun f a i ha hi => ?_, fun i hi k hk => ?_⟩
    · obtain ⟨u, hu, e⟩ := hK f a i ha hi
      rw [eK f a i ha hi] at e
      exact ⟨u, hu, ι_inj e⟩
    · have e := hI i hi k hk
      rw [eI i k hi hk] at e
      exact (map_eq_zero _).1 e
  · rintro ⟨hK, hI⟩
    refine ⟨fun f a i ha hi => ?_, fun i hi k hk => ?_⟩
    · obtain ⟨u, hu, e⟩ := hK f a i ha hi
      exact ⟨u, hu, by rw [eK f a i ha hi, e]⟩
    · rw [eI i k hi hk, hI i hi k hk, map_zero]

end Cm.Seg.TS
