-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Policy/Seg/HeadWf.lean

The segment `segHeadPol s pol` (Policy/Seg/Head.lean) is well formed and reads only places that the
cells' layout says this head reads.

Theorems with their proofs, after sections 2 and 3 of Cm/TargetSegHeadAsm.lean, the plain head's
file. What the two heads share is taken from that file; on places it is carried over by
`reads_plain_sub` (Policy/Seg/Dict.lean). The rest is shown at all 1,232,768 features of hf and all
120 bytes of hr.
`wf_mgPolEx` to `wf_sB3Ex`, `segHeadPol_wf`: every atom, and so every family, is well formed.
`IsHdM q`: the place q is in `reads Hd.main 24` (Cm/SegLayout.lean). `allPl_main`, `pl1_main`: what
reads only places of the plain head reads only places with `IsHdM`. `pl_cHfM` to `pl_sB3Ex`,
`segHeadPol_places`: the forms, the expressions, and so the segment read only such places. A name
with M is the analogue at `Hd.main` of the plain head's lemma without it.

Limits: nothing on the values of the families, on tables, on bounds of cells, or on protocols. "Well
formed" is `SegSpec.WF` (Cb/Req/ReqSpec.lean).
-/
import Policy.Seg.Head
import Cm.TargetSegHeadAsm

set_option autoImplicit false
set_option linter.unusedSectionVars false

attribute [-instance] Inst.Model.Scl.ref

namespace Policy
open Cb Inst.Model Finset Cm.Seg Cm.Seg.Ex

/-- What holds of the ledger's four identities holds of every family in their list. -/
theorem forall_ledgerIdn {Q : Fam XI Gl.E → Prop} {pol : AcceptancePolicy} (h1 : Q (jB4Fam pol)) (h2 : Q jZFam)
    (h3 : Q (sB2Fam pol)) (h4 : Q (sB3Fam pol)) : ∀ f ∈ ledgerIdn pol, Q f := by
  intro f hf
  simp only [ledgerIdn, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · exact h1
  · exact h2
  · exact h3
  · exact h4

/-! ## 1. Well-formedness -/

theorem wf_mgPolEx : WF1 (X := XI) TS.fmtRef 28 mgPolEx :=
  All.add TS.wf_mgEx (All.sc _ (WF1.aff TS.fmtRef _ _))

theorem wf_keyExPol (np : NormPar) (f : Head.Fam) :
    WF1 TS.fmtRef (vxPol f + 10) (keyExPol np f) := by
  cases f
  · exact TS.wf_keyEx np .NF
  · exact TS.wf_keyEx np .NFH
  · exact All.smul _ (All.sub (All.sub wf_mgPolEx (All.smul _ (TS.wf_k1Ex 28))) (TS.wf_k2Ex 28))
  · exact TS.wf_k1Ex _
  · exact WF1.aff TS.fmtRef _ _
  · exact TS.wf_k2Ex _
  · exact All.add (WF1.aff TS.fmtRef _ _) (All.smul _ (All.pub _))
  · exact All.add (WF1.aff TS.fmtRef _ _) (All.smul _ (All.pub _))
  · exact TS.wf_keyEx np .CNF

theorem wf_jB4Ex (pol : AcceptancePolicy) : WF1 TS.fmtRef 10 (jB4Ex pol) :=
  All.sc _ (All.sub (WF1.aff TS.fmtRef _ _) (All.con _))

theorem wf_jZEx : WF1 TS.fmtRef 10 jZEx :=
  All.sc _
    (All.sub (All.add (WF1.aff TS.fmtRef _ _) (WF1.sumA TS.fmtRef (WF0.aff TS.fmtRef _ _)))
      (All.con _))

theorem wf_sB2Ex (pol : AcceptancePolicy) : WF1 TS.fmtRef 0 (sB2Ex pol) :=
  All.sub (WF1.sumA TS.fmtRef (All.sc _ (WF0.aff TS.fmtRef _ _))) (All.pub _)

theorem wf_sB3Ex (pol : AcceptancePolicy) : WF1 TS.fmtRef 0 (sB3Ex pol) :=
  All.sub (WF1.sumA TS.fmtRef (All.sc _ (WF0.aff TS.fmtRef _ _))) (All.pub _)

/-- Every family of the head's segment is well formed. -/
theorem segHeadPol_wf : Spec.headPol_wf := fun s pol =>
  ⟨fun f hf => by
      rcases List.mem_append.1 hf with hf | hf
      · exact (TS.head_wf s.nf).1 f hf
      · exact forall_ledgerIdn (Q := fun f => f.WF TS.fmtRef) (fam_wf TS.fmtRef (wf_jB4Ex pol))
          (fam_wf TS.fmtRef wf_jZEx) (fam_wf TS.fmtRef (wf_sB2Ex pol))
          (fam_wf TS.fmtRef (wf_sB3Ex pol)) f hf,
    fun k hk => by
      obtain ⟨f, _, rfl⟩ := List.mem_map.1 hk
      exact fam_wf TS.fmtRef (wf_keyExPol s.nf f)⟩

/-! ## 2. Places -/

/-- a place that the layout says the head with the ledger reads -/
abbrev IsHdM (q : Cb.Place) : Prop := q ∈ reads Hd.main 24

/-- A form that reads only places of the plain head reads only places of this head. -/
theorem allPl_main {f : CForm Gl.E} (h : AllPl IsHd f) : AllPl IsHdM f := fun p hp =>
  reads_plain_sub 24 (h p hp)

/-- An expression that reads only places of the plain head reads only places of this head. -/
theorem pl1_main {v : ℕ} {p : Ex1 XI Gl.E} (h : Pl1 IsHd v p) : Pl1 IsHdM v p :=
  fun m hm a ha q hq => reads_plain_sub 24 (h m hm a ha q hq)

theorem pl_cHfM {φ i : ℕ} (hφ : φ < Head.nFeat .hf) (hi : i < Head.nT) :
    AllPl IsHdM (TS.cHf φ i) :=
  AllPl.cAt (Or.inr (Or.inr ⟨rfl, Or.inl ⟨Name.hf φ i, ⟨hφ, hi⟩, rfl, rfl⟩⟩))
theorem pl_cHrM {φ i : ℕ} (hφ : φ < Head.nFeat .hr) (hi : i < Head.nT) :
    AllPl IsHdM (TS.cHr φ i) :=
  AllPl.cAt (Or.inr (Or.inr ⟨rfl, Or.inl ⟨Name.hr φ i, ⟨hφ, hi⟩, rfl, rfl⟩⟩))
theorem pl_cRdM {m : ℕ} {c : ℕ → CForm Gl.E} (h : ∀ l < m, AllPl IsHdM (c l)) :
    AllPl IsHdM (TS.cRd m c) :=
  AllPl.cSum fun l hl => AllPl.smul _ (h l hl)
theorem pl_cEx {v i : ℕ} (hv : v < 202048) (hi : i < Head.nT) : AllPl IsHdM (cEx v i) :=
  AllPl.add (AllPl.cK _)
    (pl_cRdM fun l hl => pl_cHfM (by simp only [Head.fEx, Head.nFeat]; omega) hi)
theorem pl_cDvM {n i : ℕ} (hn : n < 120) (hi : i < Head.nT) : AllPl IsHdM (TS.cDv n i) :=
  AllPl.add (AllPl.cK _) (pl_cHrM hn hi)
theorem pl_cHid {a n i : ℕ} (han : a + n ≤ 120) (hi : i < Head.nT) : AllPl IsHdM (cHid a n i) :=
  AllPl.cSum fun l hl => AllPl.smul _ (pl_cDvM (by omega) hi)
theorem pl_cHe {v i : ℕ} (hv : v < 202048) (hi : i < Head.nT) : AllPl IsHdM (cHe v i) :=
  AllPl.add (allPl_main (TS.pl_cD1 hv hi)) (AllPl.smul _ (pl_cEx hv hi))

theorem pl_gdM {vx len : ℕ} {f : ℕ → ℕ → CForm Gl.E}
    (h : ∀ a < len, ∀ i < Head.nT, AllPl IsHdM (f a i)) (b : ℕ) :
    AllPl IsHdM (TS.gd vx len f b) :=
  AllPl.ite (fun ha => h _ ha _ (vi_lt b)) fun _ => AllPl.cK _

theorem pl_exIn (b : ℕ) : AllPl IsHdM (exIn b) :=
  AllPl.ite (fun h => pl_cEx h (Nat.mod_lt _ (by norm_num))) fun _ => AllPl.cK _

theorem pl_mgPolEx : Pl1 (X := XI) IsHdM 28 mgPolEx :=
  All.add (pl1_main TS.pl_mgEx)
    (All.sc _
      (Pl1.aff fun b _ =>
        AllPl.add (pl_cHid (by norm_num) (vi_lt b))
          (AllPl.smul _ (pl_cHid (by norm_num) (vi_lt b)))))

theorem pl_keyExPol (np : NormPar) (f : Head.Fam) :
    Pl1 IsHdM (vxPol f + 10) (keyExPol np f) := by
  cases f
  · exact pl1_main (TS.pl_keyEx np .NF)
  · exact pl1_main (TS.pl_keyEx np .NFH)
  · exact All.smul _
      (All.sub (All.sub pl_mgPolEx (All.smul _ (pl1_main (TS.pl_k1Ex 28))))
        (pl1_main (TS.pl_k2Ex 28)))
  · exact pl1_main (TS.pl_k1Ex _)
  · exact Pl1.aff fun b _ => pl_gdM (fun _ ha _ hi => AllPl.smul _ (pl_cDvM ha hi)) b
  · exact pl1_main (TS.pl_k2Ex _)
  · exact All.add (Pl1.aff fun b _ => pl_gdM (fun _ ha _ hi => pl_cHe (by omega) hi) b)
      (All.smul _ (All.pub _))
  · exact All.add
      (Pl1.aff fun b _ =>
        AllPl.ite (fun ha => pl_cHe (by omega) (vi_lt b)) fun _ => AllPl.cK _)
      (All.smul _ (All.pub _))
  · exact pl1_main (TS.pl_keyEx np .CNF)

theorem pl_jB4Ex (pol : AcceptancePolicy) : Pl1 IsHdM 10 (jB4Ex pol) :=
  All.sc _
    (All.sub
      (Pl1.aff fun b _ =>
        AllPl.add (pl_cHid (by norm_num) (vi_lt b)) (pl_cHid (by norm_num) (vi_lt b)))
      (All.con _))

theorem pl_jZEx : Pl1 IsHdM 10 jZEx :=
  All.sc _
    (All.sub
      (All.add (Pl1.aff fun b _ => pl_cHid (by norm_num) (vi_lt b))
        (Pl1.sumA (Pl0.aff fun b _ => pl_exIn b)))
      (All.con _))

theorem pl_sB2Ex (pol : AcceptancePolicy) : Pl1 IsHdM 0 (sB2Ex pol) :=
  All.sub
    (Pl1.sumA
      (All.sc _
        (Pl0.aff fun b _ =>
          AllPl.add
            (AllPl.add (pl_cHid (by norm_num) (vi_lt b))
              (AllPl.smul _ (pl_cHid (by norm_num) (vi_lt b))))
            (pl_cHid (by norm_num) (vi_lt b)))))
    (All.pub _)

theorem pl_sB3Ex (pol : AcceptancePolicy) : Pl1 IsHdM 0 (sB3Ex pol) :=
  All.sub
    (Pl1.sumA
      (All.sc _
        (Pl0.aff fun b _ =>
          AllPl.add (pl_cHid (by norm_num) (vi_lt b)) (pl_cHid (by norm_num) (vi_lt b)))))
    (All.pub _)

/-- Every place that the head's segment reads is among those that the layout says this head
reads. -/
theorem segHeadPol_places : Spec.headPol_places := by
  rintro s pol q (⟨f, hf, hq⟩ | ⟨k, hk, hq⟩)
  · rcases List.mem_append.1 hf with hf | hf
    · exact reads_plain_sub 24 (TS.head_places s.nf q (Or.inl ⟨f, hf, hq⟩))
    · exact forall_ledgerIdn (Q := fun f => ∀ q ∈ f.places, IsHdM q)
        (fam_places (P := IsHdM) (pl_jB4Ex pol)) (fam_places (P := IsHdM) pl_jZEx)
        (fam_places (P := IsHdM) (pl_sB2Ex pol)) (fam_places (P := IsHdM) (pl_sB3Ex pol)) f hf q hq
  · obtain ⟨f, _, rfl⟩ := List.mem_map.1 hk
    exact fam_places (P := IsHdM) (pl_keyExPol s.nf f) q hq

end Policy
