-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K8R/HeadRowsInScope.lean: the proofs of the four statements of
Johnson/P1K8R/HeadRowsInScopeStatement.lean, to the letter, and three helpers. Lemmas; none of the
library's goals.

A FURTHER TEXT. `planH2_claims` IS THE PROOF OF THE LIBRARY's `planH2_parts`
(Johnson/Desc/Kinds/Law/HeadPlanWritten.lean) WRITTEN A FURTHER TIME (the same opening of the
routine stands also in `Meaning.planH2_nm`, Johnson/Goal/Meaning/HidPlanNM.lean, and in
`Meaning.planH2_open`, HidOpen.lean), WITH ONE CLAUSE MORE (hp.nLin = claimsH h L t1 ..): that lemma
hands out t1 under "there is" and not the number of claims, so it cannot be called for this.
`head_reads_93` FOLLOWS THE LINES BY WHICH `reads_head_eq`
(Johnson/Desc/First/Link/Law/K9ReadsHeadPaid.lean) TAKES ITS SEVEN NUMBERS IN SCOPE.

How. `planH2_nLin`: `claimsH` reads of the data only `lins`, which reads f9 and NM; both ride from
the shape's return t1 to hp.tl (`Fo.addTreesF_zkeep`, `Fo.ownerHeld_zkeep`,
OnBytes/Tie/Pv/Lookup/Ends/FoMadeTail.lean; `addTrees_keeps`, Johnson/Road/FormsKeysPlan.lean;
`ownerHeld_keeps`, Johnson/Road/HeadReads.lean). `head_nLin_in_scope`: `Fo.Pub.public_H`; the
numbers by `fs_in_scope` (Johnson/Desc/Kinds/Law/HeadFsWritten.lean), `plan_in_scope` and
`hS_in_scope` (Johnson/Goal/Meaning/HeadShapeScope.lean). `head_tau_in_scope`: `head_walk`
(OnBytes/Model/Fit/HeadWalk.lean), `shapeF_caps` (ShapeFCaps.lean), `scan_of_scope`
(Johnson/Goal/Meaning/ScopeScanTies.lean). `head_rows_in_scope`: `Fo.Pub.public_H_rows`; the
matrices are the written list; ONE CLOSED FACT BY LEAN's KERNEL. THE NUMBERS: 297 claims in all, 82
and 175 of them the two lookups' sides' (`claimsH`, OnBytes/Model/HeadPlan.lean, has further
summands); 24,641,536 indices of the ties and 11,904 of the 93 reads. `head_left_is_rows`:
`firstB_is` (Johnson/Desc/First/Link/Law/K9RowsAskLaw.lean), `Fo.equationsF_sum` (FoTopOf.lean),
`public_H_mS` (Johnson/Desc/Kinds/Law/HeadPlanMs.lean), and NM = the number of matrices
(`Meaning.planH2_nm`).

Limits. Those of the statements. Nothing on any property.
-/
import Johnson.P1K8R.HeadRowsInScopeStatement
import Johnson.Desc.First.Link.Law.K9RowsAskLaw
import Johnson.Desc.First.Link.Law.K9ReadsHeadPaid
import Johnson.Desc.Kinds.Law.HeadPlanMs
import OnBytes.Model.Fit.HeadWalk
import OnBytes.Model.Fit.ShapeFCaps
import OnBytes.Tie.Pv.Lookup.Ends.FoTopOf
import Johnson.Goal.Meaning.HidPlanNM

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K8
open OnBytes OnBytes.Model
open OnBytes.Model.Head (Shape HL Border Owner HPlanH2 matsH planH2)
open OnBytes.Road (ok_of_bind)
open OnBytes.Tie.Pv.Tail.Port (firstOf)
open VerifiableInference.Desc.K9Asks (firstB firstB_is readsHN readsHN_is)
open VerifiableInference.Desc.Kinds.Head.Law.InScope (matsW plan_in_scope fs_in_scope
  border_in_scope public_H_mS)

/-- One opening of the head's plan: `planH2_parts`' own, with the number of claims. -/
theorem planH2_claims {g : Settings} {h : Shape} {L : HL} {b : Border} {O : Owner} {NGr lkW : ℕ}
    {hp : HPlanH2} (hpl : planH2 g h L b O NGr lkW = .ok hp) :
    ∃ (stream : TMat) (t1 : HTailF2) (r : HTailF2 × Fork × Tail2) (Tp2 : Tail2),
      ({ tau := g.tau, lidb := g.lidb } : HTailF2).shape (matsH h L b (1 + NGr) stream.aId)
        (Array.replicate (matsH h L b (1 + NGr) stream.aId).size none)
        #[{ name := "PXf0", K := b.kxb, a := 2, m := b.mxb, wp := 0 }]
        #[false, false, true, false] g.tau = .ok t1 ∧
      t1.addTrees {} {} #[0, 0, Head.readsLength h L b] #[] (g.hb - g.pow) g.hb = .ok r ∧
      Head.ownerHeld O NGr r.1 r.2.1 Tp2 = .ok hp.tl ∧
      hp.nLin = Head.claimsH h L t1 (Head.readsH h L b) := by
  unfold Head.planH2 at hpl
  obtain ⟨-, -, hpl⟩ := ok_of_bind hpl
  obtain ⟨-, -, hpl⟩ := ok_of_bind hpl
  obtain ⟨-, -, hpl⟩ := ok_of_bind hpl
  obtain ⟨-, -, hpl⟩ := ok_of_bind hpl
  obtain ⟨pc, -, hpl⟩ := ok_of_bind hpl
  obtain ⟨-, -, hpl⟩ := ok_of_bind hpl
  cases hs : O.tl.mats[O.iXO]? with
  | none =>
    simp only [hs] at hpl
    have h' : (Except.error "internal-h-owner-TX" : Except String HPlanH2) = .ok hp := hpl
    cases h'
  | some M0 =>
    simp only [hs] at hpl
    obtain ⟨stream, -, hpl⟩ := ok_of_bind (x := (pure M0 : Except String TMat)) hpl
    obtain ⟨t1, h1, hpl⟩ := ok_of_bind hpl
    obtain ⟨-, -, hpl⟩ := ok_of_bind hpl
    obtain ⟨r, hr, hpl⟩ := ok_of_bind hpl
    obtain ⟨-, -, hpl⟩ := ok_of_bind hpl
    obtain ⟨Tp2, -, hpl⟩ := ok_of_bind hpl
    obtain ⟨t3, h3, hpl⟩ := ok_of_bind hpl
    obtain ⟨-, -, hpl⟩ := ok_of_bind hpl
    have e := (Except.ok.inj hpl).symm
    subst e
    exact ⟨stream, t1, r, Tp2, h1, hr, h3, rfl⟩

/-- **The number of claims, at the plan's own data.** -/
theorem planH2_nLin : PlanH2NLin := by
  intro g h L b O NGr lkW hp hpl
  obtain ⟨stream, t1, r, Tp2, -, hr, h3, e⟩ := planH2_claims hpl
  obtain ⟨t2, Fp, Tp⟩ := r
  have ef : hp.tl.f9 = t1.f9 :=
    (Fo.ownerHeld_zkeep h3).2.2.2.trans (Fo.addTreesF_zkeep (tl := t1) hr).2.2.2
  have eN : hp.tl.NM = t1.NM :=
    (OnBytes.Road.Hd.ownerHeld_keeps h3).2.trans (OnBytes.Road.addTrees_keeps hr).2
  rw [e]
  unfold Head.claimsH HTailF2.lins HTailF2.linsF
  rw [ef, eN]

section
variable {Pb : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : Option ByteArray} {X : Verify.Public}

/-- In scope the head's plan has 93 reads. -/
theorem head_reads_93 (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (hpub : Verify.publicOf Pb.pol Pb.KL lay = .ok X) :
    Head.readsH X.hS X.HLy (Verify.borderOf X.layers.y) = 93 := by
  have eS := _root_.Meaning.HeadS.hS_in_scope hS hR hpub
  have eN : X.hS.NHf = 4 := by rw [eS]; rfl
  have eA : X.hS.la = 16 := by rw [eS]; rfl
  have eL : X.hS.lt = 10 := by rw [eS]; rfl
  have C := OnBytes.Road.Hd.core_of_scope hS hR hpub
  have Bc := (OnBytes.Road.Hd.eleven_of_core hpub C (OnBytes.Road.Hd.npOf X.hS)).1
  have Nm := OnBytes.Road.Hd.numH_of_layout Bc.full Bc.head
  have hb : Verify.borderOf X.layers.y = VerifiableInference.Desc.Kinds.Head.Law.Cond.bFull :=
    border_in_scope hS hR hpub
  rw [readsHN_is, eN, eA, eL, Nm.m, Nm.mD, Nm.mR, hb]
  decide

/-- In scope the head's smallness test has 128 combinations. -/
theorem head_tau_in_scope (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (hpub : Verify.publicOf Pb.pol Pb.KL lay = .ok X) : X.H.tl.tau = 128 := by
  obtain ⟨⟨m, f, tl1, hsh, -, ht⟩, -⟩ := OnBytes.Model.Verify.head_walk hpub
  have hP := OnBytes.Road.Hd.scan_of_scope hS hR hpub
  have gtau : X.P.settings.tau = 128 := by rw [hP]; rfl
  exact ht.trans ((OnBytes.Model.shapeF_caps hsh).2.2.2.trans gtau)

end

/-- **In scope the head's plan has 297 linear claims.** -/
theorem head_nLin_in_scope : HeadNLinInScope := by
  intro Pb pp lay X hS hR hpub
  obtain ⟨H0, hpl, eH⟩ := Fo.Pub.public_H hpub
  have PW := plan_in_scope hS hR hpub
  have F := fs_in_scope hS hR hpub
  have eS := _root_.Meaning.HeadS.hS_in_scope hS hR hpub
  have eX : X.hS.XL = 5 := by rw [eS]; rfl
  have e1 : X.H.nLin =
      Head.claimsH X.hS X.HLy X.H.tl (Head.readsH X.hS X.HLy (Verify.borderOf X.layers.y)) := by
    rw [eH]
    show H0.nLin =
      Head.claimsH X.hS X.HLy H0.tl (Head.readsH X.hS X.HLy (Verify.borderOf X.layers.y))
    exact planH2_nLin _ _ _ _ _ _ _ H0 hpl
  rw [e1, head_reads_93 hS hR hpub]
  unfold Head.claimsH Forest.lins Forest.Shape.v Forest.Shape.d HTailF2.lins HTailF2.linsF
    Forest.lins Forest.Shape.v Forest.Shape.d
  rw [F.dT, F.rK, F.kT, F.cK, PW.dT, PW.rK, PW.kT, PW.cK, PW.nm, eX]
  decide

/-- **In scope the head's batching's round is planned with 24,653,737 rows.** -/
theorem head_rows_in_scope : HeadRowsInScope := by
  intro Pb pp lay X hS hR hpub
  have PW := plan_in_scope hS hR hpub
  rw [Fo.Pub.public_H_rows hpub, head_nLin_in_scope Pb pp lay X hS hR hpub,
    head_reads_93 hS hR hpub]
  unfold HTailF2.equationsF HTailF2.stepF
  rw [PW.mats, head_tau_in_scope hS hR hpub]
  decide +kernel

/-- **The test's left side at the head's plan.** -/
theorem head_left_is_rows : HeadLeftIsRows := by
  intro pol KL lay X hpub n
  obtain ⟨H0, hpl, eH⟩ := Fo.Pub.public_H hpub
  have hnm : X.H.tl.NM = X.H.tl.mats.size := by
    rw [eH]
    show H0.tl.NM = H0.tl.mats.size
    exact _root_.Meaning.planH2_nm hpl
  rw [firstB_is, Fo.equationsF_sum]
  unfold firstOf
  rw [← hnm]
  congr 1
  exact Finset.sum_congr rfl fun nu hnu => by
    rw [public_H_mS hpub nu (Finset.mem_range.1 hnu)]

end P1K8

-- Each line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms P1K8.planH2_claims
#print axioms P1K8.planH2_nLin
#print axioms P1K8.head_reads_93
#print axioms P1K8.head_tau_in_scope
#print axioms P1K8.head_nLin_in_scope
#print axioms P1K8.head_rows_in_scope
#print axioms P1K8.head_left_is_rows
