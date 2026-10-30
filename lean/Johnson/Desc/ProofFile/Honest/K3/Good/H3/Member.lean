-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Good/H3/Member.lean: the kind "lookup" (K3): the bound at each of
the lookups' marks at a proof file's first chain (`k3Marks`, Honest/K3/Good/MarksList.lean), at the
member at the mark's place, at every condition on the challenges in front. Conditional. Theorems.

Terms. Honest/K3/GLOSSARY.md: see there mark (in the frame's sense), site, member, share and kit. In
this file: C is a kit; cap and kap are letters (Honest/K3/Good/H3/Defs.lean).

What is shown.
  `site_face_facts`: what the walk needs of a site's face: two planes at least; one part of keys, of
    a bit at least; the form of the leaf's factor. No hypothesis but the site.
  `k3Marks_debt_cap`: **the bound**, general in the kit: the frame's `MarkDebt`
    (Honest/Law/CoverJoin.lean) at the stated share's numerator times kap.
  `k3Marks_debt_blocks`: the same at the kit `Run.ckP .two` (strings of hash blocks), whose three
    clauses are the frame's `kit_two` (Honest/Law/KitTwo.lean).

How the proof goes. `k3Marks_debt` (Honest/K3/Good/MarksHead.lean) has the bound at the condition
"true" under three hypotheses at each site at the mark's place. `member_at_site` hands the plan's
entries; `canAll_of_plan`, `fewAll_of_cap`, `fewOutEvents_of_cap` and `leafFew_of_cap` show the
three; `markDebt_any` carries the bound to every condition.

Hypotheses that remain.
  `hC`: the three clauses on the kit (in `k3Marks_debt_cap`).
  `hcap`: `KitCap`: at strings of hash blocks it can be had by one call of `P1K8.kit_count_blocks`
    (Johnson/P1K8R/KitCount.lean), with cap that lemma's right side at one
    element. That call is not made here: no file of this folder spells that term.
  `h`: `P5J.AtMgA`: the library's hypothesis at the full size.
  `hkap`: `CapsUnder` at every site: every listed round's bound is at most kap; the listed rounds
    are the events' rounds of both marks, and alpha's. Shown by nobody. It is asked at every site,
    though one mark needs the site at its place alone.
  `hm`, `hb`, `hp`, `hf`: the mark; the member; they share a place; the data bear its rounds.


Users. Honest/K3/Good/H3/Join.lean.

Limits. The number is the stated share's numerator times a letter: the stated shares are not shown
to be held, and no number is named or evaluated (at which kap the bound says nothing:
Honest/K3/Good/MarkShare.lean, Limits). The measure is the uniform law on the member's messages:
that the messages of any run have it is not said. What a mark's silence gives is not treated. The
ground G₀ is a free letter: the list does not read it. No instance of these hypotheses is exhibited
in this file.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Good.MarksHead
import Johnson.Desc.ProofFile.Honest.K3.Good.H3.AnyP
import Johnson.Desc.ProofFile.Honest.K3.Good.H3.MemberAtSite
import Johnson.Desc.ProofFile.Honest.K3.Good.H3.CanAllPlan
import Johnson.Desc.ProofFile.Honest.K3.Good.H3.LeafOfCap
import Johnson.Desc.ProofFile.Honest.K3.Law.SitesOk
import Johnson.Desc.ProofFile.Honest.Law.KitTwo
import OnBytes.Tie.Pv.Lookup.Forest.FoHole

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Good
open scoped ENNReal
open VerifiableInference.Desc (Block Chain fieldPrimeWord)
open OnBytes.Maker (RDT WholeD)
open _root_.Run.PQ (CK)
open P5J (AtMgA TS)

/-- What the walk needs of a site's face. No premise but the site. -/
theorem site_face_facts (Zp : ProofFile.Pub) (s : Site) (hs : s ∈ lookSites Zp) :
    2 ≤ s.at_.face.planes ∧ s.at_.face.parts = [s.shape.v] ∧ 1 ≤ s.shape.v ∧ LeafForm s.at_.face
    := by
  obtain ⟨h1, h2⟩ := Law.sites_shape_ok Zp s hs
  have hv := Cb.Fo.ok_v h2
  rw [h1]
  refine ⟨?_, rfl, by omega, ?_⟩
  · show 2 ≤ 32
    omega
  · unfold LeafForm
    exact ⟨_, fun _ _ _ => rfl⟩

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **CONDITIONAL on the kit's three clauses, on KitCap, on P5J.AtMgA and on CapsUnder at every
site: the bound at each of the lookups' marks, at the member at its place, at every P.** The number
is the stated share's numerator times a letter; the bound that pays it is hkap, over hC and hcap, by
name. -/
theorem k3Marks_debt_cap (C : CK)
    (hC : ∀ e k (c : C.Ch e k), H2K.Fit.FitsDrawn e k (C.dr e k c) ∧
      (∀ z ∈ (C.dr e k c).elems, z.1 < fieldPrimeWord ∧ z.2.1 < fieldPrimeWord ∧ z.2.2 < fieldPrimeWord) ∧
      ((C.dr e k c).digest = none ∨ k = .sealed))
    (cap : Fmt.Entry → Fmt.Kind → ℝ≥0∞) (hcap : KitCap C cap)
    (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (G₀ : ProofFile.Ground) (kap : ℝ≥0∞)
    (hkap : ∀ s ∈ lookSites Zp, CapsUnder cap s.at_.face (s.p.entries.getD []) kap)
    {mk : Mark} (hm : mk ∈ k3Marks Zp G₀) {b : Block TS ProofFile.Cl} (hb : b ∈ cF.blocksInOrder)
    (hp : mk.place = b.place) (dsb : List RDT) (hf : List.Forall₂ KindFits dsb b.rounds)
    (P : List Fmt.Drawn → Prop) :
    MarkDebt C mk dsb P ((mk.share.num : ℝ≥0∞) * kap) := by
  refine markDebt_any C mk dsb _ (k3Marks_debt C kap Zp G₀ mk hm dsb fun s hs hsp => ?_) P
  obtain ⟨f2, fp, f1, fT⟩ := site_face_facts Zp s hs
  obtain ⟨hr, hes⟩ := member_at_site h s hs b hb (hp.symm.trans hsp.symm)
  rw [hr] at hf
  have h1 : ∀ v ∈ s.at_.face.parts, 1 ≤ v := by
    intro v hv
    rw [fp] at hv
    obtain rfl := List.mem_singleton.1 hv
    exact f1
  exact ⟨canAll_of_plan C hC _ _ hes dsb hf,
    fewAll_of_cap C cap hcap _ f2 _ hes dsb hf kap (hkap s hs),
    And.intro (fewOutEvents_of_cap C cap hcap _ f2 h1 _ hes dsb hf kap (hkap s hs))
      (leafFew_of_cap C cap hcap _ _ fp f2 fT _ hes dsb hf kap (hkap s hs))⟩

/-- The same AT THE KIT Run.ckP .two, whose three clauses are paid. CONDITIONAL on KitCap at that
kit, on P5J.AtMgA and on hkap. -/
theorem k3Marks_debt_blocks (cap : Fmt.Entry → Fmt.Kind → ℝ≥0∞)
    (hcap : KitCap (_root_.Run.ckP .two) cap) (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (G₀ : ProofFile.Ground) (kap₃ : ℝ≥0∞)
    (hkap : ∀ s ∈ lookSites Zp, CapsUnder cap s.at_.face (s.p.entries.getD []) kap₃)
    {mk : Mark} (hm : mk ∈ k3Marks Zp G₀) {b : Block TS ProofFile.Cl} (hb : b ∈ cF.blocksInOrder)
    (hp : mk.place = b.place) (dsb : List RDT) (hf : List.Forall₂ KindFits dsb b.rounds)
    (P : List Fmt.Drawn → Prop) :
    MarkDebt (_root_.Run.ckP .two) mk dsb P ((mk.share.num : ℝ≥0∞) * kap₃) :=
  k3Marks_debt_cap (_root_.Run.ckP .two) kit_two cap hcap h G₀ kap₃ hkap hm hb hp dsb hf P

end ProofFile.Honest.K3.Good

#print axioms ProofFile.Honest.K3.Good.site_face_facts
#print axioms ProofFile.Honest.K3.Good.k3Marks_debt_cap
#print axioms ProofFile.Honest.K3.Good.k3Marks_debt_blocks
