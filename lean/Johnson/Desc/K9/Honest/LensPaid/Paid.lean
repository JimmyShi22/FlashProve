-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K9/Honest/LensPaid/Paid.lean (kind K9): the public test `LensEqAsked` (Johnson/Desc/K9/Honest/LensEq.lean)
is a theorem in the goals' scope, and so under the library's head. The test says, at each of the 25 segments: the closed
numbers of claims of the segment's runs, added up, are the plan's number nLin. It holds because each planner computes
nLin as that very sum; what the equality leans on beside is pinned in scope.

  `lens_lay`        the test's equation at a layers' segment 2 g: the plan's number by `planG_nLin`, the reads by
                   `reads_lay_eq`, five limbs, routed experts and a second token sumcheck by ScopeFacts.lean
  `lens_att`        at an attention segment 2 g + 1: `planA_nLin`, `reads_att_public`; neither the scope nor a switch is
                   spent
  (`lens_head`      at segment 24: ScopeFacts.lean)
  `ledger_four_five`   the ledger's three numbers add up to 15 at four limbs and to 21 at five: by `rfl`
  **`lensEqAsked_in_scope`**   the scope, the reader's return, the pure road's public part Z and the verifier's own call
                   at the same three files ⊢ `LensEqAsked Z`. That a segment stands at each number, with the plan's
                   record of the smallness test: after the library's `nuAsked_in_scope`
                   (Johnson/Desc/First/Link/Law/K9NuPaid.lean), line by line
  **`lensEqAsked_of_head`**    from the library's head `P5J.AtMg`
  **`lensAsked_in_scope`, `lensAsked_of_head`**   so the library's own candidate `LensAsked` ("at most":
                   Johnson/Desc/First/Link/Law/K9LensAskLaw.lean), by `lensAsked_of_eq`

Where the test can say no (by reading; all out of scope; of the test itself no line here is an evaluation). At four
limbs the plan counts 15 claims for each instance of the ledger (`ledNO` + `ledNS` + `ledLines`,
OnBytes/Model/Ledger.lean: 3 + 7 + 5) and the test 21 (4 + 9 + 8, the numbers at five limbs): `ledger_four_five` holds
the two sums. Without routed experts, or with no call of the second token sumcheck, the plan lacks terms that the test
adds. Where a family of tables has no entry the test's reading of the tables returns nothing. So the switches are spent,
not idle.

Names. `lens_att` and `lens_head` are also short names of the library's, in another namespace, for other sentences
(Johnson/Desc/First/Link/Law/LensAtFront.lean).

Limits. In the goals' scope and at the full size alone. That the four premises are met at any files is no statement
here; ly is a free letter, tied to Pb's own layout file by no premise, as in the library's fellow. The road leans on
closed facts that Lean's kernel evaluates at written values, all in the library: `readsHead_written` beneath
`reads_head_eq`, and those beneath `layTables_in_scope`. A closed fact on the public part: no verifier asks the test,
and nothing is said of a run. No property of the protocol is claimed: nothing is said on its soundness, completeness,
binding or hiding.
-/
import Johnson.Desc.K9.Honest.LensEq
import Johnson.Desc.K9.Honest.LensPaid.ScopeFacts
import Johnson.Desc.K9.Honest.LensPaid.ReadsLay
import Johnson.Desc.K9.Honest.LensPaid.ReadsAtt
import Johnson.Desc.First.Link.Law.K9NuPaid

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model
open OnBytes.Model.Stages (SubPlanH LinkH)
open VerifiableInference.Desc (Chain K9Asks.pairsAt)
open VerifiableInference.Desc.K9Asks hiding pairsAt
open VerifiableInference.Desc.First.Att.P (planIs_public)

section
variable {Pb : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : Option ByteArray} {X : Verify.Public}

/-- The ledger's three numbers, added up, at four limbs and at five. -/
theorem ledger_four_five : ledNO 4 + ledNS 4 + ledLines 4 = 15 ∧ ledNO 5 + ledNS 5 + ledLines 5 = 21 := ⟨rfl, rfl⟩

/-- **The test's equation at a layers' segment.** -/
theorem lens_lay (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (hpub : Verify.publicOf Pb.pol Pb.KL lay = .ok X) {g : ℕ} (hg : g < 12) {hp : Layer.HPlan2}
    (hG : X.G[g]? = some hp) :
    ∃ a ps n, ownLenB X (2 * g) = some a ∧ K9Asks.pairsAt X (2 * g) = some ps ∧
      claimsAt X (2 * g) = some n ∧
      a + (4 + (hp.tl.NM + readsB hp.tl.NM hp.tl.mats ps)) + Forest.lins hp.tl.f9 = n := by
  obtain ⟨ps, h1, h2⟩ := reads_lay_eq hS hR hpub hg hG
  have hn := planG_nLin X.layers g _ hp (Fo.Pub.public_G hpub g hp hG)
  have n24 : 2 * g ≠ 24 := by omega
  have ev : 2 * g % 2 = 0 := by omega
  have dv : 2 * g / 2 = g := by omega
  refine ⟨_, ps, hp.nLin, by unfold ownLenB; rw [if_neg n24, if_pos ev, dv],
    by unfold K9Asks.pairsAt; rw [if_neg n24, if_pos ev, dv]; exact h1,
    by unfold claimsAt; rw [if_neg n24, if_pos ev, dv, hG]; rfl, ?_⟩
  rw [hn, h2]
  unfold Layer.claimsOf Layer.shownByTerms frontB HTailF2.lins HTailF2.linsF
  dsimp only
  rw [xl_in_scope hS hR hpub, p3_in_scope hS hR hpub, tsc_in_scope hS hR hpub]
  have e1 : ledNO 5 = 4 := rfl
  have e2 : ledNS 5 = 9 := rfl
  have e3 : ledLines 5 = 8 := rfl
  rw [e1, e2, e3]
  simp only [if_true, Bool.false_eq_true, if_false]
  rw [Nat.mul_add, Nat.mul_one]
  generalize (if (g == 0) = true then 1 else 0) = c
  generalize X.layers.y.NN * X.layers.y.Lam = u
  generalize X.layers.y.LamM * X.layers.y.h.NE = v
  omega

/-- **The test's equation at an attention segment.** -/
theorem lens_att (hpub : Verify.publicOf Pb.pol Pb.KL lay = .ok X) {g : ℕ} {a : Attention.Plan}
    (ha : X.A[g]? = some a) :
    ∃ b ps n, ownLenB X (2 * g + 1) = some b ∧ K9Asks.pairsAt X (2 * g + 1) = some ps ∧
      claimsAt X (2 * g + 1) = some n ∧
      b + (4 + (a.seam.tl.NM + readsB a.seam.tl.NM a.seam.tl.mats ps)) + Forest.lins a.seam.tl.f9 = n := by
  have h2 := reads_att_public (planIs_public hpub) ha
  obtain ⟨A0, pf, h0, e⟩ := planIs_public hpub g a ha
  have hn : a.nLin = Attention.ownClaims a.S a.fs (Attention.Counts.of a.S) +
      a.seam.tl.lins (Attention.tableReads a.S (Attention.Counts.of a.S)) := by
    rw [e]
    exact planA_nLin _ _ _ A0 h0
  have n24 : 2 * g + 1 ≠ 24 := by omega
  have od : ¬ (2 * g + 1) % 2 = 0 := by omega
  have dv : (2 * g + 1) / 2 = g := by omega
  refine ⟨_, attPairs a.S, a.nLin, by unfold ownLenB; rw [if_neg n24, if_neg od, dv, ha]; rfl,
    by unfold K9Asks.pairsAt; rw [if_neg n24, if_neg od, dv, ha]; rfl,
    by unfold claimsAt; rw [if_neg n24, if_neg od, dv, ha]; rfl, ?_⟩
  rw [hn, h2]
  unfold Attention.ownClaims attOwnB HTailF2.lins HTailF2.linsF
  dsimp only
  generalize a.S.NP * a.S.cf.lt = u
  omega

end

section
variable {Pb : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {ly : ByteArray} {o : ProofFile.SecondHashFunctionArgument} {Z : ProofFile.Pub}

/-- **The public test holds in the goals' scope.** -/
theorem lensEqAsked_in_scope (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (hZ : ProofFile.pureRoad.pub o Pb.pol ly Pb.KL = .ok Z)
    (hpub : Verify.publicOf Pb.pol Pb.KL (some ly) = .ok Z.p.X) : LensEqAsked Z := by
  obtain ⟨k4, kN, _, hAll⟩ := _root_.Meaning.scope_plans hS hR hpub
  have C := OnBytes.Road.Hd.core_of_scope hS hR hpub
  have hB : ProofFile.Plain.builtOf Z.p.X Z.p.chains = .ok Z.p.built :=
    IM.planned_built (ProofFile.Law.madeOf_planned (ProofFile.Law.pubBy_made
            (show ProofFile.pubBy (ProofFile.PlainG.madeOf o) ProofFile.plainStarts Pb.pol ly Pb.KL = .ok Z from hZ)))
  obtain ⟨l₀, h₀, hB⟩ := IM.plain_built hB
  unfold ProofFile.Plain.linksPlain at h₀
  rw [k4, kN] at h₀
  obtain ⟨_, _, _, p0, p24⟩ := OnBytes.L5.LinksOrder.listLinksH_with _ _ _ _ _ h₀
  obtain ⟨declared, hd⟩ := OnBytes.Road.K4.Names.built_declared hB
  obtain ⟨_, hat⟩ := OnBytes.L5.LinksOrder.declareLinks_at _ _ _ _ _ hd
  -- what every sort ends in
  have fin : ∀ (l : ℕ) (Y : LinkH), l₀[l]? = some Y →
      (∃ a ps n, ownLenB Z.p.X l = some a ∧ K9Asks.pairsAt Z.p.X l = some ps ∧
        claimsAt Z.p.X l = some n ∧
        a + (4 + (Y.tl.NM + readsB Y.tl.NM Y.tl.mats ps)) + Forest.lins Y.tl.f9 = n) →
      ∃ X, Z.p.built.links[l]? = some X ∧ lensEqB Z.p.X l X = true := by
    intro l Y hY hE
    obtain ⟨ar, har⟩ := hat l Y hY
    exact ⟨_, har, (lensEqB_iff _ l _).2 hE⟩
  intro l hl
  by_cases h24 : l = 24
  · subst h24
    exact fin 24 _ p24 (lens_head hS hR hpub)
  · have hg : l / 2 < 12 := by omega
    obtain ⟨a, ha, _⟩ := hAll (l / 2) hg
    obtain ⟨hp, hgp⟩ := _root_.Meaning.planG_there hpub C hg
    have s0 : (Z.p.X.G.map fun hp : Layer.HPlan2 =>
        ({ tl := hp.tl, Fp := hp.Fp, Tp := hp.Tp, ns := hp.ns, NCL := hp.NCL,
           run := ProofFile.Plain.notToBeRun } : SubPlanH))[l / 2]? =
        some { tl := hp.tl, Fp := hp.Fp, Tp := hp.Tp, ns := hp.ns, NCL := hp.NCL,
               run := ProofFile.Plain.notToBeRun } := by
      rw [Array.getElem?_map, hgp]
      rfl
    have t0 : (Z.p.X.A.map fun A : Attention.Plan =>
        ({ tl := A.seam.tl, Fp := A.seam.Fp, Tp := A.seam.Tp, ns := A.ns,
           run := ProofFile.Plain.notToBeRun } : SubPlanH))[l / 2]? =
        some { tl := a.seam.tl, Fp := a.seam.Fp, Tp := a.seam.Tp, ns := a.ns,
               run := ProofFile.Plain.notToBeRun } := by
      rw [Array.getElem?_map, ha]
      rfl
    obtain ⟨q0, q1⟩ := p0 (l / 2) _ _ s0 t0
    by_cases hev : l % 2 = 0
    · have el : 2 * (l / 2) = l := by omega
      have E := lens_lay hS hR hpub hg hgp
      rw [el] at q0 E
      exact fin l _ q0 E
    · have el : 2 * (l / 2) + 1 = l := by omega
      have E := lens_att hpub ha
      rw [el] at q1 E
      exact fin l _ q1 E

/-- So the library's own candidate, with "at most". -/
theorem lensAsked_in_scope (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (hZ : ProofFile.pureRoad.pub o Pb.pol ly Pb.KL = .ok Z)
    (hpub : Verify.publicOf Pb.pol Pb.KL (some ly) = .ok Z.p.X) : LensAsked Z :=
  lensAsked_of_eq (lensEqAsked_in_scope hS hR hZ hpub)

end

/-- **From the head.** -/
theorem lensEqAsked_of_head {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD}
    {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
    {cF : Chain VerifiableInference.Desc.First.S ProofFile.Cl} (h : P5J.AtMg o Z D r Zp Np cF) :
    LensEqAsked Zp :=
  lensEqAsked_in_scope h.scope h.reads h.laid.pub h.pubOne

/-- **The library's candidate, from the head.** -/
theorem lensAsked_of_head {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD}
    {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
    {cF : Chain VerifiableInference.Desc.First.S ProofFile.Cl} (h : P5J.AtMg o Z D r Zp Np cF) :
    LensAsked Zp :=
  lensAsked_of_eq (lensEqAsked_of_head h)

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.ledger_four_five
#print axioms ProofFile.Honest.K9.lens_lay
#print axioms ProofFile.Honest.K9.lens_att
#print axioms ProofFile.Honest.K9.lensEqAsked_in_scope
#print axioms ProofFile.Honest.K9.lensAsked_in_scope
#print axioms ProofFile.Honest.K9.lensEqAsked_of_head
#print axioms ProofFile.Honest.K9.lensAsked_of_head
