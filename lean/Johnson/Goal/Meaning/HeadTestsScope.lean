-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Meaning/HeadTestsScope.lean: IN THE GOALS' SCOPE THE TWO CHEAP PUBLIC TESTS planK6AtZ
AND padsAtZ (Johnson/Desc/Kinds/HeadDoorAtZ.lean) ACCEPT WHERE THE PUBLIC TEST madePinnedAt ACCEPTS
AND THE VALUE IS LAID: a verifier that asks that test need not ask these two. Theorems.




NOT FROM THE SCOPE ALONE. Each statement has four premises beside VerifierAndGoals.InScope W = true:
  h    ProofFile.pureRoad.pub o W.pol W.lay W.KL = .ok Z: Z is the public part of the IOP as written in
       Lean at W's three files and o.
  hy   madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true: other files' public test on the
       sizes, the lists of rounds, the request's layout, the sendings (and
       the shape of X) accepts. In scope, where the value is laid (LaidAt), it follows from the
       entry tests' row madeRow: P5J.pins_of_laid (Johnson/Goal/Skeleton/PinsOfLaid.lean).
  hl   LPFD.Full.proofDataAndDecisionOfPublicFiles o W.pol W.lay W.KL = .ok (D, r): the proof file's value is laid.
  hx   XPart Z.p.X (Goal/Meaning/HeadXPartScope.lean): seven equations on the public parameters. A
       theorem at publicOf's X, the second hash function, alone.

What is proved.
  seatsWritten_in_scope   under hW, h, hy, hl: SeatsWritten Z (Law/HeadViewsSeats.lean): by
          first_written_in_scope (MadeInScope.lean) and P5T.seats_in_scope (PlanSeatsTie.lean).
  **padsAtZ_in_scope**    under hW, h, hy, hl, hx: padsAtZ Z = true.
  **planK6AtZ_in_scope**  under hW, h, hy, hl, hx: planK6AtZ Z = true.
  tests_at_older          both, with hx's place taken by VerifierAndGoals.readFiles W = .ok pp and publicOf
          W.pol W.KL lay' = .ok Z.p.X. The letter o has one useful value there: at another o
          publicOf's return is in general not Z.p.X.
  **tests_at_olderK**     both, AT o := OnBytes.secondHashFunction, under hW, h, hy, hl ALONE: readFiles' return
          follows from hW (inScope_readFiles), publicOf's from h (ProofFile.Law.pub_public, with
          publicOfO_older).

No existential quantifier in these statements.
Not proved here. That madePinnedAt accepts at any files. That the value is laid. XPart at
the public parameters that another o gives. Nothing on soundness.

-/
import Johnson.Desc.Kinds.Law.HeadViewsSeats
import Johnson.P5T.PlanSeatsTie
import Johnson.Desc.ProofFile.Law.MakerPublic
import Johnson.Desc.Ok.PlanWritten.PublicAtLaws
import Johnson.Desc.K12.Law.Sizes.StageSizesAtScope

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.Kinds.Head.Law.OffPad

open VerifiableInference.PlanWritten (madePinnedAt)
open VerifiableInference.PlanWritten.Joined (first_written_in_scope)
open OnBytes.Model.Verify (publicOf)

variable {o : ProofFile.SecondHashFunctionArgument} {W : VerifierAndGoals.PublicFiles} {Z : ProofFile.Pub} {D : OnBytes.Maker.WholeD}
  {r : LPFD.Full.RunPF}

/-- The five equations, in scope, under h, hy and hl. -/
theorem seatsWritten_in_scope (hW : VerifierAndGoals.InScope W = true)
    (h : ProofFile.pureRoad.pub o W.pol W.lay W.KL = .ok Z)
    (hy : madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true)
    (hl : LPFD.Full.proofDataAndDecisionOfPublicFiles o W.pol W.lay W.KL = .ok (D, r)) : SeatsWritten Z := by
  obtain ⟨c, -, s, -, -, l⟩ := first_written_in_scope hW h hy
  obtain ⟨s1, s2, -⟩ := P5T.seats_in_scope hW h hy hl
  exact ⟨c, s, l, s1, s2⟩

/-- **In scope the second test accepts, under h, hy, hl and hx.** -/
theorem padsAtZ_in_scope (hW : VerifierAndGoals.InScope W = true)
    (h : ProofFile.pureRoad.pub o W.pol W.lay W.KL = .ok Z)
    (hy : madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true)
    (hl : LPFD.Full.proofDataAndDecisionOfPublicFiles o W.pol W.lay W.KL = .ok (D, r)) (hx : XPart Z.p.X) :
    padsAtZ Z = true :=
  padsAtZ_of_seats (seatsWritten_in_scope hW h hy hl) hx

/-- **In scope the first test accepts, under h, hy, hl and hx.** -/
theorem planK6AtZ_in_scope (hW : VerifierAndGoals.InScope W = true)
    (h : ProofFile.pureRoad.pub o W.pol W.lay W.KL = .ok Z)
    (hy : madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true)
    (hl : LPFD.Full.proofDataAndDecisionOfPublicFiles o W.pol W.lay W.KL = .ok (D, r)) (hx : XPart Z.p.X) :
    planK6AtZ Z = true :=
  planK6AtZ_of_seats h (seatsWritten_in_scope hW h hy hl) hx

/-- Both, where Z's public parameters are publicOf's. -/
theorem tests_at_older {pp : Inst.Model.ScalesAndPolicy} {lay' : Option ByteArray}
    (hW : VerifierAndGoals.InScope W = true) (hR : VerifierAndGoals.readFiles W = .ok pp)
    (h : ProofFile.pureRoad.pub o W.pol W.lay W.KL = .ok Z)
    (hy : madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true)
    (hl : LPFD.Full.proofDataAndDecisionOfPublicFiles o W.pol W.lay W.KL = .ok (D, r))
    (hp : publicOf W.pol W.KL lay' = .ok Z.p.X) : planK6AtZ Z = true ∧ padsAtZ Z = true :=
  ⟨planK6AtZ_in_scope hW h hy hl (xPart_in_scope hW hR hp),
    padsAtZ_in_scope hW h hy hl (xPart_in_scope hW hR hp)⟩

/-- **Both, at the second hash function itself, under hW, h, hy and hl alone.** -/
theorem tests_at_olderK (hW : VerifierAndGoals.InScope W = true)
    (h : ProofFile.pureRoad.pub OnBytes.secondHashFunction W.pol W.lay W.KL = .ok Z)
    (hy : madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true)
    (hl : LPFD.Full.proofDataAndDecisionOfPublicFiles OnBytes.secondHashFunction W.pol W.lay W.KL = .ok (D, r)) :
    planK6AtZ Z = true ∧ padsAtZ Z = true := by
  obtain ⟨pp, hR⟩ := H2K.Sizes.inScope_readFiles hW
  have hp : publicOf W.pol W.KL (some W.lay) = .ok Z.p.X :=
    (VerifiableInference.PlanWritten.publicOfO_older W.pol W.KL (some W.lay)).symm.trans
      (ProofFile.Law.pub_public h)
  exact tests_at_older hW hR h hy hl hp

end VerifiableInference.Desc.Kinds.Head.Law.OffPad

#print axioms VerifiableInference.Desc.Kinds.Head.Law.OffPad.seatsWritten_in_scope
#print axioms VerifiableInference.Desc.Kinds.Head.Law.OffPad.padsAtZ_in_scope
#print axioms VerifiableInference.Desc.Kinds.Head.Law.OffPad.planK6AtZ_in_scope
#print axioms VerifiableInference.Desc.Kinds.Head.Law.OffPad.tests_at_older
#print axioms VerifiableInference.Desc.Kinds.Head.Law.OffPad.tests_at_olderK
