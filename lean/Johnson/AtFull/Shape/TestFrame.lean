-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Shape/TestFrame.lean: THE PROXIMITY TEST ON THE REQUEST's GROUP (the kind K12) AT ITS
SEAT IN THE PROOF FILE's OWN FIRST CHAIN (member 354 of the flat list), IN THE FRAME's OWN FORM: ONE
OF THE TWO PREMISES THAT THE RULE FOR ACCEPTANCE ASKS AT A MEMBER: Carries
(Johnson/Desc/ProofFile/Honest/Thread/Shape.lean), at the reader shA of
Johnson/AtFull/Shape/FrameForm.lean: the chain's shape AND THE ROWS' MAKES. Under the head
P5J.AtMgA. A joining of laws; nothing is evaluated.

Carries ALONE: Returns IS NOT STATED IN THIS FILE: THIS MEMBER DOES NOT COUNT AS PAID.
TestReturnsFrame.lean states Returns at 354 on three roads: under a premise that ties the step and
the tests to its guard (test_returns_frame); at a step with that guard in front, with testV as the
test on values (test_returns_guarded); at any step, so at testA too, with the guard among the tests
on values (test_returns_vals). At testA with testV alone that file does not state it: by its own
word no law gives the guard from testGS's return. See the bad result in its head.

  `test_forms_at`: the member b at number 354 of cF.blocksInOrder is such that, where b says yes from s to t,
    the shape of s holds the finish's part f and testMk (Johnson/Desc/First/Shape/TestForms.lean) at
    the shape's core, f's group and mask and the makes of s returns the makes of t. From a yes
    alone.
  **`testA p`**: THE STEP ON ShA: testGS p (TestAtHead.lean) on the chain's shape; testMk p on the
    makes.
  **`test_strong`**: a yes of b from s to t ⊢ testA ‹the plan's numbers› (shA s) = some (shA t).
  **`test_frame`**: for every ft, G with G 354 = optE (testA (H2U.p12OfMade Zp.made)) and vals:
    Carries at 354.

Limits. As said above. No state is shown at which testA returns. G and vals are letters. test_frame
does not say that a member stands at 354 (test_forms_at and test_strong do). UNDER THE HEAD: that it
has a member is shown in scope, where the reader returns and `protocolDataWellFormed` accepts (`head_of_live`,
Johnson/P5J/HeadOfLive.lean); that these three hold together, at two named sets of public files, in
a side library. At the earlier hash. Nothing on soundness, completeness or hiding.
-/
import Johnson.AtFull.Shape.TestAtHead
import Johnson.AtFull.Shape.SwitchFrames
import Johnson.Desc.First.Shape.TestForms

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Chain KindName)
open VerifiableInference.Desc.K12 (proximityTestKind guardedProximityTestParts atFinish T12)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Shape
open OnBytes.Maker (WholeD)
open P5J (AtMgA)
open ProofFile.Honest (Carries)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

theorem test_forms_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    ∃ b : Block S ProofFile.Cl, cF.blocksInOrder[354]? = some b ∧
      ∀ s rs gs t, b.decide s rs gs = .ok t →
        ∃ f, (chainSh s).fin = some f ∧
          testMk (H2U.p12OfMade Zp.made) (chainSh s).core f.fr.group f.mask (formsOf s.st) =
            some (formsOf t.st) := by
  obtain ⟨he, ha⟩ := test_plan_at h
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨-, ⟨b, b', eb, -, rfl, la⟩, -, -⟩ := IM.back_of O
  have q := (IM.back_numbers h.scope h.reads O).1 1 b eb
  have hy := IM.yes_alone la (by intro k; cases k)
  refine ⟨_, q, fun s rs gs t hd => ?_⟩
  have h1 : (atFinish (H2U.p12OfMade Zp.made)).decide s rs gs = .ok t := ((hy s t rs gs).1 hd).1
  obtain ⟨o, t', ho, hw, hf, hk, rfl⟩ :=
    VerifiableInference.Desc.K12.Seat.atFinish_ok _ s t rs gs h1
  have hc := k12_mk _ he ha ⟨s.st, s.book, s.roots, o.fr.group, .nothing, o.mask⟩ t' rs gs hk
  obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := s
  simp only at ho hc
  subst ho
  exact ⟨finSh o, rfl, hc⟩

/-- **THE STEP ON ShA.** -/
def testA (p : VerifiableInference.Desc.K12.P12) (y : ShA) : Option ShA :=
  (testGS p y.1).bind fun a => y.1.fin.bind fun f =>
    (testMk p y.1.core f.fr.group f.mask y.2).map fun F => (a, F)

theorem test_strong (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    ∃ b : Block S ProofFile.Cl, cF.blocksInOrder[354]? = some b ∧
      ∀ s rs gs t, b.decide s rs gs = .ok t →
        testA (H2U.p12OfMade Zp.made) (shA s) = some (shA t) := by
  obtain ⟨b, hb, hc⟩ := test_carries_at h
  obtain ⟨b₂, hb₂, hm⟩ := test_forms_at h
  obtain rfl : b = b₂ := Option.some.inj (hb.symm.trans hb₂)
  refine ⟨b, hb, fun s rs gs t hd => ?_⟩
  obtain ⟨f, hf, hF⟩ := hm s rs gs t hd
  show ((testGS (H2U.p12OfMade Zp.made) (chainSh s)).bind fun a => (chainSh s).fin.bind fun f =>
    (testMk (H2U.p12OfMade Zp.made) (chainSh s).core f.fr.group f.mask (formsOf s.st)).map
      fun F => (a, F)) = _
  rw [hc s rs gs t hd, Option.bind_some, hf, Option.bind_some, hF]
  rfl

theorem test_frame (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (ft : Nat)
    (G : Nat → ShA → Except String ShA)
    (vals : Nat → S → List Fmt.RoundView → List (List (Nat × List UInt64)) → Bool)
    (hG : G 354 = optE (testA (H2U.p12OfMade Zp.made))) :
    Carries cF.blocksInOrder ft (firstZA G vals) 354 := by
  obtain ⟨b, hb, hc⟩ := test_strong h
  exact carries_of_strong hb hc ft G vals hG

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.test_forms_at
#print axioms Johnson.AtFull.Shape.test_strong
#print axioms Johnson.AtFull.Shape.test_frame
#print axioms Johnson.AtFull.Shape.testA
