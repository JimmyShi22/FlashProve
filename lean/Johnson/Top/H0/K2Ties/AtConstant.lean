-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/- Johnson/Top/H0/K2Ties/AtConstant.lean: WHAT IS OWED FOR THE CODE SWITCH's FIFTH TIE (`K2Owes`,
    T5.lean), HELD AGAINST THE COMPOSED MEANING's CLOSED CONSTANT (`P5J.mgAtAll`,
    Johnson/P5J/MgAtAll.lean). One definition, seven theorems. A law file: no
    sub-protocol imports it.

Why. A tie over parameters says something only at the closed values. Here each field of `K2Owes`
    that hangs on a parameter of the composed meaning is shown, or brought down to a named test, at
    the constant's own terms (Johnson/P5J/LettersAll.lean).

What is said, at D := `constD h`, the constant's own structure of parameters under its head h :
    `P5J.AtMgA …`.
  `decBlind_iff_noRec`: `DecBlind` (Dec.lean) IS, WORD FOR WORD,
      `First.Look.Stored.NoRec` (Johnson/Desc/First/Look/K3StoredThree.lean): the two are one
      sentence. (`DecBlind` is general in the type of cells and stands in a file with few imports.)
  `decBlind_at`: PAID: by `P5J.At.noRec_decT`.
  `reqBlind_at`: PAID: the reader of the request reads the public part alone.
  `hidBears_at`: from the named test with code `P5J.AtMg.offC`, by `P5J.AtMg.hid_bears`
      (Johnson/P5J/HidBearsAtMg.lean), at every list of tenants and every m.
      (`PlacesOffPad` itself follows from that test there.)
  `bookFacts_at`: under the head with the facts on reached states (`P5J.AtMgR`): `BookFacts`
      (FenceOf.lean) at every reached state without a mark: five projections, at the listed places L
          and the shapes of the first chain's oracle messages; THE FIRST TREE's NUMBER IS 0 BY THE
          DEFINITION OF THE FOLD's DATA (`P5J.At.foldD`, Johnson/P5J/FoldAt.lean).
  `links_same`: the list of segments at which the tests of Table.lean, FenceOf.lean and
      PubBehind.lean have been evaluated is the constant's.
  `fence_at`: the field fence.

Limits. A MEMBER OF THE CONSTANT's HEAD IS PROVED AT `storedPublicFiles` AND `zGap` ALONE (AT secondHashFunction; SIDE
LIBRARY AtFullSide/Top/). Whether the
    test `offC` accepts at the release's own files is a run's matter.
    Not paid here: left, headBack, headBears, base, indexOff's test, smp, and the one test on the
    plan in `fence_at`. No soundness is claimed.

Terms: lean/GLOSSARY.md.
-/
import Johnson.P5J.MgAtAll
import Johnson.P5J.AtMgR
import Johnson.P5J.HidBearsAtMg
import Johnson.Top.H0.K2Ties.FenceOf

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Ties
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Chain Place Wit)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (ModelPart Item start openSets)
open P5J (AtMgA AtMgR At.noRec_decT PlacesOffPad hid_bears TS)

/-- The two are one sentence. -/
theorem decBlind_iff_noRec {P S₁ : Type} {rows cols : ℕ}
    (decT : (ℕ → Option (ℕ × List UInt64)) → P × S₁ → Option (First.Look.Stored.CellsW rows cols)) :
    DecBlind decT ↔ First.Look.Stored.NoRec decT := Iff.rfl

/-- The written list of segments is the constant's. -/
theorem links_same : linksFull = P5J.At.links := rfl

section
variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- The constant's own structure of parameters (AtMgA.𝔇, MgAtAll.lean, under a short name). -/
noncomputable abbrev constD (h : AtMgA o Z D r Zp Np cF x) := AtMgA.𝔇 h

/-- **PAID**: the constant's decoder of the committed table does not read the verifier's state. -/
theorem decBlind_at (h : AtMgA o Z D r Zp Np cF x) : DecBlind (constD h).decT :=
  P5J.At.noRec_decT o Zp Np cF (P5J.At.EAt Z) h.plan.shape

/-- **PAID**: the constant's reader of the request reads the public part alone. -/
theorem reqBlind_at (h : AtMgA o Z D r Zp Np cF x) (z : ProofFile.InstPub)
    (s s' : First.S) : (constD h).H.req (z, s') = (constD h).H.req (z, s) := rfl

/-- From the named test "every named place is off the pads", by that test's own file's theorem. -/
theorem hidBears_at (h : AtMgA o Z D r Zp Np cF x) (hC : h.toAtMg.offC = true)
    (T : List (ℕ × ℕ)) (m : ℕ) : HidBears (constD h).H T m :=
  hidBears_of_eq _ T m fun w w' hw => h.toAtMg.hid_bears hC (constD h) T w w' hw

end

section
variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {A : Type} {Rch : ℕ → A → Prop}
  {at_ : A → ProofFile.InstPub × TS} {L : VerifiableInference.Desc.K12.Door.Laid}

/-- Five projections; the first tree's number is 0 by the definition of the fold's data. -/
theorem bookFacts_at (hR : AtMgR o Z D r Zp Np cF Rch at_ L) (k : ℕ) (a : A) (hr : Rch k a)
    (hm : (at_ a).2.failed = none) :
    BookFacts L (VerifiableInference.Desc.K12.Door.msgsOfChain Zp.made.proof.1) (at_ a).2 :=
  ⟨hR.fold.bookInOrder k a hr hm, hR.fold.seatsCarried k a hr hm,
    hR.fold.bookFits k a hr hm, hR.fold.msgShapes k a hr hm, hR.fold.pileMasks k a hr hm⟩

end

section
variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  {Fr : Frame}
  {Rch : ℕ → (ProofFile.InstPub × TS) × Fr.E.Str → Prop} {L : VerifiableInference.Desc.K12.Door.Laid}

/-- **The field fence of `K2Owes` at the constant**: from the head with the facts on reached states,
the table's test "the index masks' pin is open in front of k" and one test on the plan. -/
theorem fence_at (h : AtMgA o Z D r Zp Np cF x)
    (hR : AtMgR o Z D r Zp Np cF Rch Prod.fst L) (k : ℕ) (z : ProofFile.InstPub)
    (hI : pinOpenB P5J.At.links P5J.At.ps k = true)
    (hP : L.places[(P5J.At.N Zp cF).indexNo]? = some (P5J.At.N Zp cF).index) :
    ∀ a : First.S × Fr.E.Str,
      fenceAt (constD h) mgBase P5J.At.links P5J.At.ps k z (fun a => Rch k ((z, a.1), a.2)) a →
      IndexFence (constD h).N (VerifiableInference.Desc.K12.Door.msgsOfChain Zp.made.proof.1) L a.1
          :=
  fun a ha => indexFence_of (constD h) mgBase _ _ k z L _ a ha.1 ha.2.2
    (pinOpen_of_B _ _ _ hI) (bookFacts_at hR k ((z, a.1), a.2) ha.2.1 ha.2.2) hP

end

end VerifiableInference.Desc.First.K2Ties

#print axioms VerifiableInference.Desc.First.K2Ties.decBlind_iff_noRec
#print axioms VerifiableInference.Desc.First.K2Ties.links_same
#print axioms VerifiableInference.Desc.First.K2Ties.decBlind_at
#print axioms VerifiableInference.Desc.First.K2Ties.reqBlind_at
#print axioms VerifiableInference.Desc.First.K2Ties.hidBears_at
#print axioms VerifiableInference.Desc.First.K2Ties.bookFacts_at
#print axioms VerifiableInference.Desc.First.K2Ties.fence_at
