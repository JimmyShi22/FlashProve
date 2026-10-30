-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/Twin/FirstSeatedAtReadsB.lean: MADE BY PROGRAM OFF
Johnson/Desc/AtSeats/FirstSeatedAtReads.lean UNDER A MAP OF NAMES AND ONE TURN OF THE
MEANING: 1 OF ITS DECLARATIONS: firstSeated_at_reads_b. THE PROOFS ARE COPIES.

This letter is for the honest run's own forms alone: no statement on any other party may take it.
NEVER ON SOUNDNESS's ROAD: at the meaning "honest" the
clauses noColl, shown and decodes are True by definition: a law at that meaning may stand beneath
statements on completeness or zero knowledge only, never beneath a statement on soundness.

The map of names. ReadsFence to ReadsFenceB; each twinned theorem n to n_b; the library's closed
facts at its wider table of names (mwMore) to their likes at mgMore, and its laws on the wider
meaning to their likes on "honest" over mgAll (both in Twin/HonestAt.lean, typed by hand).
The turn of the meaning. Where the elder has the wider meaning (mw1 Dm.N (d13 Dm) dk (mgAll Dm Mg₀),
or plus13 (d13 Dm) dk (mgAll Dm Mg₀)), the twin has honest (mgAll Dm Mg₀) ans test
(Johnson/Desc/ProofFile/Honest/Thread/First.lean): the meaning at which the honest thread's own
promise stands; at the item "tie": mgAll Dm Mg₀. The step down from mw1 to plus13 (inAt_down) falls.
The promise itself is the library's InAt: no new text of a promise.
Laid in, on no line of a statement: the letters ans and test, behind each block of letters: implicit
in the theorems, explicit in the structure ReadsFenceB; "include dk" where the source's block binds
dk (no twin's statement names it; it is kept so that a copied call has the source's number of
arguments). Kept as they stand in the source: its namespace, open, variable, section, set_option
and attribute lines, but for one prefix that makes dk implicit (in ArmAtReadsB.lean): there "omit dk
in" stands.
The namespace is the library's, so that a copied proof finds its callees without a sign turned; the
names with the suffix _b are not the library's.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.AtSeats.FirstSeatedAtReads
import Johnson.Desc.ProofFile.Honest.K1.Twin.HonestAt
import Johnson.Desc.ProofFile.Honest.K1.Twin.OpenAt342

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 40000

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.K1
open ProofFile.Honest.FirstThread (honest)
open VerifiableInference.Desc (Strs Wit)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound (CellsQ MsgT mgMore)
variable {ans : ℕ → ℕ → ProofFile.InstPub × S → Strs → Wit (P5J.CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT → Prop}
  {test : ℕ → S → Option String}
open OnBytes OnBytes.Params OnBytes.Model OnBytes.Slice OnBytes.Maker OnBytes.Flat Johnson.G
open VerifiableInference.Desc (Chain Place Oracle)
open VerifiableInference.Desc.First (S ModelPart Pub Numbers flatPlacesOf shift)
open VerifiableInference.Desc.First.FillSent
open VerifiableInference.Desc.Sound
open VerifiableInference.PlanWritten
open Johnson.Desc.First.Walk.Tied (RchAt rchAt_raw)
open ProofFile (Cl)
open IM (k1Ix)

/-- **FirstSeated in front of each segment's reads, at the closed constant.** -/
theorem firstSeated_at_reads_b {Zl : VerifierAndGoals.PublicFiles} {D : WholeD} {r₀ : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
    {Np : H2U.Places4} {cF : Chain S Cl} {x₀ : First.Look.Place}
    (hA : P5J.AtMgA OnBytes.secondHashFunction Zl D r₀ Zp Np cF x₀)
    (hP1 : madePinnedAt Zp.p.X.P Zp.p.chains.made Zp.first Zp.made = true)
    (hC : cutOf (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = cutFirstFull) :
    ∀ l, l < 25 → ∀ a,
      RchAt (Str := (Sound.frameAt (D.at frS.P.T.a) (Sound.allOf (D.at frS.P.T.a))
          (D.at frS.P.T.a).key₁ 0).E.Str)
        (P5J.F0T OnBytes.secondHashFunction Zp Np cF) (14 * l + k1Ix l false + 2) a →
      onQ hA.𝔇.N (honest (mgAll hA.𝔇 mgBase) ans test) linksFull (flatPlacesOf linksFull true) (fun a => a)
        (14 * l + k1Ix l false + 2) a →
      a.1.2.failed = none → ∀ A, K9.segAt? a.1.2 = some A →
      FirstSeated (hA.𝔇.N.sent l 0) A l := by
  intro l hl a hr hon hm A hseg
  obtain ⟨_, hL, -, -, hbook⟩ := segAt_some hseg
  have hIn : InAt hA.𝔇.N (honest (mgAll hA.𝔇 mgBase) ans test) linksFull (flatPlacesOf linksFull true)
      (14 * l + k1Ix l false + 2) a.1 (strsOf _ a.2) := ⟨hon, hm⟩
  have h0 : sentIsB hA.𝔇.pubD.dS l a.1.2 = true := by
    have h := inAt_pubQ hIn (.more (some l) "frame.sentIs") (by
      rw [VerifiableInference.Desc.K1.honest_more_closed _ mgBase ans test rfl]
      exact inSet_of (List.all_eq_true.1 sentIn_mg l (List.mem_range.2 hl)))
    rwa [VerifiableInference.Desc.K1.honest_pub_all, First.pubAll_more_sentIs] at h
  have hbk := inAt_bookHeld hIn
  unfold First.bookAt at hbk
  simp only [Bool.and_eq_true, beq_iff_eq] at hbk
  have hreach := rchAt_raw hr
  have hF := (K13.Law.factsK13_reached hA hP1 _ a.1 hreach hm).seats
  unfold K12.Door.atFirstSeats K12.Door.seatsCarriedB at hF
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hF
  obtain ⟨p, hp, hpl⟩ := link_two l hl false _ (Or.inl rfl)
  have hsh := (K13.Law.live_reached hA _ a.1 hreach hm hp hpl A.L hL).2
  have hl' := hA.laid.run ▸ LPFD.Full.laidPOf_of hA.laid.value hA.laid.planOk hA.laid.data
    hA.laid.asks
  have e1 : hA.𝔇.shape = proofSizedFull.request :=
    (Joined.first_written_in_scope hA.scope hA.laid.pub hP1).2.2.1
  have e2 : hA.𝔇.N.msgsAt = numsW.msgsAt := by
    show (fun p => First.msgsTold (P5J.At.told cF) (First.borderOf P5J.At.ps p)) = _
    rw [K13.Law.told_of_cut (cF := cF) hC]
    rfl
  have e3 : hA.𝔇.N.sent = numsW.sent := by
    show (P5T.numbersOf (P5T.planSeats Zp Zp.D.1)).sent = _
    rw [(P5T.seats_in_scope hA.scope hA.laid.pub hP1 hl').2.2]
    rfl
  rw [e3]
  refine firstSeated_of_B firstSeated_written hl (hsh.trans e1) (fun born k => ?_) ?_ ?_
  · rw [whereIs_of_sentIs hL h0 born k, ← e2, ← e1]
    rfl
  · rw [hbook, hbk.1.2, hbk.2, e2]
  · rw [hbook]
    exact hF.1.1.1

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.firstSeated_at_reads_b
