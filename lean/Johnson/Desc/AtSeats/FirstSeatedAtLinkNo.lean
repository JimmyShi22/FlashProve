-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/AtSeats/FirstSeatedAtLinkNo.lean: firstSeated_at_reads
(Johnson/Desc/AtSeats/FirstSeatedAtReads.lean) IN ITS USER's OWN FORM: at the state's own number of
the open segment, linkNo s, in the place of the letter l: the right side is JFirst N s
(Johnson/Desc/K1/Law/ArmAttIn.lean: not imported), written out.
  sentIs_at_reads   in front of segment l's reads the table's promise holds "frame.sentIs" at l
  linkNo_at_reads   so, where a segment is open, linkNo s = l (link_of_sentIs,
                    Johnson/Desc/First/FillSent.lean): AT ALL 25 SEGMENTS, off the promise alone
  **jFirst_at_reads**   ∀ A, K9.segAt? s = some A → FirstSeated (N.sent (linkNo s) 0) A (linkNo s)
PREMISES: as firstSeated_at_reads; the first two names take the head, the promise and "no mark"
alone.
What is not claimed. That the premises can be met together: NO MEMBER. Nothing on soundness.

-/
import Johnson.Desc.AtSeats.FirstSeatedAtReads

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 40000

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model OnBytes.Slice OnBytes.Maker OnBytes.Flat Johnson.G
open VerifiableInference.Desc (Chain Place Oracle)
open VerifiableInference.Desc.First (S ModelPart Pub Numbers flatPlacesOf shift)
open VerifiableInference.Desc.First.FillSent
open VerifiableInference.Desc.Sound
open VerifiableInference.PlanWritten
open Johnson.Desc.First.Walk.Tied (RchAt rchAt_raw)
open ProofFile (Cl)
open IM (k1Ix)

section
variable {Zl : VerifierAndGoals.PublicFiles} {D : WholeD} {r₀ : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain S Cl} {x₀ : First.Look.Place}
  (hA : P5J.AtMgA OnBytes.secondHashFunction Zl D r₀ Zp Np cF x₀)

/-- In front of segment l's reads the promise holds "frame.sentIs" at l. -/
theorem sentIs_at_reads {Fr : Frame} (l : ℕ) (hl : l < 25) (a : (ProofFile.InstPub × S) × Fr.E.Str)
    (hon : onQ hA.𝔇.N (mgAll hA.𝔇 mgBase) linksFull (flatPlacesOf linksFull true) (fun a => a)
      (14 * l + k1Ix l false + 2) a)
    (hm : a.1.2.failed = none) : sentIsB hA.𝔇.pubD.dS l a.1.2 = true := by
  have hIn : InAt hA.𝔇.N (mgAll hA.𝔇 mgBase) linksFull (flatPlacesOf linksFull true)
      (14 * l + k1Ix l false + 2) a.1 (strsOf _ a.2) := ⟨hon, hm⟩
  have h := inAt_pubQ hIn (.more (some l) "frame.sentIs") (by
    rw [mgAll_more_base]
    exact inSet_of (List.all_eq_true.1 sentIn_mg l (List.mem_range.2 hl)))
  rwa [mgAll_pub, First.pubAll_more_sentIs] at h

/-- So the state's own number of the open segment is l. -/
theorem linkNo_at_reads {Fr : Frame} (l : ℕ) (hl : l < 25) (a : (ProofFile.InstPub × S) × Fr.E.Str)
    (hon : onQ hA.𝔇.N (mgAll hA.𝔇 mgBase) linksFull (flatPlacesOf linksFull true) (fun a => a)
      (14 * l + k1Ix l false + 2) a)
    (hm : a.1.2.failed = none) : linkNo a.1.2 = l := by
  have h0 := sentIs_at_reads hA l hl a hon hm
  cases hL : a.1.2.link? with
  | none =>
    unfold sentIsB at h0
    rw [hL] at h0
    cases h0
  | some L =>
    unfold linkNo
    rw [hL]
    exact link_of_sentIs hL h0

/-- **The user's form.** -/
theorem jFirst_at_reads
    (hP1 : madePinnedAt Zp.p.X.P Zp.p.chains.made Zp.first Zp.made = true)
    (hC : cutOf (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = cutFirstFull) :
    ∀ l, l < 25 → ∀ a,
      RchAt (Str := (Sound.frameAt (D.at frS.P.T.a) (Sound.allOf (D.at frS.P.T.a))
          (D.at frS.P.T.a).key₁ 0).E.Str)
        (P5J.F0T OnBytes.secondHashFunction Zp Np cF) (14 * l + k1Ix l false + 2) a →
      onQ hA.𝔇.N (mgAll hA.𝔇 mgBase) linksFull (flatPlacesOf linksFull true) (fun a => a)
        (14 * l + k1Ix l false + 2) a →
      a.1.2.failed = none → ∀ A, K9.segAt? a.1.2 = some A →
      FirstSeated (hA.𝔇.N.sent (linkNo a.1.2) 0) A (linkNo a.1.2) := by
  intro l hl a hr hon hm A hseg
  rw [linkNo_at_reads hA l hl a hon hm]
  exact firstSeated_at_reads hA hP1 hC l hl a hr hon hm A hseg

end

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.sentIs_at_reads
#print axioms VerifiableInference.Desc.K1.linkNo_at_reads
#print axioms VerifiableInference.Desc.K1.jFirst_at_reads
