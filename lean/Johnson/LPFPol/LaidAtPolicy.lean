-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LPFPol/LaidAtPolicy.lean: the fourteen entry tests of the proof file (`LPFD.lawsAsk`,
Johnson/Desc/Laid/ProofAsks.lean) and the proof file's seat (`LPFD.Full.proofDataAndDecisionOfPublicFiles`,
Johnson/Desc/Laid/ProofFull.lean) at a parameter file with another acceptance policy. Statements and
proofs.
Premises: hX, hX': `publicOfO` returns X at the first parameter file and `X.withPol C theta cap` at
the second; hs, hs': the strict scans of the two files are X.P and `X.P.withPol C theta cap`; hH:
`HeadSame X C theta cap`.
  `rowW_wp`; `atFullKey_wp`, `madeRow_wp`, `digEntry_wp`, `readsEntry_wp`, `headEntry_wp`,
      `rowsMadeB_wp`: the rows on the public record and on the public part read none of the three
      numbers: by unfolding.
  `lawsAsk_wp`: the two lists of fourteen tests are one list: under hX, hX', hs, hs', where
      `pubPlain` returns at the first file, at two descriptions with `SameDesc`, and at any two data
      (the list does not read its data).
  `laidPOf_wp`: where the seat returns at the first file, it returns at the second, with the same
      data.
Limits. The premises are not paid here. The two laid decisions are not shown to be one. Nothing on
soundness.

-/
import Johnson.LPFPol.DescAtPolicy
import Johnson.Desc.Laid.ProofFull

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

namespace LPFPol
open ProofFile
open OnBytes OnBytes.Model
open VerifiableInference
open VerifiableInference.Desc (FileDescription)
open VerifiableInference.PlanWritten (publicOfO)

section
variable (W : Verify.Public) (Z : Pub) (pol' : ByteArray) (C theta cap : Nat)

set_option maxHeartbeats 1000000 in
set_option smartUnfolding false in
theorem rowW_wp (k : Nat) :
    Desc.First.Att.P.K5Asks.rowW k (W.withPol C theta cap) = Desc.First.Att.P.K5Asks.rowW k W := rfl

theorem atFullKey_wp : Desc.Door.atFullKey (wpZ Z pol' C theta cap) = Desc.Door.atFullKey Z := rfl

set_option maxHeartbeats 1000000 in
set_option smartUnfolding false in
theorem madeRow_wp : PlanWritten.madeRow (wpZ Z pol' C theta cap) = PlanWritten.madeRow Z := rfl

set_option maxHeartbeats 1000000 in
set_option smartUnfolding false in
theorem digEntry_wp : Desc.K3Asks.digEntry (wpZ Z pol' C theta cap) = Desc.K3Asks.digEntry Z := rfl

set_option maxHeartbeats 1000000 in
set_option smartUnfolding false in
theorem readsEntry_wp : Desc.K3Asks.readsEntry (wpZ Z pol' C theta cap) =
    Desc.K3Asks.readsEntry Z := rfl

set_option maxHeartbeats 1000000 in
set_option smartUnfolding false in
theorem headEntry_wp : Desc.K3Asks.headEntry (wpZ Z pol' C theta cap) = Desc.K3Asks.headEntry Z :=
    rfl

set_option maxHeartbeats 1000000 in
set_option smartUnfolding false in
theorem rowsMadeB_wp : Desc.LinkJoin.rowsMadeB (wpZ Z pol' C theta cap) =
    Desc.LinkJoin.rowsMadeB Z := rfl

end

section
variable {o : SecondHashFunctionArgument} {pol pol' lay KL : ByteArray} {X : Verify.Public} {C theta cap : Nat}

theorem rowO_wp (hX : publicOfO o pol KL (some lay) = .ok X)
    (hX' : publicOfO o pol' KL (some lay) = .ok (X.withPol C theta cap)) (k : Nat) :
    Desc.First.Att.P.K5Asks.rowO k o pol' lay KL = Desc.First.Att.P.K5Asks.rowO k o pol lay KL := by
  unfold Desc.First.Att.P.K5Asks.rowO
  rw [hX, hX']
  exact rowW_wp X C theta cap k

theorem pinned_wp (hs : polScan pol = .ok X.P) (hs' : polScan pol' = .ok (X.P.withPol C theta cap))
    {F F' : FileDescription ProofFile.Inst} (h : SameDesc F' F) :
    PlanWritten.seatPinnedProof pol' F' = PlanWritten.seatPinnedProof pol F := by
  unfold PlanWritten.seatPinnedProof
  rw [hs, hs']
  show PlanWritten.declPinned _ _ (PlanWritten.keyOfScan X.P) F'.roundsDeclaredByBlocks F'.tableDepth =
    PlanWritten.declPinned _ _ (PlanWritten.keyOfScan X.P) F.roundsDeclaredByBlocks F.tableDepth
  rw [h.decl, h.depth]

/-- **The fourteen tests are one list.** -/
theorem lawsAsk_wp (hX : publicOfO o pol KL (some lay) = .ok X)
    (hX' : publicOfO o pol' KL (some lay) = .ok (X.withPol C theta cap))
    (hs : polScan pol = .ok X.P) (hs' : polScan pol' = .ok (X.P.withPol C theta cap))
    {Z : Pub} (hZ : pubPlain o pol lay KL = .ok Z)
    {F F' : FileDescription ProofFile.Inst} (h : SameDesc F' F) (D D' : OnBytes.Maker.WholeD) :
    LPFD.lawsAsk o pol' lay KL F' D' = LPFD.lawsAsk o pol lay KL F D := by
  have hZ' := pubPlain_wp hX hX' hZ
  have eM : Desc.Door.planOf o pol lay KL = some Z := by
    show (pubPlain o pol lay KL).toOption = _
    rw [hZ]
    rfl
  have eM' : Desc.Door.planOf o pol' lay KL = some (wpZ Z pol' C theta cap) := by
    show (pubPlain o pol' lay KL).toOption = _
    rw [hZ']
    rfl
  have eCut : PlanWritten.cutIs F' = PlanWritten.cutIs F := by
    unfold PlanWritten.cutIs
    rw [h.cut₁, h.cut₂, h.cut₃]
  unfold LPFD.lawsAsk
  rw [eM, eM']
  simp only [Desc.First.Att.P.K5Asks.masks, Desc.First.Att.P.K5Asks.usual,
      Desc.First.Att.P.K5Asks.calls,
    Desc.First.Att.P.K5Asks.nums, Desc.First.Att.P.K5Asks.pos, Desc.First.Att.P.K5Asks.units,
    Desc.First.Att.P.K5Asks.held, rowO_wp hX hX', pinned_wp hs hs' h, Desc.Door.atFull,
        Desc.Door.every,
    Option.any_some, atFullKey_wp, madeRow_wp, digEntry_wp, readsEntry_wp, headEntry_wp,
        rowsMadeB_wp,
    PlanWritten.cutRow, eCut]

theorem data_wp {F F' : FileDescription ProofFile.Inst} (h : SameDesc F' F) (file : String) :
    F'.data file = F.data file := by
  unfold FileDescription.data
  rw [h.decl, h.depth]

theorem planWord_none {F F' : FileDescription ProofFile.Inst} (h : SameDesc F' F) (hw : F.planWord = none) :
    F'.planWord = none := by
  unfold FileDescription.planWord at hw ⊢
  rw [h.planOk]
  by_cases hp : F.planOk = true
  · rw [if_pos hp]
  · rw [if_neg hp] at hw
    cases hw

/-- **The proof file's seat at the other policy.** -/
theorem laidPOf_wp (hX : publicOfO o pol KL (some lay) = .ok X)
    (hX' : publicOfO o pol' KL (some lay) = .ok (X.withPol C theta cap))
    (hs : polScan pol = .ok X.P) (hs' : polScan pol' = .ok (X.P.withPol C theta cap))
    (hH : HeadSame X C theta cap) {P : OnBytes.Maker.WholeD × LPFD.Full.RunPF}
    (hP : LPFD.Full.proofDataAndDecisionOfPublicFiles o pol lay KL = .ok P) :
    ∃ P', LPFD.Full.proofDataAndDecisionOfPublicFiles o pol' lay KL = .ok P' ∧ P'.1 = P.1 := by
  unfold LPFD.Full.proofDataAndDecisionOfPublicFiles at hP ⊢
  cases hF : onlineDescription o pol lay KL with
  | error e =>
    rw [hF] at hP
    cases hP
  | ok F =>
    rw [hF] at hP
    obtain ⟨F', hF', hS⟩ := descPure_wp hX hX' hH hF
    obtain ⟨Z, hZ, -⟩ := ProofFile.Law.descPure_made hF
    rw [hF']
    dsimp only at hP ⊢
    unfold LPFD.Full.proofDataAndDecisionOfDescription at hP ⊢
    cases hw : F.planWord with
    | some w =>
      rw [hw] at hP
      cases hP
    | none =>
      rw [hw] at hP
      rw [planWord_none hS hw, data_wp hS]
      dsimp only at hP ⊢
      cases hD : F.data "proof file" with
      | error e =>
        rw [hD] at hP
        cases hP
      | ok D =>
        rw [hD] at hP
        dsimp only at hP ⊢
        rw [lawsAsk_wp hX hX' hs hs' hZ hS D D]
        cases hn : LPFD.firstNo (LPFD.lawsAsk o pol lay KL F D) with
        | some t =>
          rw [hn] at hP
          cases hP
        | none =>
          rw [hn] at hP
          cases hP
          exact ⟨_, rfl, rfl⟩

end

end LPFPol

#print axioms LPFPol.lawsAsk_wp
#print axioms LPFPol.laidPOf_wp
