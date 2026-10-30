-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/IMR/CodesSeat.lean: "THE RECORD's CODES ARE THE START's" ALONG THE WHOLE
FIRST CHAIN AT THE PROOF FILE's SEAT: behind a yes of the file's decision every record that the
first chain's fold passes through, and its last, holds the public part's codes (Z.first.codes): so
the record at the door of kind K12's block behind the last link too.

THE RELATION: CR := ByS fun T T' => T'.codes = T.codes (Johnson/Goal/Meaning/RecGrows.lean: ByS).
WHO PAYS:
  in front of the blocks behind the last link, and kind K2's place there: "the statement grows"
    (Johnson/IMR/GrowsSeat.lean's seatKeeps_grows at Johnson/IMR/K2ShareAt.lean's k2Grows), whose
      first clause is the
    codes': through SeatKeeps.mono (Johnson/IMR/SeatKeeps.lean); the batching anew: batch_codes, by
    drawAlone_by and adds_by (RecGrows.lean).
  kind K13's two: the library's K13.atM3_grows and atM4_keeps over K1.Rel.sendAtS_keeps
    (Johnson/Desc/K13/Keeps.lean, Johnson/Desc/K1/KeepsAtS.lean).
  kind K12's block, where it passes its own test on the plan: the library's Seat.atFinish_ok
    (Johnson/Desc/K12/SeatLaws.lean) and k12_run_codes
    (Johnson/Desc/K12/Law/RunCodes.lean).
  the start: RecAll's first field at the first record (Johnson/IMR/RecRun.lean: recAll_startS,
    okBy_reqOk).
TOP: descPure_codes.
OBJECT: ProofFile.onlineDescription's value, at every o. USER: kind K12's files.
Not claimed: anything of the shared or the last chain. No soundness.
-/
import Johnson.IMR.K2ShareAt
import Johnson.Desc.K13.Keeps
import Johnson.Desc.K12.SeatLaws
import Johnson.Desc.K12.Law.RunCodes

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.K2

open OnBytes OnBytes.Model
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open VerifiableInference.Desc.Keeps (Whole Decides Fn FnCl)
open VerifiableInference.Desc.Ground (groundKeeps_grows)
open VerifiableInference.Desc.K9 (atS batch)
open ProofFile (Pub)

/-- **The relation**: the record's codes stay. -/
abbrev CR : S → S → Prop := ByS fun T T' => T'.codes = T.codes

theorem batch_codes (p : K9.Where) {claims : S → Except String (List Claim × S)}
    (hcl : FnCl CR claims) : Whole CR (K9.batch K9.atS p claims) := by
  refine ⟨fun s rs gs s' h => ?_, (fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩
  simp only [batch] at h
  obtain ⟨t₁, h1, h⟩ := bindE h
  have a1 : CR s t₁ :=
    drawAlone_by (R := fun T T' => T'.codes = T.codes) (fun _ => rfl) p s rs gs t₁ h1
  have a2 : CR t₁ s' := adds_by p p.piece "the segment's" hcl t₁ [] [] s' h
  exact a2.trans a1

theorem seatKeeps_codes : SeatKeeps CR :=
  (seatKeeps_grows k2Grows).mono (fun _ _ g => g.1) (fun _ => rfl) (fun _ _ _ h k => k.trans h)
    batch_codes

theorem seatBack_codes : SeatBack CR where
  k12 := fun m hp => ⟨fun s rs gs s' h => by
      obtain ⟨o, t', -, -, -, hk, rfl⟩ := K12.Seat.atFinish_ok _ s s' rs gs h
      exact (H2K.Out.k12_run_codes _ (atFinish_planOk hp) _ t' rs gs hk).2,
    (fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩
  k13M3 := fun p => ⟨fun s rs gs s' h => (K13.atM3_grows p s rs gs s' h).1,
    (fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩
  k13M4 := fun p P _ => ⟨fun s rs gs s' h => (K13.atM4_keeps groundKeeps_grows.quiet p _
      (K1.Rel.sendAtS_keeps groundKeeps_grows P) s rs gs s' h).1,
    (fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩

/-- **A YES OF THE FILE's DECISION: EVERY RECORD THAT THE FIRST CHAIN's FOLD PASSES THROUGH, AND ITS
LAST, HOLDS THE PUBLIC PART's CODES.** -/
theorem descPure_codes {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst}
    (h : ProofFile.onlineDescription o pol lay KL = .ok F) {x : ProofFile.Inst} {v₁ v₂ v₃ : Fmt.View}
    (hr : F.run x v₁ v₂ v₃ = true) :
    ∃ (Z : Pub) (A : ProofFile.SharedSeat) (B : ProofFile.SecondSeat) (c : Chain S ProofFile.Cl) (e₁ : S),
      ProofFile.pureRoad.pub o pol lay KL = .ok Z ∧
      F = ProofFile.fileDescBy o ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c ∧
      chainAt "the first chain" 0 c.blocksInOrder (ProofFile.startS Z x.pub) (withEmptySealRound v₁) = .ok e₁ ∧
      e₁.st.codes = Z.first.codes ∧
      ∀ (l₁ l₂ : List (Block S ProofFile.Cl)) (t : S) (rs : List Fmt.RoundView)
        (cols : List VerifiableInference.Desc.OpenedColumn), c.blocksInOrder = l₁ ++ l₂ →
        foldBlocks 0 l₁ (ProofFile.startS Z x.pub) (withEmptySealRound v₁).rounds (withEmptySealRound v₁).opened =
          .ok (t, rs, cols) → t.st.codes = Z.first.codes := by
  obtain ⟨Z, A, B, c, e₁, hZ, rfl, j, k⟩ := descPure_passes seatKeeps_codes seatBack_codes
    (fun _ _ => trivial) h hr
  have ho := FileDescription.okStart_of_run hr
  have hok : ProofFile.okBy o ProofFile.pureRoad.links Z x = true := by
    have ho' : (ProofFile.okBy o ProofFile.pureRoad.links Z x && A.okInst x.pub) = true := ho
    exact (Bool.and_eq_true _ _ ▸ ho').1
  have h0 : (ProofFile.startS Z x.pub).st.codes = Z.first.codes :=
    (recAll_startS hZ (okBy_reqOk hok)).codes
  have hs : Keeps.Passes 0 c.blocksInOrder (ProofFile.startS Z x.pub) (withEmptySealRound v₁) (ProofFile.startS Z x.pub) :=
    ⟨[], c.blocksInOrder, _, _, rfl, rfl⟩
  refine ⟨Z, A, B, c, e₁, hZ, rfl, j, ((k _ hs).2 : e₁.st.codes = _).trans h0,
    fun l₁ l₂ t rs cols hl hf => ?_⟩
  exact ((k t ⟨l₁, l₂, rs, cols, hl, hf⟩).1 : t.st.codes = _).trans h0

#print axioms seatKeeps_codes
#print axioms seatBack_codes
#print axioms descPure_codes

end Meaning.K2
