-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/LTPileR/TwoStarts.lean (over Johnson/IMR/RecRun.lean,
and the law files Johnson/Top/H0/K2Hands/SampleChain.lean and
AnsweredStored.lean): THE REQUEST'S OWN CHAIN STARTS WITHOUT AN ORACLE MESSAGE: SO BOTH INVARIANTS
ON THE STORED SAMPLE ROWS HOLD AT ITS START.

Main names (namespace `LTPile`).
  **`start_none`**: where Z is the computed public part: `(ProofFile.startS Z p).st.oracles = #[]`, at
    every public part p of an instance: in both arms of `ProofFile.startS`: the first state with the
    request's words laid, and the blank state.
  **`rowsInv_startS`**: so `K2.RowsInv Q (ProofFile.startS Z p).st`, AT EVERY Q. At Q := `K2.QGoodS` that
    is `SampleGoodS` by `sampleGoodS_iff` (an `Iff.rfl`, in
    Johnson/Top/H0/K2Hands/SampleChainS.lean): NOT CALLED HERE: that file's import cone (through
    Johnson/Top/H/SwitchSeedFits.lean) holds three modules that were not in this file's own build.
  **`answered_startS`**: `K2.AnsweredStored (ProofFile.startS Z p).st`.
  **`two_starts`**: both at the IOP as written in Lean for the proof file: F = `fileDescBy … c`, at
    that value's own `start₁`.

Every "there is", walked. Z, A, B, c: tied by `pureRoad.pub … = .ok Z` and F's equation.
Limits. Both invariants speak of the statement's oracle messages: at a statement without one they
hold for want of a case. Nothing on soundness or on hiding.

-/
import Johnson.IMR.RecRun
import Johnson.Top.H0.K2Hands.AnsweredStored

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LTPile

open OnBytes OnBytes.Model
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open ProofFile (Pub)
open Meaning.K2 (pub_start)

/-- **The chain's own start holds no oracle message.** -/
theorem start_none {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {Z : Pub}
    (h : ProofFile.pureRoad.pub o pol lay KL = .ok Z) (p : ProofFile.InstPub) :
    (ProofFile.startS Z p).st.oracles = #[] := by
  have e : Z.s₀.st.oracles = #[] := by
    have k := pub_start h
    unfold S.startP at k
    split at k
    · rw [← Option.some.inj k]
      rfl
    · cases k
  unfold ProofFile.startS
  dsimp only
  split
  · exact e
  · rfl

/-- **The invariant on the stored sample rows, at every Q.** -/
theorem rowsInv_startS {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {Z : Pub}
    (h : ProofFile.pureRoad.pub o pol lay KL = .ok Z)
    (Q : Codes → OracleShape → Nat → Array OnBytes.Row → Prop) (p : ProofFile.InstPub) :
    K2.RowsInv Q (ProofFile.startS Z p).st := by
  intro i x hx _
  rw [start_none h p] at hx
  exact absurd hx (by simp)

/-- **Every message that counts an answer has a stored sample row.** -/
theorem answered_startS {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {Z : Pub}
    (h : ProofFile.pureRoad.pub o pol lay KL = .ok Z) (p : ProofFile.InstPub) :
    K2.AnsweredStored (ProofFile.startS Z p).st := by
  intro i x hx _
  rw [start_none h p] at hx
  exact absurd hx (by simp)

/-- **BOTH, AT THE IOP AS WRITTEN IN LEAN FOR THE PROOF FILE.** -/
theorem two_starts {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst}
    (h : ProofFile.onlineDescription o pol lay KL = .ok F) :
    ∃ (Z : Pub) (A : ProofFile.SharedSeat) (B : ProofFile.SecondSeat) (c : Chain S ProofFile.Cl),
      ProofFile.pureRoad.pub o pol lay KL = .ok Z ∧
      F = ProofFile.fileDescBy o ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c ∧
      ∀ z : ProofFile.InstPub,
        K2.RowsInv K2.QGoodS ((ProofFile.fileDescBy o ProofFile.pureRoad.links Z A B (fun s => s)
          (ProofFile.startS Z) c).start₁ z).st ∧
        K2.AnsweredStored ((ProofFile.fileDescBy o ProofFile.pureRoad.links Z A B (fun s => s)
          (ProofFile.startS Z) c).start₁ z).st := by
  obtain ⟨Z, hZ, h'⟩ := ProofFile.Law.descPure_made h
  obtain ⟨B₀, base, c, A, B, -, -, -, -, -, -, -, e⟩ := IM.pure_chain h'
  exact ⟨Z, A, B, c, hZ, e, fun z => ⟨rowsInv_startS hZ _ z, answered_startS hZ z⟩⟩

#print axioms start_none
#print axioms rowsInv_startS
#print axioms answered_startS
#print axioms two_starts

end LTPile
