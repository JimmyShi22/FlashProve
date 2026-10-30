-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/- Johnson/K11R/EightAt346.lean: THE EIGHT FACTS ALONG "REACHED" THAT THE MERGE'S LAW SPENDS, ALL AT
BORDER 346 OF THE FIRST CHAIN, AS ONE VALUE: from the facts on every reached state at the head's
closed term (foldFacts_at_head', Johnson/P5J/FoldJ3Whole.lean). A JOINING: IT SHOWS NOTHING OF ITS
OWN. It imports nothing of K11's, so that it can lie beneath the merge's own files.

  Eight346 Rch cs free0 fvs L M sh   eight fields, in the text of the merge's named condition:
                    room, pileWithin, msgShapes, codes, bookInOrder, seatsCarried, bookFits,
                    liveShape
  eight_at346       under the head h and three tests on the public part: Eight346 at the head's own
                    condition "reached" (h.toAtMg.rch), at the head's codes (h.𝔇.cs), at the closed
                    term's own letters (At.foldD Zp cF L: free0, fvs, M), at L and at At.shape Zp
  shape_at_index    what hs says of M at the index masks' message's number

PREMISES THAT STAY, each a test with code on the public part: hl (the laying of the first chain's
listed places returns L), hs (FillP1.startB), hy (PlanWritten.madeRow).
Limits. A member of the head is proved at storedPublicFiles and zGap alone (at secondHashFunction; side library
AtFullSide/Top/). Where nothing is reached every field is idle. At the second
hash function. No soundness statement.

-/
import Johnson.P5J.MgAtAll
import Johnson.P5J.FourAtMg
import Johnson.P5J.FoldJ3Whole

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

namespace K11

open OnBytes (OracleShape)
open OnBytes.Params (ReqShape)
open OnBytes.Maker OnBytes.Flat OnBytes.Slice
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S flatPlacesOf)
open VerifiableInference.Desc.K13 (pileWithinC)
open VerifiableInference.Desc.K12.Door (Laid atFirstBook atFirstSeats atFirstFits atFirstShapes
  msgsOfChain)
open Johnson.Desc.First.Walk.Tied (roomIsB)
open P5J (AtMgA TS)

/-- **The eight facts along "reached", at 346.** -/
structure Eight346 {Fr : Frame} (Rch : ℕ → (ProofFile.InstPub × S) × Fr.E.Str → Prop)
    (cs : OnBytes.Codes) (free0 : ℕ) (fvs : List Bool) (L : Laid) (M : List OracleShape)
    (sh : ReqShape) : Prop where
  room : ∀ (a : (ProofFile.InstPub × S) × Fr.E.Str) p' m', Rch 346 a → a.1.2.failed = none →
    (flatPlacesOf linksFull true)[346]? = some p' → p'.link = some m' → 2 ≤ p'.piece →
    roomIsB free0 fvs m' a.1.2 = true
  pileWithin : ∀ a : (ProofFile.InstPub × S) × Fr.E.Str, Rch 346 a → a.1.2.failed = none →
    pileWithinC a.1.2 = true
  msgShapes : ∀ a : (ProofFile.InstPub × S) × Fr.E.Str, Rch 346 a → a.1.2.failed = none →
    atFirstShapes M a.1.2 = true
  codes : ∀ a : (ProofFile.InstPub × S) × Fr.E.Str, Rch 346 a → a.1.2.failed = none →
    a.1.2.st.codes = cs
  bookInOrder : ∀ a : (ProofFile.InstPub × S) × Fr.E.Str, Rch 346 a → a.1.2.failed = none →
    atFirstBook 0 a.1.2 = true
  seatsCarried : ∀ a : (ProofFile.InstPub × S) × Fr.E.Str, Rch 346 a → a.1.2.failed = none →
    atFirstSeats L a.1.2 = true
  bookFits : ∀ a : (ProofFile.InstPub × S) × Fr.E.Str, Rch 346 a → a.1.2.failed = none →
    atFirstFits a.1.2 = true
  liveShape : ∀ a : (ProofFile.InstPub × S) × Fr.E.Str, Rch 346 a → a.1.2.failed = none →
    a.1.2.live.frame.shape = sh

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **The eight, at the head's own "reached" and the closed term's own letters.** -/
theorem eight_at346 (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {L : Laid}
    (hl : P5J.At.laid? Zp = some L)
    (hs : VerifiableInference.Desc.First.FillP1.startB Zp (msgsOfChain Zp.made.proof.1)
      (P5J.At.N Zp cF).indexNo = true)
    (hy : VerifiableInference.PlanWritten.madeRow Zp = true) :
    Eight346 (Fr := frameAt (D.at frS.P.T.a) (allOf (D.at frS.P.T.a)) (D.at frS.P.T.a).key₁ 0)
      h.toAtMg.rch h.𝔇.cs (P5J.At.foldD Zp cF L).free0 (P5J.At.foldD Zp cF L).fvs L
      (P5J.At.foldD Zp cF L).M (P5J.At.shape Zp) := by
  have FF := P5J.foldFacts_at_head' h.toAtMg h.toAtMg.rch (fun _ _ hr => hr.1) hl hs
    (P5J.sendsB_of_madeRow h.toAtMg hy)
  exact
    { room := fun a p' m' hr hm hp hk h2 => FF.room 346 a p' m' hr hm hp hk h2
      pileWithin := fun a hr hm => FF.pileWithin 346 a hr hm
      msgShapes := fun a hr hm => FF.msgShapes 346 a hr hm
      codes := fun a hr hm => FF.codes 346 a hr hm
      bookInOrder := fun a hr hm => FF.bookInOrder 346 a hr hm
      seatsCarried := fun a hr hm => FF.seatsCarried 346 a hr hm
      bookFits := fun a hr hm => FF.bookFits 346 a hr hm
      liveShape := fun a hr hm => FF.liveShape 346 a hr hm }

/-- What the test startB says of the letter M at the index masks' message's number: a shape stands
there, and it is the one shape that the request announces at the chain's start. -/
theorem shape_at_index {L : Laid}
    (hs : VerifiableInference.Desc.First.FillP1.startB Zp (msgsOfChain Zp.made.proof.1)
      (P5J.At.N Zp cF).indexNo = true) :
    ∃ sh, (P5J.At.foldD Zp cF L).M[(P5J.At.N Zp cF).indexNo]? = some sh ∧
      Zp.first.shape.atStart.map (·.shape) = [sh] := by
  unfold VerifiableInference.Desc.First.FillP1.startB at hs
  cases hM : (msgsOfChain Zp.made.proof.1)[(P5J.At.N Zp cF).indexNo]? with
  | none =>
    rw [hM] at hs
    cases hs
  | some sh =>
    rw [hM] at hs
    exact ⟨sh, hM, eq_of_beq hs⟩

end K11

#print axioms K11.eight_at346
#print axioms K11.shape_at_index
