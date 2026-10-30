--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/KeyShapeFirstAccepted.lean: THE KEY FILE's FIRST CHAIN: THE FRAME's RULE (`accepted_of_shape`,
Johnson/Desc/ProofFile/Honest/Thread/Shape.lean) CALLED AT E2E/KeyShapeFirstAll.lean's LETTERS, in
the goals' scope, at the description that the verifier runs. A join: calls. A conditional statement
on our own definitions: NOTHING IS SHOWN OF ANY PROVER.

  **`values_frame`**: the frame's `Values` at every number but 15. At seventeen of these eighteen
    numbers the named test is our own constant "asks nothing"; at number 16 it is the test on the
    claims on the keys (E2E/KeyShapeValues16.lean).
  `values_frame15`: the frame's `Values` at 15, from a premise of the same form on `valsK12` alone
    (E2E/KeyShapeValues15.lean).
  **`accepted_first`**: `Accepted T₁ fall b` at every b below 19 but 15: from `FitsAt T₁ b`.
  **`accepted_first15`**: at 15: from `FitsAt T₁ 15` and that premise.

Limits.
- `FitsAt` is a premise: it is owed wherever a prover speaks. Where a sub-protocol has no round
  E2E/KeyQuietFirst.lean pays it.
- The premise at 15 is all the weight: `valsK12` comes to the ranges' proximity test's own accept
  (E2E/KeyShapeFirstAll.lean's limits). ANOTHER ROAD ENDS AT THE SAME NUMBER:
  E2E/KeyRangesSeated.lean's `accepted_ranges`, which does not go through `valsK12`; no statement
  ties the two.
- `Accepted` speaks only where a `Thread` stands at the border: that one stands anywhere is shown
  nowhere here.
- The two premises on the thread (its list is the chain's; it begins at the description's start
  alone) hold by text at the pair's laid thread.


-/
import E2E.KeyShapeValues16

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace AtPublicFiles.AtFiles.Full
open OnBytes OnBytes.Params AtPublicFiles.AtFiles AtPublicFiles.KeyShape
open ProofFile.Honest AtPublicFiles.KeyLink
open VerifiableInference.Desc (noDigest)
open VerifiableInference.Desc.Key (FirstState Source LaterPlaces rangesParams)
open ProofFile.Honest.Sh (valsK12)

variable {Z : VerifierAndGoals.PublicFiles} {X : Source} {N : H2U.PlaceNums} {P : LaterPlaces}
  {V W Xh Pb : Type} {Bk : ProverCoinCounts}

/-- **The frame's `Values` at every number but 15.** -/
theorem values_frame (hs : KeySourced Z X N P) (scope : VerifierAndGoals.InScope Z = true)
    (T₁ : Thread Bk (keyFileDescription X N P).S₁ (keyFileDescription X N P).Cl V W Xh Pb)
    (hbs : T₁.bs = (keyFileDescription X N P).first.blocksInOrder)
    (hbeg : ∀ k w h s₀, T₁.valid w → T₁.begun k w h s₀ → ∃ x, s₀ = (keyFileDescription X N P).start₁ x)
    (fall : Nat → (keyFileDescription X N P).S₁ → List Fmt.Drawn → Option String) {j : Nat} (hj : j ≠ 15) :
    Values T₁ (Z₁A (pubOf X) CF X.Y.D.1 X.Y.told.1 N) fall j :=
  fun _ _ _ _ _ _ _ _ _ hA _ _ _ _ => values_but15 hs scope T₁ hbs hbeg hj hA _ _

/-- The frame's `Values` at 15, from a premise of its form on the last clause alone. -/
theorem values_frame15 (hs : KeySourced Z X N P) (scope : VerifierAndGoals.InScope Z = true)
    (T₁ : Thread Bk (keyFileDescription X N P).S₁ (keyFileDescription X N P).Cl V W Xh Pb)
    (hbs : T₁.bs = (keyFileDescription X N P).first.blocksInOrder)
    (hbeg : ∀ k w h s₀, T₁.valid w → T₁.begun k w h s₀ → ∃ x, s₀ = (keyFileDescription X N P).start₁ x)
    (fall : Nat → (keyFileDescription X N P).S₁ → List Fmt.Drawn → Option String)
    (hv : ∀ blk, T₁.bs[15]? = some blk → ∀ k s m E ds y cols, Thr T₁ 15 k s m E →
      drawsFit blk.rounds ds = true →
      chainStopAt (T₁.φ.sees m.st.input) [blk] T₁.hs m.loc ds = none → fall 15 s ds = none →
      T₁.Moved blk k m E ds y cols →
      valsK12 (rangesParams N) (rangesState s) ((roundsOf y.1).map noDigest)
        (blk.shown T₁.ft (roundsOf y.1) cols) = true) :
    Values T₁ (Z₁A (pubOf X) CF X.Y.D.1 X.Y.told.1 N) fall 15 :=
  fun blk hblk k s m E ds y cols hA hd hst hf hMv =>
    values15 hs scope T₁ hbs hbeg hA _ _ (hv blk hblk k s m E ds y cols hA hd hst hf hMv)

/-- The rule's call, with `Values` as a premise. -/
theorem accepted_of_values (hs : KeySourced Z X N P) (scope : VerifierAndGoals.InScope Z = true)
    (T₁ : Thread Bk (keyFileDescription X N P).S₁ (keyFileDescription X N P).Cl V W Xh Pb)
    (hbs : T₁.bs = (keyFileDescription X N P).first.blocksInOrder)
    (hbeg : ∀ k w h s₀, T₁.valid w → T₁.begun k w h s₀ → ∃ x, s₀ = (keyFileDescription X N P).start₁ x)
    (fall : Nat → (keyFileDescription X N P).S₁ → List Fmt.Drawn → Option String) {b : Nat} (hb : b < 19)
    (hF : FitsAt T₁ b) (hV : Values T₁ (Z₁A (pubOf X) CF X.Y.D.1 X.Y.told.1 N) fall b) :
    Accepted T₁ fall b := by
  obtain ⟨hsh, -, hyes, hlen, hC, hR⟩ := all_sourced hs scope T₁.ft
  refine accepted_of_shape T₁ (Z₁A (pubOf X) CF X.Y.D.1 X.Y.told.1 N) (a₀ := T0) (n := 19)
    (le_of_eq (by rw [hbs, hlen])) hb hyes (fun k w h s₀ h1 h2 => ?_) (fun j => ?_) ?_ hF hV
  · obtain ⟨x, rfl⟩ := hbeg k w h s₀ h1 h2
    exact hsh x
  · rw [hbs]
    exact hC j
  · rw [hbs]
    exact hR b

/-- **THE FRAME's RULE AT EVERY NUMBER BUT 15: FROM `FitsAt` ALONE.** -/
theorem accepted_first (hs : KeySourced Z X N P) (scope : VerifierAndGoals.InScope Z = true)
    (T₁ : Thread Bk (keyFileDescription X N P).S₁ (keyFileDescription X N P).Cl V W Xh Pb)
    (hbs : T₁.bs = (keyFileDescription X N P).first.blocksInOrder)
    (hbeg : ∀ k w h s₀, T₁.valid w → T₁.begun k w h s₀ → ∃ x, s₀ = (keyFileDescription X N P).start₁ x)
    (fall : Nat → (keyFileDescription X N P).S₁ → List Fmt.Drawn → Option String) {b : Nat} (hb : b < 19)
    (h15 : b ≠ 15) (hF : FitsAt T₁ b) : Accepted T₁ fall b :=
  accepted_of_values hs scope T₁ hbs hbeg fall hb hF (values_frame hs scope T₁ hbs hbeg fall h15)

/-- **At 15: from `FitsAt` and the premise on the last clause.** -/
theorem accepted_first15 (hs : KeySourced Z X N P) (scope : VerifierAndGoals.InScope Z = true)
    (T₁ : Thread Bk (keyFileDescription X N P).S₁ (keyFileDescription X N P).Cl V W Xh Pb)
    (hbs : T₁.bs = (keyFileDescription X N P).first.blocksInOrder)
    (hbeg : ∀ k w h s₀, T₁.valid w → T₁.begun k w h s₀ → ∃ x, s₀ = (keyFileDescription X N P).start₁ x)
    (fall : Nat → (keyFileDescription X N P).S₁ → List Fmt.Drawn → Option String) (hF : FitsAt T₁ 15)
    (hv : ∀ blk, T₁.bs[15]? = some blk → ∀ k s m E ds y cols, Thr T₁ 15 k s m E →
      drawsFit blk.rounds ds = true →
      chainStopAt (T₁.φ.sees m.st.input) [blk] T₁.hs m.loc ds = none → fall 15 s ds = none →
      T₁.Moved blk k m E ds y cols →
      valsK12 (rangesParams N) (rangesState s) ((roundsOf y.1).map noDigest)
        (blk.shown T₁.ft (roundsOf y.1) cols) = true) : Accepted T₁ fall 15 :=
  accepted_of_values hs scope T₁ hbs hbeg fall (by decide) hF
    (values_frame15 hs scope T₁ hbs hbeg fall hv)

end AtPublicFiles.AtFiles.Full

#print axioms AtPublicFiles.AtFiles.Full.values_frame
#print axioms AtPublicFiles.AtFiles.Full.values_frame15
#print axioms AtPublicFiles.AtFiles.Full.accepted_of_values
#print axioms AtPublicFiles.AtFiles.Full.accepted_first
#print axioms AtPublicFiles.AtFiles.Full.accepted_first15
