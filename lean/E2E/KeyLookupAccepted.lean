--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/KeyLookupAccepted.lean: A LOOKUP'S SUB-PROTOCOL, AT ANY TYPE OF STATE, IS ACCEPTED (`Accepted`,
Johnson/Desc/ProofFile/Honest/Thread/Pays.lean), BY THE CUT «STRUCTURE | VALUES»: from the seven
premises under which it plays (`K3PlaysAt`,
Johnson/Desc/ProofFile/Honest/K3/Law/Thread/PlaysAnyState.lean), the shape's run, (B1) at every
sub-protocol, and `ExactAt` (E2E/KeyShapeLink.lean) at this one. General: no chain, state or shape
is named. Conditional lemmas, by calls. NOTHING IS SHOWN OF ANY PROVER: no completeness.

Why. That file's `accepted_k3S` asks beside the seven a field that holds the sub-protocol's own
accepting step AND what stands behind the hearing's yes; the laws for the latter that we have found
(`leftInnerP`, `heardInnerP`, Johnson/Desc/ProofFile/Honest/K3/Law/HBPaid.lean) speak of a face with
ONE part of keys. The key file's two faces have twelve (E2E/KeyFacesFull.lean). The rule of the cut
(`accepted_of_shape`, Johnson/Desc/ProofFile/Honest/Thread/Shape.lean) asks neither.

What is defined. `noVals Z`: the letters of a cut with no named test on values.
What is shown.
  `run_noVals`, `yes_noVals`: the shape's run does not read the named tests on values.
  **`accepted_of_exact`**: the shape's run returns · the first state has the first shape · (B1) at
    every sub-protocol · `ExactAt` at this one · what was played passes the step's own tests
    (`FitsAt`): then it is accepted, at every letter "fall". WHATEVER THE CUT'S NAMED TESTS ON
    VALUES ARE: none is spent.
  **`fitsAt_k3`**: the seven give `FitsAt`: `fitsAt_half`
    (Johnson/Desc/ProofFile/Honest/Thread/ShapeRow.lean) with `lookSeat_rounds` and `fit_length`
    (Johnson/Desc/ProofFile/Honest/K3/Law/MemberSite.lean).
  **`accepted_k3_shape`**: so the seven, the run, (B1) and `ExactAt` give that the lookup's
    sub-protocol is accepted.

Limits.
- Every premise is a letter's: that a value of the type `Thread` for the key file meets the seven,
  that its shape's run returns, and (B1) are other files'. `ExactAt` at a lookup's own sub-protocol
  of the key file's first chain: E2E/KeyShapeLink.lean's `link_exact`.
- ACCEPTED SAYS THAT THE STEP RETURNS ON WHAT WAS PLAYED: nothing on what the played values are
  worth: what stands behind the hearing's yes is not had here.
- It stands over files that are not reviewed: its imports under Johnson/Desc/ProofFile/Honest/.
- Nothing on completeness, on soundness or on what is hidden.


-/
import E2E.KeyShapeLink
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.PlaysAnyState
import Johnson.Desc.ProofFile.Honest.K3.Law.MemberSite
import Johnson.Desc.ProofFile.Honest.Thread.ShapeRow

set_option autoImplicit false

namespace AtPublicFiles.KeyShape
open ProofFile.Honest
open ProofFile.Honest.K3
open ProofFile.Honest.K3.Law (lookSeat_rounds fit_length)
open ProofFile.Honest.K3.Law.AtThr (K3PlaysAt)

variable {S Cl V W X Pb Wj : Type} {Bk : ProverCoinCounts}

/-! ## 1. The rule of the cut, with no named test on values -/

/-- The letters of a cut with no named test on values. -/
def noVals (Z : Shape S) : Shape S := { Z with vals := fun _ _ _ _ => true }

theorem run_noVals (Z : Shape S) : ∀ (n : ℕ) (a : Z.Sh), (noVals Z).run n a = Z.run n a
  | 0, _ => rfl
  | n + 1, a => by
    show ((noVals Z).run n a).bind (Z.g n) = (Z.run n a).bind (Z.g n)
    rw [run_noVals Z n a]
    rfl

theorem yes_noVals (Z : Shape S) (a : Z.Sh) (n : ℕ) : (noVals Z).yes a n = Z.yes a n := by
  unfold Shape.yes
  rw [run_noVals]
  rfl

theorem accepted_of_exact (T : Thread Bk S Cl V W X Pb) (Z : Shape S) {a₀ : Z.Sh} {n b : ℕ}
    {fall : ℕ → S → List Fmt.Drawn → Option String} (hn : n ≤ T.bs.length) (hb : b < n)
    (hyes : Z.yes a₀ n = true) (hfirst : ∀ k w h s₀, T.valid w → T.begun k w h s₀ → Z.sh s₀ = a₀)
    (hC : ∀ j, Carries T.bs T.ft Z j)
    (hE : ∀ blk, T.bs[b]? = some blk → ExactAt T.ft Z.sh blk (Z.g b)) (hF : FitsAt T b) :
    Accepted T fall b :=
  accepted_of_shape T (noVals Z) (a₀ := a₀) hn hb ((yes_noVals Z a₀ n).trans hyes) hfirst
    (fun j => (hC j : Carries T.bs T.ft (noVals Z) j)) (returns_of_exact (Z := noVals Z) hE) hF
    fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ => rfl

/-! ## 2. A lookup's sub-protocol -/

theorem fitsAt_k3 (T : Thread Bk S Cl V W X Pb) {b : ℕ} {a : K3.At} {J : LookJobs Wj} {wit : W → Wj}
    {es : List Fmt.Entry} (hS : K3PlaysAt T b a J wit es) : FitsAt T b := by
  intro blk hblk
  exact fitsAt_half T hblk (hS.half blk hblk)
    (by rw [lookSeat_rounds _ J wit a (two_le_planes_of_ok _ hS.ok), hS.rounds blk hblk,
      List.length_map, fit_length _ _ hS.entries])
    (by rw [hS.oracles blk hblk, hS.rounds blk hblk, List.length_map, List.length_map]) blk hblk

theorem accepted_k3_shape (T : Thread Bk S Cl V W X Pb) {b : ℕ} {a : K3.At} {J : LookJobs Wj}
    {wit : W → Wj} {es : List Fmt.Entry} (hS : K3PlaysAt T b a J wit es) (Z : Shape S) {a₀ : Z.Sh}
    {n : ℕ} {fall : ℕ → S → List Fmt.Drawn → Option String} (hn : n ≤ T.bs.length) (hb : b < n)
    (hyes : Z.yes a₀ n = true) (hfirst : ∀ k w h s₀, T.valid w → T.begun k w h s₀ → Z.sh s₀ = a₀)
    (hC : ∀ j, Carries T.bs T.ft Z j)
    (hE : ∀ blk, T.bs[b]? = some blk → ExactAt T.ft Z.sh blk (Z.g b)) : Accepted T fall b :=
  accepted_of_exact T Z hn hb hyes hfirst hC hE (fitsAt_k3 T hS)

end AtPublicFiles.KeyShape

#print axioms AtPublicFiles.KeyShape.run_noVals
#print axioms AtPublicFiles.KeyShape.yes_noVals
#print axioms AtPublicFiles.KeyShape.accepted_of_exact
#print axioms AtPublicFiles.KeyShape.fitsAt_k3
#print axioms AtPublicFiles.KeyShape.accepted_k3_shape
