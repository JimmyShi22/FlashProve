-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sound/MgAt/InOrderBlind.lean: "IN ORDER" AT THE COMPOSED MEANING OVER `mgBase` READS
NOTHING OF THE VERIFIER's STATE. Statements with their proofs; no definition.

In plain words. The composed meaning's test "in order" is the test of the meaning beneath, and one
test more on the request's bytes, which are read off the public part alone (`mgAll_inOrder_at`,
Johnson/Desc/Sound/MgAll.lean). Over the closed meaning beneath, `mgBase`, whose "in order" is true
outright, it is that one test (`mgAll_inOrder_base`, Johnson/Desc/Sound/MgBase.lean). So:
  `mgAll_inOrder_blind`   over `mgBase`: at one public part z and ANY two states s and t the test
                          gives the same Bool
  `mgAll_inOrder_rides`   so, over `mgBase`, a yes at (z, s) is a yes at (z, t): the form of the
                          premise hIn of `merge_t2` (Johnson/Top/H0/MergeLaw/TieOneTwo.lean), at
                          s := a.1 and t := b.1
  `mgAll_inOrder_rides_of`  over any meaning Mg beneath: the like, where Mg's own "in order" rides
                          from (z, s) to (z, t)
No step of the verifier is named: the first two hold whatever lies between s and t.

What is not claimed. That the test says yes at any public part. No soundness statement.

-/
import Johnson.Desc.Sound.MgBase

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (Meaning)

section
variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : OnBytes.Model.Verify.Public}
  (𝔇 : MgData Xi P Tok rows cols nR X)

/-- Over the closed meaning beneath, "in order" gives the same Bool at any two states. -/
theorem mgAll_inOrder_blind (z : P) (s t : First.S) :
    (mgAll 𝔇 mgBase).inOrder (z, s) = (mgAll 𝔇 mgBase).inOrder (z, t) :=
  (mgAll_inOrder_base 𝔇 (z, s)).trans (mgAll_inOrder_base 𝔇 (z, t)).symm

/-- **"In order" rides**, over the closed meaning beneath, from any state to any state. -/
theorem mgAll_inOrder_rides (z : P) (s t : First.S)
    (h : (mgAll 𝔇 mgBase).inOrder (z, s) = true) : (mgAll 𝔇 mgBase).inOrder (z, t) = true :=
  (mgAll_inOrder_blind 𝔇 z s t).symm.trans h

/-- Over any meaning beneath: it rides where that meaning's own "in order" rides. -/
theorem mgAll_inOrder_rides_of (Mg : Meaning P (Wit (CellsQ rows cols) Tok MsgT)) (z : P)
    (s t : First.S) (hM : Mg.inOrder (z, s) = true → Mg.inOrder (z, t) = true)
    (h : (mgAll 𝔇 Mg).inOrder (z, s) = true) : (mgAll 𝔇 Mg).inOrder (z, t) = true := by
  rw [mgAll_inOrder_at] at h ⊢
  rw [Bool.and_eq_true] at h ⊢
  exact ⟨hM h.1, h.2⟩

end

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.mgAll_inOrder_blind
#print axioms VerifiableInference.Desc.Sound.mgAll_inOrder_rides
#print axioms VerifiableInference.Desc.Sound.mgAll_inOrder_rides_of
