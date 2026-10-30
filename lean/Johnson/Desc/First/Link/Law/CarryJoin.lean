-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/CarryJoin.lean: FROM «A CODE WORD IS NEAR THE OPEN WORD THAT THE
SWITCH's TEXT READS, AND THE CARRIED CLAIM's VECTOR HAS THE TARGET ON ITS MESSAGE» (what the code
switch's files' sentence «carry» gives: `carryOf_claim`, Johnson/Top/H0/K2Hands/CarryOf.lean) TO
`CarryAt` (Johnson/Desc/First/Close/Law/Carry.lean) OF THE TYPED FOLD OF THE
TABLE's OWN WORDS: THE FIRST HALF OF `CarriedAt` (Leads.lean). By `open_word_eq` (OpenWordEq.lean)
and `outVec_eq_vecOf` (CarryVecs.lean). A theorem.

  `carryAt_of_near`: **a pair c = (message, randomness) of the folded code whose encoding parts from
    a word w in at most e' ≤ e long positions, with ∑ j, v j * c.1 j = τ · the typed folded word is
    w · outVec N rows = v · readE rows.target = τ ⊢ CarryAt R N rows ‹the typed folded word›.**
    General in the group R.
Limits. The second half of `CarriedAt` (the kept messages' own joint) is not treated. Nothing on
soundness.
-/
import Johnson.Desc.First.Link.Law.OpenWordEq
import Johnson.Desc.First.Link.Law.CarryVecs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Slice Cb Iop IOR Johnson.Top.H
open VerifiableInference.Desc.First.Close (CarryAt SlotNames outVec)

theorem carryAt_of_near {S : Sig GE} (R : RowsK S) (N : SlotNames R) (rows : SingleRows)
    (word w : R.Sh.Cf.ext.Str) (hw : word = w) {e' : ℕ} (he : e' ≤ R.G.e) {τ : GE}
    {v : R.Sh.Cf.J → GE} (hτ : readE rows.target = τ) (hv : outVec N rows = v)
    (h : ∃ c : R.Sh.Cf.N.Wit, offCnt w (R.Sh.Cf.N.enc c.1 c.2) ≤ e' ∧ ∑ j, v j * c.1 j = τ) :
    CarryAt R N rows word := by
  obtain ⟨c, h1, h2⟩ := h
  subst hw hτ hv
  exact ⟨c, Nat.le_trans h1 he, h2⟩

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.carryAt_of_near
