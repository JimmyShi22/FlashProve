-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Key/Laid/SentMoreDef.lean: THE DEFINITION SentMore, BY ITSELF: two facts more on what a
yes of K1's sending's decision lays: the roots received, and a new sampled message's ledger. Over
the library's plain records alone: it names no routine and imports no ground and no kind's text.
That a yes of decideSend gives it: send_more (Johnson/Desc/Key/Laid/SendMore.lean).
  SentMore sent codes roots roots' st st'.
  fresh_left      the fresh ledger of a shape with mask rows, written out: it has just the free
                  mask entries left (the library's Send.freeMaskEntries), and its mark "shut" is the
                  record's default, no: by freshLedger's own text.
-/
import OnBytes.Slice.BlkCalls

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Key.LaidW
open OnBytes

/-- **Two facts more on what a sending lays.** -/
structure SentMore (sent : Array OracleNotice) (codes : Codes) (roots roots' : Nat)
    (st st' : Statement) : Prop where
  /-- as many roots more as the layout has trees -/
  roots : ∃ lay, layTrees st.codes sent = some lay ∧ roots' = roots + lay.shapes.size
  /-- a new sampled message's ledger is the fresh one of its shape -/
  ledger : ∀ (i : Nat) (n : OracleNotice), sent[i]? = some n → n.shape.answers ≠ 0 →
    ∃ x : OnBytes.Oracle, st'.oracles[st.oracles.size + i]? = some x ∧
      x.ledger = Slice.freshLedger codes n.shape

/-- The fresh ledger of a shape with mask rows. -/
theorem fresh_left (codes : Codes) (s : OracleShape) (h : 0 < s.maskRows) :
    Slice.freshLedger codes s = some
      { next := 0
        left := Send.freeMaskEntries s.maskRows (codes.mask.getD s.maskCode default).ell s.answers
        rows := max s.maskRows 1, logRows := ceilLog2 s.maskRows } := by
  unfold Slice.freshLedger
  rw [if_pos h]

end VerifiableInference.Desc.Key.LaidW
