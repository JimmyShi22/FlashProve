-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Key/Laid/Laid2Def.lean: WHAT THE SHARED CHAIN's TWO SENDINGS LAY ON THE VERIFIER's
STATE, as relations between the state in front and the state behind. Definitions alone, over
SendLaid's own eleven fields (Johnson/Desc/Key/Laid/SendLaid.lean).
  inFrontOf d   K14's state as K1's own block is handed it: the small part emptied.
  SentAt Q d d' ids   SendLaid at these two · a new sampled message's ledger is the fresh one of its
                shape · a statement in order stays in order.
  Laid22 S Q d d'   "send o_u": SentAt, and the small part notes o_u's number with its layout, and
                the first mask's number.
  Laid25 Q d d'     "send o_omega": SentAt, and the small part notes o_omega's and o_sp's numbers.
That a yes gives them: Johnson/Desc/Key/Laid/Laid2.lean. Nothing on soundness.
-/
import Johnson.Desc.K14.Text
import Johnson.Desc.Means.Order
import Johnson.Desc.Key.Laid.SendLaid
import Johnson.Desc.Key.Laid.SentMoreDef

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Key.LaidW
open OnBytes OnBytes.Params
open Desc.Plain (DState)
open _root_.Desc.K14 (St)

/-- K14's state as K1's own block is handed it. -/
def inFrontOf (d : St) : DState (Array Nat) :=
  { st := d.st, book := d.book, roots := d.roots, opened := d.opened, loc := #[] }

/-- What a sending lays on K14's state, but for the small part. -/
structure SentAt (Q : K1.Par) (d d' : St) (ids : Array Nat) : Prop where
  laid : SendLaid Q (inFrontOf d) (inFrontOf d') ids
  /-- a new sampled message's ledger is the fresh one of its shape -/
  ledger : ∀ (i : Nat) (n : OracleNotice), Q.sent[i]? = some n → n.shape.answers ≠ 0 →
    ∃ x : OnBytes.Oracle, d'.st.oracles[d.st.oracles.size + i]? = some x ∧
      x.ledger = Slice.freshLedger Q.codes n.shape
  order : Means.InOrder d.st → Means.InOrder d'.st

/-- **What "send o_u" lays.** -/
def Laid22 (S : LinShape) (Q : K1.Par) (d d' : St) : Prop :=
  ∃ ids i0 i1, SentAt Q d d' ids ∧ ids[0]? = some i0 ∧ ids[1]? = some i1 ∧
    d'.loc = { d.loc with
      oU := ⟨i0, vectorLay d'.st.codes S.fold.u S.fold.rowsHigh⟩, firstMask := some i1 }

/-- **What "send o_omega" lays.** -/
def Laid25 (Q : K1.Par) (d d' : St) : Prop :=
  ∃ ids i0 i1, SentAt Q d d' ids ∧ ids[0]? = some i0 ∧ ids[1]? = some i1 ∧
    d'.loc = { d.loc with oOmega := i0, oSp := i1 }

end VerifiableInference.Desc.Key.LaidW
