-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Desc/First/K4/ShownUnder.lean: WHAT EVERY LATER LEDGER SHOWS UNDER THE SLOTS OF HIDDEN
VALUES THAT THE LAYERS' OWN ROUNDS HAVE HEARD: the very words that the tape's round sent.
Statements and proofs. The like for a product layer's and a token sumcheck's end values stands in
OnBytes/Desc/First/P1/Heard.lean (`level_shown`, `tsc_shown`).

  `hideRun_shown`: a run of values v, laid from the slot first on in a ledger with arrays of the
    right sizes: every ledger later than the one that this gives shows v's entry i under slot
    first + i, for i below v's size; v's entries are named by a list l that is v's.
  `sent_shown`: hidden values that are sent outside a sumcheck (the sums' scalars, the products'
    scalars): with the equation by which the flat text lays them (as `hearNorms_tape` states it)
    and the tape's round that sent them: every later ledger shows, under the old next slot + i,
    entry i of what the tape's first round sent (`sentOf`), for i below their number.
  `stackVals_shown`: where the batched sumcheck `hearStack` returns from such a ledger: every ledger
    later than the one returned shows, under slot S.sA0 + i, entry i of what the round of the end
    values sent (`stackVals`, OnBytes/Desc/First/K4/StackEnded.lean), for i below
    2 + (1 + P.y.LamM) + NCLp.

Limits. What a ledger SHOWS under a slot (its array vp): the masked word as it was sent; nothing on
the hidden value behind it. One direction: from a return. "Later" is `Fo.Later`
(OnBytes/Tie/Pv/Lookup/Forest/FoForm.lean); a ledger is later than itself.
-/
import OnBytes.Desc.First.K4.StackEnded
import OnBytes.Desc.First.P1.Heard

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.K4
open OnBytes OnBytes.K.Kc
open OnBytes.Model hiding layerObject stackRounds wsForkLin
open OnBytes.Model.Layer hiding shownRun hearNorms hearTerms joinStart hearStack hearGated
  claimsNorms claimRowBatch claimsTerms claimsEnds claimsGated claimsOneHot claimsPlanes
  claimEmbedding freeSlotTest
open OnBytes.PscRun (Sized Filled hideRun_ok)
open OnBytes.Desc.First.P1 (sentOf sentOf_cons array_getD_toList)

/-- What a run of values leaves under its slots is shown by every later ledger. -/
theorem hideRun_shown {F G H : Fork} {first : Nat} {v : Array E} {f : E} {l : List E}
    (hF : Sized F) (h : F.hideRun first v f = some G) (hl : v.toList = l) (hL : Fo.Later G H)
    (i : Nat) (hi : i < v.size) : H.vp.getD (first + i) zeroE = l.getD i zeroE := by
  obtain ⟨_, _, hin, _⟩ := hideRun_ok F G first v f hF h
  have k := hin i hi
  have g := hL.keep (first + i) k.2.2.1
  rw [g.2.1, k.2.2.2.1, array_getD_toList, hl]

/-- Hidden values that are sent outside a sumcheck. -/
theorem sent_shown {F G H : Fork} {n : Nat} {v : Array E} {t more : Tape} {nm : Option String}
    {z k : Nat} {d : List E} (hF : Sized F)
    (h : ({ F with next := F.next + n } : Fork).hideRun F.next v oneE = some G)
    (ht : t = ⟨nm, z, k, v.toList, d⟩ :: more) (hL : Fo.Later G H) (i : Nat) (hi : i < v.size) :
    H.vp.getD (F.next + i) zeroE = (sentOf t).getD i zeroE := by
  have hF' : Sized ({ F with next := F.next + n } : Fork) := hF
  exact hideRun_shown hF' h (by rw [ht, sentOf_cons]) hL i hi

/-- **The batched sumcheck's end values.** -/
theorem stackVals_shown {P : Pub} {v : Env} {H : Heard} {lamS NCLp : Nat} {F G : Fork} {t u : Tape}
    {S : HeardStack} (hF : Sized F) (h : hearStack engFl P v H lamS NCLp F t = some (S, G, u)) :
    ∀ Hl : Fork, Fo.Later G Hl → ∀ i, i < 2 + (1 + P.y.LamM) + NCLp →
      Hl.vp.getD (S.sA0 + i) zeroE = (stackVals lamS t).getD i zeroE := by
  obtain ⟨_, _, _, _, _, vals, G1, hl, hs, hG1, hG⟩ := stack_heard h
  have hF' : Sized ({ F with next := F.next + 1 + 2 * lamS + 2 + (2 + (1 + P.y.LamM) + NCLp) } :
      Fork) := hF
  obtain ⟨_, hS1, _, _⟩ := hideRun_ok _ G1 _ _ _ hF' hG1
  have l2 := Fo.hideRun_later hS1 hG
  intro Hl hL i hi
  exact hideRun_shown hF' hG1 hl (l2.trans hL) i (by rw [hs]; exact hi)

end OnBytes.Desc.First.K4

#print axioms OnBytes.Desc.First.K4.hideRun_shown
#print axioms OnBytes.Desc.First.K4.sent_shown
#print axioms OnBytes.Desc.First.K4.stackVals_shown
