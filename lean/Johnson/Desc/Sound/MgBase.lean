-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/MgBase.lean: the closed meaning beneath the composed meaning of the open claims
(`mgAll`, Johnson/Desc/Sound/MgAll.lean), and what that term is over it. A definition and theorems.
  `mgBase`: "in order": true · the list of extra public tests: empty · every public test: FALSE ·
    every sentence on a witness: False · A PUBLIC SENTENCE WITHOUT A TEST (`pubP`): True just where
    the written table gives "no sentence is meant" (`First.saysNone`,
    Johnson/Desc/First/AllSaid.lean), ELSE False. SO WHATEVER NO PART GIVES IS FALSE AT EVERY STATE.
    THAT IS LOUD IN A RUN, WHICH FAILS THERE; IN A LAW IT IS SILENT: a promise that asked such an
    item would hold at no state, and every law behind it would hold for nothing. (Not so at "in
    order": there the base accepts.)
  `mgAll_inOrder_base`: "in order" over it is one test, on the public part alone.
  `mgAll_more_base`: the list of extra public tests over it is the parts' own, merged, less the
  names
    that leave (`mgMore`, Johnson/Desc/Sound/MgAllAt.lean).
  `mgAll_pub_base`: where a part claims a public item (`First.whoFills`), the term's answer over it
  is the
    answer over ANY meaning beneath.
  `mgAll_pubP_said`: over it, at an item of that table, the term's public sentence holds.
  `mgAll_pubP_else`: outside left, leftOn and hasRow it IS that table's word.
  `mgAll_pubP_unsaid`: over it, at an item for which nobody answers (`First.whoSays`), it is false.
Limits: a base. That nothing asked falls to it are tests (Johnson/Desc/First/AllFilled.lean,
AllSaid.lean), evaluated at the two written lists of places. No soundness is claimed.

-/
import Johnson.Desc.Sound.MgAllAt
import Johnson.Desc.First.PubAllAt
import Johnson.Desc.First.AllSaid

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (Meaning Pub)

/-- **The closed meaning beneath.** -/
def mgBase {P W : Type} : Meaning P W where
  pin := fun _ _ _ _ _ => False
  noColl := fun _ _ _ _ => False
  shown := fun _ _ _ => False
  held := fun _ _ _ => false
  pinW := fun _ _ _ => False
  decodes := fun _ _ => False
  inOrder := fun _ => true
  pub := fun _ _ => false
  pubP := fun q _ => (First.saysNone q).isSome = true
  more := {}
  constr := fun _ _ _ _ _ => False
  tie := fun _ _ _ _ => False
  forms := fun _ _ _ _ _ _ => False
  formsT := fun _ _ _ _ _ _ => False
  worth := fun _ _ _ _ _ _ => False
  wo := fun _ _ _ _ => False
  totalB := fun _ _ _ _ => False
  total := fun _ _ _ _ => False
  row := fun _ _ _ _ _ => False
  carry := fun _ _ _ _ => False
  pile := fun _ _ _ => False
  pileOne := fun _ _ _ => False
  wrow := fun _ _ _ => False

section
variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : OnBytes.Model.Verify.Public}
  (𝔇 : MgData Xi P Tok rows cols nR X)

theorem mgAll_inOrder_base (a : P × First.S) : (mgAll 𝔇 mgBase).inOrder a =
    (_root_.Meaning.backReq (𝔇.reqB a.1)).isSome := rfl

theorem mgAll_more_base : (mgAll 𝔇 mgBase).more = mgMore := mgAll_more_closed 𝔇 mgBase rfl

theorem mgAll_pub_base (Mg : Meaning P (Wit (CellsQ rows cols) Tok MsgT)) (q : Pub)
    (a : P × First.S) (h : (First.whoFills 𝔇.pubD q).isSome = true) :
    (mgAll 𝔇 mgBase).pub q a = (mgAll 𝔇 Mg).pub q a := by
  rw [mgAll_pub, mgAll_pub]
  exact First.pubAll_some 𝔇.pubD _ _ q a h

/-- At an item to which `First.saysNone` gives "no sentence is meant" the sentence holds. -/
theorem mgAll_pubP_said (q : Pub) (a : P × First.S) (h : (First.saysNone q).isSome = true) :
    (mgAll 𝔇 mgBase).pubP q a := by
  rw [mgAll_pubP]
  cases q with
  | left m => simp [First.saysNone] at h
  | leftOn m => simp [First.saysNone] at h
  | hasRow m => simp [First.saysNone] at h
  | _ => exact h

/-- Outside left, leftOn and hasRow the sentence over the base is the table's own word. -/
theorem mgAll_pubP_else (q : Pub) (a : P × First.S) (hq : First.whoSays q = First.saysNone q) :
    (mgAll 𝔇 mgBase).pubP q a = ((First.saysNone q).isSome = true) := by
  rw [mgAll_pubP]
  cases q with
  | left m => simp [First.whoSays, First.saysNone] at hq
  | leftOn m => simp [First.whoSays, First.saysNone] at hq
  | hasRow m => simp [First.whoSays, First.saysNone] at hq
  | _ => rfl

/-- At an item for which nobody answers the sentence is false. -/
theorem mgAll_pubP_unsaid (q : Pub) (a : P × First.S) (h : First.whoSays q = none) :
    ¬ (mgAll 𝔇 mgBase).pubP q a := by
  have hq : First.whoSays q = First.saysNone q := by
    cases q <;> first | rfl | (simp [First.whoSays] at h)
  rw [mgAll_pubP_else 𝔇 q a hq, ← hq, h]
  simp

end

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.mgAll_inOrder_base
#print axioms VerifiableInference.Desc.Sound.mgAll_more_base
#print axioms VerifiableInference.Desc.Sound.mgAll_pub_base
#print axioms VerifiableInference.Desc.Sound.mgAll_pubP_said
#print axioms VerifiableInference.Desc.Sound.mgAll_pubP_else
#print axioms VerifiableInference.Desc.Sound.mgAll_pubP_unsaid
