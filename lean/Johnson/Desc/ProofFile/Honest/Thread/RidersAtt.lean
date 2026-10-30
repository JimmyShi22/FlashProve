-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Thread/RidersAtt.lean: a fact on an attention segment's own part of
the state, as a clause of `rides`. `riderHead` (Honest/Thread/Riders.lean) is the clause "the chain
is in the head's link, and P holds of that part"; here its counterpart at an attention segment, with
the general form of its staying (the counterpart of `staysBy_head_of`,
Honest/Thread/RidersStayH.lean) and the form for a condition that reads one field which the
sub-protocol leaves. One definition. Two conditional lemmas on this folder's definitions and the
library's state (Johnson/Desc/First/State.lean).

  `riderAtt`   the clause
  `staysBy_att_of`   it stays where the sub-protocol's clause of `keeps` passes the condition on
  `staysBy_att_read`   the same for a condition on a reading f of the part that the sub-protocol
     leaves

Limits.
  * Which condition is a clause of `rides`, who establishes it and at which borders is not said
    here.
  * None is one of the library's goals.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.Riders

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc.First (S AttOwn)

/-- **A fact on an attention segment's own part of the state**: the chain is in an attention
segment, and P holds of that part. -/
def riderAtt {W : Type} (lo hi : Nat) (P : AttOwn → Prop) : RiderCl W S :=
  ⟨lo, hi, fun _ _ s => ∃ a, s.here = .att a ∧ P a⟩

variable {Cl V W X Pb : Type} {Bk : ProverCoinCounts} (T : Thread Bk S Cl V W X Pb)

/-- **The general form**: the clause stays, if by `keeps` the chain is after the sub-protocol in an
attention segment still, at a part of which the condition holds if it held before. The hypothesis is
the clause's staying written out at the part, and a little more (a part after the sub-protocol also
where the condition fails before): no more is proved than a change of form. -/
theorem staysBy_att_of {b lo hi : Nat} {P : AttOwn → Prop}
    (hk : ∀ s s', T.keeps b s s' → ∀ a, s.here = .att a →
      ∃ a', s'.here = .att a' ∧ (P a → P a')) : StaysBy T b (riderAtt lo hi P) :=
  fun _ s s' hK ⟨a, ha, hP⟩ =>
    let ⟨a', ha', hPP⟩ := hk s s' hK a ha
    ⟨a', ha', hPP hP⟩

/-- **A condition on one reading of the part**, where the sub-protocol leaves that reading. -/
theorem staysBy_att_read {α : Type} {b lo hi : Nat} (f : AttOwn → α) {R : α → Prop}
    (hk : ∀ s s', T.keeps b s s' → ∀ a, s.here = .att a →
      ∃ a', s'.here = .att a' ∧ f a' = f a) : StaysBy T b (riderAtt lo hi fun a => R (f a)) :=
  staysBy_att_of T fun s s' hK a ha =>
    let ⟨a', ha', e⟩ := hk s s' hK a ha
    ⟨a', ha', fun hR => e ▸ hR⟩

end ProofFile.Honest

#print axioms ProofFile.Honest.staysBy_att_of
#print axioms ProofFile.Honest.staysBy_att_read
