-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Thread/RidersStayH.lean: A FACT ON THE HEAD's OWN PART STAYS PAST A
MEMBER THAT TURNS OTHER FIELDS OF THAT PART. `staysBy_head` (Honest/Thread/RidersStay.lean) draws
on "s'.here = s.here". Found by the authors of K8's lemmas: that is false at the smallness test's
draw: the test's data lie INSIDE `here`, and the draw lays two of their fields; the like holds of
every member that moves the ledger or the link's context (the library's `rest9` blanks just these
three fields). Here the form that serves there: the member's clause of `keeps` says that behind it
the chain still stands in the head's link, at a part a' of which the clause's sentence holds if it
held of a. With it one corollary, for a part that differs in `tl` alone, at a sentence that does not
read it.

  `staysBy_head_of`   the general form
  `staysBy_head_tl`   keeps: ∃ tl', s'.here = .head { a with tl := tl' }

Limits. None is one of the library's goals. This file proves nothing about soundness, completeness,
hiding or any other property of the protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.RidersStay

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc.First (S HeadOwn)

variable {Cl V W X Pb : Type} {Bk : ProverCoinCounts} (T : Thread Bk S Cl V W X Pb)

/-- **THE GENERAL FORM**: behind the member the chain stands in the head's link still, at a part of
which the sentence holds if it held in front. -/
theorem staysBy_head_of {b lo hi : Nat} {P : HeadOwn → Prop}
    (hk : ∀ s s', T.keeps b s s' → ∀ a, s.here = .head a →
      ∃ a', s'.here = .head a' ∧ (P a → P a')) : StaysBy T b (riderHead lo hi P) :=
  fun _ s s' hK ⟨a, ha, hP⟩ =>
    let ⟨a', ha', hPP⟩ := hk s s' hK a ha
    ⟨a', ha', hPP hP⟩

/-- Where the member turns the smallness test's data alone, at a sentence that does not read
them. -/
theorem staysBy_head_tl {b lo hi : Nat} {P : HeadOwn → Prop}
    (hk : ∀ s s', T.keeps b s s' → ∀ a, s.here = .head a →
      ∃ tl', s'.here = .head { a with tl := tl' })
    (hP : ∀ a tl', P a → P { a with tl := tl' }) : StaysBy T b (riderHead lo hi P) :=
  staysBy_head_of T fun s s' hK a ha =>
    let ⟨tl', h'⟩ := hk s s' hK a ha
    ⟨_, h', hP a tl'⟩

end ProofFile.Honest

#print axioms ProofFile.Honest.staysBy_head_of
#print axioms ProofFile.Honest.staysBy_head_tl
