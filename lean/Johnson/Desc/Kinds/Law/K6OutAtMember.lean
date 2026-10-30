-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/K6OutAtMember.lean.
WHAT IT IS NOT. Every statement is CONDITIONAL. THAT THE ROUNDS ARE AT THE TRUTH OF THE CELLS
(TruthK6N, Law/K06ClosedTruth.lean) AND THAT THE KEYS' SENTENCE HOLDS IN FRONT (KeysWorth) ARE
PREMISES: no prover's text is read, and no state, cells or rounds are shown at which they hold.
TruthK6N HOLDS MORE THAN VALUES: through the library's NormTruthW and HeadTruth it holds that the
four sumchecks' own forms are worth 0: FOUR OF THE 35 FORMS THAT Opened SAYS ARE WORTH 0 GO IN AS
THEY COME OUT, in bare_out and in member_out alike; 31 are derived.
Nothing on chance: "no bad element is sampled" is neither asked nor concluded. Nothing on soundness,
on completeness or on hiding.
WHAT IT IS. What the output head's sub-protocol opens (K6Out, Law/RowPins.lean: all that Opened
says, and the form of "join" at what the lookup has heard is worth 0), BEHIND ITS STEP; THAT THE
STEP ACCEPTS IS CONCLUDED; at the public parameters' own letters: at the bare sub-protocol
(blockAt), and at the member, seated as in the IOP as written in Lean (K6MemberIs,
Law/K6WayUp.lean).
  bare_out        CONDITIONAL: what is asked of the state in front (K6On), no mark, the opened
                  head's link, the rounds at the truth, what the lookup has heard, the keys'
                  sentence in front: the bare sub-protocol's step accepts and takes no column;
                  behind it the ledger and what was heard are the hearing's own return, and K6Out
                  holds.
  K6MemberIs.on   CONDITIONAL on the member's form: where the member passes its test on the plan and
                  the state its own test on the request, K6On follows from the three clauses that
                  are left of it (K6Left, Law/SeatedSays.lean).
  member_out      CONDITIONAL: the first at the member's own step, under K6Left in K6On's stead, and
                  four premises more: the member passes its test on the plan; the state its own
                  test on the request; two on the letters of the member's form: the place's kind is
                  not K7; the guard same accepts two states that hold one reply.
AT THE ROUNDS THEMSELVES, not at the rounds without the sealed digest: TruthK6N holds "the rounds
have the table's shape" (ShapedNZ), and a round of that shape bears no digest.
LETTERS. s' stands under "there is", pinned by the step's equation. gk: pinned by hgk.
CALLED: yes_out (Law/K06ClosedTruth.lean), Came.lookHeard_leaves (Law/RowPins.lean), k6On_of_start
(Law/K6OrdLeft.lean), IM.alone_planOk (IMR/SeatForm.lean), K6MemberIs.step_iff. Nothing is typed
anew.

-/
import Mathlib
import Johnson.Desc.Kinds.Law.K6WayUp
import Johnson.Desc.Kinds.Law.K06ClosedTruth
import Johnson.Desc.Kinds.Law.K6OrdLeft

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E)
open VerifiableInference.Desc (Block OpenedColumn Place KindName Claim)
open VerifiableInference.Desc.First (S)
open OnBytes.Model (Fork)

/-- AT THE BARE SUB-PROTOCOL, AT THE PUBLIC PARAMETERS' OWN LETTERS. CONDITIONAL. -/
theorem bare_out (W : OnBytes.Model.Verify.Public) (l ft : Nat) (cols : List OpenedColumn) (s : S)
    (c : NCells) (mask : Nat → E) (rs : List Fmt.RoundView) (H : HeardAll) (G : Fork) (hOn : K6On W s)
    (hfail : s.failed = none) (hopen : HeadOpen s)
    (R : TruthK6N W.hS (readsOf W) (workOf W) s c mask rs H G)
    (gk : OnBytes.Model.Forest.Heard) (hgk : s.lookHeard? = some gk)
    (hK : KeysWorth (parOf W.hS (workOf W)) (seatAt W.hS (readsOf W)) s c mask gk) :
    ∃ s' : S, (blockAt W.hS (readsOf W) (workOf W) l).step ft s rs cols = .ok (s', 0) ∧
      (seatAt W.hS (readsOf W)).ledger s' = G ∧ (seatAt W.hS (readsOf W)).heard s' = some H ∧
      K6Out W s' (c, mask) := by
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := hOn
  obtain ⟨s', hst, hd, bL, bH, hO, _, hJ⟩ := yes_out W.hS (readsOf W) (workOf W) l ft cols s c
    mask rs H G a1 a2 a3 a4 a5 hfail hopen R
  have hlk : s'.lookHeard? = s.lookHeard? :=
    Came.lookHeard_leaves W.hS (readsOf W) (workOf W) l s rs [] s' hd
  exact ⟨s', hst, bL, bH, hO, gk, hlk.trans hgk, hJ gk (a6 gk hgk) hK⟩

/-- What is asked of the state in front, from what is left of it where the member passes its test on
the plan and the state its own test on the request. CONDITIONAL on the member's form. -/
theorem K6MemberIs.on {W : OnBytes.Model.Verify.Public} {l : Nat} {same : S → S → Bool}
    {a : Place} {b : Block S Claim} (M : K6MemberIs W l same a b) (hp : b.planOk = true) {s : S}
    (hstart : startOk W s = true) (hL : K6Left W s) : K6On W s := by
  obtain ⟨ms, bS, name, hS, hla⟩ := M
  exact k6On_of_start hS (by rw [← IM.alone_planOk hla]; exact hp) hstart hL

/-- AT THE MEMBER, SEATED AS IN THE IOP AS WRITTEN IN LEAN. CONDITIONAL. -/
theorem member_out {W : OnBytes.Model.Verify.Public} {l : Nat} {same : S → S → Bool} {a : Place}
    {b : Block S Claim} (M : K6MemberIs W l same a b) (hk : a.kind ≠ KindName.K7)
    (hsm : ∀ s t : S, t.out.reply = s.out.reply → same s t = true) (hp : b.planOk = true)
    (ft : Nat) (cols : List OpenedColumn) (s : S) (c : NCells) (mask : Nat → E) (rs : List Fmt.RoundView)
    (H : HeardAll) (G : Fork) (hL : K6Left W s) (hfail : s.failed = none) (hopen : HeadOpen s)
    (hstart : startOk W s = true)
    (R : TruthK6N W.hS (readsOf W) (workOf W) s c mask rs H G)
    (gk : OnBytes.Model.Forest.Heard) (hgk : s.lookHeard? = some gk)
    (hK : KeysWorth (parOf W.hS (workOf W)) (seatAt W.hS (readsOf W)) s c mask gk) :
    ∃ s' : S, b.step ft s rs cols = .ok (s', 0) ∧
      (seatAt W.hS (readsOf W)).ledger s' = G ∧ (seatAt W.hS (readsOf W)).heard s' = some H ∧
      K6Out W s' (c, mask) := by
  obtain ⟨s', hst, bL, bH, hO⟩ := bare_out W l ft cols s c mask rs H G (M.on hp hstart hL) hfail
    hopen R gk hgk hK
  exact ⟨s', (M.step_iff hk hsm ft s s' rs cols 0).2 ⟨hst, hstart⟩, bL, bH, hO⟩

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.bare_out
#print axioms VerifiableInference.Desc.Kinds.Head.Law.K6MemberIs.on
#print axioms VerifiableInference.Desc.Kinds.Head.Law.member_out
