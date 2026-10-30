-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Thread/Ans.lean: what a pin says at the invariants: the definition for
the parameter `ans` (Honest/Thread/First.lean: `Letters.ans`; `honest` puts it in place of the
meaning's whole field `pin`). A pin is the library's item that ties a committed message to the
witness. The library's pin (`pinJT`, Johnson/Desc/Sound/MeaningSig.lean; `PinAt`, MsgSig.lean) says
of a member of a sending: the verifier's state holds its sample, every leaf is shown, and the
committed word decodes, with the sample, to the witness's message. An invariant speaks of a run of
the honest side's own parts, where the witness's message is a given function of the coins, the input
and the challenges. There the pin says only: the verifier's state holds the member's sample, and the
witness's message has that sample's answers at its seed. No oracle is read. Definitions: what an
item means at the invariants; and lemmas on them. They are general in the parameters of the
library's own pin. (In this file a member is an entry of a sending, `Mem`, not a sub-protocol.)

  1  `AnsAt`, `ansJT`   one member; tenant t of tree j: the definition for `ans`
  2  `ansJT_congr`   it reads the verifier's state through the reader of samples alone
  3  `rowAt₀`, `formsAt_row`, `ansAt_row`, `ansJT_rows`   at the library's reader by the message's
     fixed number (`smpNamed`): through the first sample row of that message alone

What section 3 is for. An item that is a pin stays open past sub-protocols, and has to be proved
again after some. Whoever proves it needs, from each such sub-protocol's clause of `keeps`, that
what the pin reads of the verifier's state is unchanged. By `ansJT_rows` that is: at the fixed
numbers of the messages that are at the pin's seats, the statement's first sample row.

Limits.
  * That the witness's message has the answers is proved here of no run.
  * Nothing ties this definition to the library's pin: that `PinAt` gives `AnsAt` (a decoder's value
    has the sample's answers) is not stated here.
  * One answer for each message, as in the library's reader.
  * None is one of the library's goals.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.Sound.MeaningSig
import Johnson.Desc.Sound.SmpNamed

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace ProofFile.Honest
open VerifiableInference.Desc (Strs Wit)
open VerifiableInference.Desc.Sound (MsgT Mem Sending SitsAt msgsOf smpNamed smpNamed_stays numAt)
open VerifiableInference.Desc.First (S)
open Johnson.Pack (sigOf)

variable (cs : OnBytes.Codes) {A Cells Tok : Type} (arr : ℕ → ℕ → ℕ)

/-! ## 1 The definition for `ans` -/

/-- **Member `i` answers**: the argument `a` (at the invariants: what the chain was given, with the
verifier's state) holds its sample, as read by `smp`, and the witness's message has the sample's
answers at its seed. It is a definition: what an item means at the invariants. -/
def AnsAt (l : List (OnBytes.OracleShape × ℕ)) (seat : Fin l.length → ℕ × ℕ)
    (smp : A → (i : Fin l.length) → Option ((sigOf cs l).om i).Smp) (i : Fin l.length) (a : A)
    (w : Wit Cells Tok MsgT) : Prop :=
  ∃ z, smp a i = some z ∧ ((sigOf cs l).om i).Z.val z.1 (msgsOf cs l seat arr w i) = z.2

/-- **A pin at the invariants**: tenant t of tree j: a member of `ms` is committed there, and every
member of `ms` that is committed there answers. The form of the library's `pinJT`, with `AnsAt` in
place of `PinAt`. The oracles are not read. -/
def ansJT (smp : A → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
    (ms : List Mem) (j t : ℕ) (a : A) (_ : Strs) (w : Wit Cells Tok MsgT) : Prop :=
  (∃ x ∈ ms, SitsAt x j t) ∧
    ∀ x ∈ ms, SitsAt x j t → AnsAt cs arr x.1.l x.1.seat (fun z => smp z x.1) x.2 a w

/-! ## 2 It reads the verifier's state through the reader of samples alone -/

theorem ansJT_congr
    {smp : A → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp}
    {ms : List Mem} {j t : ℕ} {a a' : A} {y y' : Strs} {w : Wit Cells Tok MsgT}
    (h : ∀ x ∈ ms, SitsAt x j t → smp a' x.1 x.2 = smp a x.1 x.2)
    (h0 : ansJT cs arr smp ms j t a y w) : ansJT cs arr smp ms j t a' y' w := by
  obtain ⟨h1, h2⟩ := h0
  refine ⟨h1, fun x hx hs => ?_⟩
  obtain ⟨z, hz, hv⟩ := h2 x hx hs
  exact ⟨z, (h x hx hs).trans hz, hv⟩

/-! ## 3 At the library's reader by the message's fixed number -/

/-- The first sample row that a statement holds of message number `o`. -/
def rowAt₀ (St : OnBytes.Statement) (o : ℕ) : Option OnBytes.Row :=
  (St.oracles[o]?).bind fun x => x.sampleRows[0]?

theorem formsAt_row (s : OnBytes.OracleShape) (St : OnBytes.Statement) (o : ℕ) :
    VerifiableInference.Desc.K1.formsAt cs s St o =
      (rowAt₀ St o).map fun r _ => VerifiableInference.Desc.K1.formRow cs s o r := by
  unfold VerifiableInference.Desc.K1.formsAt rowAt₀
  cases St.oracles[o]? <;> rfl

theorem ansAt_row (St : OnBytes.Statement) (o : ℕ) :
    VerifiableInference.Desc.K1.ansAt St o =
      (rowAt₀ St o).map fun r _ => OnBytes.Slice.readE r.target := by
  unfold VerifiableInference.Desc.K1.ansAt rowAt₀
  cases St.oracles[o]? <;> rfl

/-- **What a pin reads of the verifier's state**: if, at the fixed number of every member that is
committed at the seat, the two states' statements hold the same first sample row, the pin says of
the one what it says of the other. `P`: what the chain was given: it is not read. -/
theorem ansJT_rows {P : Type} {seats : List (ℕ × ℕ)} {ms : List Mem} {j t : ℕ} {p p' : P}
    {s s' : S} {y y' : Strs} {w : Wit Cells Tok MsgT}
    (h : ∀ x ∈ ms, SitsAt x j t → rowAt₀ s'.st (numAt seats x) = rowAt₀ s.st (numAt seats x))
    (h0 : ansJT cs arr (smpNamed cs seats) ms j t (p, s) y w) :
    ansJT cs arr (smpNamed cs seats) ms j t (p', s') y' w := by
  refine ansJT_congr cs arr (fun x hx hs => ?_) h0
  obtain ⟨sd, i⟩ := x
  refine smpNamed_stays cs seats (p, s) (p', s') sd i ?_ ?_
  · rw [formsAt_row, formsAt_row, h ⟨sd, i⟩ hx hs]
  · rw [ansAt_row, ansAt_row, h ⟨sd, i⟩ hx hs]

end ProofFile.Honest

#print axioms ProofFile.Honest.ansJT_congr
#print axioms ProofFile.Honest.formsAt_row
#print axioms ProofFile.Honest.ansAt_row
#print axioms ProofFile.Honest.ansJT_rows
