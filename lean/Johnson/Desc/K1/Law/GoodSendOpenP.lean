-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/GoodSendOpenP.lean: a block whose yes holds a yes of the sending that is written
over the verifier program's own functions (sendP, at either value of its flag), or of the kind's
decision where the caller goes on (decideOpen), is in the class of the law of a sending whose block
goes on (IsSendOpen, GoodSendOpen.lean).

Main names: isSendOpen_of_sendP, isSendOpen_of_open.

What is not claimed. No block is shown to meet the premise. Nothing on soundness of a protocol, on
an honest prover or on hiding.

-/
import Johnson.Desc.K1.Law.GoodSendOpen
import Johnson.Desc.K1.Law.SendP5

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model Desc.Plain
open VerifiableInference.Desc (Block)

variable {T Cl : Type}

/-- **Every block that calls sendP.** -/
theorem isSendOpen_of_sendP (P : Par) (hB : planOkOwn P = true) (hl : P.codes.lengthsOk = true)
    (stOf : T → Statement) (first : T → Nat) (b : Block T Cl)
    (h : ∀ s s' r₁ rs gs, b.decide s (r₁ :: rs) gs = .ok s' →
      ∃ (L : Type) (d d' : DState L) (own : Bool) (r₂ : Fmt.RoundView) (ids : Array Nat) (sd an : List E)
        (need : Nat), sendP groundG P.gp own d P.sent r₁ r₂ = some (ids, sd, an, need, d') ∧
          d.st.codes = P.codes ∧ OldMsgs d'.st (stOf s') ∧ first s' = d.st.oracles.size) :
    IsSendOpen P stOf first b := by
  intro s s' r₁ rs gs hy
  obtain ⟨L, d, d', own, r₂, ids, sd, an, need, h1, hc, h2, h3⟩ := h s s' r₁ rs gs hy
  exact ⟨L, d, d', none, ids, cutTo P r₂,
    (decide_of_sendP P own d d' r₁ r₂ ids sd an need hB hl hc h1).1, h2, h3⟩

/-- **Every block that calls the kind's decision where the caller goes on.** -/
theorem isSendOpen_of_open (P : Par) (stOf : T → Statement) (first : T → Nat) (b : Block T Cl)
    (h : ∀ s s' r₁ rs gs, b.decide s (r₁ :: rs) gs = .ok s' →
      ∃ (L : Type) (d d' : DState L) (owed : Option Nat) (r₂ : Fmt.RoundView) (ids : Array Nat) (n : Nat),
        decideOpen P owed d [r₁, r₂] = .ok (ids, n, d') ∧ OldMsgs d'.st (stOf s') ∧
          first s' = d.st.oracles.size) :
    IsSendOpen P stOf first b := by
  intro s s' r₁ rs gs hy
  obtain ⟨L, d, d', owed, r₂, ids, n, h1, h2, h3⟩ := h s s' r₁ rs gs hy
  have h1' : (decideSend P owed d [r₁, cutTo P r₂]).map (fun x => (x.1, P.answers, x.2)) =
      .ok (ids, n, d') := h1
  cases hyes : decideSend P owed d [r₁, cutTo P r₂] with
  | error e =>
    rw [hyes] at h1'
    cases h1'
  | ok x =>
    rw [hyes] at h1'
    obtain ⟨e1, e23⟩ := Prod.mk.inj (Except.ok.inj h1')
    obtain ⟨_, e3⟩ := Prod.mk.inj e23
    subst e1 e3
    exact ⟨L, d, x.2, owed, x.1, cutTo P r₂, hyes, h2, h3⟩

end VerifiableInference.Desc.K1
