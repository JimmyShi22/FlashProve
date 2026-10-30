-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/SealStays.lean: a sealed message stays sealed along every step that leaves the
codes and the sampled messages (SmpStay, SmpStay.lean): so along every plain function of the ground
and the beginning of a proximity test, whichever kind's block calls them.

Main names: smpStay_of_old, SeedIs.stays, Sealed.stays.

What is not claimed. The word of the message is an argument of Sealed: that a reader of the oracles
returns the same word behind the step is not said here (sealed_rides, GoodSendEarlierMessages.lean). Nothing
on soundness of a protocol, on an honest prover or on hiding.

-/
import Johnson.Desc.K1.Law.SmpStay
import Johnson.Desc.K1.Law.GoodSend5

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model Desc.Plain
open OnBytes.Slice Johnson.Pack Cb Cb.Ood

/-- The older relation, on all messages, gives this one. -/
theorem smpStay_of_old {A B : Statement} (h : OldMsgs A B) : SmpStay A B := by
  refine ⟨h.1, fun i x hx s => ?_⟩
  have hi : i < A.oracles.size := by
    by_contra hn
    rw [Array.getElem?_eq_none (Nat.le_of_not_lt hn)] at hx
    cases hx
  have e := h.2 i hi
  rw [hx] at e
  obtain ⟨x', hx', e⟩ := Option.map_eq_some_iff.1 e
  obtain ⟨e1, e23⟩ := Prod.mk.inj e
  obtain ⟨e2, e3⟩ := Prod.mk.inj e23
  exact ⟨x', hx', e1, e2.trans s, e3⟩

/-- The record's sample rows of a sampled message are as they were. -/
theorem SeedIs.stays {cs : Codes} {s : OracleShape} {A B : Statement} {o : Nat}
    {ρ : (Fin (bitsZ cs s) → GE) × GEˣ} {y : GE} (h : SeedIs cs s A o ρ y) (hs : SmpStay A B) :
    SeedIs cs s B o ρ y := by
  obtain ⟨hc, x, z, β, t, hx, h1, h2, h3, h4, h5⟩ := h
  obtain ⟨x', hx', e1, e2, e3⟩ := hs.2 o x hx h2
  exact ⟨hs.1.trans hc, x', z, β, t, hx', e1.trans h1, e2, e3.trans h3, h4, h5⟩

/-- **A sealed message stays sealed.** -/
theorem Sealed.stays {cs : Codes} {s : OracleShape} {e : Nat} {f : (portOmZ cs s e).Str}
    {A B : Statement} {o : Nat} (h : Sealed cs s e f A o) (hs : SmpStay A B) :
    Sealed cs s e f B o := by
  obtain ⟨ρ, y, h1, h2⟩ := h
  exact ⟨ρ, y, h1.stays hs, h2⟩

end VerifiableInference.Desc.K1
