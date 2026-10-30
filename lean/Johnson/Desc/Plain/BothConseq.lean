-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Plain/BothConseq.lean: THE PLAIN FORM FOR A BATCH IS MONOTONE, WITH THE YES AT HAND.
Theorems; general: no kind, no table is named.

WHY. A block's law in the form LeadsB (Johnson/Desc/Plain/Both.lean) stands at one filling of a
table's letters; a rule that spends it asks it at another, with a STRONGER promise in front and
behind. No law need turn: the two lost sets and the two lists of errors stay.

  LeadsB.conseq    from a stronger condition in front; to another relation, which may be concluded
                   from the old one WITH the condition in front and the block's yes at hand: so
                   whatever a yes hands on for certain may be laid beside.
  LeadsB.beside    the corollary: a test T in front and T' behind are laid beside, where a yes
                   inside the condition carries T to T'.
KIN: LeadsBN.conseq (Johnson/Desc/Plain/KeyAlone.lean): the same at one list of errors for N slots:
it lies; this is its like at the two lists apart, which a rule that sums them itself asks.
leadsB_carryS (Johnson/Desc/Plain/CarryBoth.lean): the carriage between TWO reductions along a map
of transcripts: wider; at one reduction it wants an identity map with its two fits: not called.
What is not claimed. That any law holds. Nothing on soundness.

-/
import Johnson.Desc.Plain.Both

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Iop.Reduction
variable {A B κ : Type}

/-- **Monotone, with the yes at hand.** -/
theorem LeadsB.conseq {K : Reduction A B} {key : A → κ} {on on' : A → Prop} {Q Q' : A → B → Prop}
    {εK εO : Err K.shape} (h : K.LeadsB key on Q εK εO) (h0 : ∀ a, on' a → on a)
    (h1 : ∀ a τ b, on' a → K.out a τ = some b → Q a b → Q' a b) : K.LeadsB key on' Q' εK εO := by
  obtain ⟨lostK, lostO, hK, hO, hQ⟩ := h
  exact ⟨lostK, lostO, hK, fun a ha => hO a (h0 a ha),
    fun a τ b ha hk ho hb => h1 a τ b ha hb (hQ a τ b (h0 a ha) hk ho hb)⟩

/-- **A test laid beside.** -/
theorem LeadsB.beside {K : Reduction A B} {key : A → κ} {on : A → Prop} {Q : A → B → Prop}
    {εK εO : Err K.shape} (h : K.LeadsB key on Q εK εO) (T : A → Prop) (T' : B → Prop)
    (hT : ∀ a τ b, on a → T a → K.out a τ = some b → T' b) :
    K.LeadsB key (fun a => on a ∧ T a) (fun a b => Q a b ∧ T' b) εK εO :=
  h.conseq (fun _ ha => ha.1) fun a τ b ha hb hq => ⟨hq, hT a τ b ha.1 ha.2 hb⟩

end Iop.Reduction
