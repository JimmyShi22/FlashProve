-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Plain/CarryBoth.lean: THE CARRIAGE IN TWO PARTS: a typed reduction's law for a batch in
two parts (`LeadsB`, Johnson/Desc/Plain/Both.lean) is carried to a block's written rounds: the plain
twin of
`pieceLostBoth`: `CarryS.doomed` twice, `Fits` twice, the reading a function of the key.

  `leadsB_carryS`: K over written rounds, K' typed; F k reads a transcript of K as one of K', at K's
    key k; fk the typed key; the key's game and the slot's own game are each carried along F. The
    one premise with content (`hout`) is `leadsK_carryS`' (Johnson/Desc/Plain/Carry.lean).
  `leadsBN_carryS`: with one list of errors of K that bears the carried split for N slots.
Limits: those of Both.lean and Carry.lean.
Nearest kin: `CarryS.doomed` (OnBytes/Flat/CarrySkip.lean; called twice); `pieceLostBoth`
(FoldSlotsCarry.lean; not in this library): the knowledge form's twin.

-/
import Johnson.Desc.Plain.Both
import Johnson.Desc.Plain.Carry

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Flat
open _root_.Iop

variable {A B A' B' κ κ' : Type}

theorem leadsB_carryS (K : Reduction A B) (K' : Reduction A' B') (key : A → κ) (key' : A' → κ')
    (F : κ → CarryS K.shape K'.shape) (fk : κ → κ') (εK εO : Err K'.shape) (δK δO : Err K.shape)
    (hFK : ∀ k, (F k).Fits εK δK) (hFO : ∀ k, (F k).Fits εO δO) (fa : A → A')
    (hk : ∀ a, key' (fa a) = fk (key a)) (on : A → Prop) (on' : A' → Prop) (Q : A → B → Prop)
    (Q' : A' → B' → Prop) (hon : ∀ a, on a → on' (fa a))
    (hout : ∀ a τ b, on a → K.out a τ = some b →
      ∃ τ' b', (F (key a)).tr τ = some τ' ∧ K'.out (fa a) τ' = some b' ∧ (Q' (fa a) b' → Q a b))
    (h : K'.LeadsB key' on' Q' εK εO) : K.LeadsB key on Q δK δO := by
  obtain ⟨lK, lO, dK, dO, q⟩ := h
  refine ⟨fun k τ => ∀ τ', (F k).tr τ = some τ' → lK (fk k) τ',
    fun a τ => ∀ τ', (F (key a)).tr τ = some τ' → lO (fa a) τ', fun k => ?_, fun a ha => ?_,
    fun a τ b ha hK hO hb => ?_⟩
  · exact CarryS.doomed (F k) εK δK (hFK k) _ (lK (fk k))
      (fun τ hτ τ' h' => by rw [hτ] at h'; cases h')
      (fun τ τ' hτ hl τ'' h' => by
        rw [hτ] at h'
        obtain rfl := Option.some.inj h'
        exact hl) (dK (fk k))
  · exact CarryS.doomed (F (key a)) εO δO (hFO (key a)) _ (lO (fa a))
      (fun τ hτ τ' h' => by rw [hτ] at h'; cases h')
      (fun τ τ' hτ hl τ'' h' => by
        rw [hτ] at h'
        obtain rfl := Option.some.inj h'
        exact hl) (dO (fa a) (hon a ha))
  · obtain ⟨τ', b', h1, h2, h3⟩ := hout a τ b ha hb
    exact h3 (q (fa a) τ' b' (hon a ha) (by rw [hk]; exact hK τ' h1) (hO τ' h1) h2)

theorem leadsBN_carryS (K : Reduction A B) (K' : Reduction A' B') (key : A → κ) (key' : A' → κ')
    (F : κ → CarryS K.shape K'.shape) (fk : κ → κ') (εK εO : Err K'.shape) (δK δO : Err K.shape)
    (N : ℕ) (δ : Err K.shape) (hle : Err.le (Err.add δK (Err.times N δO)) δ)
    (hFK : ∀ k, (F k).Fits εK δK) (hFO : ∀ k, (F k).Fits εO δO) (fa : A → A')
    (hk : ∀ a, key' (fa a) = fk (key a)) (on : A → Prop) (on' : A' → Prop) (Q : A → B → Prop)
    (Q' : A' → B' → Prop) (hon : ∀ a, on a → on' (fa a))
    (hout : ∀ a τ b, on a → K.out a τ = some b →
      ∃ τ' b', (F (key a)).tr τ = some τ' ∧ K'.out (fa a) τ' = some b' ∧ (Q' (fa a) b' → Q a b))
    (h : K'.LeadsB key' on' Q' εK εO) : K.LeadsBN key on Q N δ :=
  ⟨δK, δO, hle, leadsB_carryS K K' key key' F fk εK εO δK δO hFK hFO fa hk on on' Q Q' hon hout h⟩

end OnBytes.Flat

#print axioms OnBytes.Flat.leadsB_carryS
#print axioms OnBytes.Flat.leadsBN_carryS
