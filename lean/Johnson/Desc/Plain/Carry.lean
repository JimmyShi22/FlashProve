-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Plain/Carry.lean: A REDUCTION THAT THE LIBRARY HAS PROVED IS CARRIED TO A BLOCK's
WRITTEN ROUNDS, NOT PROVED AGAIN. The plain twin of the library's `know_carryS`
(OnBytes/Flat/CarrySkip.lean), by the same `CarryS.doomed`.

K: a reduction over written rounds (a block at its stretch: `Piece.ior.red`): hash blocks are drawn,
with bits of work. K': a typed reduction of the library with a proved clause (field elements are
drawn). F a: reads a transcript of K as one of K' (`CarryS`); `Fits`: K's written counts bear K''s
along it. fa: reads a statement of K as one of K'.

  `leads_carryS`: from K'.Leads. The one premise with content (`hout`), at every statement with `on`
    and EVERY transcript: WHERE K SAYS YES, K' SAYS YES AT THE SAME TRANSCRIPT READ BY F, and what
    K''s relation says of its two statements gives what K's says of its two.
  `leads_of_know`: the same from the library's `Know` of K' (by `Know.toLeads`): no extractor of K
    is named, and none of K' is read.
  `leadsK_carryS`: with keys: the reading F and the typed statement's key hang on K's key alone.
Limits: those of Leads.lean and of CarrySkip.lean.

Nearest kin in the library. `know_carryS`, `sound_carryS`, `CarryS.doomed`
(OnBytes/Flat/CarrySkip.lean), `know_carry` (OnBytes/Flat/Transport.lean): `CarryS.doomed` is
called; the rest is the plain form's bookkeeping.


-/
import Johnson.Desc.Plain.Keyed
import OnBytes.Flat.CarrySkip

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Flat
open _root_.Iop

variable {A B A' B' κ κ' : Type}

theorem leads_carryS (K : Reduction A B) (K' : Reduction A' B') (F : A → CarryS K.shape K'.shape)
    (ε : Err K'.shape) (ε' : Err K.shape) (hF : ∀ a, (F a).Fits ε ε') (fa : A → A')
    (on : A → Prop) (on' : A' → Prop) (Q : A → B → Prop) (Q' : A' → B' → Prop)
    (hon : ∀ a, on a → on' (fa a))
    (hout : ∀ a τ b, on a → K.out a τ = some b →
      ∃ τ' b', (F a).tr τ = some τ' ∧ K'.out (fa a) τ' = some b' ∧ (Q' (fa a) b' → Q a b))
    (h : K'.Leads on' Q' ε) : K.Leads on Q ε' := fun a ha =>
  CarryS.doomed (F a) ε ε' (hF a) (fun τ => ∀ b, K.out a τ = some b → Q a b)
    (fun τ' => ∀ b', K'.out (fa a) τ' = some b' → Q' (fa a) b')
    (fun τ hτ b hb => by
      obtain ⟨τ', _, h1, _⟩ := hout a τ b ha hb
      rw [hτ] at h1
      cases h1)
    (fun τ τ' hτ hbad b hb => by
      obtain ⟨τ'', b', h1, h2, h3⟩ := hout a τ b ha hb
      rw [hτ] at h1
      cases h1
      exact h3 (hbad b' h2))
    (h (fa a) (hon a ha))

theorem leads_of_know {WA' WB' : Type} (K : Reduction A B) (K' : Reduction A' B')
    (F : A → CarryS K.shape K'.shape) (ε : Err K'.shape) (ε' : Err K.shape)
    (hF : ∀ a, (F a).Fits ε ε') (fa : A → A') (on : A → Prop) (on' : A' → Prop)
    (Q : A → B → Prop) (RA' : A' → WA' → Prop) (RB' : B' → WB' → Prop)
    (ext' : A' → Tr K'.shape → WB' → WA') (hon : ∀ a, on a → on' (fa a))
    (hout : ∀ a τ b, on a → K.out a τ = some b →
      ∃ τ' b', (F a).tr τ = some τ' ∧ K'.out (fa a) τ' = some b' ∧
        (((∃ w, RB' b' w) → ∃ w, RA' (fa a) w) → Q a b))
    (h : K'.Know on' RA' RB' ext' ε) : K.Leads on Q ε' :=
  leads_carryS K K' F ε ε' hF fa on on' Q _ hon hout h.toLeads

theorem leadsK_carryS (K : Reduction A B) (K' : Reduction A' B') (key : A → κ) (key' : A' → κ')
    (F : κ → CarryS K.shape K'.shape) (fk : κ → κ') (ε : Err K'.shape) (ε' : Err K.shape)
    (hF : ∀ k, (F k).Fits ε ε') (fa : A → A') (hk : ∀ a, key' (fa a) = fk (key a))
    (on : A → Prop) (on' : A' → Prop) (Q : A → B → Prop) (Q' : A' → B' → Prop)
    (hon : ∀ a, on a → on' (fa a))
    (hout : ∀ a τ b, on a → K.out a τ = some b →
      ∃ τ' b', (F (key a)).tr τ = some τ' ∧ K'.out (fa a) τ' = some b' ∧ (Q' (fa a) b' → Q a b))
    (h : K'.LeadsK key' on' Q' ε) : K.LeadsK key on Q ε' := fun k =>
  CarryS.doomed (F k) ε ε' (hF k)
    (fun τ => ∀ a, key a = k → on a → ∀ b, K.out a τ = some b → Q a b)
    (fun τ' => ∀ a', key' a' = fk k → on' a' → ∀ b', K'.out a' τ' = some b' → Q' a' b')
    (fun τ hτ a hka ha b hb => by
      obtain ⟨τ', _, h1, _⟩ := hout a τ b ha hb
      rw [hka, hτ] at h1
      cases h1)
    (fun τ τ' hτ hbad a hka ha b hb => by
      obtain ⟨τ'', b', h1, h2, h3⟩ := hout a τ b ha hb
      rw [hka, hτ] at h1
      cases h1
      exact h3 (hbad (fa a) (by rw [hk, hka]) (hon a ha) b' h2))
    (h (fk k))

end OnBytes.Flat

#print axioms OnBytes.Flat.leads_carryS
#print axioms OnBytes.Flat.leads_of_know
#print axioms OnBytes.Flat.leadsK_carryS
