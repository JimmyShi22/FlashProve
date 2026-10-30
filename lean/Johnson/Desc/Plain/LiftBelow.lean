-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Plain/LiftBelow.lean: FROM A KIND's OWN LAW TO THE PIECE THAT A DESCRIPTION HOLDS. A
description's pieces hold the blocks `(below b).lift get set` (`OfDesc`,
Johnson/Desc/Sound/DescThree.lean):
the test "every word is below the prime" in front; lifted from the kind's own part S₀ of the record
to the chain's record S. Whoever proves a kind's law proves ONE plain law, of its own block b, at
its own part.

  `Piece.under`: the piece with `below b` in b's place. `leads_under` | `leadsK_under`: where the
    words of the piece's rounds behind (`p.back`) are below the prime (hb), it has every plain law
    that the piece has: it says yes at fewer transcripts, and puts out the same.
  `leads_lift` | `leadsK_lift`: the lifted piece (`Piece.lift`, Johnson/Desc/Sound/LiftRule.lean)
    has, where `get` reads back what `set` lays and a second `set` overlays the first (h1, h2), the
    law read at the part, AND, FOR CERTAIN, "the record behind is the record in front with the part
    laid anew": so whatever rides beside the part is carried (`Keeps.beside` | `KeepsW.beside` are
    fed by it).
Taken from Johnson/Desc/Sound/: `below`, `foldBelow`, `Piece.lift`, `atPart`, `liftOut`.
Limits: those of Leads.lean.
Nearest kin: `liftOut` (LiftRule.lean) and `foldBelow` (FoldBelowProof.lean), both called.

-/
import Johnson.Desc.Plain.FoldChainK
import Johnson.Desc.Sound.LiftRule
import Johnson.Desc.Sound.FoldBelowProof

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.Plain
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open _root_.Iop (Reduction Err Shape IOR ExtSpec oneExternalString Doomed)
open VerifiableInference.Desc.Sound

variable {S S₀ Cl W κ : Type} {C : CK} {F : Frame}

/-- The piece with the test "every word is below the prime" in front of its block's decision. -/
def _root_.VerifiableInference.Desc.Sound.Piece.under (p : Piece C F S Cl W) : Piece C F S Cl W :=
  ⟨below p.b, p.base, p.ds, p.back, p.ext, p.err⟩

/-- Where the piece with the test in front puts out, the piece puts out the same. -/
theorem under_out (p : Piece C F S Cl W) (hb : viewWordsBelowPrime ⟨p.back, []⟩ = true) (a : S × F.E.Str)
    (τ : Iop.Tr (uLT C p.ds)) (b : S × F.E.Str) (h : p.under.ior.red.out a τ = some b) :
    p.ior.red.out a τ = some b := by
  have e : p.under.run = foldRunW F p.b.name [p.b] p.back :=
    foldBelow S Cl F p.b.name [p.b] p.back hb
  have h' : ((if sTests C p.stage a.2 τ then p.under.run a.1 (sView C p.stage a.2 τ) else none).map
      fun xo => (xo, p.ior.imp a.2 τ)) = some b := h
  show ((if sTests C p.stage a.2 τ then p.run a.1 (sView C p.stage a.2 τ) else none).map
      fun xo => (xo, p.ior.imp a.2 τ)) = some b
  rw [e] at h'
  unfold foldRunW at h'
  split at h'
  · rename_i ht
    rw [if_pos ht]
    split at h'
    · exact h'
    · cases h'
  · cases h'

theorem leads_under (p : Piece C F S Cl W) (hb : viewWordsBelowPrime ⟨p.back, []⟩ = true)
    (on : S × F.E.Str → Prop) (Q : S × F.E.Str → S × F.E.Str → Prop)
    (h : p.ior.red.Leads on Q p.err) : p.under.ior.red.Leads on Q p.under.err := fun a ha =>
  Doomed.mono _ _ (fun τ hτ b hb' => hτ b (under_out p hb a τ b hb')) (h a ha)

theorem leadsK_under (p : Piece C F S Cl W) (hb : viewWordsBelowPrime ⟨p.back, []⟩ = true)
    (key : S × F.E.Str → κ) (on : S × F.E.Str → Prop) (Q : S × F.E.Str → S × F.E.Str → Prop)
    (h : p.ior.red.LeadsK key on Q p.err) : p.under.ior.red.LeadsK key on Q p.under.err :=
  fun k => Doomed.mono _ _
    (fun τ hτ a hk ha b hb' => hτ a hk ha b (under_out p hb a τ b hb')) (h k)

/-- **One law, at the block's own part.** -/
theorem leads_lift (get : S → S₀) (set : S → S₀ → S) (p : Piece C F S₀ Cl W)
    (on : S₀ × F.E.Str → Prop) (Q : S₀ × F.E.Str → S₀ × F.E.Str → Prop)
    (h1 : ∀ t s, get (set t s) = s) (h2 : ∀ t s s', set (set t s) s' = set t s')
    (h : p.ior.red.Leads on Q p.err) :
    (p.lift get set).ior.red.Leads (fun a => on (atPart get a))
      (fun a b => Q (atPart get a) (atPart get b) ∧ b.1 = set a.1 (get b.1))
      (p.lift get set).err := by
  intro a ha
  refine Doomed.mono _ _ ?_ (h (atPart get a) ha)
  intro τ hτ b hb
  rw [liftOut S S₀ Cl W C F get set p h1 h2 a τ] at hb
  obtain ⟨b₀, hb₀, rfl⟩ := Option.map_eq_some_iff.1 hb
  have e : atPart get ((set a.1 b₀.1, b₀.2) : S × F.E.Str) = b₀ := by
    show (get (set a.1 b₀.1), b₀.2) = b₀
    rw [h1]
  refine ⟨?_, ?_⟩
  · rw [e]
    exact hτ b₀ hb₀
  · show set a.1 b₀.1 = set a.1 (get (set a.1 b₀.1))
    rw [h1]

theorem leadsK_lift (get : S → S₀) (set : S → S₀ → S) (p : Piece C F S₀ Cl W)
    (key : S₀ × F.E.Str → κ) (on : S₀ × F.E.Str → Prop)
    (Q : S₀ × F.E.Str → S₀ × F.E.Str → Prop)
    (h1 : ∀ t s, get (set t s) = s) (h2 : ∀ t s s', set (set t s) s' = set t s')
    (h : p.ior.red.LeadsK key on Q p.err) :
    (p.lift get set).ior.red.LeadsK (fun a => key (atPart get a)) (fun a => on (atPart get a))
      (fun a b => Q (atPart get a) (atPart get b) ∧ b.1 = set a.1 (get b.1))
      (p.lift get set).err := by
  intro k
  refine Doomed.mono _ _ ?_ (h k)
  intro τ hτ a hk ha b hb
  rw [liftOut S S₀ Cl W C F get set p h1 h2 a τ] at hb
  obtain ⟨b₀, hb₀, rfl⟩ := Option.map_eq_some_iff.1 hb
  have e : atPart get ((set a.1 b₀.1, b₀.2) : S × F.E.Str) = b₀ := by
    show (get (set a.1 b₀.1), b₀.2) = b₀
    rw [h1]
  refine ⟨?_, ?_⟩
  · rw [e]
    exact hτ (atPart get a) hk ha b₀ hb₀
  · show set a.1 b₀.1 = set a.1 (get (set a.1 b₀.1))
    rw [h1]

/-- The law of keys goes over likewise. -/
theorem keyLaw_lift (get : S → S₀) (set : S → S₀ → S) (p : Piece C F S₀ Cl W)
    (key key' : S₀ × F.E.Str → κ)
    (h1 : ∀ t s, get (set t s) = s) (h2 : ∀ t s s', set (set t s) s' = set t s')
    (h : p.ior.red.KeyLaw key key') :
    (p.lift get set).ior.red.KeyLaw (fun a => key (atPart get a)) fun a => key' (atPart get a) := by
  obtain ⟨g, l⟩ := h
  refine ⟨g, fun a τ b hb => ?_⟩
  rw [liftOut S S₀ Cl W C F get set p h1 h2 a τ] at hb
  obtain ⟨b₀, hb₀, rfl⟩ := Option.map_eq_some_iff.1 hb
  have e : atPart get ((set a.1 b₀.1, b₀.2) : S × F.E.Str) = b₀ := by
    show (get (set a.1 b₀.1), b₀.2) = b₀
    rw [h1]
  show key' (atPart get ((set a.1 b₀.1, b₀.2) : S × F.E.Str)) = g (key (atPart get a)) τ
  rw [e]
  exact l (atPart get a) τ b₀ hb₀

end VerifiableInference.Desc.Plain

#print axioms VerifiableInference.Desc.Plain.leads_under
#print axioms VerifiableInference.Desc.Plain.leads_lift
#print axioms VerifiableInference.Desc.Plain.leadsK_lift
#print axioms VerifiableInference.Desc.Plain.keyLaw_lift
