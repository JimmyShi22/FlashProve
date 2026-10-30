-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/GoodSend1.lean: towards the law of a sending in the form of the rule of
composition (Piece.GoodIn): the two written rounds of a sending read as one typed round that keeps
the prover's message and draws one seed; and a bridge from a count of lost seeds to GoodIn where the
set of lost seeds may hang on the prover's message of that very round.

Main names: seedRound, seedMaps, seedMaps_ok, seedMaps_pass; shownAt; goodIn_of_count_msg.
No kind is named in this file.

What is not claimed. The carriage, that its errors fit, and that it reads the value which the block
reads are premises of the bridge. A block that refuses all has GoodIn too. One seed alone. Nothing
on soundness of a protocol, on an honest prover or on hiding.

-/
import Johnson.Desc.Sound.GoodIn
import OnBytes.Flat.CarrySForms
import OnBytes.Slice.RoundsMaps

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes
open Iop Prob Run OnBytes.Maker OnBytes.Flat OnBytes.Slice
open VerifiableInference.Desc (Block noDigest)
open VerifiableInference.Desc.Sound (Frame Piece)
open _root_.Run.PQ (CK)

/-- The written round d with its prover's message as it is, and for its challenge one seed: c
elements and a factor other than 0. -/
def seedRound (d : RDT) (c : Nat) : Round :=
  { Orc := (wT d).Orc, Pos := (wT d).Pos, Sym := (wT d).Sym, rd := (wT d).rd
    Plain := (wT d).Plain, Chal := (Fin c → GE) × GEˣ, dOrc := (wT d).dOrc
    dPlain := (wT d).dPlain }

/-- The two written rounds of a sending: the first is read as that typed round, the second is
passed by. -/
noncomputable def seedMaps (d₁ d₂ : RDT) (c : Nat) : Maps [d₁, d₂] [seedRound d₁ c] :=
  .step (RMap.seed (r' := seedRound d₁ c) (fun m => m) c id) (.skip d₂ .nil)

/-- It is as the library asks, where the first round draws c elements and a factor other than 0. -/
theorem seedMaps_ok {d₁ : RDT} (d₂ : RDT) {c : Nat}
    (hp : PlainDraws (Fmt.dsOf d₁.entry d₁.kind)) (hE : nE (Fmt.dsOf d₁.entry d₁.kind) = c + 1)
    (hP : nP (Fmt.dsOf d₁.entry d₁.kind) = 0) (hz : IsNZ (Fmt.dsOf d₁.entry d₁.kind) c)
    (hl : d₁.entry.logN ≤ 64) : (seedMaps d₁ d₂ c).OK :=
  ⟨RMap.seed_ok _ hp hE hP hz hl Function.injective_id, trivial⟩

/-- Where the stretch's tests of work pass, so does the one that the maps ask. -/
theorem seedMaps_pass (d₁ d₂ : RDT) (c : Nat) (τ : Tr (uLT (ckP .two) [d₁, d₂]))
    (h : passT (ckP .two) [d₁, d₂] (rhoT (ckP .two) [d₁, d₂] τ) = true) :
    (seedMaps d₁ d₂ c).pass τ = true := by
  obtain ⟨m, c1, m2, c2, ⟨⟩⟩ := τ
  have h' : (GChal.pass (b := d₁.entry.work) c1 &&
      (GChal.pass (b := d₂.entry.work) c2 && true)) = true := h
  show (GChal.pass (b := d₁.entry.work) c1 && true) = true
  rw [(Bool.and_eq_true_iff.1 h').1]
  rfl

/-- What the verifier is shown of one written round. -/
def shownAt (d : RDT) (m : (wT d).Msg) (c : (wT d).Chal) : Fmt.RoundView :=
  ⟨PQ.PlainOf.gots d.items (GPlain.old (b := d.entry.work) m.2),
    (ckP .two).dr d.entry d.kind (GChal.old (b := d.entry.work) c)⟩

/-- What is shown of a stretch of two written rounds. -/
theorem rvT_two (d₁ d₂ : RDT) (m₁ : (wT d₁).Msg) (c₁ : (wT d₁).Chal) (m₂ : (wT d₂).Msg)
    (c₂ : (wT d₂).Chal) :
    rvT (ckP .two) [d₁, d₂] (m₁, c₁, m₂, c₂, ()) = [shownAt d₁ m₁ c₁, shownAt d₂ m₂ c₂] := rfl

variable {S Cl W : Type} {C : CK} {F : Frame}

/-- **A bridge**: let the stretch's written rounds read as one typed round r; let the statement in
front and the prover's message of that round fix a set of lost values of its challenge, no more
than c; let a yes at a value that is not lost keep the promise and carry a witness back. Then the
piece has GoodIn at its written errors. -/
theorem goodIn_of_count_msg (p : Piece C F S Cl W) (on on' : S × F.E.Str → Prop)
    (R R' : S × F.E.Str → W → Prop) (r : Round) (c : Nat)
    (G : S × F.E.Str → CarryS (uLT C p.ds) [r])
    (fits : ∀ a, (G a).Fits ((c, ()) : Nat × Unit) p.err)
    (Lost : S × F.E.Str → r.Msg → r.Chal → Prop) (hcount : ∀ a m, on a → cnt (Lost a m) ≤ c)
    (hinv : ∀ a τ b, on a → p.ior.red.out a τ = some b →
      ∃ τ', (G a).tr τ = some τ' ∧
        (¬ Lost a τ'.1 τ'.2.1 → on' b ∧ ∀ w, R' b w → R a (p.ext a τ w))) :
    p.GoodIn on on' R R' := by
  intro a ha
  refine CarryS.doomed (G a) _ _ (fits a) _ (fun τ' => ¬ Lost a τ'.1 τ'.2.1) ?_ ?_ ?_
  · intro τ hτ b hb
    obtain ⟨τ', h1, _⟩ := hinv a τ b ha hb
    rw [hτ] at h1
    cases h1
  · intro τ τ' hτ hbad b hb
    obtain ⟨τ'', h1, h2⟩ := hinv a τ b ha hb
    rw [hτ] at h1
    cases h1
    exact h2 hbad
  · exact fun m => le_trans (cnt_mono fun z hz => not_not.1 hz) (hcount a m ha)

end VerifiableInference.Desc.K1
