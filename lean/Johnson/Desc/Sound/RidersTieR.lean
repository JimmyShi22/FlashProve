-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sound/RidersTieR.lean: the tie for what rides past a sub-protocol, in the leaner form
of Johnson/Desc/Sound/RidersTie.lean (`t5_of_test`), with one condition more on the statement in
front, and with both premises asked only where the tie itself is asked. One theorem. A rule over
letters.

Why. `t5_of_test` asks that the riding items' sentences bear the extractor's value at every two
statements. A sentence that finds a seat through the book of trees in the verifier's state bears it
only inside the promise, at a state that the IOP's own fold has reached. So here the premise on an
accept (`hyes`) and the premise on the witness (`hX`) both stand under: the promise in front · Rch,
a letter for "reached" · no mark · an accept of the piece from a to b · the promise behind. The
conclusion has Rch as one premise more, behind the promise in front.

Limits. Those of RidersTie.lean. Rch is a letter: at Rch := fun _ => True this is a form of
`t5_of_test` with a weaker premise on the witness; at Rch := fun _ => False it says nothing. No
soundness of any verifier follows from this file.

Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.Sound.RidersTie

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open VerifiableInference.Desc.First (ModelPart Item Meaning Numbers start)

variable {P W Cl : Type} {C : CK} {Fr : Frame}

/-- **The leaner form, inside the promise and at a reached state.** -/
theorem t5R_of_test (N : Numbers) (Mg : Meaning P W) (links : List ModelPart) (ps : List Place) (k : ℕ)
    (z : P) (rel : P × First.S → Strs → P × First.S → Strs → Prop) (p : Piece C Fr First.S Cl W)
    (X : First.S × Fr.E.Str → First.S × Fr.E.Str → W → W) (Rch : First.S × Fr.E.Str → Prop)
    (ok : Item → Bool) (hB : (ridersL links ps k).all ok = true)
    (hG : ∀ i, ok i = true → GoesBack rel (i.holds N Mg))
    (hyes : ∀ a τ b, onQ N Mg links ps (fun s => (z, s)) k a → Rch a → ¬ a.1.failed ≠ none →
      p.ior.red.out a τ = some b → onQ N Mg links ps (fun s => (z, s)) (k + 1) b →
      rel (z, a.1) (strsOf Fr a.2) (z, b.1) (strsOf Fr b.2))
    (hX : ∀ i, openAfter (insQ links ps) (outsQ links ps) (· ∈ start links) k i →
      ¬ insQ links ps k i → ∀ a τ b w, onQ N Mg links ps (fun s => (z, s)) k a → Rch a →
      ¬ a.1.failed ≠ none → p.ior.red.out a τ = some b →
      onQ N Mg links ps (fun s => (z, s)) (k + 1) b →
      meansQ N Mg (fun s => (z, s)) i a w → meansQ N Mg (fun s => (z, s)) i a (X a b w)) :
    ∀ a τ b w i, onQ N Mg links ps (fun s => (z, s)) k a → Rch a → ¬ a.1.failed ≠ none →
      p.ior.red.out a τ = some b → onQ N Mg links ps (fun s => (z, s)) (k + 1) b →
      relQ N Mg links ps (fun s => (z, s)) (k + 1) b w →
      openAfter (insQ links ps) (outsQ links ps) (· ∈ start links) k i → ¬ insQ links ps k i →
      meansQ N Mg (fun s => (z, s)) i a (X a b w) := by
  intro a τ b w i ha hR hm hb hb' hrel ho hn
  have h1 : meansQ N Mg (fun s => (z, s)) i b w := hrel i (Or.inl ⟨ho, hn⟩)
  exact hX i ho hn a τ b w ha hR hm hb hb'
    (hG i (List.all_eq_true.1 hB i (rider_mem links ps k i ho hn)) _ _ _ _ w
      (hyes a τ b ha hR hm hb hb') h1)

end VerifiableInference.Desc.Sound
