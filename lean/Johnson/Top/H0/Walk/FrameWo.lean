-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Walk/FrameWo.lean: the premise PileGivesWo of the frame's tie at "cleared"
(FrameTied.lean), paid at every filling of the table's letters "pile" and "wo" of one make: "pile"
gives that every pending row in the verifier's state holds (asked only where the chain stands
between two links), "wo m" asks that the row which the frame's reader rowAt gives at the state
holds, both in one sense Hold, which may read the statement and goes back over the step. HERE THE
FLAG "a row is left" IS SPENT: only where it says yes is the row laid on the pile.

  rowAt_of_left     the row by the link's own reader "left" is the row by rowAt, where "left" is one
                    of the readers that leftOf gathers
  pileGivesWo_of

Limits. Hold, and the three facts on the filling, are letters and premises. No soundness statement.

-/
import Johnson.Top.H0.Walk.FrameTied

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Desc.First.Walk.Tied
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First (S Meaning)

theorem rowAt_of_left {left : S → Option WsForkOut} {lay : WsLay} {n : Nat} {lin : Params.LinShape}
    {s : S} {r : TensorRow} (hl : ∀ w, left s = some w → Law.leftOf s = some w)
    (h : Law.rowBy left lay n lin s = some r) : Law.rowAt lay n lin s = some r := by
  obtain ⟨w, os, h1, h2⟩ := Law.rowBy_some.1 h
  exact Law.rowBy_some.2 ⟨w, os, hl w h1, h2⟩

/-- **The pile behind gives "wo" in front.** -/
theorem pileGivesWo_of {P W : Type} (Mg : Meaning P W) (m : Nat) (f : S → Except String S)
    (X : LinkPub) (left : S → Option WsForkOut) (lay : WsLay) (lin : Params.LinShape) (base : Nat)
    (In : P × S → VerifiableInference.Desc.Strs → Prop) (Hold : P × S → W → TensorRow → Prop)
    (hf : ∀ s t, f s = .ok t → ClearedRec X left lay lin s t) (hv : X.fv = true)
    (hl : ∀ s w, left s = some w → Law.leftOf s = some w)
    (hwo : ∀ a y w, (∀ r, Law.rowAt lay X.NCL lin a.2 = some r → Hold a w r) → Mg.wo m a y w)
    (hpile : ∀ a y w, a.2.atBetween = true → Mg.pile a y w → ∀ r ∈ a.2.out.pending, Hold a w r)
    (hback : ∀ p s t y w r, f s = .ok t → In (p, s) y → Hold (p, t) w r → Hold (p, s) w r) :
    PileGivesWo Mg m (Yes f) base In := by
  intro p s t y y' w hr _ hI hp
  refine hwo (p, s) y w fun r hrow => ?_
  obtain ⟨r', h1, h2⟩ := (hf s t hr).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 hv
  have e : r = r' := Option.some.inj (hrow.symm.trans (rowAt_of_left (hl s) h1))
  subst e
  exact hback p s t y w r hr hI (hpile (p, t) y' w (hf s t hr).1 hp r (by rw [h2]; simp))

#print axioms pileGivesWo_of

end Johnson.Desc.First.Walk.Tied
