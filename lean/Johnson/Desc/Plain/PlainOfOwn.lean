-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Plain/PlainOfOwn.lean: FROM A KIND's LAW FOR THE ITEMS THAT ITS BLOCK CLOSES, AND THE
RIDING OF THE REST, TO THE PLAIN LAW OVER ALL OPEN ITEMS, AT ANY LIST OF ERRORS. A tool: no kind, no
table and no protocol is named.

The matter. A table of joints says which items are open at a border (Op in front; behind: those of
Op that the block's row does not name, and those that it opens). A ledger of plain laws asks of each
block, at the kind's OWN errors ε (not the piece's): "the promise behind; and for every witness w:
all that is open behind holds at w → all that is open in front holds at E a w". A kind's files have
its law in the form of the rule of composition (Piece.GoodIn) between what its row names in front
(In: closed or read) and behind (Out: opened or read).

  leads_of_own_frames   the kind's law, at the piece with the extractor E and the errors ε laid in
                        (the reduction is the same: it reads neither), and the riders' riding FOR
                        CERTAIN give the plain law over all open items at ε.
  leads_of_sure_items   the case without chance: all items, for certain.
What is not claimed. Rules: as empty as their premises. Nothing on soundness.

-/
import Johnson.Desc.Plain.Leads
import Johnson.Desc.Sound.GoodIn

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Plain
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK)
open _root_.Iop (Reduction Err Doomed)
open VerifiableInference.Desc.Sound

variable {S Cl W ι : Type} {C : CK} {F : Frame}

/-- **The law for what the row names, and the riding of the rest, give the plain law over all open
items.** mA i a w, mB i b w: item i holds in front, behind. -/
theorem leads_of_own_frames (x : Piece C F S Cl W) (ε : Err (uLT C x.ds))
    (E : S × F.E.Str → W → W) (on on' : S × F.E.Str → Prop)
    (mA mB : ι → S × F.E.Str → W → Prop) (Op In Out : ι → Prop)
    (own : ({ x with ext := fun a _ w => E a w, err := ε } : Piece C F S Cl W).GoodIn on on'
      (fun a w => ∀ i, In i → mA i a w) (fun b w => ∀ i, Out i → mB i b w))
    (frames : ∀ a τ b w i, on a → x.ior.red.out a τ = some b → on' b → Op i → ¬ In i →
      mB i b w → mA i a (E a w)) :
    x.ior.red.Leads on
      (fun a b => on' b ∧ ∀ w, (∀ i, (Op i ∧ ¬ In i) ∨ Out i → mB i b w) →
        ∀ i, Op i → mA i a (E a w)) ε := by
  intro a ha
  refine Doomed.mono _ _ (fun τ hτ b hb => ?_) (own a ha)
  obtain ⟨hon, hw⟩ := hτ b hb
  refine ⟨hon, fun w h i hi => ?_⟩
  by_cases hI : In i
  · exact hw w (fun j hj => h j (Or.inr hj)) i hI
  · exact frames a τ b w i ha hb hon hi hI (h i (Or.inl ⟨hi, hI⟩))

/-- The case without chance. -/
theorem leads_of_sure_items (x : Piece C F S Cl W) (ε : Err (uLT C x.ds))
    (E : S × F.E.Str → W → W) (on on' : S × F.E.Str → Prop)
    (mA mB : ι → S × F.E.Str → W → Prop) (Op Op' : ι → Prop)
    (h : ∀ a τ b, on a → x.ior.red.out a τ = some b →
      on' b ∧ ∀ w, (∀ i, Op' i → mB i b w) → ∀ i, Op i → mA i a (E a w)) :
    x.ior.red.Leads on
      (fun a b => on' b ∧ ∀ w, (∀ i, Op' i → mB i b w) → ∀ i, Op i → mA i a (E a w)) ε :=
  Reduction.Leads.of_sure (K := x.ior.red) ε h

end VerifiableInference.Desc.Plain
