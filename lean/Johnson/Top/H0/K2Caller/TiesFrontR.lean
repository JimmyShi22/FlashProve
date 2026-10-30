-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Caller/TiesFrontR.lean: the code switch: THE FOURTH TIE TO THE TABLE OF
JOINTS, WITH THE TABLE's PROMISE AND A CONDITION Rch BESIDE IT IN HAND: the form of the fourth
clause of TiedAtR (Johnson/Desc/Sound/ChainOfPromisesR.lean, which is not imported: Rch is
a letter here as there).
  t4R_front    from the law's relation in front, at a witness w with Laid a w (a letter: meant: «w
               is what the sub-protocol's extractor lays at a»), to every item that the switch's row
               closes: carry m, pinKept m, «no mark»: from fC and fP, EACH OF WHICH MAY SPEND the
               table's promise at the border, Rch k a and «no mark». General in the type A of what
               the chain carries and its reading get
AGAINST TiesFront.lean's t4_front (which stands): fC and fP take the promise and Rch; the law's «on»
is asked no more; A and get are letters.
LIMITS. A rule over letters: nothing is paid here. No soundness is claimed.
-/
import Johnson.Top.H0.K2Caller.TiesFront

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Caller
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (ModelPart Item Meaning Numbers)

variable {A P W : Type} {F : Frame} (N : Numbers) (Mg : Meaning P W) (links : List ModelPart)
  (ps : List Place) (get : A → P × First.S) (Rch : ℕ → A × F.E.Str → Prop) (k m : ℕ)

/-- **The fourth tie, with the promise and Rch in hand.** -/
theorem t4R_front (hins : (rowQ links ps k).ins = [.carry m, .pinKept m])
    (hctx : (rowQ links ps k).ctx = []) (R Laid : A × F.E.Str → W → Prop)
    (fC : ∀ a w, onQ N Mg links ps get k a → Rch k a → ¬ (get a.1).2.failed ≠ none → R a w →
      Mg.carry m (get a.1) (strsOf F a.2) w)
    (fP : ∀ a w, onQ N Mg links ps get k a → Rch k a → ¬ (get a.1).2.failed ≠ none → R a w →
      Laid a w → ∀ x ∈ N.keptOf m, Mg.pin x.1 x.2 (get a.1) (strsOf F a.2) w)
    (a : A × F.E.Str) (w : W) (ha : onQ N Mg links ps get k a) (hr : Rch k a)
    (hm : ¬ (get a.1).2.failed ≠ none) (hR : R a w) (hL : Laid a w) :
    relAt (meansQ N Mg get) (insQ links ps k) a w := by
  intro i hi
  rcases ins_cases links ps k m hins hctx i hi with rfl | rfl | rfl
  · exact fC a w ha hr hm hR
  · exact fP a w ha hr hm hR hL
  · exact not_not.1 hm

end VerifiableInference.Desc.First.K2Caller

#print axioms VerifiableInference.Desc.First.K2Caller.t4R_front
