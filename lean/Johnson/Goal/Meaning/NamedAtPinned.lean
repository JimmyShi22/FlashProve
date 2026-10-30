-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Meaning/NamedAtPinned.lean: IN THE GOALS' SCOPE, AT THE SECOND HASH FUNCTION: WHERE THE
PINNED TEST madePinnedAt (Johnson/Desc/Ok/PlanWritten/MadeTestLaws.lean) ACCEPTS AT THE PUBLIC PART
OF WHICH THE IOP AS WRITTEN IN LEAN FOR THE PROOF FILE IS MADE, THE TEST namedThere
(Johnson/Goal/Meaning/LaidCovered.lean) ACCEPTS THERE. Theorems, proved.

  pins_of_pinned   in scope (at every o) the pinned test's accepting gives the two equations:
    xShapeOf Z.p.X = xShapeFull and Z.first.layout = layoutFull: by key_in_scope_pure
    (Johnson/Goal/Numbers/KeyInScope.lean: in scope the key is the full size's) and made_of_pinned.
    (The same two equations stand as xShape_in_scope and layout_in_scope in
    Johnson/Goal/Numbers/MadeInScope.lean, whose imports are heavier; drawn here in three
    lines, so that this file stays light.)
  namedAt_of_pinned   so namedAt Z = true (named_of_pins, Johnson/Goal/Meaning/NamedViewFull.lean:
    the closed fact, by the kernel): at every o.
  namedThere_of_pinned   at the second hash function: namedThere: named_of_B under fullShaped_scope
    (Johnson/Goal/Meaning/NamedAskLaw.lean).

OBJECT: namedThere at Z.p.X, sizesOf Z.p.X and Z.first.layout. LETTERS:
W, pp, Z: free.

What is not claimed. That madePinnedAt accepts at any files. namedThere at another hash than the
older one. No soundness.
-/
import Johnson.Goal.Meaning.NamedViewFull
import Johnson.Goal.Meaning.NamedAskLaw
import Johnson.Desc.Ok.PlanWritten.MadeTestLaws
import Johnson.Goal.Numbers.KeyInScope
import Johnson.Desc.ProofFile.Law.MakerPublic
import Johnson.Desc.Ok.PlanWritten.PublicAtLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace Meaning.NamedAsk

open VerifiableInference.PlanWritten (madePinnedAt made_of_pinned key_in_scope_pure xShapeOf
  publicOfO_older)
open Johnson.G (xShapeFull layoutFull)

/-- In scope the pinned test's accepting gives the two equations. -/
theorem pins_of_pinned {o : ProofFile.SecondHashFunctionArgument} {W : VerifierAndGoals.PublicFiles} {Z : ProofFile.Pub}
    (hW : VerifierAndGoals.InScope W = true) (h : ProofFile.pureRoad.pub o W.pol W.lay W.KL = .ok Z)
    (hy : madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true) :
    xShapeOf Z.p.X = xShapeFull ∧ Z.first.layout = layoutFull := by
  unfold madePinnedAt at hy
  rw [key_in_scope_pure hW h] at hy
  exact ⟨(made_of_pinned hy).2.2.2, (made_of_pinned hy).2.1.2.2.2.2.2⟩

/-- **namedAt FROM THE PINNED TEST, IN SCOPE**: at every o. -/
theorem namedAt_of_pinned {o : ProofFile.SecondHashFunctionArgument} {W : VerifierAndGoals.PublicFiles} {Z : ProofFile.Pub}
    (hW : VerifierAndGoals.InScope W = true) (h : ProofFile.pureRoad.pub o W.pol W.lay W.KL = .ok Z)
    (hy : madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true) : namedAt Z = true :=
  named_of_pins (pins_of_pinned hW h hy).1 (pins_of_pinned hW h hy).2

/-- **namedThere FROM THE PINNED TEST, IN SCOPE, AT THE SECOND HASH FUNCTION.** -/
theorem namedThere_of_pinned {W : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {Z : ProofFile.Pub}
    (hW : VerifierAndGoals.InScope W = true) (hR : VerifierAndGoals.readFiles W = .ok pp)
    (h : ProofFile.pureRoad.pub OnBytes.secondHashFunction W.pol W.lay W.KL = .ok Z)
    (hy : madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true) :
    Meaning.namedThere Z.p.X (Meaning.sizesOf Z.p.X) Z.first.layout = true :=
  named_of_B
    (fullShaped_scope hW hR ((publicOfO_older W.pol W.KL (some W.lay)).symm.trans
      (ProofFile.Law.pub_public h)))
    (namedAt_of_pinned hW h hy)

end Meaning.NamedAsk

#print axioms Meaning.NamedAsk.pins_of_pinned
#print axioms Meaning.NamedAsk.namedAt_of_pinned
#print axioms Meaning.NamedAsk.namedThere_of_pinned
