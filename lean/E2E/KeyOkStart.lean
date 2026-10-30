-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/KeyOkStart.lean: a tied input of the offline prover passes the description's test on the instance.

Why. The test on the instance is the first clause of what a run owes (`AtRunS`). `okStart_named` (E2E/KeyPasses.lean) has it
at the written key of every sample, and the relation in `Tied` says that a tied instance is such a key.

Main names. `okStart_of_tied`. `relation_of_tied`: the sentence that the first and last threads' letters are to hold.

Nothing of the prover is read but through `Tied`'s relation. No law over coins.

Nothing on soundness, completeness, hiding or binding.

-/
import E2E.OfflineAtParts
import E2E.KeyPasses

set_option autoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtPublicFiles.AtFiles
open AtPublicFiles.KeyFile (KeyParts)
open VerifiableInference.Desc.Key (Source LaterPlaces)
open VerifierAndGoals (PublicFiles InScope)
open AtPublicFiles.Committed (pads_nonempty PadZ AZ holdZ)

local instance (priority := high) instNonemptyPadZKeyOkStart : Nonempty PadZ := pads_nonempty OnBytes.Slice.frS 402653181

/-- **A tied input passes the test on the instance.** -/
theorem okStart_of_tied {Z : PublicFiles} {X : Source} {N : H2U.PlaceNums} {P : LaterPlaces}
    {Q₂ Q₃ X₀ Xh Wk : Type} [Inhabited Q₃] {val₂ : Q₂ → ByteArray} {val₃ : Q₃ → ByteArray}
    {K : KeyParts FullSizeMatrix ((Cz Z).Pad × (Cz Z).Rnd) X₀ Xh Wk} {ok : FullSizeMatrix → Prop}
    {w : FullSizeMatrix × ((Cz Z).Pad × (Cz Z).Rnd) × (Cz Z).Seed} {x : KeyInst}
    (hn : KeyNamed Z X N P) (scope : InScope Z = true)
    (ht : TiedOffline Z X N P val₂ val₃ K ok w x) : (keyFileDescription X N P).okStart x = true := by
  obtain ⟨s, e, -⟩ := (relKey_iff (AZ Z) PadZ (holdZ Z) ok w.1 w.2.1 x).1 ht.rel
  rw [e]
  exact okStart_named hn scope _

/-- **The first and the last thread's sentence on an input**, at their letters `Rel` and `Vd`: it holds at a tied input. Lay
`Rel := relKeyZ Z ok` and `Vd := fun v => relKeyZ Z ok v.w₀ v.rc v.x`. The shared thread needs no sentence: `Vd := fun _ => True`
serves there. -/
theorem relation_of_tied {Z : PublicFiles} {X : Source} {N : H2U.PlaceNums} {P : LaterPlaces}
    {Q₂ Q₃ X₀ Xh Wk : Type} [Inhabited Q₃] {val₂ : Q₂ → ByteArray} {val₃ : Q₃ → ByteArray}
    {K : KeyParts FullSizeMatrix ((Cz Z).Pad × (Cz Z).Rnd) X₀ Xh Wk} {ok : FullSizeMatrix → Prop}
    {w : FullSizeMatrix × ((Cz Z).Pad × (Cz Z).Rnd) × (Cz Z).Seed} {x : KeyInst}
    (ht : TiedOffline Z X N P val₂ val₃ K ok w x) : relKeyZ Z ok w.1 w.2.1 x :=
  ht.rel

end AtPublicFiles.AtFiles

#print axioms AtPublicFiles.AtFiles.okStart_of_tied
#print axioms AtPublicFiles.AtFiles.relation_of_tied
