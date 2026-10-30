-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/PlanLeft.lean: THE SMALLNESS TEST: FIVE OF THE EIGHT FACTS ON THE PLAN AND
THE LEDGER THAT `K8Left` ASKS (Johnson/Desc/ProofFile/Honest/K8/RestJoin.lean), AS ONE NAMED
SENTENCE ON THE TEST's DATA, `PlanLeft`: the data's blocks are the loop's at the data's number of
combinations · not none · at most two · the array of the bits is not the array of the digits · no
matrix's array is the array of the digits. IT HOLDS OF WHATEVER THE VERIFIER's OWN MAKER RETURNS;
THE THREE LATER ROUTINES BY WHICH THE PLANS LAY THE DATA KEEP IT (that the plans lay them by no
other is a reading of the three plans, not a lemma); IT IS BLIND TO THE FOURTEEN FIELDS THAT THE
RUNS WRITE. And two facts more, at the ledger that the plan lays: the digits' array has its two last
virtual rows. Lemmas on the verifier's own text; none of the library's goals.

  `PlanLeft tl`   the five
  **`planLeft_shape`**   tl0.shapeF m txOf f hasU tau = .ok tl → PlanLeft tl: by `shape_blocks`
                   (Johnson/Desc/K8/Honest/BlocksPlanned.lean) and the library's `Fo.shapeF_ix`
                   (OnBytes/Tie/Pv/Lookup/Ends/FoShapeF.lean)
  **`planLeft_addTrees`**   tl.addTreesF F T nU aTX hb hbLine = .ok (tl', G, T') → PlanLeft tl →
                   PlanLeft tl' ∧ HasRow G tl'.ix.ZZ tl'.zzRowReads ∧ HasRow G tl'.ix.ZZ
                   tl'.zzRowTies: by the library's `Fo.addTreesF_rows`, `Fo.addTreesF_core`
  `planLeft_ownerIs`, `planLeft_borderMeans`   the two routines on the owners' records keep it
  **`planLeft_blank`**, `planLeft_of_blank`   PlanLeft (blank u t) ↔ PlanLeft t; so it passes
                   between two data that agree but for the fourteen fields (the library's `blank`,
                   Johnson/Desc/First/TailClaims/EquationsBlank.lean)
  `planLeft_lsTail`   the laying of the kept slots leaves it
Limits. THAT A STATE's DATA AGREE, BUT FOR THE FOURTEEN FIELDS, WITH A PLAN's, AND THAT THE PLAN IS
MADE BY THESE ROUTINES, IS NOT SHOWN HERE. THE TWO ROWS ARE HAD AT THE PLAN's OWN LEDGER: that the
ledger at which the tests are called still has them is not said. Of the eight facts the three others
(the window ends inside the ledger's coefficients; the two rows at that ledger) stay.
Nothing is claimed on completeness, soundness or hiding.

-/
import Johnson.Desc.K8.Honest.BlocksPlanned
import OnBytes.Tie.Pv.Lookup.Ends.FoShapeF
import OnBytes.Tie.Pv.Lookup.Ends.FoAddTrees
import OnBytes.Tie.Pv.Lookup.Ends.FoTailCore
import Johnson.Desc.First.TailClaims.EquationsBlank

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open Fo (HasRow)
open VerifiableInference.Desc.First.TailClaims.Law (blank)

/-- Five facts on the test's data, on public numbers alone. -/
def PlanLeft (tl : HTailF2) : Prop :=
  t2BL tl.tau = .ok tl.blocks ∧ tl.blocks.size ≠ 0 ∧ tl.blocks.size ≤ 2 ∧
    tl.ix.BZ ≠ tl.ix.ZZ ∧ ∀ mu, mu < tl.NM → tl.gtTree.getD mu 0 ≠ tl.ix.ZZ

/-- **At what the maker returns.** -/
theorem planLeft_shape {tl0 tl : HTailF2} {m : Array TMat} {txOf : Array (Option Nat)}
    {f : Array T2Foreign} {hasU : Array Bool} {tau : Nat}
    (h : tl0.shapeF m txOf f hasU tau = .ok tl) : PlanLeft tl := by
  obtain ⟨b0, b1, b2⟩ := shape_blocks h
  obtain ⟨-, hB, hm⟩ := Fo.shapeF_ix h
  refine ⟨b0, b1, b2, by omega, fun mu hmu => ?_⟩
  rcases hm mu hmu with h1 | h1 <;> omega

/-- **The routine that lays the arrays keeps it, and lays the two rows.** -/
theorem planLeft_addTrees {tl tl' : HTailF2} {F G : Fork} {T T' : Tail2} {nU aTX : Array Nat}
    {hb hbLine : Nat} (h : tl.addTreesF F T nU aTX hb hbLine = .ok (tl', G, T'))
    (hP : PlanLeft tl) :
    PlanLeft tl' ∧ HasRow G tl'.ix.ZZ tl'.zzRowReads ∧ HasRow G tl'.ix.ZZ tl'.zzRowTies := by
  obtain ⟨⟨e1, e2, -, -, e5, e6⟩, hR, -, -⟩ := Fo.addTreesF_rows h
  obtain ⟨-, -, e7⟩ := Fo.addTreesF_core h
  obtain ⟨b0, b1, b2, hB, hm⟩ := hP
  have ez : tl'.zzBlocks = tl.zzBlocks := by
    unfold HTailF2.zzBlocks
    rw [e2]
  refine ⟨⟨by rw [e7, e2]; exact b0, by rw [e2]; exact b1, by rw [e2]; exact b2,
    by rw [e1]; exact hB, fun mu hmu => by rw [e5, e1]; exact hm mu (e6 ▸ hmu)⟩, ?_, ?_⟩
  · unfold HTailF2.zzRowReads
    rw [e1, ez]
    exact hR _ (by omega)
  · unfold HTailF2.zzRowTies
    rw [e1, ez]
    exact hR _ (by omega)

theorem planLeft_ownerIs (tl : HTailF2) (no : Nat) : PlanLeft (tl.ownerIs no) ↔ PlanLeft tl :=
  Iff.rfl

theorem planLeft_borderMeans {tl tl' : HTailF2} {iF ownerNo index : Nat}
    (e : tl.borderMeans iF ownerNo index = .ok tl') (hP : PlanLeft tl) : PlanLeft tl' := by
  unfold HTailF2.borderMeans at e
  split at e
  · cases e
  · split at e
    · cases e
    · cases e
      exact hP

/-- **It is blind to the fourteen fields that the runs write.** -/
theorem planLeft_blank (u t : HTailF2) : PlanLeft (blank u t) ↔ PlanLeft t := Iff.rfl

theorem planLeft_of_blank {u t t' : HTailF2} (h : blank u t = blank u t') (hP : PlanLeft t') :
    PlanLeft t :=
  (planLeft_blank u t).1 (h ▸ (planLeft_blank u t').2 hP)

theorem planLeft_lsTail (tl : HTailF2) (x : Array E) :
    PlanLeft { tl with lsTail := x } ↔ PlanLeft tl := Iff.rfl

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.planLeft_shape
#print axioms VerifiableInference.Desc.First.K8.Honest.planLeft_addTrees
#print axioms VerifiableInference.Desc.First.K8.Honest.planLeft_ownerIs
#print axioms VerifiableInference.Desc.First.K8.Honest.planLeft_borderMeans
#print axioms VerifiableInference.Desc.First.K8.Honest.planLeft_blank
#print axioms VerifiableInference.Desc.First.K8.Honest.planLeft_of_blank
#print axioms VerifiableInference.Desc.First.K8.Honest.planLeft_lsTail
