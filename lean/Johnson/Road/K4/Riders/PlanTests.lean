-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/Riders/PlanTests.lean: THREE FIELDS OF `K4RowPlan` (K4RowOfMeans.lean) AS TESTS WITH
CODE OVER ALL OF K4's PLACES AT ONCE, each with the lemma that draws the field out at one place; and
one field as a lemma. Definitions, statements and proofs.

  `k4OnlyFit` / `only_of_fit`: of the items callerIn m' at feed-forward segments, the one of K4's
    own segment alone is open in front of K4's sub-protocol.
  `k4ObjFit` / `objOpen_of_fit`: the lookup's own claims (formsT m 2 "objects") are open there.
  `k4OpenAllFit` / `openAll_of_fit`: the six public items under which the verifier's state reads as
    the public parameters say (Rec/Whole.lean: `openAllB`) are open there.
  `placeAt_link`: the parameters of segment m's lookup bear the segment's number m (the lookups'
    `lookAt_link`).

Limits. Tests: evaluated in Riders/PlanFull.lean, at the full size's lists alone. K04_law, the law
of K4's sub-protocol itself, IS NOT PROVED. Nothing on soundness.
-/
import Johnson.Road.K4.Riders.KeepsOfMeans
import Johnson.Road.K4.Rec.Whole
import Johnson.Desc.First.Look.K3CallsAddress

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.Riders

open OnBytes OnBytes.Model
open OnBytes.Road.K4.Rec (openAllB)
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.First (ModelPart Item Pub More start openSets pubSets)
open VerifiableInference.Desc.First.FillK4 (isLay isK4At)
open VerifiableInference.Desc.First.Look (placeAt lookAt)

variable {links : List ModelPart} {ps : List Place} {k m : ℕ} {pl : Place}

/-- At every place of K4's a test on the border's number and the segment's. -/
def atK4s (links : List ModelPart) (ps : List Place) (t : ℕ → ℕ → Bool) : Bool :=
  (List.range ps.length).all fun k =>
    match ps[k]? with
    | none => true
    | some pl => !isK4At links pl || t k (pl.link.getD 0)

theorem atK4s_at {t : ℕ → ℕ → Bool} (H : AtK4 links ps k m pl) (h : atK4s links ps t = true) :
    t k m = true := by
  have hk : k < ps.length := (List.getElem?_eq_some_iff.mp H.here).1
  have h2 := List.all_eq_true.1 h k (List.mem_range.2 hk)
  rw [H.here] at h2
  simpa [isK4At_of H, H.link] using h2

def k4OnlyFit (M : More) (links : List ModelPart) (ps : List Place) : Bool :=
  atK4s links ps fun k m => ((pubSets M links ps)[k]?.getD []).all fun x =>
    match x with
    | .callerIn m' => !isLay links m' || m' == m
    | _ => true

theorem only_of_fit {M : More} (H : AtK4 links ps k m pl) (h : k4OnlyFit M links ps = true) :
    ∀ m', isLay links m' = true → Pub.callerIn m' ∈ (pubSets M links ps)[k]?.getD [] → m' = m := by
  intro m' hl hm
  have h1 := List.all_eq_true.1 (atK4s_at H h) _ hm
  simpa [hl] using h1

def k4ObjFit (links : List ModelPart) (ps : List Place) : Bool :=
  atK4s links ps fun k m =>
    decide (Item.formsT m 2 "objects" ∈ (openSets links ps (start links))[k]?.getD [])

theorem objOpen_of_fit (H : AtK4 links ps k m pl) (h : k4ObjFit links ps = true) :
    Item.formsT m 2 "objects" ∈ (openSets links ps (start links))[k]?.getD [] :=
  of_decide_eq_true (atK4s_at H h)

def k4OpenAllFit (M : More) (links : List ModelPart) (ps : List Place) : Bool :=
  atK4s links ps fun k m => openAllB M links ps k m

theorem openAll_of_fit {M : More} (H : AtK4 links ps k m pl)
    (h : k4OpenAllFit M links ps = true) : openAllB M links ps k m = true :=
  atK4s_at H h

/-- The parameters of segment i's lookup bear the segment's number. -/
theorem placeAt_link {X : Verify.Public} {i : ℕ} {dg : Bool}
    {p : VerifiableInference.Desc.First.Look.P} (h : placeAt X i dg = some p) : p.link = i := by
  unfold placeAt at h
  obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.1 h
  exact VerifiableInference.OnPublicFiles.lookAt_link hx

end OnBytes.Road.K4.Riders

#print axioms OnBytes.Road.K4.Riders.only_of_fit
#print axioms OnBytes.Road.K4.Riders.objOpen_of_fit
#print axioms OnBytes.Road.K4.Riders.openAll_of_fit
#print axioms OnBytes.Road.K4.Riders.placeAt_link
