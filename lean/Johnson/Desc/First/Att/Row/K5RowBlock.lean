-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/Row/K5RowBlock.lean: kind K5's lot (H2K5.lotN,
Johnson/Desc/ProofFile/Lot/K5.lean), FORWARD: what the lot returns where the public data have the
twelve plans, and what a row of the written cut (PlanWritten.cutOf,
Johnson/Desc/Ok/PlanWritten/CutTest.lean) and the test on the plan read of one of its sub-protocols.
General laws: at every Z, every ground, every plan. NOTHING IS EVALUATED; NO WRITTEN VALUE IS NAMED.
Why. The earlier laws on k5AtN, on its test on the plan and on claimsOkAtO all go the other way:
from an opening, from a sub-protocol's accepted test, or from the head. For
"the proof file's IOP is made, with the written cut" they are wanted forward.

Main names (namespace H2K5.Row):
  nRounds own: the number of the kind's rounds, off the planner's eleven numbers.
    blockAt W l p before: k5AtN's value at a plan p. dress Z nm b: the lot's dress (the test on the
    plan with "and before can be made").
  k5AtN_some: W.A[g]? = some p → k5AtN W l g before = some (blockAt W l p before).
  blockAt_place | _rounds | _oracles | _told | _before | _planOk: the columns, as terms of l, p.own,
    before; the test on the plan as three conjuncts.
  planOk_own: the first conjunct reads own alone.
  **k5OwnN_at**: where the ground's attention segments are the twelve
    (2 g + 1, "A" ++ toString g, g) and the public data have a plan at each g below 12: the lot
    returns the twelve dressed sub-protocols, in order.
IS IT EMPTY HERE? Equations at letters: nothing to meet.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.ProofFile.Lot.K5
import Johnson.Desc.Ok.PlanWritten.CutTest

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K5.Row
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Place Claim)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Att.P
open VerifiableInference.PlanWritten (cutOf toldRounds)

/-- The number of the kind's rounds, off the planner's numbers. -/
def nRounds (own : Params.AttentionRounds) : ℕ := (entriesOf 0 (script own)).length

/-- The parameters of the kind's sub-protocol at segment l and plan p. -/
def parAt (W : Verify.Public) (l : ℕ) (p : Attention.Plan) (before : List (ℕ × ℕ)) : Par :=
  { link := l, piece := 3, work := (Params.settingOf W.P.frame).workOf .field .request, own := p.own, before := before }

/-- k5AtN's value at a plan. -/
def blockAt (W : Verify.Public) (l : ℕ) (p : Attention.Plan) (before : List (ℕ × ℕ)) : Block S Claim :=
  { attentionKind seatSO (runsN p) (parAt W l p before) with planOk := (attentionKind seatSO (runsN p) (parAt W l p before)).planOk && claimsOkAtO p }

/-- The lot's dress. -/
def dress (Z : ProofFile.Pub) (nm : String) (b : Block S Claim) : Block S Claim :=
  { b with planOk := b.planOk && (H2K5.k5Before? Z nm).isSome }

variable {W : Verify.Public} {l g : ℕ} {p : Attention.Plan} {before : List (ℕ × ℕ)}

/-- **Where the public data have the plan, the kind's sub-protocol is made.** -/
theorem k5AtN_some (hp : W.A[g]? = some p) : k5AtN W l g before = some (blockAt W l p before) := by
  unfold k5AtN
  rw [hp]
  rfl

theorem blockAt_place : (blockAt W l p before).place = ⟨1, some l, 3, .K5⟩ := rfl
theorem blockAt_before : (blockAt W l p before).before = before := rfl

theorem blockAt_rounds : (blockAt W l p before).rounds.length = nRounds p.own := by
  show (rounds (parAt W l p before)).length = _
  unfold rounds nRounds
  rw [List.length_map]
  rfl

theorem blockAt_oracles : (blockAt W l p before).oracles.length = nRounds p.own := by
  show ((rounds (parAt W l p before)).map fun _ => ([] : List VerifiableInference.Desc.Oracle)).length = _
  rw [List.length_map]
  exact blockAt_rounds

/-- Of a list of empty lists no member tells a tree. -/
theorem told_nil {α : Type} (L : List α) (k : ℕ) :
    (((L.map fun _ => ([] : List VerifiableInference.Desc.Oracle)).zipIdx k).filter fun x => !x.1.isEmpty) = [] := by
  induction L generalizing k with
  | nil => rfl
  | cons a L ih =>
    rw [List.map_cons, List.zipIdx_cons, List.filter_cons_of_neg (by simp)]
    exact ih (k + 1)

theorem blockAt_told : toldRounds (blockAt W l p before) = [] := by
  unfold toldRounds
  show ((((rounds (parAt W l p before)).map fun _ => ([] : List VerifiableInference.Desc.Oracle)).zipIdx.filter fun x => !x.1.isEmpty).map fun x => (x.2, x.1)) = []
  rw [told_nil]
  rfl

/-- The test on the plan: three conjuncts with the dress. -/
theorem blockAt_planOk : (blockAt W l p before).planOk = (planOk (parAt W l p before) && claimsOkAtO p) := rfl

theorem dress_planOk (Z : ProofFile.Pub) (nm : String) (b : Block S Claim) :
    (dress Z nm b).planOk = (b.planOk && (H2K5.k5Before? Z nm).isSome) := rfl

/-- The first conjunct, off own alone. -/
def planOkOwn (own : Params.AttentionRounds) : Bool :=
  planOk { link := 0, piece := 0, work := 0, own := own, before := [] }

theorem planOk_own : planOk (parAt W l p before) = planOkOwn p.own := rfl

/-- Where every member is sent to a value, filterMap is map. -/
theorem filterMap_all_some {α β : Type} (L : List α) (f : α → Option β) (h : α → β) (H : ∀ a ∈ L, f a = some (h a)) :
    L.filterMap f = L.map h := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    rw [List.filterMap_cons, H a List.mem_cons_self, List.map_cons, ih fun b hb => H b (List.mem_cons_of_mem _ hb)]

/-- **THE LOT RETURNS ITS TWELVE.** -/
theorem k5OwnN_at (Z : ProofFile.Pub) (G : ProofFile.Ground) (P : ℕ → Attention.Plan)
    (hB : H2K5.k5Places G = (List.range 12).map fun g => (2 * g + 1, "A" ++ toString g, g))
    (hA : ∀ g, g < 12 → G.W.A[g]? = some (P g)) :
    H2K5.k5OwnN Z G = (List.range 12).map fun g =>
      dress Z ("A" ++ toString g) (blockAt G.W (2 * g + 1) (P g) ((H2K5.k5Before? Z ("A" ++ toString g)).getD [])) := by
  unfold H2K5.k5OwnN
  rw [hB, List.filterMap_map]
  refine filterMap_all_some _ _ _ fun g hg => ?_
  show (k5AtN G.W (2 * g + 1) g ((H2K5.k5Before? Z ("A" ++ toString g)).getD [])).map _ = _
  rw [k5AtN_some (hA g (List.mem_range.1 hg))]
  rfl

end H2K5.Row

#print axioms H2K5.Row.k5AtN_some
#print axioms H2K5.Row.blockAt_rounds
#print axioms H2K5.Row.blockAt_oracles
#print axioms H2K5.Row.blockAt_told
#print axioms H2K5.Row.k5OwnN_at
#print axioms H2K5.Row.blockAt_place
#print axioms H2K5.Row.blockAt_before
#print axioms H2K5.Row.told_nil
#print axioms H2K5.Row.blockAt_planOk
#print axioms H2K5.Row.dress_planOk
#print axioms H2K5.Row.planOk_own
#print axioms H2K5.Row.filterMap_all_some
