-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/Row/K5Row.lean: **KIND K5's ROW OF "THE FOURTEEN" BENEATH
"THE PROOF FILE's IOP IS MADE, WITH THE WRITTEN CUT": GENERAL IN ITS WRITTEN VALUES.** Where the
ground and the public part agree BY FIELD with a structure V of values (K5Vals), and one Bool on V
alone accepts: (i) the kind's lot (H2K5.lotN, Johnson/Desc/ProofFile/Lot/K5.lean) returns its twelve
sub-protocols · (ii) each has the columns of its row of the written cut
(Johnson/Desc/Ok/PlanWritten/CutLit.lean) but for the name and the place as the seat lays them ·
(iii) each one's test on the plan is true. NOTHING IS EVALUATED; NO WRITTEN VALUE IS NAMED: V IS A
LETTER.
Why so. What Lean's kernel is to walk must be tied to the public files' own plan by equations; which
values these are is other files' to show (the planner's run at the full size). So the row asks the
equations by field and the Bool at V.

Main names (namespace H2K5.Row):
  K5Vals: own · geo · fs · nW · mats at each group; the cuts' pairs (look, take); the roots in front
    of a round.
  K5Reads Z G P V: what the lot reads, as equations: the twelve places · the twelve plans P g · of
    each plan: own · the geometry · the lookup's shape · iU3 = 0 · nW · the planned array's columns
    are nW · the matrices' rows and columns · of Z: the cuts' pairs · the roots.
  k5RowB V: at each g below 12: the rounds' number is 162 · the test on own · claimsBy · "before"
    is [(1, 4 + 6 g)].
  the_block Z G P g: the lot's sub-protocol at group g.
  **k5_row (R : K5Reads Z G P V) (hV : k5RowB V = true)**: (i) ∧ (ii) ∧ (iii).
WHAT IS OWED BEHIND IT: every field of K5Reads at the full size's public files (places · iU3 ·
cols have payers in Johnson/Desc/First/Att/Row/K5RowSeat.lean, in scope or where publicOf returns;
the other eight: no payer there; but see hc_made, own_in_scope, under premises) · k5RowB V = true
AT THOSE VALUES: its conjunct claimsBy has, as it stands, been put to no kernel; for its twin, see
(Johnson/Desc/First/Att/Row/K5RowTwins.lean, its head; Johnson/Desc/First/Att/Row/K5DryTwin.lean).
IS IT EMPTY HERE? AN IMPLICATION. THAT K5Reads HOLDS AT ANY Z, OR k5RowB AT ANY V, IS NOT SHOWN.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.Row.K5RowBlock
import Johnson.Desc.First.Att.Row.K5RowTwins

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K5.Row
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Place Claim)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Att.P
open VerifiableInference.PlanWritten (toldRounds)

/-- The values that the row's Bool reads. -/
structure K5Vals where
  own : ℕ → Params.AttentionRounds
  geo : ℕ → Geo
  fs : ℕ → Forest.Shape
  nW : ℕ → ℕ
  mats : ℕ → Array (ℕ × ℕ)
  cuts : List (String × ℕ)
  rb : ℕ → ℕ

/-- **What the lot reads, as equations by field.** -/
structure K5Reads (Z : ProofFile.Pub) (G : ProofFile.Ground) (P : ℕ → Attention.Plan) (V : K5Vals) : Prop where
  places : H2K5.k5Places G = (List.range 12).map fun g => (2 * g + 1, "A" ++ toString g, g)
  plan : ∀ g, g < 12 → G.W.A[g]? = some (P g)
  own : ∀ g, g < 12 → (P g).own = V.own g
  geo : ∀ g, g < 12 → geoOf (P g).S = V.geo g
  fs : ∀ g, g < 12 → (P g).fs = V.fs g
  iU3 : ∀ g, g < 12 → (P g).iU3 = 0
  nW : ∀ g, g < 12 → (P g).nW = V.nW g
  cols : ∀ g, g < 12 → ((P g).seam.Fp.trees[(P g).iU3]?).map (·.K) = some (V.nW g)
  mats : ∀ g, g < 12 → ((P g).mats.map fun M => (M.m, M.k)) = V.mats g
  cuts : (Z.cuts.map fun c => (c.look, c.take)) = V.cuts
  roots : rootsOf Z = V.rb

/-- **The row's Bool, on the values alone.** -/
def k5RowB (V : K5Vals) : Bool :=
  (List.range 12).all fun g =>
    decide (nRounds (V.own g) = 162) && planOkOwn (V.own g) && claimsBy (V.geo g) 0 (V.nW g) (V.nW g) (V.mats g) (V.fs g) &&
      decide (beforeBy V.cuts V.rb ("A" ++ toString g) = some [(1, 4 + 6 * g)])

/-- What its accept says at a group. -/
theorem k5RowB_gives {V : K5Vals} (h : k5RowB V = true) {g : ℕ} (hg : g < 12) :
    nRounds (V.own g) = 162 ∧ planOkOwn (V.own g) = true ∧ claimsBy (V.geo g) 0 (V.nW g) (V.nW g) (V.mats g) (V.fs g) = true ∧
      beforeBy V.cuts V.rb ("A" ++ toString g) = some [(1, 4 + 6 * g)] := by
  unfold k5RowB at h
  have e := List.all_eq_true.1 h g (List.mem_range.2 hg)
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at e
  exact ⟨e.1.1.1, e.1.1.2, e.1.2, e.2⟩

/-- The lot's sub-protocol at group g. -/
def the_block (Z : ProofFile.Pub) (G : ProofFile.Ground) (P : ℕ → Attention.Plan) (g : ℕ) : Block S Claim :=
  dress Z ("A" ++ toString g) (blockAt G.W (2 * g + 1) (P g) ((H2K5.k5Before? Z ("A" ++ toString g)).getD []))

variable {Z : ProofFile.Pub} {G : ProofFile.Ground} {P : ℕ → Attention.Plan} {V : K5Vals}

/-- "before" at a group, under the equations and the Bool. -/
theorem before_at (R : K5Reads Z G P V) (hV : k5RowB V = true) {g : ℕ} (hg : g < 12) :
    H2K5.k5Before? Z ("A" ++ toString g) = some [(1, 4 + 6 * g)] := by
  rw [k5Before_by, R.cuts, R.roots]
  exact (k5RowB_gives hV hg).2.2.2

/-- The third conjunct at a group. -/
theorem claims_at (R : K5Reads Z G P V) (hV : k5RowB V = true) {g : ℕ} (hg : g < 12) : claimsOkAtO (P g) = true := by
  rw [claimsOkAtO_by, R.cols g hg, R.geo g hg, R.iU3 g hg, R.nW g hg, R.mats g hg, R.fs g hg]
  exact (k5RowB_gives hV hg).2.2.1

/-- **THE ROW.** -/
theorem k5_row (R : K5Reads Z G P V) (hV : k5RowB V = true) :
    H2K5.k5OwnN Z G = (List.range 12).map (the_block Z G P) ∧
      (∀ g, g < 12 →
        (the_block Z G P g).place = ⟨1, some (2 * g + 1), 3, .K5⟩ ∧ (the_block Z G P g).rounds.length = 162 ∧
          (the_block Z G P g).oracles.length = 162 ∧ toldRounds (the_block Z G P g) = [] ∧
          (the_block Z G P g).before = [(1, 4 + 6 * g)]) ∧
      ∀ g, g < 12 → (the_block Z G P g).planOk = true := by
  refine ⟨k5OwnN_at Z G P R.places R.plan, fun g hg => ⟨rfl, ?_, ?_, ?_, ?_⟩, fun g hg => ?_⟩
  · exact (blockAt_rounds (W := G.W) (l := 2 * g + 1) (p := P g)).trans ((congrArg nRounds (R.own g hg)).trans (k5RowB_gives hV hg).1)
  · exact (blockAt_oracles (W := G.W) (l := 2 * g + 1) (p := P g)).trans ((congrArg nRounds (R.own g hg)).trans (k5RowB_gives hV hg).1)
  · exact blockAt_told (W := G.W) (l := 2 * g + 1) (p := P g)
  · show (H2K5.k5Before? Z ("A" ++ toString g)).getD [] = _
    rw [before_at R hV hg]
    rfl
  · show ((planOk (parAt G.W (2 * g + 1) (P g) _) && claimsOkAtO (P g)) && (H2K5.k5Before? Z ("A" ++ toString g)).isSome) = true
    rw [planOk_own, R.own g hg, (k5RowB_gives hV hg).2.1, claims_at R hV hg, before_at R hV hg]
    rfl

end H2K5.Row

#print axioms H2K5.Row.k5RowB_gives
#print axioms H2K5.Row.before_at
#print axioms H2K5.Row.claims_at
#print axioms H2K5.Row.k5_row
