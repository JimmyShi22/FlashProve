-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/Row/K5RowSeat.lean: kind K5's row (Johnson/Desc/First/Att/Row/K5Row.lean) AT
THE SEAT: the row of the written cut and the test on the plan of the sub-protocol AS IT STANDS IN
THE FIRST CHAIN (IM.LaidAlone, Johnson/IMR/SeatForm.lean); and three of the row's equations by field
paid from other files' theorems: the twelve places, "U3 is the first array",
"the planned U3 has nW columns". Calls. NOTHING IS EVALUATED.
THE GROUND. The lot is handed a ground G, not the public part Z: the seat's ground is the value of
ProofFile.blankBy ProofFile.pureRoad.links Z (Johnson/Desc/ProofFile/Pub.lean). Where that returns G:
G.W = Z.p.X (ProofFile.Law.blankBy_W, Johnson/Desc/ProofFile/Law/MakerPublic.lean: ground_W here); in
scope G.built has 25 links with the names and kinds (IM.ground_gets | ground_named). THAT blankBy
RETURNS IS A PREMISE HERE: NO LOT's TO PAY.

Main names (namespace H2K5.Row):
  the_block_dress: the_block is IM.k5Dress (Johnson/IMR/K5Seat.lean) of blockAt: by unfolding.
  **k5_row_alone**: K5Reads · k5RowB V = true · g < 12 · b is the lot's sub-protocol at g, alone,
    under the seat's name at the seat's place →
    PlanWritten.cutOf [b] = [(name, a, 162, 162, [], [(1, 4 + 6 g)])] ∧ b.planOk = true. THE NAME
    AND THE PLACE ARE THE SEAT's LETTERS: not the lot's to pay.
  **k5Places_scope**: in scope, where the public part and the ground are made: the field places of
    K5Reads.
  ground_W: the ground's public data are the public part's.
  u3_of_public: where the public data are publicOf's value: the fields iU3 and cols of K5Reads at
    each of its plans, at nW := the plan's own.
IS IT EMPTY HERE? IMPLICATIONS. NOTHING IS SHOWN AT ANY PUBLIC FILE.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.Row.K5Row
import Johnson.Desc.First.Att.Row.K5RowPlaces
import Johnson.IMR.K5Seat
import Johnson.IMR.PureJoin
import Johnson.Desc.First.Att.Claims.OfPlan

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K5.Row
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Place Claim)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Att.P
open VerifiableInference.PlanWritten (cutOf toldRounds)

variable {Z : ProofFile.Pub} {G : ProofFile.Ground} {P : ℕ → Attention.Plan} {V : K5Vals}

/-- The lot's sub-protocol in terms of IM.k5Dress (Johnson/IMR/K5Seat.lean). -/
theorem the_block_dress (g : ℕ) :
    the_block Z G P g =
      IM.k5Dress Z ("A" ++ toString g) (blockAt G.W (2 * g + 1) (P g) ((H2K5.k5Before? Z ("A" ++ toString g)).getD [])) := rfl

/-- **THE ROW OF THE WRITTEN CUT, AND THE TEST ON THE PLAN, AT THE SEAT.** -/
theorem k5_row_alone (R : K5Reads Z G P V) (hV : k5RowB V = true) {g : ℕ} (hg : g < 12) {same : S → S → Bool} {b : Block S ProofFile.Cl}
    {name : String} {a : Place} (la : IM.LaidAlone same b (the_block Z G P g) name a) :
    cutOf [b] = [(name, a, 162, 162, [], [(1, 4 + 6 * g)])] ∧ b.planOk = true := by
  obtain ⟨-, h2, h3⟩ := k5_row R hV
  obtain ⟨-, r, o, t, bf⟩ := h2 g hg
  refine ⟨?_, (IM.alone_planOk la).trans (h3 g hg)⟩
  have ht : toldRounds b = toldRounds (the_block Z G P g) := by
    unfold toldRounds
    rw [IM.alone_oracles la]
  show [(b.name, b.place, b.rounds.length, b.oracles.length, toldRounds b, b.before)] = _
  rw [IM.alone_name la, IM.alone_place la, IM.alone_rounds la, IM.alone_oracles la, ht, IM.alone_before la, r, o, t, bf]

/-- **The twelve places, in scope, where the public part and the ground are made.** -/
theorem k5Places_scope {Pb : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {G₀ : ProofFile.Ground} (hS : VerifierAndGoals.InScope Pb = true)
    (hR : VerifierAndGoals.readFiles Pb = .ok pp) (hZ : ProofFile.pubPlain OnBytes.secondHashFunction Pb.pol lay Pb.KL = .ok Z)
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Z = some G₀) :
    H2K5.k5Places G₀ = (List.range 12).map fun g => (2 * g + 1, "A" ++ toString g, g) := by
  obtain ⟨hN, l, hl, kl, -⟩ := IM.ground_named hS hR hZ hG
  refine places_of_named G₀.built (IM.ground_gets hS hR hZ hG).1 (fun g hg => ?_) ⟨l, hl, kl⟩
  obtain ⟨x, y, hx, kx, -, -, hy, ky, gy, ny⟩ := hN g hg
  exact ⟨x, y, hx, kx, hy, ky, gy, ny.name⟩

/-- The ground's public data are the public part's. -/
theorem ground_W {G₀ : ProofFile.Ground} (hG : ProofFile.blankBy ProofFile.pureRoad.links Z = some G₀) : G₀.W = Z.p.X := ProofFile.Law.blankBy_W hG

/-- **"U3 is the first array" and "the planned U3 has nW columns"**, at every plan of publicOf's
value. -/
theorem u3_of_public {pol KL : ByteArray} {layout : Option ByteArray} {X : Verify.Public} (hX : Verify.publicOf pol KL layout = .ok X) {g : ℕ}
    {p : Attention.Plan} (hp : X.A[g]? = some p) : p.iU3 = 0 ∧ (p.seam.Fp.trees[p.iU3]?).map (·.K) = some p.nW := by
  obtain ⟨h0, T, hT, -, hK, -⟩ := K5Law.ofPlan_u3_tree (K5Law.public_ofPlan hX g p hp)
  exact ⟨h0, by rw [hT, Option.map_some, hK]⟩

end H2K5.Row

#print axioms H2K5.Row.the_block_dress
#print axioms H2K5.Row.k5_row_alone
#print axioms H2K5.Row.k5Places_scope
#print axioms H2K5.Row.ground_W
#print axioms H2K5.Row.u3_of_public
