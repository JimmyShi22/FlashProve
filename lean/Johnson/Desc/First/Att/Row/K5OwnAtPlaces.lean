-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/Row/K5OwnAtPlaces.lean: kind K5: **CONDITIONAL (hZ · hG ARE SHOWN AT NO
PUBLIC FILES HERE): IN THE GOALS' SCOPE EVERY PLAN OF AN
ATTENTION SEGMENT's GROUP, AS THE LOT REACHES IT (over H2K5.k5Places G₀, at the ground's own public
data G₀.W), HAS THE WRITTEN NUMBERS OF ITS OWN ROUNDS, WHATEVER ITS FIELD rows.** Calls alone.
NOTHING IS EVALUATED.
WHY. own_in_scope (Johnson/Desc/First/Att/Row/K5OwnInScope.lean) says it at a group g below 12 of
publicOf's return. The lot (H2K5.lotN, Johnson/Desc/ProofFile/Lot/K5.lean) walks k5Places G₀ and
reads G₀.W.A at a place's group x.2.2. Here the law stands in the lot's own letters.
Main name (namespace H2K5.Row): **own_at_places** (hS) (hR) (hZ) (hG) : ∀ x ∈ H2K5.k5Places G₀, ∀ a,
G₀.W.A[x.2.2]? = some a → a.own = { ownW with rows := a.own.rows }.
IS IT EMPTY HERE? AN IMPLICATION: hS · hR are the goals' own premises; hZ · hG (the front's and
the ground's returns) are shown at no public files here. Under them k5Places G₀ has twelve members
(k5Places_scope) and each group has a plan (k5_plans_exist,
Johnson/Desc/First/Att/Row/K5RowOwn.lean).
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.Row.K5RowSeat
import Johnson.Desc.First.Att.Row.K5OwnInScope
import Johnson.Desc.ProofFile.Law.MakerPublic
import Johnson.Desc.Ok.PlanWritten.PublicAtLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K5.Row
open OnBytes OnBytes.Model

variable {Pb : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {Z : ProofFile.Pub} {G₀ : ProofFile.Ground}

/-- **The written numbers, at every plan that the lot reaches.** -/
theorem own_at_places (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (hZ : ProofFile.pubPlain OnBytes.secondHashFunction Pb.pol lay Pb.KL = .ok Z)
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Z = some G₀) :
    ∀ x ∈ H2K5.k5Places G₀, ∀ a,
      G₀.W.A[x.2.2]? = some a → a.own = { ownW with rows := a.own.rows } := by
  intro x hx a ha
  rw [k5Places_scope hS hR hZ hG] at hx
  obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hx
  have hX : Verify.publicOf Pb.pol Pb.KL (some lay) = .ok Z.p.X :=
    (VerifiableInference.PlanWritten.publicOfO_older Pb.pol Pb.KL (some lay)).symm.trans
      (ProofFile.Law.pub_public hZ)
  have ha' : Z.p.X.A[g]? = some a := by
    rw [← ground_W hG]
    exact ha
  exact own_in_scope hS hR hX (List.mem_range.1 hg) ha'

end H2K5.Row

#print axioms H2K5.Row.own_at_places
