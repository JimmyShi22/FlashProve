-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/Row/K5OwnAtPlacesW.lean: kind K5: **CONDITIONAL (hZ · hG ARE SHOWN AT NO
PUBLIC FILES HERE): THE PREMISE hA OF THE ROW ON THE LOT's
ROUNDS (k5_row_by, Johnson/AtFull/Rounds/K5At.lean), IN THE GOALS' SCOPE, TO THE LETTER.** Calls and
one rfl. NOTHING IS EVALUATED HERE.
TWO WRITINGS OF ONE VALUE. That file writes the numbers of an attention segment's own rounds as
k5OwnW rows; Johnson/Desc/First/Att/Row/K5OwnW.lean as ownW, with rows := 0. ownW_rows: the two are
one, field for field, BY LEAN's OWN UNFOLDING: were one number other, it would not compile.
Main names (namespace H2K5.Row): ownW_rows (r) : { ownW with rows := r } =
Johnson.AtFull.Rounds.k5OwnW r · **k5_hA** (hS) (hR) (hZ) (hG) : ∀ x ∈ H2K5.k5Places G₀, ∀ a,
G₀.W.A[x.2.2]? = some a → a.own = Johnson.AtFull.Rounds.k5OwnW a.own.rows.
WHAT IS NOT HERE: that row's two other premises (hw: the policy's work is 0 · hN: the names at the
places).
IS IT EMPTY HERE? k5_hA IS AN IMPLICATION: as own_at_places
(Johnson/Desc/First/Att/Row/K5OwnAtPlaces.lean).
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.Row.K5OwnAtPlaces
import Johnson.AtFull.Rounds.K5At

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K5.Row
open OnBytes OnBytes.Model

/-- The two writings are one. -/
theorem ownW_rows (r : ℕ) : { ownW with rows := r } = Johnson.AtFull.Rounds.k5OwnW r := rfl

variable {Pb : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {Z : ProofFile.Pub} {G₀ : ProofFile.Ground}

/-- **hA, in scope.** -/
theorem k5_hA (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (hZ : ProofFile.pubPlain OnBytes.secondHashFunction Pb.pol lay Pb.KL = .ok Z)
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Z = some G₀) :
    ∀ x ∈ H2K5.k5Places G₀, ∀ a,
      G₀.W.A[x.2.2]? = some a → a.own = Johnson.AtFull.Rounds.k5OwnW a.own.rows :=
  fun x hx a ha => (own_at_places hS hR hZ hG x hx a ha).trans (ownW_rows a.own.rows)

end H2K5.Row

#print axioms H2K5.Row.ownW_rows
#print axioms H2K5.Row.k5_hA
