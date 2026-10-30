-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Tie/Pv/Tail/EndFormsFrom.lean: objectsF_forms (OnBytes/Tie/Pv/Tail/EndForms.lean) with the
plan's number of claims and the batching element read off the state before objectsF.

A statement and its proof, from objectsF_spread_from (OnBytes/Tie/Pv/Tail/EndInv.lean).
Main names:
  `objectsF_forms_from`: if objectsF returns G from a state F that has one coefficient for each
    slot: no two exponents of `rowsForm Y ρ tl funs F.planClaimsF` are equal; each lies from the
    plan's number of claims on and is at most that number plus the number of indices, less 1; behind
    the lookup's claims the total grows by the gap on m of the one form of that list at F's
    batching element.
Limits: premises: `Fits tl`, and `RawRows` at the cells of m. Of what the lookup's claims add to the
total nothing is said.
-/
import OnBytes.Tie.Pv.Tail.EndForms
import OnBytes.Tie.Pv.Tail.EndInv

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Tail.Port

open OnBytes OnBytes.Model

open Finset OnBytes.Road.Rows

variable {K : Type} [Field K] {J : Type} [Fintype J] (Y : Lay J)

/-- objectsF_forms, from the state before objectsF. -/
theorem objectsF_forms_from (ρ : Reading K) (W : World K) (tl tl' : HTailF2) (funs : Array HFun)
    (F G : Fork) (c c' : Ctx) (h : tl.objectsF funs F c = .ok ((tl', G), c')) (hfit : Fits tl)
    (hs : F.LS.size = F.ns) (m : J → K)
    (hV : RawRows W tl G funs (ρ.val F.theta) fun t r c => Y.cellAt m t r c) :
    ((rowsForm Y ρ tl funs F.planClaimsF).map Prod.fst).Nodup ∧
    (∀ p ∈ rowsForm Y ρ tl funs F.planClaimsF,
      F.planClaimsF ≤ p.1 ∧ p.1 ≤ F.planClaimsF + topOf tl funs - 1) ∧
    ∃ g Fa ca tla Fb cb tlb Fc cc,
      tl.heard = some g ∧ Forest.objects g F c = .ok (((), Fa), ca) ∧
      tl.linJoin9 Fa ca = .ok ((tla, Fb), cb) ∧ tla.linBits9 Fb cb = .ok ((tlb, Fc), cc) ∧
      c' = cc ∧ Kept Fc G ∧ G.nClaim = Fc.nClaim + tl.NM + (readsList tl funs).length ∧
      G.total ρ W = Fc.total ρ W +
        (batchAt (ρ.val F.theta) (rowsForm Y ρ tl funs F.planClaimsF)).gap m := by
  obtain ⟨hr, hb, g, Fa, ca, tla, Fb, cb, tlb, Fc, cc, hg, hFo, hJ, hB, e1, hk, hn, ht⟩ :=
    objectsF_spread_from ρ W tl tl' funs F G c c' h hfit hs _ hV
  refine ⟨by rw [fst_rowsForm]; exact nodup_of_rising hr, fun p hp => ?_,
    g, Fa, ca, tla, Fb, cb, tlb, Fc, cc, hg, hFo, hJ, hB, e1, hk, hn,
    by rw [ht, batch_rowsForm]⟩
  obtain ⟨r, hr', rfl⟩ := List.mem_map.1 hp
  have := hb r hr'
  show F.planClaimsF ≤ r.1 ∧ r.1 ≤ F.planClaimsF + topOf tl funs - 1
  omega

end OnBytes.Tie.Pv.Tail.Port

#print axioms OnBytes.Tie.Pv.Tail.Port.objectsF_forms_from
