-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoBitsLaw.lean: the three claims on the planes that the smallness test
writes by hand, under the one law of the virtual rows.

bits9_paid (OnBytes/Tie/Pv/Lookup/Ends/FoBitsPayAt.lean) asks three propositions VirtRow on the
array BZ, with weights written out. Here they follow from RowsLaw
(OnBytes/Tie/Pv/Lookup/Ends/FoRowsLaw.lean) at the state that HTailF2.coefficientsF leaves, by the
weights that this routine declares (coef_bz, OnBytes/Tie/Pv/Lookup/Ends/FoCoef.lean).

 - bits9_law: the three claims (form and run) that HTailF2.linBits9 adds are worth claimLeaves,
   claimBits and countK of the lookup's claims, at the columns' sums of the lookup's own cells.
   Fc: the state in which coefficientsF is run. cellAt: the arrays' own entries.

Hypotheses on the world: RowsLaw at coefAll tl g Fc; CellsBZ: the lookup's cells are BZ's entries; ν
reads 0 at the place that is no cell.
Premises on public numbers and on the state: FoNums.ok; 2^cK = NC; 5 ≤ kT + cK; Fc has BZ's three
virtual rows; BZ has 32 rows; no matrix's array is BZ.
Kept from bits9_claim (OnBytes/Tie/Pv/Lookup/Ends/FoTailBits.lean): tl.f9 = g.shape; the run of
pscRow on the leaves' sumcheck returns from (F, c), with the form row, and leaves F1; HeardIs ρ g F0
(endsOf g.shape 5 jLK rsK): the record g, with the state F0, holds the flat function's end values at
the rounds rsK (OnBytes/Tie/Pv/Lookup/Port/FoHeard.lean); Later F0 F; Sized F; Later F1 H. No
premise ties Fc to F, F1 or H.

Not claimed: anything on soundness, completeness or hiding.
Nor is it claimed that RowsLaw holds of committed arrays.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoBitsPayAt
import OnBytes.Tie.Pv.Lookup.Ends.FoRowsLaw

set_option autoImplicit false

namespace Fo
open TwV Finset FoNums Cb.Fo Cb.Fo.Pin OnBytes OnBytes.Model OnBytes.DgP OnBytes.PscRun

theorem bits9_law {K : Type} [CommRing K] (ρ : Reading K) (tl : HTailF2) (g : Forest.Heard)
    (jLK : ℕ) (rsK : Rounds K) (F0 F F1 : Fork) (c c1 : Ctx) (row : Aff) (p' : Psc)
    (hs : tl.f9 = g.shape) (h : pscRow g.leaves oneE {} F c = .ok (((row, p'), F1), c1))
    (hI : HeardIs ρ g F0 (endsOf g.shape 5 jLK rsK)) (h0 : Later F0 F)
    (hok : FoNums.ok g.shape = true) (hF : Sized F) (hfull : 2 ^ g.shape.cK = g.shape.NC)
    (h5 : 5 ≤ g.shape.kT + g.shape.cK) (H : Fork) (hH : Later F1 H) (ν : Pl → K)
    (entry : ℕ → ℕ → ℕ → K) (hz : ν .zero = 0) (Fc : Fork) (r0 : HasRow Fc tl.ix.BZ 0)
    (r1 : HasRow Fc tl.ix.BZ 1) (r2 : HasRow Fc tl.ix.BZ 2)
    (hm : ∀ mu < tl.NM, tl.gtTree.getD mu 0 ≠ tl.ix.BZ) (hR : (Fc.trees.getD tl.ix.BZ {}).R = 32)
    (cellAt : ℕ → ℕ → ℕ → K)
    (hL : RowsLaw ρ (coefAll tl g Fc) (H.worldOf ρ (fun j => ν (.mask j)) entry) cellAt)
    (hB : CellsBZ g.shape ν (cellAt tl.ix.BZ)) :
    [row.value ρ (H.worldOf ρ (fun j => ν (.mask j)) entry) +
        Run2.value ρ (H.worldOf ρ (fun j => ν (.mask j)) entry)
          (bzRun tl 0 (mulE g.leaves.eps g.leavesA)
            (eqTab (g.zb0.extract 5 (5 + tl.f9.kT + tl.f9.cK)))),
      (Aff.slot g.sBit).value ρ (H.worldOf ρ (fun j => ν (.mask j)) entry) +
        Run2.value ρ (H.worldOf ρ (fun j => ν (.mask j)) entry)
          (bzRun tl 1 (subE zeroE oneE) (eqTab (g.zb1.extract 5 (5 + tl.f9.kT + tl.f9.cK)))),
      (Aff.ofConst (subE zeroE (ofNat (2 ^ tl.f9.v - tl.f9.padding)))).value ρ
          (H.worldOf ρ (fun j => ν (.mask j)) entry) +
        Run2.value ρ (H.worldOf ρ (fun j => ν (.mask j)) entry) (bzRun tl 2 oneE (pinW tl))] =
    [claimLeaves g.shape 5 jLK rsK ν (colsK g.shape 5 (endsOf g.shape 5 jLK rsK).zb0 ν),
      claimBits g.shape 5 jLK rsK ν (colsK g.shape 5 (endsOf g.shape 5 jLK rsK).zb1 ν),
      countK g.shape 5 (pinColK 5 ν)] := by
  obtain ⟨v0, v1, v2⟩ := virt_bz ρ tl g Fc r0 r1 r2 hm hR _ cellAt hL _ _ hI.zb0 hI.zb1
    tl.bzColumns
  exact bits9_paid ρ tl g jLK rsK F0 F F1 c c1 row p' hs h hI h0 hok hF hfull h5 H hH ν entry
    (cellAt tl.ix.BZ) hz hB v0 v1 v2

end Fo
