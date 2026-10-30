-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K13/FillFitsAtHead.lean: THE PILE's FILLER OVER THE CHAIN's OWN SITES
MEETS THE PREMISE hfill OF THE THREE GUARDS, UNDER THE LIBRARY's ONE HYPOTHESIS AT THE FULL SIZE AND
NO OTHER PREMISE. One definition with code, and statements with their proofs.

FillFits.lean of this folder has hfill at `pileBySites` from four public facts. Here the four are
shown at the plan's own numbers `h.𝔇.P13`, the one layout Zp.p.X.layers.wsLay, the shape
Zp.first.lin and the list `sitesAt cF Zp` (SitesAtFlat.lean):
  as many sites as the plan has rows: `sitesAt_length` (13, by the list's text) and `m3_rows`
    (GuardsAtM3.lean of this folder);
  the layout has as many column bits as the shape: the library's `LT28.K11Tests.table_of_pub`
    (Johnson/Desc/Sound/K11Tests/PendAllNoPin.lean);
  the filler's shape is the plan's own: by unfolding (`K13.whereOf`,
    Johnson/Desc/ProofFile/Lot/K13.lean);
  more than one column: `m3_kCol` (GuardsAtM3.lean).
Main names:
  `fillerAt cF Zp claims`: **the filler at the chain's own sites**: `pileBySites` at that layout,
    that shape and `(sitesAt cF Zp).map (·.m)`. claims: the parameter: free.
  `hfill_at_head`: **hfill at `fillerAt cF Zp claims`, at every parameter**, under h alone.

What is not claimed. That h holds at any public files. That the filler yields a row anywhere.
Nothing on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K13.FillFits
import Johnson.Desc.ProofFile.Honest.K13.SitesAtFlat
import Johnson.Desc.Sound.K11Tests.PendAllNoPin

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K13
open OnBytes OnBytes.Params OnBytes.Model
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K13.Honest (rowReads SiteClaims pileBySites)
open OnBytes.Maker (WholeD)
open P5J (AtMgA TS)

/-- The list has thirteen sites. -/
theorem sitesAt_length (c : Chain S ProofFile.Cl) (Z : ProofFile.Pub) : (sitesAt c Z).length = 13 := by
  unfold sitesAt
  simp

/-- **The filler at the chain's own sites.** claims: the parameter. -/
def fillerAt {Xi : Type} (c : Chain S ProofFile.Cl) (Z : ProofFile.Pub) (claims : SiteClaims Xi) :
    Xi → List Fmt.Drawn → List TensorRow :=
  pileBySites Z.p.X.layers.wsLay Z.first.lin ((sitesAt c Z).map (·.m)) claims

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **hfill AT THE FILLER OVER THE CHAIN's OWN SITES, UNDER h ALONE.** -/
theorem hfill_at_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Xi : Type}
    (claims : SiteClaims Xi) :
    ∀ x heard, fillerAt cF Zp claims x heard ≠ [] →
      pileFits h.𝔇.P13 ((fillerAt cF Zp claims x heard).map rowReads) = true := by
  have key := pileBySites_hfill h.𝔇.P13 Zp.p.X.layers.wsLay Zp.first.lin
    ((sitesAt cF Zp).map fun σ => σ.m) claims
    (by rw [List.length_map, sitesAt_length, m3_rows h])
    (LT28.K11Tests.table_of_pub h.laid.pub).2.symm rfl (by rw [m3_kCol h]; decide)
  exact key

end ProofFile.Honest.K13

#print axioms ProofFile.Honest.K13.sitesAt_length
#print axioms ProofFile.Honest.K13.hfill_at_head
