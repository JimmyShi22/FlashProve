-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Opts/SpotsOfRowsRead.lean: THE NAMED TEST At.spotsB ACCEPTS UNDER THE ONE NAME OF THE
COMMON RESIDUE, P5J.rowsRead Z (Johnson/Goal/Skeleton/RowsRead.lean: «the second
reading of the three public files returns, with one radius a shape»). One line over
SpotsAtName.lean's spotsB_at_name: of that condition it spends «returns» alone (rowsRead.rows).
A law file; no running text imports it.
rowsRead Z IS NOT PAID: a condition on the public files alone.
Limits. The full size alone. Nothing on soundness.

-/
import Johnson.Top.H0.Opts.SpotsAtName
import Johnson.Goal.Skeleton.RowsRead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P5J.At

theorem spotsB_of_rowsRead {Z : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Z = true) {pp : Inst.Model.ScalesAndPolicy}
    (hR : VerifierAndGoals.readFiles Z = .ok pp) {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
    {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain TS ProofFile.Cl}
    (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF) (h : rowsRead Z) :
    spotsB Zp Z.lay = true :=
  spotsB_at_name hZ hR L h.rows

end P5J.At

#print axioms P5J.At.spotsB_of_rowsRead
