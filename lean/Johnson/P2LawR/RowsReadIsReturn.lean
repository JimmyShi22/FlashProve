-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P2LawR/RowsReadIsReturn.lean: THE NAMED CONDITION IN FRONT OF THE HEAD,
P5J.rowsRead Z (Johnson/Goal/Skeleton/RowsRead.lean), SAYS NO MORE THAN "THE
MAKER OF THE ROWS OF THE SENDINGS RETURNS AT THE THREE PUBLIC FILES": in the goals' scope, where the
public part returns at the hash secondHashFunction and the pin on what was made accepts. One theorem
and its form under "laid": two calls of theorems in Johnson/HB/LLHARD/.
Why. rowsRead Z has two halves: the maker returns some rows; in the first proof chain's rows one
shape has one radius. The second follows from the first: radii_in_scope
(Johnson/HB/LLHARD/RadiiInScope.lean): the rows' column is the written list; rowsRead_of_radii
(Johnson/HB/LLHARD/RadOneWritten.lean): at the written list the test accepts, by Lean's kernel.
  **rowsRead_iff_returns**   see its statement.
  rowsRead_iff_returns_laid the same under LaidAt in scope: the pin is the entry tests' own row
      (pins_of_laid).
Limits. THIS FILE SHOWS AT NO FILES THAT THE MAKER RETURNS. Elsewhere in this library rowsRead Z
follows from a yes of protocolDataWellFormed (P5J.owed_of_live, Johnson/Goal/Skeleton/OwedOfLive.lean) and is
proved at storedPublicFiles (headMember_zFull, AtFullSide/Top/HeadMemberAtFull.lean). It cannot
be taken from the head of the closed constant: that head is made with rowsRead Z. At OnBytes.secondHashFunction
alone. The full size alone. Nothing on soundness.

-/
import Johnson.HB.LLHARD.RadiiInScope
import Johnson.HB.LLHARD.RadOneWritten
import Johnson.Goal.Skeleton.PinsOfLaid

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P5J
open VerifiableInference.Desc (Chain)
open OnBytes.Maker (WholeD)
open VerifiableInference.PlanWritten (madePinnedAt)

/-- **THE NAMED CONDITION IS "THE MAKER RETURNS".** -/
theorem rowsRead_iff_returns {W : VerifierAndGoals.PublicFiles} (hW : VerifierAndGoals.InScope W = true) {Z : ProofFile.Pub}
    (h : ProofFile.pubPlain OnBytes.secondHashFunction W.pol W.lay W.KL = .ok Z)
    (hy : madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true) :
    rowsRead W ↔ ∃ R, Johnson.G.sendRowsOf W.pol W.lay W.KL = .ok R :=
  ⟨fun t => t.rows, fun ⟨_, hR⟩ =>
    P5T.rowsRead_of_radii hR (VerifiableInference.Desc.LinkJoin.radii_in_scope hW h hy hR)⟩

/-- The same where the verifier's own value is laid. -/
theorem rowsRead_iff_returns_laid {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
    {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} (hZ : VerifierAndGoals.InScope Z = true)
    (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF) :
    rowsRead Z ↔ ∃ R, Johnson.G.sendRowsOf Z.pol Z.lay Z.KL = .ok R :=
  rowsRead_iff_returns hZ L.pub (pins_of_laid hZ L).1

end P5J

#print axioms P5J.rowsRead_iff_returns
#print axioms P5J.rowsRead_iff_returns_laid
