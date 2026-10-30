-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/MakersFitPlan.lean: CONDITIONAL. A statement with its proof.

What is here: THE CLAUSE ON THE MAKERS OF THE PUBLIC TEST ON THE PARTS OF THE FEED-FORWARD LAYERS'
OWN ROUNDS (`k4MakersFit`, Honest/K4/Part.lean; the sub-protocol K4) IS TRUE, ALL FIFTEEN CLAUSES,
FROM PREMISES ON PUBLIC DATA AND THE TEST ON WHAT THE LOOKUP HAS SAMPLED. No evaluation: the test
does each maker's whole work at the zero input; here each clause is a law: eleven are general in the
input and the sampled values and are laid at the zero input and the zero challenges; the four on the
lists of powers speak of the zero challenges alone.
How. The two lengths, the squares, the row products, the batched sumcheck and the two gated
products: Law/W/FitNorms.lean, FitRows.lean, FitStackPub.lean, LamRoomOfFit.lean, FitGated.lean. The
second token sumcheck: Law/FitTerms.lean over Law/SidesWhole.lean. The merge's three:
Law/FitMergeZero.lean. The four lists of powers: Law/FitPowers.lean. The sampled values' sizes at
the zero challenges: Law/ZeroSizes.lean.

Not shown here. THE PREMISES: the public facts `K4Plan` and profile 4; the plan names the reads'
array (hU); the list of tables is laid (hl); that array has a column (hK); the row of the first free
entry behind the tables fits 32 bits (hb); the two tests with code `claimsB` and `pansB` at the
plan's own arguments; the weights' layout is what the verifier's `wsLayOf` returns for a model with
routed experts (hws); what the heads' weights read at the blank structure (hq); `k4LookFits` at fo
(hL); `k4TokensFit` at as many zero tokens as the layout counts (hV). Law/MakersFitHead.lean pays
eleven of the twelve, all but hL, under the library's hypothesis on the public files; apart from
that no example of all premises together is known. RETURNS, SHAPES AND SIZES ALONE: nothing on what
any maker's table is worth. The three other tests of `k4Fits` are not here. Nothing on soundness, on
completeness or on any other property. No property is claimed.

  `makersFit_plan`   **`k4MakersFit Q fo = true`**
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.FitTerms
import Johnson.Desc.ProofFile.Honest.K4.Law.ZeroSizes
import Johnson.Desc.ProofFile.Honest.K4.Law.SumPaid
import Johnson.Desc.ProofFile.Honest.K4.Law.W.FitNorms
import Johnson.Desc.ProofFile.Honest.K4.Law.W.FitRows
import Johnson.Desc.ProofFile.Honest.K4.Law.W.FitGated
import Johnson.Desc.ProofFile.Honest.K4.Law.W.FitStackPub
import Johnson.Desc.ProofFile.Honest.K4.Law.W.LamRoomOfFit

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4
open OnBytes (E zeroE)
open OnBytes.Model (HTailF2 WsShape wsLayOf Forest.Heard)
open OnBytes.Model.Layer (TableAsk TableAt layTables tableAsks nEndT)
open OnBytes.Road (admitted_of_layout)
open OnBytes.Road.K4.W (K4Plan)
open OnBytes.Road.K4.C (QkRd rowMaps_returns envOf_pub)
open OnBytes.Desc.First.K4.RtPub (claimsB zkFits blankClaims pansB blankEnv nclpOf)
open OnBytes.Desc.First.K4.Honest
open ProofFile.Honest.K4.W (wSums_length squares_fit rowProducts_length rows_fit gated_fit gated2_fit
  stack_fit_pub lam_room_of_fit)
open Inst.Model.FFSeg (Dim)

variable {Q : K4Pub} {fo : Forest.Heard} {iU3 : ℕ}
  {r : List TableAt × List (TableAsk × List (ℕ × ℕ)) × ℕ}
  {hS : OnBytes.Model.Layer.Shape} {pc : List (List String)} {tl : HTailF2} {D : Dim}

/-- CONDITIONAL on every hypothesis named. **THE CLAUSE ON THE MAKERS IS TRUE.** -/
theorem makersFit_plan (A : K4Plan hS pc Q.P Q.g tl D) (hp4 : hS.p4 = true)
    (hU : Q.hp.tl.ix.U.getD 2 none = some iU3)
    (hl : layTables (matsOf Q) (tableAsks Q.P.y Q.P.rd Q.g) 0 = some r)
    (hK : ((Q.hp.Fp.trees[iU3]?).map (·.K)).getD 0 ≠ 0)
    (hb : r.2.2 / ((Q.hp.Fp.trees[iU3]?).map (·.K)).getD 0 < 2 ^ 32)
    (hB : claimsB Q.P Q.hp Q.g = true)
    (hPB : pansB Q.P (blankEnv Q.P Q.hp Q.g iU3 r.1) Q.hp.lamS (nclpOf Q.hp Q.g) = true)
    {sw s : WsShape} {lk : ℕ} (hws : wsLayOf sw true lk = .ok Q.P.wsLay)
    (hq : QkRd (blankClaims Q.P Q.hp Q.g) s) (hL : k4LookFits Q fo = true)
    (hV : k4TokensFit Q (Array.replicate Q.P.y.T 0) = true) :
    k4MakersFit Q fo = true := by
  have Ad := admitted_of_layout A.lay A.sw.p3
  have hxl : Q.P.y.h.xl = 5 := by
    rw [Ad.shape]
    exact A.sw.xl
  have eT : D.lT = Q.P.y.h.lt := by
    rw [Ad.shape]
    exact A.sized.lT
  have eL : D.lL = Q.P.y.h.ll := by
    rw [Ad.shape]
    exact A.sized.lL
  have ela : Q.P.y.ls + Q.P.y.h.lt = Q.P.y.h.la := by
    rw [Ad.shape, Ad.la]
  -- what the test on the lookup's sizes has
  have hz : zkFits Q.P fo.zk = true := zk_of_look hL
  have hL' := hL
  unfold k4LookFits at hL'
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hL'
  have hla : Q.P.y.h.la ≤ fo.zx.size := by
    rw [hL'.1.1.1.2]
    exact hL'.1.1.1.1.2
  have hlt' : Q.P.y.h.lt ≤ fo.zx.size := by omega
  have hzt : ∀ n, (ztOf Q (k4ZeroPts Q fo n)).size = Q.P.y.h.lt := fun n =>
    ztOf_size_of_le Q (k4ZeroPts Q fo n) hlt'
  -- the fifteen
  obtain ⟨ms0, hms0⟩ := rowMaps_returns A hp4 hU hl hK hb (k4ZeroIn Q fo)
    (k4ZeroPts Q fo ((rowsNamed Q .batSigma).getD 1 0))
  obtain ⟨ms1, hms1⟩ := rowMaps_returns A hp4 hU hl hK hb (k4ZeroIn Q fo)
    (k4ZeroPts Q fo ((starts Q).getD 1 0))
  obtain ⟨j0, a0, f0⟩ := squares_fit A (k4ZeroIn Q fo) (k4ZeroPts Q fo ((starts Q).getD 0 0))
    (rhoI_zero Q fo) (PV_zero Q fo 0 (by omega))
  obtain ⟨j1, a1, f1⟩ := rows_fit A hms1 (PV_zero Q fo 1 (by omega))
  obtain ⟨S2, hS2⟩ := sides_whole (w := k4ZeroIn Q fo)
    (p := k4ZeroPts Q fo ((starts Q).getD 2 0)) A hp4 hU hl hK hb hB hz hla hws hq
  obtain ⟨j2, a2, f2⟩ := terms_fit A hU hl hPB hS2 (hzt _)
  obtain ⟨j3, a3, f3⟩ := stack_fit_pub A hp4 hU hl hK hb hB hPB hws hq (k4ZeroIn Q fo)
    (p := k4ZeroPts Q fo ((starts Q).getD 3 0))
    (shownT := Array.replicate (nEndT Q.P.y) zeroE) hz hla
    (om_zero Q fo) (rt_zero_at Q fo 3 (by omega) (by omega)) Array.size_replicate
  obtain ⟨r1, r2⟩ := lam_room_of_fit A a3 f3 (by omega)
  obtain ⟨j4, a4, f4⟩ := gated_fit A (k4ZeroIn Q fo) (k4ZeroPts Q fo ((starts Q).getD 4 0))
    (by rw [rs_zero_at Q fo 4 (by omega) (by omega)]; exact r1) (by rw [hzt, eT])
  obtain ⟨j5, a5, f5⟩ := gated2_fit A (k4ZeroIn Q fo) (k4ZeroPts Q fo ((starts Q).getD 5 0))
    (by rw [rhoM_zero, eL]) (by rw [rs_zero_at Q fo 5 (by omega) (by omega)]; exact r2)
    (by rw [rt_zero_at Q fo 5 (by omega) (by omega), eT])
  obtain ⟨m1, m2, m3⟩ :=
    merge_zero hB (envOf_pub hU hl (k4ZeroPts Q fo ((starts Q).getD 6 0))) hL hV
  unfold k4MakersFit
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, m1⟩, m2⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, m3⟩
  · rw [wSums_length]
    exact beq_self_eq_true _
  · rw [rowProducts_length hms0 hxl]
    exact beq_self_eq_true _
  · rw [a0]
    exact f0
  · rw [a1]
    exact f1
  · rw [a2]
    exact f2
  · rw [a3]
    exact f3
  · rw [a4]
    exact f4
  · rw [a5]
    exact f5
  · rw [gp_zero]
    exact beq_self_eq_true _
  · rw [omV_zero]
    exact beq_self_eq_true _
  · rw [om_zero]
    rfl
  · rw [rhoW_zero]
    exact beq_self_eq_true _

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.makersFit_plan
