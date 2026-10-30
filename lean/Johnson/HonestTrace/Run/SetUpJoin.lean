-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/HonestTrace/Run/SetUpJoin.lean

Where "publicOfO" (Johnson/Desc/Ok/PlanWritten/PublicAt.lean) returns at the stored full-size
files, it returns at all files in scope, with plans that are alike. Theorems alone; the proofs
are calls.

Main theorems:
* "public_in_scope": if "publicOfO OnBytes.secondHashFunction" returns X₀ at "VerifierAndGoals.storedPublicFiles" and F is in scope
  ("VerifierAndGoals.InScope F = true"), it returns at F an X with "SamePlans X X₀"
  (Johnson/HonestTrace/Run/SetUpSame.lean).
* "read_of_scope": in scope the goals' reader "VerifierAndGoals.readFiles" returns.
* "sameForAtt_turn": what attention reads of a scan is the same at the turned scan.

What gives which hypothesis of "public_turn" (Johnson/HonestTrace/Run/SetUpWalk.lean); a theorem
named without a path stands in the namespace "HonestTraceRun.SetUp", in a file imported here:
* p1: "polLayout_turn" over "scan_turn", "shape_turn_in_scope", "free_bounds" and "layout_eps".
* h3, h4, p4, p5, p10, p11: "ledger_tables", "ledger_h4" (Johnson/Unfolds/LedgerTables.lean).
* p2, p3, p6: "scales_return" (Johnson/Goal/Meaning/ScalesReturn.lean). p7: "hPar_in_scope".
* p13: "headLayout_turn" over "headLayout_norm" and "LPFPol.layout_returns"
  (Johnson/LPFPol/PublicAtPolicy.lean).
* p14: "config_turn" over "group_turn", with "shifts_of_read" and "base_facts".

Limits. At "OnBytes.secondHashFunction" alone. That "publicOfO" returns at the stored files is the hypothesis
h₀: it is not proved here. "attribute [-instance]" takes "Inst.Model.Scl.ref" out for this file.

No property of a release, of a verifier or of a prover is claimed.
-/
import Johnson.HonestTrace.Run.SetUpWalk
import Johnson.HonestTrace.Run.SetUpScan
import Johnson.HonestTrace.Run.SetUpAttConfig
import Johnson.HonestTrace.Run.SetUpBase
import Johnson.Unfolds.LedgerTables
import Johnson.Goal.PlanValues.ScopeAtPlan

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace HonestTraceRun

namespace SetUp

open OnBytes OnBytes.Model OnBytes.Model.Verify
open VerifiableInference.PlanWritten (publicOfO)

/-- In scope the goals' reader returns. -/
theorem read_of_scope {Z : VerifierAndGoals.PublicFiles} (h : VerifierAndGoals.InScope Z = true) :
    ∃ pp, VerifierAndGoals.readFiles Z = .ok pp := by
  cases hR : VerifierAndGoals.readFiles Z with
  | error e =>
    unfold VerifierAndGoals.InScope at h
    rw [hR] at h
    simp at h
  | ok pp => exact ⟨pp, rfl⟩

/-- What attention reads of the scan has not turned. -/
theorem sameForAtt_turn (P : PolScan) (vals : List (String × Nat)) (v : VerifierAndGoals.FreeLines) :
    SameForAtt (scanTurn P vals v) P :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem public_in_scope {X₀ : Public}
    (h₀ : publicOfO OnBytes.secondHashFunction VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.KL (some VerifierAndGoals.storedPublicFiles.lay) = .ok X₀)
    {F : VerifierAndGoals.PublicFiles} (hC : VerifierAndGoals.InScope F = true) :
    ∃ X, publicOfO OnBytes.secondHashFunction F.pol F.KL (some F.lay) = .ok X ∧ SamePlans X X₀ := by
  obtain ⟨pp, hR⟩ := read_of_scope hC
  have S₀ := VerifiableInference.PlanWritten.publicSteps_of_O h₀
  obtain ⟨fLam, fNGr, fldh, fk, fS, fr, fT, fone⟩ := base_facts h₀
  -- the two scans
  have hP₀ : polScan VerifierAndGoals.storedPublicFiles.pol = .ok X₀.P := polLayout_scan S₀.layout
  obtain ⟨P, hP, hshape⟩ := Meaning.Ret.shape_of_read hC hR
  have hP' : polScan (VerifierAndGoals.policyFile (VerifierAndGoals.freeLinesOf pp)) = .ok P := by
    rw [← OnBytes.Road.Hd.policy_of_scope hC hR]
    exact hP
  have eP : P = scanTurn X₀.P (VerifierAndGoals.Lines.valuesAt (VerifierAndGoals.freeLinesOf pp)) (VerifierAndGoals.freeLinesOf pp) :=
    scan_turn (v₀ := VerifierAndGoals.storedLines) hP' hP₀
  subst eP
  obtain ⟨b1, b2, bF, bM, bK, bt, bc, bC⟩ := free_bounds hR
  -- p1, and what the library's lemmas give from it
  have p1 := polLayout_turn S₀.layout hP (shape_turn_in_scope hC hR hP hP₀) b1 b2
  obtain ⟨h3, p4, p5, p10, p11⟩ := Johnson.Unfolds.ledger_tables hC hR p1
  have h4 := Johnson.Unfolds.ledger_h4 hC hR p1
  -- the scale file
  obtain ⟨q2, q3, q6⟩ := Meaning.Ret.scales_return hC hR
  obtain ⟨c1, c2, -⟩ := Lk6.AtPlan.layout_sizes (Lk6.AtPlan.polLayout_layout p1)
  have hyh := c1.trans hshape
  have hdq : (layTurn X₀.layers.y (VerifierAndGoals.freeLinesOf pp)).dq = 5120 := by
    rw [c2, hshape]
    try rfl
  have p2 : Layer.scalesOf (layTurn X₀.layers.y (VerifierAndGoals.freeLinesOf pp)).h (fileWords F.KL) =
      .ok (Meaning.Ret.recOf F.KL) := by
    rw [hyh]
    exact q2
  have p3 : Layer.scalesHeld (layTurn X₀.layers.y (VerifierAndGoals.freeLinesOf pp)).h
      (Meaning.Ret.recOf F.KL) = .ok () := by
    rw [hyh]
    exact q3
  have p6 : Layer.noWrap (layTurn X₀.layers.y (VerifierAndGoals.freeLinesOf pp)).h (Meaning.Ret.recOf F.KL)
      (layTurn X₀.layers.y (VerifierAndGoals.freeLinesOf pp)).dq = .ok () := by
    rw [hyh, hdq]
    exact q6
  -- the digest of the three files
  obtain ⟨hp, p7⟩ := hPar_in_scope h₀ hC
  -- the head's layout
  have k13 : Head.layout (headShape X₀.P X₀.layers.y) X₀.layers.y.tauFC = .ok X₀.HLy := by
    rw [← S₀.hS]
    exact S₀.head
  have p13 := headLayout_turn (VerifierAndGoals.Lines.valuesAt (VerifierAndGoals.freeLinesOf pp)) k13 bM bK bF bt
    (by rw [fT]; exact bc) (by omega) bC
  -- attention
  refine public_turn h₀ h3 h4 p1 p2 p3 p4 p5 p6 p7 p10 p11 p13 fun c₀ k9 => ?_
  obtain ⟨c, e1, -, e3, e4, e5⟩ := config_turn
    (sameForAtt_turn X₀.P (VerifierAndGoals.Lines.valuesAt (VerifierAndGoals.freeLinesOf pp)) (VerifierAndGoals.freeLinesOf pp))
    (layTurn X₀.layers.y (VerifierAndGoals.freeLinesOf pp)).h (s' := Meaning.Ret.recOf F.KL) k9
    (by simp [fNGr, fLam]) fk fS fr fldh
    (fun g hg => ⟨X₀.layers.sc.klSh (g * 4 + 0), fun lam hl => by
      rw [fLam] at hl ⊢
      exact fone g (by rw [fNGr] at hg; exact hg) lam hl⟩)
    (fun g hg => by
      have hg' : g < 12 := by
        rw [fNGr] at hg
        exact hg
      refine ⟨(Meaning.Ret.recOf F.KL).klSh (g * 4), (shifts_of_read hC hR hg' (l := 0) (by omega)).2.1,
        (shifts_of_read hC hR hg' (l := 0) (by omega)).2.2, fun lam hl => ?_⟩
      rw [fLam] at hl ⊢
      exact (shifts_of_read hC hR hg' hl).1)
  exact ⟨c, e1, e3, e4, e5⟩

end SetUp

end HonestTraceRun

#print axioms HonestTraceRun.SetUp.public_in_scope
#check @HonestTraceRun.SetUp.public_in_scope
