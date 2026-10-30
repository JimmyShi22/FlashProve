-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/TablesPlanInScope.lean: AT ALL PUBLIC FILES IN THE GOALS' SCOPE THE TWO TESTS
ON PUBLIC NUMBERS OF Law/TablesPlanCode.lean ACCEPT: tabsPlanB AND readsPlanB ARE THEOREMS THERE.
Statements and proofs.

By Law/HeadPlanWritten.lean (the written list of the head's eight matrices; the length of the vector
of reads; the list of tables is open) and Law/HeadFsWritten.lean's opening of the head's layout (the
six calls). What is left is closed terms, which Lean's kernel evaluates ("decide +kernel").

  callsW           the head's six calls, as "place" makes them of written sizes.
  calls_in_scope   X.HLy.calls is that list.
  headTabsW            the fifteen tables without their weights, at the written list of matrices.
  tabs_is          tabsOfPlan X.hS X.H = headTabsW.
  needW, need_is   the twelve tables that the head's forms name, with what they spend of each.
  tabsPlan_in_scope, readsPlan_in_scope   MAIN.

WHAT IT IS NOT. Facts on public parameters alone. Nothing on soundness. UNDER THE LIBRARY's publicOf
ALONE. The arrays of columns that "place" builds are not evaluated: the tests read the segments'
names alone.
LETTERS. No letter stands under "there is".

-/
import Johnson.Desc.Kinds.Law.HeadPlanWritten
import Johnson.Desc.Kinds.Law.TablesPlanCode

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.Kinds.Head.Law.InScope

open OnBytes.Model (CallD place)
open OnBytes.Model.Head (Tables)

/-- **The head's six calls**, of written sizes. -/
def callsW : List CallD :=
  [place "R16a" "R16" [("NF", 5120, false), ("NFH", 5120, false), ("HD0", 202048, false)] (27 - 10),
   place "R16b" "R16" [("HD1", 202048, false)] (27 - 10),
   place "R8" "R8" [("ROW", OnBytes.Model.ledNRH 5, false), ("HD2", 202048, false)] (27 - 10),
   place "FEa" "FE" [("HE0", 131072, false)] (27 - 10),
   place "FEb" "FE" [("HE1", 202048 - 131072, false)] (27 - 10),
   place "FC" "FC" [("CNF", 5120, false)] (27 - 10)]

variable {Z : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : Option ByteArray}
  {X : OnBytes.Model.Verify.Public}

theorem calls_in_scope (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : OnBytes.Model.Verify.publicOf Z.pol Z.KL lay = .ok X) :
    X.HLy.calls = callsW.toArray := by
  have St := VerifiableInference.PlanWritten.publicSteps_of h
  have hP := OnBytes.Road.Hd.scan_of_scope hZ hR h
  have Zs : SizesH X.hS := by
    rw [St.hS, hP]
    exact sizesH_scan _ _
  obtain ⟨L0, calls, fs0, pub, h3, h4, hc0, _, _, _, _⟩ := layout_fs St.head
  obtain ⟨j1, j2⟩ := numbers_JV h3
  have hJV : L0.JV = 202048 := by
    rw [j1, Zs.V, Zs.S2]
    decide
  have hJVa : L0.JVa = 131072 := by
    rw [j2, Zs.V, Zs.S2]
    decide
  have hc := calls_six h4 Zs.lines
  rw [Zs.d, hJV, hJVa, Zs.XL, Zs.floor, Zs.lt] at hc
  rw [hc0, hc]
  rfl

/-- The fifteen tables without their weights, at the written list of matrices. -/
def headTabsW : Option Tables :=
  ([(0, 4, 2 ^ 16, "hf@Z"), (0, 4, 2 ^ 16, "hf@phiZ"),
    (4 + 1 + 1 + 1, 1, 2 ^ 16, "xbL@Z_V"), (4 + 1 + 1 + 1, 1, 2 ^ 16, "xbL@Y_N"),
    (4, 1, 1024, "hd@zt_FC"), (4, 1, 1024, "hd@r_H"),
    (4 + 1, 1, 1024, "hr@zt_ROW"), (4 + 1, 1, 1024, "hr@P_V"),
    (4 + 1, 1, 1024, "hr@r_tV"), (4 + 1, 1, 1024, "hr@rt_N"),
    (4 + 1, 1, 1024, "hr@phiC"), (4 + 1, 1, 1024, "hr@rhoC"),
    (4 + 1 + 1, 1, 2 ^ 15, "bH-bits-0"), (4 + 1 + 1, 1, 2 ^ 15, "bH-bits-1"),
    (4 + 1 + 1, 1, 2 ^ 15, "bH-pin")] : List (Nat × Nat × Nat × String)).foldlM
    (fun t a => Own.tableAdded matsW t a.1 a.2.1 a.2.2.1 #[] a.2.2.2) {}

/-- Five more sizes of the head's shape. -/
theorem sizes_five (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : OnBytes.Model.Verify.publicOf Z.pol Z.KL lay = .ok X) :
    X.hS.NHf = 4 ∧ X.hS.la = 16 ∧ X.hS.T = 1024 ∧ X.hS.lmbH = 15 ∧ X.hS.ls = 6 ∧ X.hS.lt = 10 ∧
      X.hS.d = 5120 ∧ X.hS.V = 202048 := by
  rw [Meaning.HeadS.hS_in_scope hZ hR h]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem tabs_is (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : OnBytes.Model.Verify.publicOf Z.pol Z.KL lay = .ok X) :
    tabsOfPlan X.hS X.H = headTabsW := by
  obtain ⟨s1, s2, s3, s4, _, _, _, _⟩ := sizes_five hZ hR h
  unfold tabsOfPlan skeleton
  rw [(plan_in_scope hZ hR h).mats, s1, s2, s3, s4]
  rfl

/-- The twelve tables that the head's forms name, with what they spend of each. -/
def needW : List (String × Nat) :=
  [("xbL@Z_V", 400), ("xbL@Y_N", 400), ("hd@zt_FC", 10240), ("hr@zt_ROW", 120), ("hr@P_V", 99),
   ("hr@r_tV", 99), ("hr@rt_N", 99), ("hf@Z", 19262), ("hf@phiZ", 19262), ("hd@r_H", 10240),
   ("hr@phiC", 120), ("hr@rhoC", 120)]

theorem need_is (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : OnBytes.Model.Verify.publicOf Z.pol Z.KL lay = .ok X) : readsNeed X.hS = needW := by
  obtain ⟨_, _, _, _, s5, _, s7, s8⟩ := sizes_five hZ hR h
  unfold readsNeed
  show [("xbL@Z_V", 5 * X.hS.d / 2 ^ X.hS.ls), ("xbL@Y_N", 5 * X.hS.d / 2 ^ X.hS.ls),
    ("hd@zt_FC", 2 * X.hS.d), ("hr@zt_ROW", NR + 21), ("hr@P_V", NR), ("hr@r_tV", NR),
    ("hr@rt_N", NR),
    ("hf@Z", (4 * X.hS.d + 6 * ((X.hS.V + 2 ^ X.hS.ls - 1) / 2 ^ X.hS.ls * 2 ^ X.hS.ls)) /
      2 ^ X.hS.ls),
    ("hf@phiZ", (4 * X.hS.d + 6 * ((X.hS.V + 2 ^ X.hS.ls - 1) / 2 ^ X.hS.ls * 2 ^ X.hS.ls)) /
      2 ^ X.hS.ls),
    ("hd@r_H", 2 * X.hS.d), ("hr@phiC", NR + 21), ("hr@rhoC", NR + 21)] = needW
  rw [s5, s7, s8]
  decide

set_option maxRecDepth 100000 in
theorem callWith_cnf : ((callsW.toArray.findIdx? fun c =>
    (c.segs.find? fun g => g.name == "CNF").isSome).isSome) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem callWith_row : ((callsW.toArray.findIdx? fun c =>
    (c.segs.find? fun g => g.name == "ROW").isSome).isSome) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem headTabs_fill :
    (headTabsW.any fun t => t.p == (#[0, 0, 61680] : Array Nat).getD 2 0) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem headTabs_need : (headTabsW.any fun t0 => needW.all fun n =>
    (t0.tab.find? fun e => e.1 == n.1).any fun e => Nat.ble n.2 e.2.2) = true := by
  decide +kernel

/-- **AT ALL PUBLIC FILES IN THE GOALS' SCOPE: the list of tables is open; la = ls + lt; two calls
bear the segments "CNF" and "ROW"; the fifteen tables fill the vector of reads.** -/
theorem tabsPlan_in_scope (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : OnBytes.Model.Verify.publicOf Z.pol Z.KL lay = .ok X) :
    tabsPlanB X.hS X.HLy X.H = true := by
  obtain ⟨_, s2, _, _, s5, s6, _, _⟩ := sizes_five hZ hR h
  have Pw := plan_in_scope hZ hR h
  unfold tabsPlanB Own.callWith
  rw [Pw.funOpen, s2, s5, s6, calls_in_scope hZ hR h, callWith_cnf, callWith_row,
    tabs_is hZ hR h, Pw.nU, headTabs_fill]
  rfl

/-- **AND EACH OF THE TWELVE TABLES THAT THE HEAD's FORMS NAME IS THERE, NO SHORTER THAN WHAT THEY
SPEND OF IT.** -/
theorem readsPlan_in_scope (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : OnBytes.Model.Verify.publicOf Z.pol Z.KL lay = .ok X) : readsPlanB X.hS X.H = true := by
  unfold readsPlanB
  rw [tabs_is hZ hR h, need_is hZ hR h]
  exact headTabs_need

end VerifiableInference.Desc.Kinds.Head.Law.InScope

#print axioms VerifiableInference.Desc.Kinds.Head.Law.InScope.calls_in_scope
#print axioms VerifiableInference.Desc.Kinds.Head.Law.InScope.tabs_is
#print axioms VerifiableInference.Desc.Kinds.Head.Law.InScope.need_is
#print axioms VerifiableInference.Desc.Kinds.Head.Law.InScope.tabsPlan_in_scope
#print axioms VerifiableInference.Desc.Kinds.Head.Law.InScope.readsPlan_in_scope
