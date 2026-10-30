-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoTabsTied.lean.
What a run of Head.tablesOf returns, with every letter tied.

Fo.tablesOf_ok (OnBytes/Tie/Pv/Lookup/Ends/FoTabsH2.lean) says that the tables are what the list of
fifteen asks makes, but leaves four of the list's letters free: the point of the squares' table, the
point of the stream's table, and the two vectors of weights of the planes' tables. This file ties
them to the routines that make them, and names the state and the context in which the run ends.

States:
  tablesOf_tied: a run of Head.tablesOf from (F, c) that returns: it ends in (F, c); ZV is what
    lastOf gives of the squares' point; the stream's point is made of what cutLast gives of the
    column point of the call with NF; qFC and qROW are the calls with CNF and ROW; b0 and b1 are
    Forest.phiB at 0 and 1; the list of tables was open; the tables are what the fifteen asks make
    from nothing; their length is the plan's.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoTabsH2

set_option autoImplicit false

namespace Fo
open OnBytes OnBytes.Model OnBytes.PscRun

theorem tablesOf_tied (h : Head.Shape) (L : Head.HL) (hp : Head.HPlanH2) (cov : Head.Covered)
    (x : Head.Heard) (F G : Fork) (c c' : Ctx) (t : Head.Tables)
    (hh : Head.tablesOf h L hp cov x F c = .ok ((t, G), c')) :
    G = F ∧ c' = c ∧ hp.tl.funOpen = true ∧ h.la = h.ls + h.lt ∧ t.p = hp.nU.getD 2 0 ∧
      ∃ ZV lowN qFC qROW b0 b1, lastOf x.wpl.r h.la = .ok ZV ∧
        cutLast (Head.zjOf L x.g1 x.qN) h.ls = .ok lowN ∧
        (longPoint lowN.2 x.tN.r).size = h.la ∧
        Head.callNo L "CNF" = some qFC ∧ Head.callNo L "ROW" = some qROW ∧
        Forest.phiB x.g1 h.lmbH 0 = some b0 ∧ Forest.phiB x.g1 h.lmbH 1 = some b1 ∧
        (asksH h L cov x ZV (longPoint lowN.2 x.tN.r) qFC qROW b0 b1).foldlM
          (askStep hp.tl.mats) {} = some t := by
  unfold Head.tablesOf at hh
  dsimp only at hh
  obtain ⟨m0, hh⟩ := bindMustAs_ok _ _ _ F c _ hh
  obtain ⟨ZV, z1, hh⟩ := bindHeld_ok _ _ F c _ hh
  obtain ⟨lowN, z2, hh⟩ := bindHeld_ok _ _ F c _ hh
  obtain ⟨m1, hh⟩ := bindMustAs_ok _ _ _ F c _ hh
  obtain ⟨qFC, e1, hh⟩ := bindGetAs_ok _ _ _ F c _ hh
  obtain ⟨qROW, e2, hh⟩ := bindGetAs_ok _ _ _ F c _ hh
  obtain ⟨b0, z3, hh⟩ := bindGetAs_ok _ _ _ F c _ hh
  obtain ⟨b1, z4, hh⟩ := bindGetAs_ok _ _ _ F c _ hh
  obtain ⟨t', e3, hh⟩ := bindGetAs_ok _ _ _ F c _ hh
  obtain ⟨m2, hh⟩ := bindMustAs_ok _ _ _ F c _ hh
  have e4 := (pure_ok _ _ _ _).1 hh
  have e5 : t = t' := congrArg (fun y : (Head.Tables × Fork) × Ctx => y.1.1) e4
  have e6 : G = F := congrArg (fun y : (Head.Tables × Fork) × Ctx => y.1.2) e4
  have e7 : c' = c := congrArg (fun y : (Head.Tables × Fork) × Ctx => y.2) e4
  simp only [Bool.and_eq_true, beq_iff_eq] at m1 m2
  exact ⟨e6, e7, m0, m1.2, e5 ▸ m2, ZV, lowN, qFC, qROW, b0, b1, z1, z2, m1.1, e1, e2, z3, z4,
    e5 ▸ e3⟩

end Fo
