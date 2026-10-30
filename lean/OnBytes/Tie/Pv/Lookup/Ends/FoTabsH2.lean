-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoTabsH2.lean.
The head's tables of reads, off a run of Head.tablesOf.

States:
  bindGetAs_ok, bindHeld_ok, bindMustAs_ok: a test or a look-up before a routine, if the whole
    returns.
  tablesOf_ok: a run of Head.tablesOf that returns the tables t: t is what the list of fifteen asks
    (asksH) makes from nothing, where qFC and qROW are the numbers of the calls with the segments
    CNF and ROW. The two points ZV, YN and the two vectors b0, b1, which give the weights of four
    other tables, are left open (there are such).
  tab_hfZ, tab_hdFC, tab_hrROW, tab_hrPhiC: the four tables that the head's key forms read, under
    the conclusion of tablesOf_ok: each is found under its name with some first entry p0 (TabIs),
    and the records of its parts, counted from p0, bear the weights named.
Not claimed: that any run of Head.tablesOf returns.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoTabsH
import OnBytes.Tie.Pv.Lookup.Ends.FoKeyFormRun

set_option autoImplicit false

namespace Fo
open OnBytes OnBytes.Model OnBytes.PscRun

section
variable {α β : Type}

theorem bindGetAs_ok (name : String) (x : Option α) (f : α → SubM β) (F : Fork) (c : Ctx)
    (r : (β × Fork) × Ctx)
    (h : ((liftM (Head.getAs name x) : SubM α) >>= f) F c = .ok r) :
    ∃ a, x = some a ∧ f a F c = .ok r := by
  rw [bind_ok] at h
  obtain ⟨a, G, d, h1, h2⟩ := h
  obtain ⟨a', e1, e2⟩ := getAsL_ok name x F c _ h1
  have t0 : a = a' := congrArg (fun y : (α × Fork) × Ctx => y.1.1) e2
  have t1 : G = F := congrArg (fun y : (α × Fork) × Ctx => y.1.2) e2
  have t2 : d = c := congrArg (fun y : (α × Fork) × Ctx => y.2) e2
  rw [t0, t1, t2] at h2
  exact ⟨a', e1, h2⟩

theorem bindHeld_ok (x : Except String α) (f : α → SubM β) (F : Fork) (c : Ctx)
    (r : (β × Fork) × Ctx) (h : ((liftM (Head.held x) : SubM α) >>= f) F c = .ok r) :
    ∃ a, x = .ok a ∧ f a F c = .ok r := by
  rw [bind_ok] at h
  obtain ⟨a, G, d, h1, h2⟩ := h
  obtain ⟨a', d', k1, k2⟩ := (lift_ok (Head.held x) F c _).1 h1
  cases x with
  | error e =>
    have z : (Except.error { name := e } : Except Failure (α × Ctx)) = .ok (a', d') := k1
    cases z
  | ok b =>
    have z : (b, c) = (a', d') := Except.ok.inj k1
    have t0 : a = a' := congrArg (fun y : (α × Fork) × Ctx => y.1.1) k2
    have t1 : G = F := congrArg (fun y : (α × Fork) × Ctx => y.1.2) k2
    have t2 : d = d' := congrArg (fun y : (α × Fork) × Ctx => y.2) k2
    have z0 : b = a' := congrArg Prod.fst z
    have z1 : c = d' := congrArg Prod.snd z
    rw [t0, t1, t2, ← z0, ← z1] at h2
    exact ⟨b, rfl, h2⟩

theorem bindMustAs_ok (name : String) (b : Bool) (f : Unit → SubM β) (F : Fork) (c : Ctx)
    (r : (β × Fork) × Ctx) (h : ((liftM (mustAs name b) : SubM Unit) >>= f) F c = .ok r) :
    b = true ∧ f () F c = .ok r := by
  rw [bind_ok] at h
  obtain ⟨a, G, d, h1, h2⟩ := h
  obtain ⟨hb, e⟩ := (mustAs_ok name b F c _).1 h1
  have t1 : G = F := congrArg (fun y : (Unit × Fork) × Ctx => y.1.2) e
  have t2 : d = c := congrArg (fun y : (Unit × Fork) × Ctx => y.2) e
  rw [t1, t2] at h2
  exact ⟨hb, h2⟩

end

/-- The head's fifteen asks. -/
def asksH (h : Head.Shape) (L : Head.HL) (cov : Head.Covered) (x : Head.Heard) (ZV YN : Array E)
    (qFC qROW : ℕ) (b0 b1 : Array E) : List Ask :=
  [(0, h.NHf, 2 ^ h.la, longPhi x.Zl h.ls h.lt, "hf@Z"),
    (0, h.NHf, 2 ^ h.la,
      Array.map (fun i => (Head.costWeights cov (Head.ztOf h L x.g1 x.qH)).1.getD (i % h.T) zeroE)
        (Array.range (2 ^ h.la)), "hf@phiZ"),
    (h.NHf + 1 + 1 + 1, 1, 2 ^ h.la, longPhi ZV h.ls h.lt, "xbL@Z_V"),
    (h.NHf + 1 + 1 + 1, 1, 2 ^ h.la, longPhi YN h.ls h.lt, "xbL@Y_N"),
    (h.NHf, 1, h.T, eqTab (Head.ztOf h L x.g1 qFC), "hd@zt_FC"),
    (h.NHf, 1, h.T, eqTab x.tH.r, "hd@r_H"),
    (h.NHf + 1, 1, h.T, eqTab (Head.ztOf h L x.g1 qROW), "hr@zt_ROW"),
    (h.NHf + 1, 1, h.T, eqTab x.PV, "hr@P_V"),
    (h.NHf + 1, 1, h.T, eqTab x.tV.r, "hr@r_tV"),
    (h.NHf + 1, 1, h.T, eqTab x.tN.r, "hr@rt_N"),
    (h.NHf + 1, 1, h.T, (Head.costWeights cov (Head.ztOf h L x.g1 x.qH)).1, "hr@phiC"),
    (h.NHf + 1, 1, h.T, (Head.costWeights cov (Head.ztOf h L x.g1 x.qH)).2.2, "hr@rhoC"),
    (h.NHf + 1 + 1, 1, 2 ^ h.lmbH, b0, "bH-bits-0"),
    (h.NHf + 1 + 1, 1, 2 ^ h.lmbH, b1, "bH-bits-1"),
    (h.NHf + 1 + 1, 1, 2 ^ h.lmbH, Forest.phiP h.lmbH, "bH-pin")]

/-- **What a run of Head.tablesOf returns.** -/
theorem tablesOf_ok (h : Head.Shape) (L : Head.HL) (hp : Head.HPlanH2) (cov : Head.Covered)
    (x : Head.Heard) (F G : Fork) (c c' : Ctx) (t : Head.Tables)
    (hh : Head.tablesOf h L hp cov x F c = .ok ((t, G), c')) :
    ∃ ZV YN qFC qROW b0 b1, Head.callNo L "CNF" = some qFC ∧ Head.callNo L "ROW" = some qROW ∧
      h.la = h.ls + h.lt ∧
      (asksH h L cov x ZV YN qFC qROW b0 b1).foldlM (askStep hp.tl.mats) {} = some t := by
  unfold Head.tablesOf at hh
  dsimp only at hh
  obtain ⟨_, hh⟩ := bindMustAs_ok _ _ _ F c _ hh
  obtain ⟨ZV, _, hh⟩ := bindHeld_ok _ _ F c _ hh
  obtain ⟨lowN, _, hh⟩ := bindHeld_ok _ _ F c _ hh
  obtain ⟨m1, hh⟩ := bindMustAs_ok _ _ _ F c _ hh
  obtain ⟨qFC, e1, hh⟩ := bindGetAs_ok _ _ _ F c _ hh
  obtain ⟨qROW, e2, hh⟩ := bindGetAs_ok _ _ _ F c _ hh
  obtain ⟨b0, _, hh⟩ := bindGetAs_ok _ _ _ F c _ hh
  obtain ⟨b1, _, hh⟩ := bindGetAs_ok _ _ _ F c _ hh
  obtain ⟨t', e3, hh⟩ := bindGetAs_ok _ _ _ F c _ hh
  obtain ⟨_, hh⟩ := bindMustAs_ok _ _ _ F c _ hh
  have e4 := (pure_ok _ _ _ _).1 hh
  have e5 : t = t' := congrArg (fun y : (Head.Tables × Fork) × Ctx => y.1.1) e4
  simp only [Bool.and_eq_true, beq_iff_eq] at m1
  exact ⟨ZV, longPoint lowN.2 x.tN.r, qFC, qROW, b0, b1, e1, e2, m1.2, e5 ▸ e3⟩

/-- The table of this name: where it is found, and the records of its parts. -/
def TabIs (mats : Array TMat) (t : Head.Tables) (nm : String) (M0 parts Lf : ℕ) (phi : Array E) :
    Prop :=
  ∃ p0 len, (t.tab.find? fun e => e.1 == nm) = some (nm, p0, len) ∧
    len = partStart mats M0 Lf p0 parts - p0 ∧
    ∀ p < parts, partRec mats M0 Lf p0 phi p ∈ t.funs.toList

section
variable {h : Head.Shape} {L : Head.HL} {cov : Head.Covered} {x : Head.Heard} {ZV YN : Array E}
  {qFC qROW : ℕ} {b0 b1 : Array E} {mats : Array TMat} {t : Head.Tables}

theorem tab_hfZ (e : (asksH h L cov x ZV YN qFC qROW b0 b1).foldlM (askStep mats) {} = some t) :
    TabIs mats t "hf@Z" 0 h.NHf (2 ^ h.la) (longPhi x.Zl h.ls h.lt) :=
  asks_find mats [] _ (0, h.NHf, 2 ^ h.la, longPhi x.Zl h.ls h.lt, "hf@Z") {} t e
    (fun _ he => absurd he (by simp)) (fun _ hb => absurd hb (by simp))

theorem tab_hdFC (e : (asksH h L cov x ZV YN qFC qROW b0 b1).foldlM (askStep mats) {} = some t) :
    TabIs mats t "hd@zt_FC" h.NHf 1 h.T (eqTab (Head.ztOf h L x.g1 qFC)) :=
  asks_find mats ((asksH h L cov x ZV YN qFC qROW b0 b1).take 4) _
    (h.NHf, 1, h.T, eqTab (Head.ztOf h L x.g1 qFC), "hd@zt_FC") {} t e
    (fun _ he => absurd he (by simp))
    (fun b hb => by
      simp only [asksH, List.take_succ_cons, List.take_zero, List.mem_cons, List.not_mem_nil,
        or_false] at hb
      rcases hb with rfl | rfl | rfl | rfl <;> (dsimp only; decide))

theorem tab_hrROW (e : (asksH h L cov x ZV YN qFC qROW b0 b1).foldlM (askStep mats) {} = some t) :
    TabIs mats t "hr@zt_ROW" (h.NHf + 1) 1 h.T (eqTab (Head.ztOf h L x.g1 qROW)) :=
  asks_find mats ((asksH h L cov x ZV YN qFC qROW b0 b1).take 6) _
    (h.NHf + 1, 1, h.T, eqTab (Head.ztOf h L x.g1 qROW), "hr@zt_ROW") {} t e
    (fun _ he => absurd he (by simp))
    (fun b hb => by
      simp only [asksH, List.take_succ_cons, List.take_zero, List.mem_cons, List.not_mem_nil,
        or_false] at hb
      rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;> (dsimp only; decide))

theorem tab_hrPhiC (e : (asksH h L cov x ZV YN qFC qROW b0 b1).foldlM (askStep mats) {} = some t) :
    TabIs mats t "hr@phiC" (h.NHf + 1) 1 h.T
      (Head.costWeights cov (Head.ztOf h L x.g1 x.qH)).1 :=
  asks_find mats ((asksH h L cov x ZV YN qFC qROW b0 b1).take 10) _
    (h.NHf + 1, 1, h.T, (Head.costWeights cov (Head.ztOf h L x.g1 x.qH)).1, "hr@phiC") {} t e
    (fun _ he => absurd he (by simp))
    (fun b hb => by
      simp only [asksH, List.take_succ_cons, List.take_zero, List.mem_cons, List.not_mem_nil,
        or_false] at hb
      rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        (dsimp only; decide))

end

end Fo
