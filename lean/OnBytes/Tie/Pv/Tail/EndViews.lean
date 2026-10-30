-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Tail/EndViews.lean: the premise `RawRows` of the theorems on what objectsF adds
(OnBytes/Tie/Pv/Tail/EndAll.lean, EndSpread.lean), at the checks of the three kinds of sub-proof,
from the plan's run and one run of the check that begins at the plan's state and on a view.

Theorems with their proofs. OnBytes/Tie/Pv/Tail/EndPlans.lean asks that the context in which the
weights are tested is a view, not a dry run. Every call of the layer group's and the head's check
leaves a view where it began on one (`KeepsM`, OnBytes/Tie/Pv/Keeps/KeepsLift.lean, with its
instances in OnBytes/Tie/Pv/Keeps/KeepsModel.lean). So here the runs of the two checks are taken
apart once more, with the view carried from call to call. For the attention sub-proof
OnBytes/Tie/Pv/Keeps/KeepsChainA2.lean has the run taken apart, with the views.

Main names:
  `peelV`, `bindV`: a run of «x, then f» on a view: f has run on a view; with what x keeps, or with
    the run of x.
  `layer_ranV`, `head_ranV`: `layer_ran` (OnBytes/Tie/Pv/Tail/EndLayer.lean) and `head_ran`
    (OnBytes/Tie/Pv/Tail/EndHeadRun.lean) for a check that began on a view: the weights are tested
    on a view.
  `rawRows_layer_view`, `rawRows_head_view`, `rawRows_attention_view`: `RawRows` as the theorems on
    objectsF ask it.

Limits: the check must begin at the plan's state and on a view. The world reads the four kinds of
virtual row as sums of the arrays' entries (`ReadsRaw`, OnBytes/Tie/Pv/Tail/EndRaw.lean).


-/
import OnBytes.Tie.Pv.Keeps.KeepsChainA2
import OnBytes.Tie.Pv.Keeps.KeepsModel
import OnBytes.Tie.Pv.Keeps.KeepsRuns
import OnBytes.Tie.Pv.Tail.EndAttAll
import OnBytes.Tie.Pv.Tail.EndPlans

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Tail.Walk
open OnBytes OnBytes.Model OnBytes.Tie.Pv.Tail OnBytes.L5

variable {R : Fork → Fork → Prop}

/-- A run of «x, then f» on a view: x has run, it has left a view, and f has run from there. -/
theorem bindV {α β : Type} {x : LinkM α} {f : α → LinkM β} (hk : KeepsM x) {L : LinkCtx}
    {F : Fork} {c : Ctx} {r : ((β × LinkCtx) × Fork) × Ctx} (h : (x >>= f) L F c = .ok r)
    (d : c.ch.dry = false) :
    ∃ a L1 F1 c1, x L F c = .ok (((a, L1), F1), c1) ∧ c1.ch.dry = false ∧
      f a L1 F1 c1 = .ok r := by
  obtain ⟨a, L1, F1, c1, h1, h2⟩ := (bindL_ok _ _ _ _ _ _).1 h
  have hr : Runs x (L, F, c) a (L1, F1, c1) := h1
  exact ⟨a, L1, F1, c1, h1, runs_view (k := hk) hr d, h2⟩

/-- A run of «x, then f» on a view, where x keeps R: f has run on a view, from a state that stands
in R to the first. -/
theorem peelV {α β : Type} {x : LinkM α} {f : α → LinkM β} (hx : PresL R x) (hk : KeepsM x)
    {L : LinkCtx} {F : Fork} {c : Ctx} {r : ((β × LinkCtx) × Fork) × Ctx}
    (h : (x >>= f) L F c = .ok r) (d : c.ch.dry = false) :
    ∃ a L1 F1 c1, R F F1 ∧ c1.ch.dry = false ∧ f a L1 F1 c1 = .ok r := by
  obtain ⟨a, L1, F1, c1, h1, d1, h2⟩ := bindV hk h d
  exact ⟨a, L1, F1, c1, hx.out _ _ _ _ _ _ _ h1, d1, h2⟩

/-- `layer_ran` for a check that began on a view. -/
theorem layer_ranV (P : Layer.Pub) (hp : Layer.HPlan2) (g : Nat) (L L' : LinkCtx) (F0 F' : Fork)
    (c c' : Ctx) (wo : WsForkOut)
    (h : Layer.runForkHidG2 P hp g L F0 c = .ok (((wo, L'), F'), c')) (d : c.ch.dry = false) :
    ∃ (funs : Array HFun) (tl1 tlA tl : HTailF2) (F7 G F10 F11 F12 : Fork) (c7 c9 cT cT' : Ctx),
      cT.ch.dry = false ∧ hp.tl.closeFuns funs = some tl1 ∧ RecordKept tl1 tlA ∧ ShapesKept F0 F7 ∧
      tlA.objectsF funs F7 c7 = .ok ((tl, G), c9) ∧ FrameKept G F10 ∧
      tl.coefficientsF F10 cT = .ok (((), F11), cT) ∧
      tl.tileSelfTestF F11 cT = .ok (((), F12), cT') := by
  unfold Layer.runForkHidG2 at h
  obtain ⟨_, _, _, _, k1, d, h⟩ := peelV (R := ShapesKept) (by walkA) (by keepsM) h d
  obtain ⟨_, _, _, _, k2, d, h⟩ := peelV (R := ShapesKept) (by walkA) (by keepsM) h d
  obtain ⟨_, _, _, _, k3, d, h⟩ := peelV (R := ShapesKept) (by walkA) (by keepsM) h d
  obtain ⟨_, _, _, _, k4, d, h⟩ := peelV (R := ShapesKept) (by walkA) (by keepsM) h d
  obtain ⟨_, _, _, _, k5, d, h⟩ := peelV (R := ShapesKept) (by walkA) (by keepsM) h d
  obtain ⟨_, _, _, _, k6, d, h⟩ := peelV (R := ShapesKept) (by walkA) (by keepsM) h d
  obtain ⟨o, _, _, _, k7, d, h⟩ := peelV (R := ShapesKept) (by walkA) (by keepsM) h d
  obtain ⟨_, _, F8p, _, k8, d, h⟩ := peelV (R := ShapesKept) (by walkA) (by keepsM) h d
  obtain ⟨tl1, La, Fa, ca, hc, d, h⟩ := bindV (by keepsM) h d
  obtain ⟨hc, -⟩ := (subL_ok _ _ _ _ _ _ _ _).1 hc
  obtain ⟨hclosed, eFa, -⟩ := (Port.get_ok _ _ _ _ _ _).1 hc
  have k8b : ShapesKept F8p Fa := by
    rw [eFa]
    exact ShapesKept.refl _
  obtain ⟨tlA, Lb, Fb, cb, htr, d, h⟩ := bindV (by keepsM) h d
  have k9 := (inferInstance : PresL ShapesKept tl1.transcriptF).out _ _ _ _ _ _ _ htr
  obtain ⟨_, _, _, _, k10, d, h⟩ := peelV (R := ShapesKept) (by walkA) (by keepsM) h d
  obtain ⟨_, _, _, _, k11, d, h⟩ := peelV (R := ShapesKept) (by walkA) (by keepsM) h d
  obtain ⟨_, _, _, _, k12, d, h⟩ := peelV (R := ShapesKept) (by walkA) (by keepsM) h d
  obtain ⟨_, _, _, _, k13, d, h⟩ := peelV (R := ShapesKept) (by walkA) (by keepsM) h d
  obtain ⟨_, _, _, _, k14, d, h⟩ := peelV (R := ShapesKept) (by walkA) (by keepsM) h d
  obtain ⟨_, _, _, _, k15, d, h⟩ := peelV (R := ShapesKept) (by walkA) (by keepsM) h d
  obtain ⟨_, _, _, _, k16, d, h⟩ := peelV (R := ShapesKept) (by walkA) (by keepsM) h d
  obtain ⟨_, _, _, _, k17, d, h⟩ := peelV (R := ShapesKept) (by walkA) (by keepsM) h d
  obtain ⟨_, _, _, _, k18, d, h⟩ := peelV (R := ShapesKept) (by walkA) (by keepsM) h d
  obtain ⟨_, _, _, _, k19, d, h⟩ := peelV (R := ShapesKept) (by walkA) (by keepsM) h d
  obtain ⟨_, _, _, _, k20, d, h⟩ := peelV (R := ShapesKept) (by walkA) (by keepsM) h d
  obtain ⟨_, _, _, _, k21, d, h⟩ := peelV (R := ShapesKept) (by walkA) (by keepsM) h d
  obtain ⟨_, _, _, _, k22, d, h⟩ := peelV (R := ShapesKept) (by walkA) (by keepsM) h d
  obtain ⟨_, _, _, _, k23, d, h⟩ := peelV (R := ShapesKept) (by walkA) (by keepsM) h d
  obtain ⟨_, _, _, _, k24, d, h⟩ := peelV (R := ShapesKept) (by walkA) (by keepsM) h d
  obtain ⟨_, _, _, _, k25, d, h⟩ := peelV (R := ShapesKept) (by walkA) (by keepsM) h d
  obtain ⟨_, _, _, _, k26, d, h⟩ := peelV (R := ShapesKept) (by walkA) (by keepsM) h d
  obtain ⟨_, _, _, _, k27, d, h⟩ := peelV (R := ShapesKept) (by walkA) (by keepsM) h d
  dsimp only at h
  split at h
  all_goals
    obtain ⟨_, _, _, _, k28, d, h⟩ := peelV (R := ShapesKept) (by walkA) (by keepsM) h d
    obtain ⟨_, _, _, _, k29, d, h⟩ := peelV (R := ShapesKept) (by walkA) (by keepsM) h d
    obtain ⟨_, _, _, _, k30, d, h⟩ := peelV (R := ShapesKept) (by walkA) (by keepsM) h d
    obtain ⟨_, _, _, _, k31, d, h⟩ := peelV (R := ShapesKept) (by walkA) (by keepsM) h d
    obtain ⟨tl, Lo, G, c9, ho, d, h⟩ := bindV (by keepsM) h d
    obtain ⟨ho, -⟩ := liftSubL_ok _ _ _ _ _ _ _ _ ho
    obtain ⟨_, _, _, _, f1, d, h⟩ := peelV (R := FrameKept) (by walkA) (by keepsM) h d
    obtain ⟨_, _, _, _, f2, d, h⟩ := peelV (R := FrameKept) (by walkA) (by keepsM) h d
    obtain ⟨_, _, _, _, f3, d, h⟩ := peelV (R := FrameKept) (by walkA) (by keepsM) h d
    obtain ⟨_, _, _, _, f4, d, h⟩ := peelV (R := FrameKept) (by walkA) (by keepsM) h d
    obtain ⟨_, _, _, _, f5, d, h⟩ := peelV (R := FrameKept) (by walkA) (by keepsM) h d
    obtain ⟨_, _, _, _, f6, d, h⟩ := peelV (R := FrameKept) (by walkA) (by keepsM) h d
    obtain ⟨_, _, _, _, f7, d, h⟩ := peelV (R := FrameKept) (by walkA) (by keepsM) h d
    obtain ⟨_, _, _, _, f8, d, h⟩ := peelV (R := FrameKept) (by walkA) (by keepsM) h d
    obtain ⟨_, _, _, _, f9, d, h⟩ := peelV (R := FrameKept) (by walkA) (by keepsM) h d
    obtain ⟨_, _, _, _, f10, d, h⟩ := peelV (R := FrameKept) (by walkA) (by keepsM) h d
    obtain ⟨_, _, _, _, f11, d, h⟩ := peelV (R := FrameKept) (by walkA) (by keepsM) h d
    obtain ⟨_, L7, F7, c7, h7, h⟩ := (bindL_ok _ _ _ _ _ _).1 h
    obtain ⟨s7, -⟩ := liftSubL_ok _ _ _ _ _ _ _ _ h7
    obtain ⟨eF7, ec7⟩ := selfTestF_both tl _ _ _ _ _ s7
    obtain ⟨_, L8, F8, c8, h8, h⟩ := (bindL_ok _ _ _ _ _ _).1 h
    obtain ⟨s8, -⟩ := liftSubL_ok _ _ _ _ _ _ _ _ h8
    obtain ⟨-, ec8⟩ := Port.coefficientsF_rest tl _ _ _ _ s8
    obtain ⟨_, L9, F9, c9', h9, h⟩ := (bindL_ok _ _ _ _ _ _).1 h
    obtain ⟨s9, -⟩ := liftSubL_ok _ _ _ _ _ _ _ _ h9
    rw [eF7, ec7] at s8
    rw [ec8, ec7] at s9
    rw [ec8] at s8
    rw [ec7] at s8
    refine ⟨o.funs, tl1, tlA, tl, _, G, _, F8, F9, _, c9, _, c9', d, hclosed,
      transcriptF_record htr, ?_, ho, ?_, s8, s9⟩
    · exact
        (((((((((((((((((((((((((((((((k1.trans k2).trans k3).trans k4).trans k5).trans k6).trans
        k7).trans k8).trans k8b).trans k9).trans k10).trans k11).trans k12).trans k13).trans
        k14).trans k15).trans k16).trans k17).trans k18).trans k19).trans k20).trans k21).trans
        k22).trans k23).trans k24).trans k25).trans k26).trans k27).trans k28).trans k29).trans
        k30).trans k31)
    · exact
        ((((((((((f1.trans f2).trans f3).trans f4).trans f5).trans f6).trans f7).trans f8).trans
        f9).trans f10).trans f11)

/-- `head_ran` for a check that began on a view. -/
theorem head_ranV (hS : Head.Shape) (Lh : Head.HL) (b : Head.Border) (hp : Head.HPlanH2)
    (O : Head.Owner) (cov : Head.Covered) (wsLay : WsLay) (L L' : LinkCtx) (F0 F' : Fork)
    (c c' : Ctx) (wo : WsForkOut)
    (h : Head.runForkHidH2 hS Lh b hp O cov wsLay L F0 c = .ok (((wo, L'), F'), c'))
    (d : c.ch.dry = false) :
    ∃ (funs : Array HFun) (tl1 tlA tl : HTailF2) (F7 G F10 F11 F12 : Fork) (c7 c9 cT cT' : Ctx),
      cT.ch.dry = false ∧ hp.tl.closeFuns funs = some tl1 ∧ RecordKept tl1 tlA ∧ ShapesKept F0 F7 ∧
      tlA.objectsF funs F7 c7 = .ok ((tl, G), c9) ∧ FrameKept G F10 ∧
      tl.coefficientsF F10 cT = .ok (((), F11), cT) ∧
      tl.tileSelfTestF F11 cT = .ok (((), F12), cT') := by
  unfold Head.runForkHidH2 at h
  obtain ⟨_, _, _, _, k1, d, h⟩ := peelV (R := ShapesKept) (by walkA) (by keepsM) h d
  obtain ⟨_, _, _, _, k2, d, h⟩ := peelV (R := ShapesKept) (by walkA) (by keepsM) h d
  obtain ⟨_, _, _, _, k3, d, h⟩ := peelV (R := ShapesKept) (by walkA) (by keepsM) h d
  obtain ⟨_, _, _, _, k4, d, h⟩ := peelV (R := ShapesKept) (by walkA) (by keepsM) h d
  obtain ⟨_, _, _, _, k5, d, h⟩ := peelV (R := ShapesKept) (by walkA) (by keepsM) h d
  obtain ⟨_, _, _, _, k6, d, h⟩ := peelV (R := ShapesKept) (by walkA) (by keepsM) h d
  obtain ⟨_, _, _, _, k7, d, h⟩ := peelV (R := ShapesKept) (by walkA) (by keepsM) h d
  obtain ⟨x, _, _, _, k8, d, h⟩ := peelV (R := ShapesKept) (by walkA) (by keepsM) h d
  obtain ⟨_, _, _, _, k9, d, h⟩ := peelV (R := ShapesKept) (by walkA) (by keepsM) h d
  obtain ⟨t, _, F10p, _, k10, d, h⟩ := peelV (R := ShapesKept) (by walkA) (by keepsM) h d
  obtain ⟨tl1, La, Fa, ca, hc, d, h⟩ := bindV (by keepsM) h d
  obtain ⟨hc, -, eFa⟩ := liftBlkL_ok _ _ _ _ _ _ _ _ hc
  obtain ⟨hclosed, -⟩ := getAs_ok _ _ _ _ _ hc
  have k10b : ShapesKept F10p Fa := by
    rw [eFa]
    exact ShapesKept.refl _
  obtain ⟨tlA, Lb, Fb, cb, htr, d, h⟩ := bindV (by keepsM) h d
  have k11 := (inferInstance : PresL ShapesKept tl1.transcriptF).out _ _ _ _ _ _ _ htr
  obtain ⟨_, _, _, _, k12, d, h⟩ := peelV (R := ShapesKept) (by walkA) (by keepsM) h d
  obtain ⟨_, _, _, _, k13, d, h⟩ := peelV (R := ShapesKept) (by walkA) (by keepsM) h d
  obtain ⟨_, _, _, _, k14, d, h⟩ := peelV (R := ShapesKept) (by walkA) (by keepsM) h d
  obtain ⟨_, _, _, _, k15, d, h⟩ := peelV (R := ShapesKept) (by walkA) (by keepsM) h d
  obtain ⟨_, _, _, _, k16, d, h⟩ := peelV (R := ShapesKept) (by walkA) (by keepsM) h d
  obtain ⟨_, _, _, _, k17, d, h⟩ := peelV (R := ShapesKept) (by walkA) (by keepsM) h d
  obtain ⟨_, _, _, _, k18, d, h⟩ := peelV (R := ShapesKept) (by walkA) (by keepsM) h d
  obtain ⟨tl, Lw, Fw, cw, hw, d, h⟩ := bindV (by keepsM) h d
  obtain ⟨_, Ls, Fs, cs, hs, h⟩ := (bindL_ok _ _ _ _ _ _).1 h
  obtain ⟨F7, c7, G, c9, kb, hobj, ka⟩ := head_walk_ran _ _ _ _ _ _ _ _ _ _ hw
  obtain ⟨F11, hco, htile⟩ := head_selfTests_ran _ _ _ _ _ _ _ _ _ hs
  refine ⟨_, tl1, tlA, tl, F7, G, Fw, F11, Fs, c7, c9, cw, cs, d, hclosed,
    transcriptF_record htr, ?_, hobj, ka, hco, htile⟩
  exact
    (((((((((((((((((((k1.trans k2).trans k3).trans k4).trans k5).trans k6).trans k7).trans
    k8).trans k9).trans k10).trans k10b).trans k11).trans k12).trans k13).trans k14).trans
    k15).trans k16).trans k17).trans k18).trans kb.shapes)

end OnBytes.Tie.Pv.Tail.Walk

namespace OnBytes.Tie.Pv.Tail
open OnBytes OnBytes.Model OnBytes.Tie.Pv.Tail.Port OnBytes.Tie.Pv.Tail.Walk

variable {K : Type} [CommRing K] (ρ : Reading K)

/-- `RawRows` at the check of a layer group's sub-proof, from the plan's run and one run of the
check that begins at the plan's state and on a view. -/
theorem rawRows_layer_view (P : Layer.Pub) (g : Nat) (O : Option Layer.HPlan2)
    (hp : Layer.HPlan2) (L L' : LinkCtx) (F' : Fork) (c c' : Ctx) (wo : WsForkOut)
    (hplan : Layer.planG P g O = .ok hp)
    (h : Layer.runForkHidG2 P hp g L hp.Fp c = .ok (((wo, L'), F'), c'))
    (d : c.ch.dry = false) :
    ∃ (funs : Array HFun) (tlA tl : HTailF2) (F7 G F10 F11 : Fork) (c7 c9 cT : Ctx),
      tlA.objectsF funs F7 c7 = .ok ((tl, G), c9) ∧
      tl.coefficientsF F10 cT = .ok (((), F11), cT) ∧
      ∀ (W : World K) (A : Nat → Nat → Nat → K),
        ReadsRaw ρ tl funs F11 W A → RawRows W tlA G funs (ρ.val G.theta) A := by
  obtain ⟨tl0, tla, Fa, Ta, nU, aTX, hb, hbLine, hadd, hrec, eF⟩ := planG_ok P g O hp hplan
  obtain ⟨funs, tl1, tlA, tl, F7, G, F10, F11, F12, c7, c9, cT, cT', hv, hclosed, hrk, kS, hobj,
    kF, hco, htile⟩ := layer_ranV P hp g L L' hp.Fp F' c c' wo h d
  have a9 := (inferInstance : Pres ShapesKept (tlA.objectsF funs)).out _ _ _ _ _ hobj
  have k0 : ShapesKept Fa hp.Fp := by
    rw [eF]
    exact trimL_shapes Fa
  exact ⟨funs, tlA, tl, F7, G, F10, F11, c7, c9, cT, hobj, hco, fun W A hW =>
    rawRows_kept ρ tl0 tla tlA tl funs {} Fa F7 G F10 F11 F12 {} Ta nU aTX hb hbLine
      c7 c9 cT cT cT cT' W A hadd ((hrec.trans (closeFuns_record hclosed)).trans hrk) hobj
      ((k0.trans kS).trans a9) kF hco hv htile hW⟩

/-- `RawRows` at the check of the head's sub-proof, from the plan's run and one run of the check
that begins at the plan's state and on a view. -/
theorem rawRows_head_view (g : Settings) (hS : Head.Shape) (Lh : Head.HL) (b : Head.Border)
    (O : Head.Owner) (NGr lkW : Nat) (hp : Head.HPlanH2) (cov : Head.Covered) (wsLay : WsLay)
    (L L' : LinkCtx) (F' : Fork) (c c' : Ctx) (wo : WsForkOut)
    (hplan : Head.planH2 g hS Lh b O NGr lkW = .ok hp)
    (h : Head.runForkHidH2 hS Lh b hp O cov wsLay L hp.Fp c = .ok (((wo, L'), F'), c'))
    (d : c.ch.dry = false) :
    ∃ (funs : Array HFun) (tlA tl : HTailF2) (F7 G F10 F11 : Fork) (c7 c9 cT : Ctx),
      tlA.objectsF funs F7 c7 = .ok ((tl, G), c9) ∧
      tl.coefficientsF F10 cT = .ok (((), F11), cT) ∧
      ∀ (W : World K) (A : Nat → Nat → Nat → K),
        ReadsRaw ρ tl funs F11 W A → RawRows W tlA G funs (ρ.val G.theta) A := by
  obtain ⟨tl0, tla, Ta, nU, aTX, hb, hbLine, hadd, hrec⟩ := planH2_ok g hS Lh b O NGr lkW hp hplan
  obtain ⟨funs, tl1, tlA, tl, F7, G, F10, F11, F12, c7, c9, cT, cT', hv, hclosed, hrk, kS, hobj,
    kF, hco, htile⟩ := head_ranV hS Lh b hp O cov wsLay L L' hp.Fp F' c c' wo h d
  have a9 := (inferInstance : Pres ShapesKept (tlA.objectsF funs)).out _ _ _ _ _ hobj
  exact ⟨funs, tlA, tl, F7, G, F10, F11, c7, c9, cT, hobj, hco, fun W A hW =>
    rawRows_kept ρ tl0 tla tlA tl funs {} hp.Fp F7 G F10 F11 F12 {} Ta nU aTX hb hbLine
      c7 c9 cT cT cT cT' W A hadd ((hrec.trans (closeFuns_record hclosed)).trans hrk) hobj
      (kS.trans a9) kF hco hv htile hW⟩

/-- `RawRows` at the check of an attention sub-proof, from the plan's run and one run of the check
that begins at the plan's state and on a view. -/
theorem rawRows_attention_view (s0 : Attention.Seam) (P : Attention.Plan) (nU3 hb hbLine : Nat)
    (L L' : LinkCtx) (F' : Fork) (c c' : Ctx) (hplan : s0.plan nU3 hb hbLine = .ok P.seam)
    (h : Attention.run P L P.seam.Fp c = .ok ((((), L'), F'), c')) (d : c.ch.dry = false) :
    ∃ (funs : Array HFun) (tlA tl : HTailF2) (F7 G F10 F11 : Fork) (c7 c9 cT cT' : Ctx),
      tlA.objectsF funs F7 c7 = .ok ((tl, G), c9) ∧
      tl.coefficientsF F10 cT = .ok (((), F11), cT') ∧
      ∀ (W : World K) (A : Nat → Nat → Nat → K),
        ReadsRaw ρ tl funs F11 W A → RawRows W tlA G funs (ρ.val G.theta) A := by
  obtain ⟨tl0, f, t, tl1, tlA, tl, laid, L1, L2, L3, L4, F1, F2, F3, F4, F5, F6, F7, F8, F9, F10,
    F11, F12, F13, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, X⟩ :=
    OnBytes.L5.attention_ran P d h
  exact ⟨t.funs, tlA, tl, F7, F8, F10, F11, c8, c9, c11, c12, X.objects, X.coefficients,
    fun W A hW => rawRows_attention_runs ρ s0 P nU3 hb hbLine _ f [P.iU3] t.funs P.ns P.nLin _
      P.nMsg P.seam.nU tl0 tl1 tlA tl L L1 L2 L3 L4 F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12
      c c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 W A hplan X.start X.hear X.root X.closed
      X.transcript X.setPlan X.batch X.claims X.objects X.noFree X.selfTest X.coefficients X.v12
      X.tile hW⟩

end OnBytes.Tie.Pv.Tail

#print axioms OnBytes.Tie.Pv.Tail.rawRows_attention_view
#print axioms OnBytes.Tie.Pv.Tail.Walk.layer_ranV
#print axioms OnBytes.Tie.Pv.Tail.Walk.head_ranV
#print axioms OnBytes.Tie.Pv.Tail.rawRows_layer_view
#print axioms OnBytes.Tie.Pv.Tail.rawRows_head_view
