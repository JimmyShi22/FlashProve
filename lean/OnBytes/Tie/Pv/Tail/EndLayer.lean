-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Tail/EndLayer.lean: the premise `RawRows` of the theorems on what objectsF adds
(OnBytes/Tie/Pv/Tail/EndAll.lean, EndSpread.lean), at the check of a layer group's sub-proof
(`Layer.runForkHidG2`, OnBytes/Model/Layer.lean), from one run of the whole check.

Definitions, and theorems with their proofs.

Main names:
  `peelBy`: a run of «x, then f», where x keeps R: f has run from a state that stands in R to the
    first.
  `walkA`: the walk through the text of a routine that also calls the chain, down into the routines
    of the sub-proof that it lifts.
  `layer_ran`: a run of the check holds: the closing of the list of tables; a run of objectsF; the
    runs of the routine that sets the row weights and of the test of the weights, both in one
    context; the arrays' shapes are kept from the check's first state to objectsF, shapes and
    batching element from objectsF to the state at which the row weights are set; the record's
    numbers of the arrays, blocks and lengths are kept from the closed list to objectsF.
  `rawRows_layer_run`: `RawRows` as the theorems on objectsF ask it.

Limits: the premises on the plan stay: the run of addTreesF, that the plan's record has its arrays'
numbers, blocks and lengths (`RecordKept`), and that the check begins at a state with the shapes
that addTreesF left (`ShapesKept`). The context in which the weights are tested must be a view, not
a dry run: that it is one where the check began on a view is not shown here.


-/
import OnBytes.Tie.Pv.Tail.EndHead
import OnBytes.Tie.Pv.Tail.EndWalkLayer

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Tail.Walk
open OnBytes OnBytes.Model OnBytes.Tie.Pv.Tail

variable {R : Fork → Fork → Prop}

/-- A run of «x, then f», where x keeps R: f has run from a state that stands in R to the first. -/
theorem peelBy {α β : Type} {x : LinkM α} {f : α → LinkM β} (hx : PresL R x) {L : LinkCtx}
    {F : Fork} {c : Ctx} {r : ((β × LinkCtx) × Fork) × Ctx} (h : (x >>= f) L F c = .ok r) :
    ∃ a L1 F1 c1, R F F1 ∧ f a L1 F1 c1 = .ok r := by
  obtain ⟨a, L1, F1, c1, h1, h2⟩ := (bindL_ok _ _ _ _ _ _).1 h
  exact ⟨a, L1, F1, c1, hx.out _ _ _ _ _ _ _ h1, h2⟩

/-- A lifted routine of the sub-proof keeps what the routine keeps. -/
theorem presL_subOf {α : Type} {x : SubM α} (hx : Pres R x) : PresL R (LinkM.sub x) :=
  @presL_sub R α x hx

/-- The same, as the checks' texts write a lift. -/
theorem presL_liftOf {α : Type} {x : SubM α} (hx : Pres R x) : PresL R (liftM x : LinkM α) :=
  @presL_sub R α x hx

/-- One step of the walk through the text of a routine that also calls the chain, down into the
routines of the sub-proof that it lifts. -/
macro "walkA_step" : tactic => `(tactic| first
  | walkL_step | refine presL_subOf ?_ | refine presL_liftOf ?_ | walk2_step)

/-- The walk through the text of a routine that also calls the chain. -/
macro "walkA" : tactic => `(tactic| repeat' walkA_step)

/-- A run of the check of a layer group's sub-proof, as far as the smallness test's claims go. -/
theorem layer_ran (P : Layer.Pub) (hp : Layer.HPlan2) (g : Nat) (L L' : LinkCtx) (F0 F' : Fork)
    (c c' : Ctx) (wo : WsForkOut)
    (h : Layer.runForkHidG2 P hp g L F0 c = .ok (((wo, L'), F'), c')) :
    ∃ (funs : Array HFun) (tl1 tlA tl : HTailF2) (F7 G F10 F11 F12 : Fork) (c7 c9 cT cT' : Ctx),
      hp.tl.closeFuns funs = some tl1 ∧ RecordKept tl1 tlA ∧ ShapesKept F0 F7 ∧
      tlA.objectsF funs F7 c7 = .ok ((tl, G), c9) ∧ FrameKept G F10 ∧
      tl.coefficientsF F10 cT = .ok (((), F11), cT) ∧
      tl.tileSelfTestF F11 cT = .ok (((), F12), cT') := by
  unfold Layer.runForkHidG2 at h
  obtain ⟨_, _, _, _, k1, h⟩ := peelBy (R := ShapesKept) (by walkA) h
  obtain ⟨_, _, _, _, k2, h⟩ := peelBy (R := ShapesKept) (by walkA) h
  obtain ⟨_, _, _, _, k3, h⟩ := peelBy (R := ShapesKept) (by walkA) h
  obtain ⟨_, _, _, _, k4, h⟩ := peelBy (R := ShapesKept) (by walkA) h
  obtain ⟨_, _, _, _, k5, h⟩ := peelBy (R := ShapesKept) (by walkA) h
  obtain ⟨_, _, _, _, k6, h⟩ := peelBy (R := ShapesKept) (by walkA) h
  obtain ⟨o, _, _, _, k7, h⟩ := peelBy (R := ShapesKept) (by walkA) h
  obtain ⟨_, _, F8p, _, k8, h⟩ := peelBy (R := ShapesKept) (by walkA) h
  obtain ⟨tl1, La, Fa, ca, hc, h⟩ := (bindL_ok _ _ _ _ _ _).1 h
  obtain ⟨hc, -⟩ := (subL_ok _ _ _ _ _ _ _ _).1 hc
  obtain ⟨hclosed, eFa, -⟩ := (Port.get_ok _ _ _ _ _ _).1 hc
  have k8b : ShapesKept F8p Fa := by
    rw [eFa]
    exact ShapesKept.refl _
  obtain ⟨tlA, Lb, Fb, cb, htr, h⟩ := (bindL_ok _ _ _ _ _ _).1 h
  have k9 := (inferInstance : PresL ShapesKept tl1.transcriptF).out _ _ _ _ _ _ _ htr
  obtain ⟨_, _, _, _, k10, h⟩ := peelBy (R := ShapesKept) (by walkA) h
  obtain ⟨_, _, _, _, k11, h⟩ := peelBy (R := ShapesKept) (by walkA) h
  obtain ⟨_, _, _, _, k12, h⟩ := peelBy (R := ShapesKept) (by walkA) h
  obtain ⟨_, _, _, _, k13, h⟩ := peelBy (R := ShapesKept) (by walkA) h
  obtain ⟨_, _, _, _, k14, h⟩ := peelBy (R := ShapesKept) (by walkA) h
  obtain ⟨_, _, _, _, k15, h⟩ := peelBy (R := ShapesKept) (by walkA) h
  obtain ⟨_, _, _, _, k16, h⟩ := peelBy (R := ShapesKept) (by walkA) h
  obtain ⟨_, _, _, _, k17, h⟩ := peelBy (R := ShapesKept) (by walkA) h
  obtain ⟨_, _, _, _, k18, h⟩ := peelBy (R := ShapesKept) (by walkA) h
  obtain ⟨_, _, _, _, k19, h⟩ := peelBy (R := ShapesKept) (by walkA) h
  obtain ⟨_, _, _, _, k20, h⟩ := peelBy (R := ShapesKept) (by walkA) h
  obtain ⟨_, _, _, _, k21, h⟩ := peelBy (R := ShapesKept) (by walkA) h
  obtain ⟨_, _, _, _, k22, h⟩ := peelBy (R := ShapesKept) (by walkA) h
  obtain ⟨_, _, _, _, k23, h⟩ := peelBy (R := ShapesKept) (by walkA) h
  obtain ⟨_, _, _, _, k24, h⟩ := peelBy (R := ShapesKept) (by walkA) h
  obtain ⟨_, _, _, _, k25, h⟩ := peelBy (R := ShapesKept) (by walkA) h
  obtain ⟨_, _, _, _, k26, h⟩ := peelBy (R := ShapesKept) (by walkA) h
  obtain ⟨_, _, _, _, k27, h⟩ := peelBy (R := ShapesKept) (by walkA) h
  dsimp only at h
  split at h
  all_goals
    obtain ⟨_, _, _, _, k28, h⟩ := peelBy (R := ShapesKept) (by walkA) h
    obtain ⟨_, _, _, _, k29, h⟩ := peelBy (R := ShapesKept) (by walkA) h
    obtain ⟨_, _, _, _, k30, h⟩ := peelBy (R := ShapesKept) (by walkA) h
    obtain ⟨_, _, _, _, k31, h⟩ := peelBy (R := ShapesKept) (by walkA) h
    obtain ⟨tl, Lo, G, c9, ho, h⟩ := (bindL_ok _ _ _ _ _ _).1 h
    obtain ⟨ho, -⟩ := liftSubL_ok _ _ _ _ _ _ _ _ ho
    obtain ⟨_, _, _, _, f1, h⟩ := peelBy (R := FrameKept) (by walkA) h
    obtain ⟨_, _, _, _, f2, h⟩ := peelBy (R := FrameKept) (by walkA) h
    obtain ⟨_, _, _, _, f3, h⟩ := peelBy (R := FrameKept) (by walkA) h
    obtain ⟨_, _, _, _, f4, h⟩ := peelBy (R := FrameKept) (by walkA) h
    obtain ⟨_, _, _, _, f5, h⟩ := peelBy (R := FrameKept) (by walkA) h
    obtain ⟨_, _, _, _, f6, h⟩ := peelBy (R := FrameKept) (by walkA) h
    obtain ⟨_, _, _, _, f7, h⟩ := peelBy (R := FrameKept) (by walkA) h
    obtain ⟨_, _, _, _, f8, h⟩ := peelBy (R := FrameKept) (by walkA) h
    obtain ⟨_, _, _, _, f9, h⟩ := peelBy (R := FrameKept) (by walkA) h
    obtain ⟨_, _, _, _, f10, h⟩ := peelBy (R := FrameKept) (by walkA) h
    obtain ⟨_, _, _, _, f11, h⟩ := peelBy (R := FrameKept) (by walkA) h
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
    refine ⟨o.funs, tl1, tlA, tl, _, G, _, F8, F9, _, c9, _, c9', hclosed, transcriptF_record htr,
      ?_,
      ho, ?_, s8, s9⟩
    · exact
        (((((((((((((((((((((((((((((((k1.trans k2).trans k3).trans k4).trans k5).trans k6).trans
        k7).trans k8).trans k8b).trans k9).trans k10).trans k11).trans k12).trans k13).trans
        k14).trans
        k15).trans k16).trans k17).trans k18).trans k19).trans k20).trans k21).trans k22).trans
        k23).trans k24).trans k25).trans k26).trans k27).trans k28).trans k29).trans k30).trans k31)
    · exact
        ((((((((((f1.trans f2).trans f3).trans f4).trans f5).trans f6).trans f7).trans f8).trans
        f9).trans f10).trans f11)

end OnBytes.Tie.Pv.Tail.Walk

namespace OnBytes.Tie.Pv.Tail
open OnBytes OnBytes.Model OnBytes.Tie.Pv.Tail.Port OnBytes.Tie.Pv.Tail.Walk

variable {K : Type} [CommRing K] (ρ : Reading K)

/-- `RawRows` as the theorems on objectsF ask it, at the check of a layer group's sub-proof: a run
of objectsF, the state F11 at which the weights are tested and the context cT of that test; and, if
cT is a view, `RawRows` in every world that reads the four kinds of virtual row at F11 as sums of
the arrays' entries. -/
theorem rawRows_layer_run (tl0 tla : HTailF2) (Fz Fa : Fork) (Tz Ta : Tail2) (nU aTX : Array Nat)
    (hb hbLine : Nat) (P : Layer.Pub) (hp : Layer.HPlan2) (g : Nat) (L L' : LinkCtx)
    (F0 F' : Fork) (c c' : Ctx) (wo : WsForkOut)
    (hadd : tl0.addTreesF Fz Tz nU aTX hb hbLine = .ok (tla, Fa, Ta))
    (hrec : RecordKept tla hp.tl) (hk0 : ShapesKept Fa F0)
    (h : Layer.runForkHidG2 P hp g L F0 c = .ok (((wo, L'), F'), c')) :
    ∃ (funs : Array HFun) (tlA tl : HTailF2) (F7 G F10 F11 : Fork) (c7 c9 cT : Ctx),
      tlA.objectsF funs F7 c7 = .ok ((tl, G), c9) ∧
      tl.coefficientsF F10 cT = .ok (((), F11), cT) ∧
      (cT.ch.dry = false → ∀ (W : World K) (A : Nat → Nat → Nat → K),
        ReadsRaw ρ tl funs F11 W A → RawRows W tlA G funs (ρ.val G.theta) A) := by
  obtain ⟨funs, tl1, tlA, tl, F7, G, F10, F11, F12, c7, c9, cT, cT', hclosed, hrk, kS, hobj, kF,
    hco, htile⟩ := layer_ran P hp g L L' F0 F' c c' wo h
  have a9 := (inferInstance : Pres ShapesKept (tlA.objectsF funs)).out _ _ _ _ _ hobj
  exact ⟨funs, tlA, tl, F7, G, F10, F11, c7, c9, cT, hobj, hco, fun hv W A hW =>
    rawRows_kept ρ tl0 tla tlA tl funs Fz Fa F7 G F10 F11 F12 Tz Ta nU aTX hb hbLine
      c7 c9 cT cT cT cT' W A hadd ((hrec.trans (closeFuns_record hclosed)).trans hrk) hobj
      ((hk0.trans kS).trans a9) kF hco hv htile hW⟩

end OnBytes.Tie.Pv.Tail

#print axioms OnBytes.Tie.Pv.Tail.Walk.layer_ran
#print axioms OnBytes.Tie.Pv.Tail.rawRows_layer_run
