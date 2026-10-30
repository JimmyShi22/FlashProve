-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Tail/EndPlans.lean: the premise `RawRows` of the theorems on what objectsF adds
(OnBytes/Tie/Pv/Tail/EndAll.lean, EndSpread.lean), at the checks of a layer group's and of the
head's sub-proof, from the plan's run and one run of the check that begins at the plan's state.

Theorems with their proofs. OnBytes/Tie/Pv/Tail/EndLayer.lean and EndHeadRun.lean ask three things
of the plan: a run of addTreesF, that the plan's record has its arrays' numbers, blocks and lengths,
and that the check begins at a state with the shapes that addTreesF left. Here the plans
(`Layer.planG`, OnBytes/Model/LayerPlan.lean; `Head.planH2`, OnBytes/Model/HeadPlan.lean) are taken
apart, and the three follow.

Main names:
  `trimL_shapes`: taking the column weights off every virtual row keeps the shapes.
  `planG_ok`, `planH2_ok`: a plan's run holds a run of addTreesF; the plan's record keeps what
    addTreesF returned; the plan's state is the one that addTreesF returned (for a layer group:
    without the column weights).
  `ownerHeld_record`: the comparison with the plan of the last group of layers keeps the record's
    three fields.
  `rawRows_layer_plan`, `rawRows_head_plan`: `RawRows` as the theorems on objectsF ask it.

Limits: the check must begin at the plan's state. The context in which the weights are tested must
be a view, not a dry run: that it is one where the check began on a view is not shown here. The
world reads the four kinds of virtual row as sums of the arrays' entries (`ReadsRaw`,
OnBytes/Tie/Pv/Tail/EndRaw.lean).


-/
import OnBytes.Tie.Pv.Tail.EndHeadRun

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Tail
open OnBytes OnBytes.Model OnBytes.Tie.Pv.Tail.Port OnBytes.Tie.Pv.Tail.Walk

/-- Taking the column weights off every virtual row keeps the shapes. -/
theorem trimL_shapes (F : Fork) : ShapesKept F F.trimL := by
  refine ⟨by simp [Fork.trimL], fun t => ?_⟩
  unfold shapeAt Fork.trimL
  by_cases ht : t < F.trees.size
  · simp [Array.getD, ht]
  · simp [Array.getD, ht]

/-- The plan of a layer group's sub-proof, as far as the list of arrays goes. -/
theorem planG_ok (P : Layer.Pub) (g : Nat) (O : Option Layer.HPlan2) (hp : Layer.HPlan2)
    (h : Layer.planG P g O = .ok hp) :
    ∃ (tl0 tla : HTailF2) (Fa : Fork) (Ta : Tail2) (nU aTX : Array Nat) (hb hbLine : Nat),
      tl0.addTreesF {} {} nU aTX hb hbLine = .ok (tla, Fa, Ta) ∧ RecordKept tla hp.tl ∧
      hp.Fp = Fa.trimL := by
  unfold Layer.planG at h
  obtain ⟨⟨mats, txOf, ft⟩, -, h⟩ := (excBind_ok _ _ _).1 h
  obtain ⟨tl0, -, h⟩ := (excBind_ok _ _ _).1 h
  obtain ⟨⟨tla, Fa, Ta⟩, hadd, h⟩ := (excBind_ok _ _ _).1 h
  obtain ⟨Tp, -, h⟩ := (excBind_ok _ _ _).1 h
  obtain ⟨_, -, h⟩ := (excBind_ok _ _ _).1 h
  dsimp only at h
  cases O with
  | none =>
    dsimp only at h
    obtain ⟨_, -, h⟩ := (excBind_ok _ _ _).1 h
    obtain ⟨y, hy, h⟩ := (excBind_ok _ _ _).1 h
    obtain ⟨_, -, h⟩ := (excBind_ok _ _ _).1 h
    obtain rfl := Except.ok.inj hy
    obtain rfl := Except.ok.inj h
    exact ⟨_, _, _, _, _, _, _, _, hadd, ownerIs_record _ _, rfl⟩
  | some O =>
    dsimp only at h
    split at h
    · obtain ⟨y, -, h⟩ := (excBind_ok _ _ _).1 h
      obtain ⟨_, -, h⟩ := (excBind_ok _ _ _).1 h
      obtain ⟨_, -, h⟩ := (excBind_ok _ _ _).1 h
      obtain ⟨tlB, hbm, h⟩ := (excBind_ok _ _ _).1 h
      obtain ⟨_, -, h⟩ := (excBind_ok _ _ _).1 h
      obtain ⟨_, -, h⟩ := (excBind_ok _ _ _).1 h
      obtain ⟨y2, hy, h⟩ := (excBind_ok _ _ _).1 h
      obtain ⟨_, -, h⟩ := (excBind_ok _ _ _).1 h
      obtain rfl := Except.ok.inj hy
      obtain rfl := Except.ok.inj h
      exact ⟨_, _, _, _, _, _, _, _, hadd, (ownerIs_record _ _).trans (borderMeans_record hbm),
        rfl⟩
    · exact absurd h (throw_bind_ne _ _ _)

/-- The comparison with the plan of the last group of layers keeps the record's three fields. -/
theorem ownerHeld_record (O : Head.Owner) (NGr : Nat) (tl tl' : HTailF2) (Fp : Fork) (Tp : Tail2)
    (h : Head.ownerHeld O NGr tl Fp Tp = .ok tl') : RecordKept tl tl' := by
  unfold Head.ownerHeld at h
  dsimp only at h
  split at h
  · obtain ⟨y, -, h⟩ := (excBind_ok _ _ _).1 h
    obtain ⟨_, -, h⟩ := (excBind_ok _ _ _).1 h
    obtain ⟨_, -, h⟩ := (excBind_ok _ _ _).1 h
    obtain ⟨tlB, hbm, h⟩ := (excBind_ok _ _ _).1 h
    obtain ⟨_, -, h⟩ := (excBind_ok _ _ _).1 h
    obtain ⟨_, -, h⟩ := (excBind_ok _ _ _).1 h
    obtain rfl := Except.ok.inj h
    exact borderMeans_record hbm
  · exact absurd h (throw_bind_ne _ _ _)

/-- The plan of the head's sub-proof, as far as the list of arrays goes. -/
theorem planH2_ok (g : Settings) (hS : Head.Shape) (Lh : Head.HL) (b : Head.Border)
    (O : Head.Owner) (NGr lkW : Nat) (hp : Head.HPlanH2)
    (h : Head.planH2 g hS Lh b O NGr lkW = .ok hp) :
    ∃ (tl0 tla : HTailF2) (Ta : Tail2) (nU aTX : Array Nat) (hb hbLine : Nat),
      tl0.addTreesF {} {} nU aTX hb hbLine = .ok (tla, hp.Fp, Ta) ∧ RecordKept tla hp.tl := by
  unfold Head.planH2 at h
  obtain ⟨_, -, h⟩ := (excBind_ok _ _ _).1 h
  obtain ⟨_, -, h⟩ := (excBind_ok _ _ _).1 h
  obtain ⟨_, -, h⟩ := (excBind_ok _ _ _).1 h
  obtain ⟨_, -, h⟩ := (excBind_ok _ _ _).1 h
  obtain ⟨_, -, h⟩ := (excBind_ok _ _ _).1 h
  obtain ⟨_, -, h⟩ := (excBind_ok _ _ _).1 h
  dsimp only at h
  split at h
  · obtain ⟨_, -, h⟩ := (excBind_ok _ _ _).1 h
    obtain ⟨tl0, -, h⟩ := (excBind_ok _ _ _).1 h
    obtain ⟨_, -, h⟩ := (excBind_ok _ _ _).1 h
    obtain ⟨⟨tla, Fa, Ta⟩, hadd, h⟩ := (excBind_ok _ _ _).1 h
    obtain ⟨_, -, h⟩ := (excBind_ok _ _ _).1 h
    obtain ⟨Tp, -, h⟩ := (excBind_ok _ _ _).1 h
    obtain ⟨tlF, ho, h⟩ := (excBind_ok _ _ _).1 h
    obtain ⟨_, -, h⟩ := (excBind_ok _ _ _).1 h
    obtain rfl := Except.ok.inj h
    exact ⟨_, _, _, _, _, _, _, hadd, ownerHeld_record _ _ _ _ _ _ ho⟩
  · exact absurd h (throw_bind_ne _ _ _)

variable {K : Type} [CommRing K] (ρ : Reading K)

/-- `RawRows` at the check of a layer group's sub-proof, from the plan's run and one run of the
check that begins at the plan's state. -/
theorem rawRows_layer_plan (P : Layer.Pub) (g : Nat) (O : Option Layer.HPlan2)
    (hp : Layer.HPlan2) (L L' : LinkCtx) (F' : Fork) (c c' : Ctx) (wo : WsForkOut)
    (hplan : Layer.planG P g O = .ok hp)
    (h : Layer.runForkHidG2 P hp g L hp.Fp c = .ok (((wo, L'), F'), c')) :
    ∃ (funs : Array HFun) (tlA tl : HTailF2) (F7 G F10 F11 : Fork) (c7 c9 cT : Ctx),
      tlA.objectsF funs F7 c7 = .ok ((tl, G), c9) ∧
      tl.coefficientsF F10 cT = .ok (((), F11), cT) ∧
      (cT.ch.dry = false → ∀ (W : World K) (A : Nat → Nat → Nat → K),
        ReadsRaw ρ tl funs F11 W A → RawRows W tlA G funs (ρ.val G.theta) A) := by
  obtain ⟨tl0, tla, Fa, Ta, nU, aTX, hb, hbLine, hadd, hrec, eF⟩ := planG_ok P g O hp hplan
  exact rawRows_layer_run ρ tl0 tla {} Fa {} Ta nU aTX hb hbLine P hp g L L' hp.Fp F' c c' wo hadd
    hrec (by rw [eF]; exact trimL_shapes Fa) h

/-- `RawRows` at the check of the head's sub-proof, from the plan's run and one run of the check
that begins at the plan's state. -/
theorem rawRows_head_plan (g : Settings) (hS : Head.Shape) (Lh : Head.HL) (b : Head.Border)
    (O : Head.Owner) (NGr lkW : Nat) (hp : Head.HPlanH2) (cov : Head.Covered) (wsLay : WsLay)
    (L L' : LinkCtx) (F' : Fork) (c c' : Ctx) (wo : WsForkOut)
    (hplan : Head.planH2 g hS Lh b O NGr lkW = .ok hp)
    (h : Head.runForkHidH2 hS Lh b hp O cov wsLay L hp.Fp c = .ok (((wo, L'), F'), c')) :
    ∃ (funs : Array HFun) (tlA tl : HTailF2) (F7 G F10 F11 : Fork) (c7 c9 cT : Ctx),
      tlA.objectsF funs F7 c7 = .ok ((tl, G), c9) ∧
      tl.coefficientsF F10 cT = .ok (((), F11), cT) ∧
      (cT.ch.dry = false → ∀ (W : World K) (A : Nat → Nat → Nat → K),
        ReadsRaw ρ tl funs F11 W A → RawRows W tlA G funs (ρ.val G.theta) A) := by
  obtain ⟨tl0, tla, Ta, nU, aTX, hb, hbLine, hadd, hrec⟩ := planH2_ok g hS Lh b O NGr lkW hp hplan
  exact rawRows_head_run ρ tl0 tla {} hp.Fp {} Ta nU aTX hb hbLine hS Lh b hp O cov wsLay L L'
    hp.Fp F' c c' wo hadd hrec (ShapesKept.refl _) h

end OnBytes.Tie.Pv.Tail

#print axioms OnBytes.Tie.Pv.Tail.planG_ok
#print axioms OnBytes.Tie.Pv.Tail.planH2_ok
#print axioms OnBytes.Tie.Pv.Tail.rawRows_layer_plan
#print axioms OnBytes.Tie.Pv.Tail.rawRows_head_plan
