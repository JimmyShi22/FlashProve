-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Rows/ArmsOfFields.lean: THE TEST `armsB` (Johnson/LPFE1R/RowsAtArms.lean: the 26
links' arms off a public part X are the written ones) FROM WHAT `armOf` READS OF X: first as a law
at every X, then from written numbers, arm by arm. General laws, and closed equations between
written terms. Nothing is evaluated at any files. A law file; no running text imports it. Nothing on
codes.

Why. The maker of the rows of the sendings returns only at the planner's own arms, and no test of a
verifier holds the arms. An arm is some twenty small numbers. Here is said which, so that whoever
walks the makers of a public part at given files knows what to deliver, and delivers no more.

  `headArm X`, `layerArm X g`, `attArm X g`: the three kinds of arm as functions of X.
    `armOf_parts`: `armOf X link` is one of these, by X.p4, X.NGr and the link's number.
  `arm_congr`: **(1) two public parts with one p4, one NGr and these three alike have the same
    arms.** `arm_congr_fields`: the same from agreement on fields: HLy.fs · H.own hS · H.tl · y.fo ·
    at each g the layers' numbers, tl and nBatched (`sameLayer`) · at each g the attention's fs, own
    and seam.tl (`sameAtt`).
  `headArm_of`, `layerArm_of`, `attArm_of`, `attArm_none`: each arm from its three or four parts:
    the lookup's sizes (`forestSize`), the own numbers, the smallness test's sizes (`smallSize`),
    and for the layers the number of batched rows.
  `armsB_of_arms`: p4 · twelve groups · the 26 arms are `armAtW`'s ⊢ armsB X = true.
  `lookL`, `numsL g`, `smallL`, `claimsL g` · `lookA`, `ownA`, `smallA` · `lookH`, `ownH`, `smallH`:
    THE WRITTEN NUMBERS: laid here by program off the text of `armsW`
    (Johnson/LPFE1R/RowsAtWritten.lean). FOUR ARMS IN ALL: the first group's layers; every later
    group's layers (they part from the first in `firstGroup` and in the batched rows); the
    attention's, one at all twelve groups; the head's.
  `written_layers`, `written_attention`, `written_head`, `written_beyond`: these numbers ARE
    `armsW`'s, at each of the 26: by the kernel: no second list. `written_teeth`: three bent arms
    are not.
  `armsB_of_fields`: **(2) p4 · twelve groups · at each g < 12 a layers' plan with these four parts
    and an attention's plan with these three · no thirteenth attention's plan · the head's three
    parts ⊢ armsB X = true.**

Limits. EVERY PREMISE IS A PREMISE: NONE IS SHOWN HERE AT ANY FILES: NO MEMBER. THE DEBT IS CUT, NOT
LESSENED: under p4 and twelve groups the premises of `armsB_of_fields` say as much as armsB X =
true. Of them p4 and the twelve groups alone are had in scope from a law that lies
(`H2K.Sizes.PubFull`); the rest is paid only by a walk of the public part's makers at given files.
WHENCE `armsW`: an evaluator's print at the stored full-size example's public files (that file's
head): the numbers are no theorem on any files. The two laws (1) say what suffices; that an arm
moves with each of these parts is not said. `written_teeth` bites on closed arms: no tooth here is
on armsB at an X. Which fields of X the parts themselves read (`layerNumbers`, `HPlanH2.own`,
`smallSize`) is those definitions' to say. The full size alone. Nothing on what an arm means to a
plan. Nothing on soundness.

-/
import Johnson.LPFE1R.RowsAtArms

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFull.Rows
open OnBytes OnBytes.Params OnBytes.Model
open OnBytes.Model.Verify (Public layerNumbers)
open VerifiableInference.Desc.LinkJoin

/-! ## 1 What an arm reads -/

/-- The head's arm. -/
def headArm (X : Public) : Arm :=
  .head (forestSize X.HLy.fs) (X.H.own X.hS) (smallSize X.H.tl)

/-- The arm of the layers' group g; none where there is no such plan. -/
def layerArm (X : Public) (g : Nat) : Arm :=
  match X.G[g]? with
  | some hp => .layer (forestSize X.y.fo) (layerNumbers X.layers hp g) (smallSize hp.tl) hp.nBatched
  | none => .none

/-- The arm of the attention of group g; none where there is no such plan. -/
def attArm (X : Public) (g : Nat) : Arm :=
  match X.A[g]? with
  | some a => .attention (forestSize a.fs) a.own (smallSize a.seam.tl)
  | none => .none

/-- `armOf` in these three. -/
theorem armOf_parts (X : Public) (link : Nat) :
    armOf X link =
      if link == (if X.p4 then 2 else 1) * X.NGr then headArm X
      else if link % (if X.p4 then 2 else 1) == 0 then layerArm X (link / (if X.p4 then 2 else 1))
      else attArm X (link / (if X.p4 then 2 else 1)) := by
  unfold armOf headArm layerArm attArm
  rfl

/-- **(1) An arm hangs on these alone.** -/
theorem arm_congr {X X' : Public} (h4 : X.p4 = X'.p4) (hN : X.NGr = X'.NGr)
    (hH : headArm X = headArm X') (hL : ∀ g, layerArm X g = layerArm X' g)
    (hA : ∀ g, attArm X g = attArm X' g) (j : Nat) : armOf X j = armOf X' j := by
  rw [armOf_parts, armOf_parts, h4, hN, hH, hL, hA]

/-- What the law below asks of two layers' plans at one g, and of two attention's plans. -/
def sameLayer (X X' : Public) (g : Nat) : Prop :=
  match X.G[g]?, X'.G[g]? with
  | some hp, some hp' =>
    layerNumbers X.layers hp g = layerNumbers X'.layers hp' g ∧ hp.tl = hp'.tl ∧
      hp.nBatched = hp'.nBatched
  | none, none => True
  | _, _ => False

def sameAtt (X X' : Public) (g : Nat) : Prop :=
  match X.A[g]?, X'.A[g]? with
  | some a, some a' => a.fs = a'.fs ∧ a.own = a'.own ∧ a.seam.tl = a'.seam.tl
  | none, none => True
  | _, _ => False

/-- **(1), on fields**: two public parts that agree on these have the same arms. -/
theorem arm_congr_fields {X X' : Public} (h4 : X.p4 = X'.p4) (hN : X.NGr = X'.NGr)
    (e1 : X.HLy.fs = X'.HLy.fs) (e2 : X.H.own X.hS = X'.H.own X'.hS) (e3 : X.H.tl = X'.H.tl)
    (eo : X.y.fo = X'.y.fo) (hL : ∀ g, sameLayer X X' g) (hA : ∀ g, sameAtt X X' g) (j : Nat) :
    armOf X j = armOf X' j := by
  refine arm_congr h4 hN ?_ (fun g => ?_) (fun g => ?_) j
  · unfold headArm
    rw [e1, e2, e3]
  · have h := hL g
    unfold sameLayer at h
    unfold layerArm
    cases hg : X.G[g]? with
    | none =>
      cases hg' : X'.G[g]? with
      | none => rfl
      | some hp' =>
        rw [hg, hg'] at h
        exact False.elim h
    | some hp =>
      cases hg' : X'.G[g]? with
      | none =>
        rw [hg, hg'] at h
        exact False.elim h
      | some hp' =>
        rw [hg, hg'] at h
        obtain ⟨a1, a2, a3⟩ := h
        show Arm.layer _ _ _ _ = Arm.layer _ _ _ _
        rw [eo, a1, a2, a3]
  · have h := hA g
    unfold sameAtt at h
    unfold attArm
    cases hg : X.A[g]? with
    | none =>
      cases hg' : X'.A[g]? with
      | none => rfl
      | some a' =>
        rw [hg, hg'] at h
        exact False.elim h
    | some a =>
      cases hg' : X'.A[g]? with
      | none =>
        rw [hg, hg'] at h
        exact False.elim h
      | some a' =>
        rw [hg, hg'] at h
        obtain ⟨a1, a2, a3⟩ := h
        show Arm.attention _ _ _ = Arm.attention _ _ _
        rw [a1, a2, a3]

theorem headArm_of {X : Public} {l : ForestSize} {x : HeadRounds} {s : SmallSize}
    (e1 : forestSize X.HLy.fs = l) (e2 : X.H.own X.hS = x) (e3 : smallSize X.H.tl = s) :
    headArm X = .head l x s := by
  unfold headArm
  rw [e1, e2, e3]

theorem layerArm_of {X : Public} {g : Nat} {hp : Layer.HPlan2} {l : ForestSize} {x : LayerRounds}
    {s : SmallSize} {c : Nat} (hg : X.G[g]? = some hp) (e1 : forestSize X.y.fo = l)
    (e2 : layerNumbers X.layers hp g = x) (e3 : smallSize hp.tl = s) (e4 : hp.nBatched = c) :
    layerArm X g = .layer l x s c := by
  unfold layerArm
  rw [hg]
  show Arm.layer (forestSize X.y.fo) (layerNumbers X.layers hp g) (smallSize hp.tl) hp.nBatched = _
  rw [e1, e2, e3, e4]

theorem attArm_of {X : Public} {g : Nat} {a : Attention.Plan} {l : ForestSize}
    {x : AttentionRounds} {s : SmallSize} (hg : X.A[g]? = some a) (e1 : forestSize a.fs = l)
    (e2 : a.own = x) (e3 : smallSize a.seam.tl = s) : attArm X g = .attention l x s := by
  unfold attArm
  rw [hg]
  show Arm.attention (forestSize a.fs) a.own (smallSize a.seam.tl) = _
  rw [e1, e2, e3]

theorem attArm_none {X : Public} {g : Nat} (hg : X.A[g]? = none) : attArm X g = .none := by
  unfold attArm
  rw [hg]

/-! ## 2 From the arms to the test -/

/-- At profile 4. -/
theorem armOf_two {X : Public} (h4 : X.p4 = true) (link : Nat) :
    armOf X link =
      if link == 2 * X.NGr then headArm X
      else if link % 2 == 0 then layerArm X (link / 2) else attArm X (link / 2) := by
  rw [armOf_parts, h4]
  rfl

theorem arm_at_of_arms {X : Public} (h4 : X.p4 = true) (hN : X.NGr = 12)
    (hL : ∀ g, g < 12 → layerArm X g = armAtW (2 * g))
    (hA : ∀ g, g < 12 → attArm X g = armAtW (2 * g + 1)) (hH : headArm X = armAtW 24)
    (hE : attArm X 12 = armAtW 25) (j : Nat) (hj : j < 26) : armOf X j = armAtW j := by
  rw [armOf_two h4, hN]
  by_cases e24 : j = 24
  · subst e24
    rw [if_pos (by decide)]
    exact hH
  · rw [if_neg fun h => e24 (beq_iff_eq.1 h)]
    by_cases ev : j % 2 = 0
    · rw [if_pos (beq_iff_eq.2 ev), hL (j / 2) (by omega), show 2 * (j / 2) = j by omega]
    · rw [if_neg fun h => ev (beq_iff_eq.1 h)]
      by_cases hg : j / 2 < 12
      · rw [hA (j / 2) hg, show 2 * (j / 2) + 1 = j by omega]
      · obtain rfl : j = 25 := by omega
        exact hE

/-- The written list is the table `armAtW` at 0 to 25. -/
theorem armsW_table : armsW = (List.range 26).map armAtW := by decide +kernel

/-- **From the 26 arms.** -/
theorem armsB_of_arms {X : Public} (h4 : X.p4 = true) (hN : X.NGr = 12)
    (hL : ∀ g, g < 12 → layerArm X g = armAtW (2 * g))
    (hA : ∀ g, g < 12 → attArm X g = armAtW (2 * g + 1)) (hH : headArm X = armAtW 24)
    (hE : attArm X 12 = armAtW 25) : armsB X = true := by
  unfold armsB
  refine decide_eq_true ?_
  rw [armsW_table]
  exact List.map_congr_left fun j hj =>
    arm_at_of_arms h4 hN hL hA hH hE j (List.mem_range.1 hj)

/-! ## 3 The written numbers, arm by arm -/

/-- The layers' lookup. -/
def lookL : ForestSize := { v := 30, d := 19, shifted := true }

/-- The layers' own numbers: the first group's, and every later group's. -/
def numsL (g : Nat) : LayerRounds :=
  if g = 0 then
    { lt := 10, ls := 6, lNI := 3, lPd := 13, ll := 2, lPf := 14, lfe := 13, lamS := 23,
      lkW := 18, NI := 8, NS := 9, NP := 7, NO := 4, withTerms := true, shownByTheTerms := 266,
      neverSent := 3, weightClaims := 32, firstGroup := true, routed := true }
  else
    { lt := 10, ls := 6, lNI := 3, lPd := 13, ll := 2, lPf := 14, lfe := 13, lamS := 23,
      lkW := 18, NI := 8, NS := 9, NP := 7, NO := 4, withTerms := true, shownByTheTerms := 266,
      neverSent := 3, weightClaims := 32, firstGroup := false, routed := true }

/-- The layers' smallness test. -/
def smallL : SmallSize :=
  { columns := 24086, tau := 128, digits := { v := 27, d := 11, shifted := true } }

/-- The rows that the layers' last round batches. -/
def claimsL (g : Nat) : Nat := if g = 0 then 32005923 else 32005793

/-- The attention's lookup, own numbers and smallness test: one value at all twelve groups. -/
def lookA : ForestSize := { v := 29, d := 18, shifted := true }

def ownA : AttentionRounds :=
  { lt := 10, lgk := 3, pairs := 20, Lam := 4, planeMessages := 2, score := [(17, 20), (14,
    20)], e := 13, valueM := 16, valueD := 13, attained := 20, bits := 17, rows := 14166783 }

def smallA : SmallSize :=
  { columns := 10248, tau := 128, digits := { v := 26, d := 11, shifted := true } }

/-- The head's. -/
def lookH : ForestSize := { v := 31, d := 19, shifted := true }

def ownH : HeadRounds :=
  { lt := 10, lPd := 13, lkW := 18, sums := 9, products := 7, rowValues := 4, rows := 24653737 }

def smallH : SmallSize :=
  { columns := 20703, tau := 128, digits := { v := 27, d := 11, shifted := true } }

/-- **These numbers are the written list's**: no second list. -/
theorem written_layers :
    ∀ g, g < 12 → Arm.layer lookL (numsL g) smallL (claimsL g) = armAtW (2 * g) := by
  decide +kernel

theorem written_attention : ∀ g, g < 12 → Arm.attention lookA ownA smallA = armAtW (2 * g + 1) := by
  decide +kernel

theorem written_head : Arm.head lookH ownH smallH = armAtW 24 := by decide +kernel

theorem written_beyond : Arm.none = armAtW 25 := by decide +kernel

/-- **(2) From the numbers, arm by arm.** -/
theorem armsB_of_fields {X : Public} (h4 : X.p4 = true) (hN : X.NGr = 12)
    (hL : ∀ g, g < 12 → ∃ hp, X.G[g]? = some hp ∧ forestSize X.y.fo = lookL ∧
      layerNumbers X.layers hp g = numsL g ∧ smallSize hp.tl = smallL ∧ hp.nBatched = claimsL g)
    (hA : ∀ g, g < 12 → ∃ a, X.A[g]? = some a ∧ forestSize a.fs = lookA ∧ a.own = ownA ∧
      smallSize a.seam.tl = smallA)
    (hE : X.A[12]? = none)
    (hH : forestSize X.HLy.fs = lookH ∧ X.H.own X.hS = ownH ∧ smallSize X.H.tl = smallH) :
    armsB X = true := by
  refine armsB_of_arms h4 hN (fun g hg => ?_) (fun g hg => ?_) ?_ ?_
  · obtain ⟨hp, e0, e1, e2, e3, e4⟩ := hL g hg
    rw [layerArm_of e0 e1 e2 e3 e4]
    exact written_layers g hg
  · obtain ⟨a, e0, e1, e2, e3⟩ := hA g hg
    rw [attArm_of e0 e1 e2 e3]
    exact written_attention g hg
  · rw [headArm_of hH.1 hH.2.1 hH.2.2]
    exact written_head
  · rw [attArm_none hE]
    exact written_beyond

/-- Three bent closed arms are not the written ones: the layers' lookup one bit deeper; a later
group's numbers and rows at the first link; the layers' smallness test at an attention's link. These
are teeth of the equations `written_…`, on closed arms: no X is named. -/
theorem written_teeth :
    Arm.layer { lookL with d := lookL.d + 1 } (numsL 0) smallL (claimsL 0) ≠ armAtW 0 ∧
      Arm.layer lookL (numsL 1) smallL (claimsL 1) ≠ armAtW 0 ∧
      Arm.attention lookA ownA smallL ≠ armAtW 1 := by
  decide +kernel

end AtFull.Rows

#print axioms AtFull.Rows.armOf_parts
#print axioms AtFull.Rows.arm_congr
#print axioms AtFull.Rows.arm_congr_fields
#print axioms AtFull.Rows.headArm_of
#print axioms AtFull.Rows.layerArm_of
#print axioms AtFull.Rows.attArm_of
#print axioms AtFull.Rows.attArm_none
#print axioms AtFull.Rows.armOf_two
#print axioms AtFull.Rows.arm_at_of_arms
#print axioms AtFull.Rows.armsW_table
#print axioms AtFull.Rows.armsB_of_arms
#print axioms AtFull.Rows.written_layers
#print axioms AtFull.Rows.written_attention
#print axioms AtFull.Rows.written_head
#print axioms AtFull.Rows.written_beyond
#print axioms AtFull.Rows.armsB_of_fields
#print axioms AtFull.Rows.written_teeth
