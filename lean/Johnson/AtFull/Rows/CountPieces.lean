-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Rows/CountPieces.lean: THE ROUNDS OF AN ARM OVER THREE MOMENTS, CUT IN PIECES, AND
THE COUNT OF THEIR SCALARS BY THE WALK (Johnson/AtFull/Rows/CountWalk.lean). Definitions, theorems
and three rules more for the tactic `frp` (Johnson/AtFull/Rows/FrameP.lean). A law file; no running
text imports it. Nothing on codes.

Definitions.
  `partsP x`: A SECOND TEXT of `planLookup`'s «parts» (OnBytes/Params/Planner.lean).
  `lookHeadP x`, `lookEndP x`: SECOND TEXTS of `planLookup`'s lines in front of its product trees
    and behind them.
  `lookPiecesP x`: the head, one piece a product tree, the end. `forestPieces x`: the like for
    `planForest`; its written argument is A SECOND TEXT of `planForest`'s
    (OnBytes/Params/SubRounds.lean).
  `armPieces a`: the pieces of an arm's rounds over the moments 0, 1, 2.
  `countIsW a n`: a test with code: the walk over these pieces, at the written setting, returns, and
    gives the count n.
Statements.
  `planLookup_seq`, `planForest_seq`: each routine is `seqP` of its pieces.
  `arm_seq`: the routine that `armCount` counts (Johnson/AtFull/Rows/ArmCount.lean) is `seqP` of the
    arm's pieces.
  `frP_armPieces`: each piece reads no round.
  `count_of_isW`: a yes of `countIsW` gives armCount a = .ok n. `is_of_count`: that equation gives a
    yes of `countIs`.

Limits. The four second texts are no running text. `planLookup_seq` ties three of them to
`planLookup`, `planForest_seq` the fourth to `planForest`. They will have to be turned with these
two routines; the equations would then fail. `armPieces` will have to be turned with `headRounds`,
`layerRounds` and `attentionRounds` (OnBytes/Params/SubRounds.lean); `arm_seq` would then fail. The
three rules for `frp` are not scoped: they hold in every file that imports this one. No closed fact
is here but `range3` (by `rfl`). Nothing on soundness.

-/
import Johnson.AtFull.Rows.CountWalk
import Johnson.AtFull.Rows.ArmCount

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFull.Rows
open OnBytes OnBytes.Params VerifiableInference.Desc.LinkJoin
open VerifiableInference.PlanWritten.Joined (writtenSized)

/-! ## A lookup in pieces -/

theorem ite_bindP {α β : Type} (c : Prop) [Decidable c] (a b : Planning α)
    (f : α → Planning β) : (if c then a else b) >>= f = if c then a >>= f else b >>= f := by
  split <;> rfl

/-- A second text of planLookup's «parts». -/
def partsP (x : LookupSize) : List Nat := if x.parts.isEmpty then [x.v] else x.parts

/-- planLookup's lines in front of its product trees. -/
def lookHeadP (x : LookupSize) : Planning Unit := do
  let s ← theSetting
  let slots := 2 ^ min x.mu 6
  let w := if x.live != 0 then x.live else slots
  let parts := if x.parts.isEmpty then [x.v] else x.parts
  let keys := sumT (parts.map (2 ^ ·))
  needs (decide (1 ≤ x.mu) && decide (x.mu ≤ 6) && decide (2 ≤ w) && decide (w ≤ slots))
  needs (decide (keys < 2 ^ w) && decide (2 ^ x.d * (2 ^ w - 1) < s.p))
  if x.shifted then planShift (2 ^ x.d)
  close "LKP" .field (Bound.ratio (keys - 1) s.cardE) { drawE := 1, priced := .callersWord }
  planPsc { degreeY := 3, values := 3 }
  times (w - 2) (planPsc { degreeY := 3, values := 2 })
  times (parts.length - 1) (planPsc {})
  planJoin x.mu

/-- planLookup's lines behind its product trees. -/
def lookEndP (x : LookupSize) : Planning Unit := do
  planPsc { degree := List.replicate x.d 3 ++ List.replicate x.mu 2, withY := false }
  planZero (x.mu + x.d)
  planPsc { degree := List.replicate (x.mu + x.d) 3, degreeY := 2, values := 1 }

/-- The pieces of a lookup: one product tree a piece. -/
def lookPiecesP (x : LookupSize) : List (Planning Unit) :=
  lookHeadP x :: (partsP x).map (fun v => planProductTree v 0) ++
    [planProductTree x.d x.mu, lookEndP x]

/-- **A lookup is its pieces, one behind the other.** -/
theorem planLookup_seq (x : LookupSize) : planLookup x = seqP (lookPiecesP x) := by
  unfold lookPiecesP
  rw [List.cons_append]
  unfold seqP
  rw [seqP_append, ← forEach_seqP]
  simp only [seqP, bind_pure_unit]
  unfold planLookup lookHeadP lookEndP partsP
  simp only [bind_assoc, ite_bindP, pure_bind]

/-- The pieces of a lookup of a group of calls. -/
def forestPieces (x : ForestSize) : List (Planning Unit) :=
  lookPiecesP { v := x.v, d := x.d, mu := 5, shifted := x.shifted }

theorem planForest_seq (x : ForestSize) : planForest x = seqP (forestPieces x) :=
  planLookup_seq _

/-! ## An arm in pieces -/

/-- The pieces of an arm's rounds over the moments 0, 1, 2. -/
def armPieces : Arm → List (Planning Unit)
  | .head l x s =>
    forestPieces l ++ [planHeadOwn x, planSmall s 0] ++ forestPieces s.digits ++ [planHeadEnd x]
  | .layer l x s c =>
    forestPieces l ++ [planLayerOwn x, planSmall s 0] ++ forestPieces s.digits ++ [planBatSigma c]
  | .attention l x s =>
    forestPieces l ++ [planAttentionOwn x, planSmall s 0] ++ forestPieces s.digits ++
      [planBatSigma x.rows]
  | .none => [needs false, needs false, needs false]

theorem range3 : List.range 3 = [0, 1, 2] := rfl

theorem planSmall_one (s : SmallSize) : planSmall s 1 = planForest s.digits := by
  simp [planSmall, needs]

theorem head_0 (l : ForestSize) (x : HeadRounds) (s : SmallSize) :
    headRounds l x s 0 = (planForest l >>= fun _ => planHeadOwn x) := by
  simp [headRounds]

theorem head_1 (l : ForestSize) (x : HeadRounds) (s : SmallSize) :
    headRounds l x s 1 = planSmall s 0 := by
  simp [headRounds]

theorem head_2 (l : ForestSize) (x : HeadRounds) (s : SmallSize) :
    headRounds l x s 2 = (planSmall s 1 >>= fun _ => planHeadEnd x) := by
  simp [headRounds]

theorem layer_0 (l : ForestSize) (x : LayerRounds) (s : SmallSize) (c : Nat) :
    layerRounds l x s c 0 = (planForest l >>= fun _ => planLayerOwn x) := by
  simp [layerRounds]

theorem layer_1 (l : ForestSize) (x : LayerRounds) (s : SmallSize) (c : Nat) :
    layerRounds l x s c 1 = planSmall s 0 := by
  simp [layerRounds]

theorem layer_2 (l : ForestSize) (x : LayerRounds) (s : SmallSize) (c : Nat) :
    layerRounds l x s c 2 = (planSmall s 1 >>= fun _ => planBatSigma c) := by
  simp [layerRounds]

theorem att_0 (l : ForestSize) (x : AttentionRounds) (s : SmallSize) :
    attentionRounds l x s 0 = (planForest l >>= fun _ => planAttentionOwn x) := by
  simp [attentionRounds]

theorem att_1 (l : ForestSize) (x : AttentionRounds) (s : SmallSize) :
    attentionRounds l x s 1 = planSmall s 0 := by
  simp [attentionRounds]

theorem att_2 (l : ForestSize) (x : AttentionRounds) (s : SmallSize) :
    attentionRounds l x s 2 = (planSmall s 1 >>= fun _ => planBatSigma x.rows) := by
  simp [attentionRounds]

/-- **The routine that `armCount` counts is its pieces, one behind the other.** -/
theorem arm_seq (a : Arm) :
    (forEach (List.range 3) fun m => armRounds a m) = seqP (armPieces a) := by
  rw [range3, forEach_seqP]
  cases a with
  | head l x s =>
    simp only [List.map_cons, List.map_nil, armRounds, armPieces, head_0, head_1, head_2,
      planSmall_one, seqP_append, seqP, ← planForest_seq, bind_assoc, pure_bind]
  | layer l x s c =>
    simp only [List.map_cons, List.map_nil, armRounds, armPieces, layer_0, layer_1, layer_2,
      planSmall_one, seqP_append, seqP, ← planForest_seq, bind_assoc, pure_bind]
  | attention l x s =>
    simp only [List.map_cons, List.map_nil, armRounds, armPieces, att_0, att_1, att_2,
      planSmall_one, seqP_append, seqP, ← planForest_seq, bind_assoc, pure_bind]
  | none =>
    simp only [List.map_cons, List.map_nil, armRounds, armPieces]

/-! ## Each piece reads no round -/

theorem frP_times {x : Planning Unit} (h : FrP x) : ∀ n : Nat, FrP (times n x)
  | 0 => by
    unfold times
    exact frP_pure _
  | k + 1 => by
    unfold times
    exact frP_bind h fun _ => frP_times h k
macro_rules | `(tactic| frp_step) => `(tactic| with_reducible apply frP_times)
macro_rules | `(tactic| frp_step) => `(tactic| with_reducible apply frP_forEach)

theorem frP_lookHeadP (x : LookupSize) : FrP (lookHeadP x) := by
  unfold lookHeadP
  frp

theorem frP_lookEndP (x : LookupSize) : FrP (lookEndP x) := by
  unfold lookEndP
  frp

theorem frP_lookPiecesP (x : LookupSize) : ∀ y ∈ lookPiecesP x, FrP y := by
  intro y hy
  unfold lookPiecesP at hy
  rcases List.mem_append.1 hy with hy | hy
  · rcases List.mem_cons.1 hy with rfl | hy
    · exact frP_lookHeadP x
    · obtain ⟨v, -, rfl⟩ := List.mem_map.1 hy
      exact frP_planProductTree _ _
  · rcases List.mem_cons.1 hy with rfl | hy
    · exact frP_planProductTree _ _
    · rcases List.mem_singleton.1 hy with rfl
      exact frP_lookEndP x

theorem frP_planForest (x : ForestSize) : FrP (planForest x) := by
  rw [planForest_seq]
  exact frP_seqP _ (frP_lookPiecesP _)
macro_rules | `(tactic| frp_step) => `(tactic| with_reducible exact frP_planForest _)

theorem frP_planSmall (x : SmallSize) (which : Nat) : FrP (planSmall x which) := by
  unfold planSmall
  frp

theorem frP_planHeadOwn (x : HeadRounds) : FrP (planHeadOwn x) := by
  unfold planHeadOwn
  frp

theorem frP_planHeadEnd (x : HeadRounds) : FrP (planHeadEnd x) := by
  unfold planHeadEnd
  frp

theorem frP_planLayerOwn (x : LayerRounds) : FrP (planLayerOwn x) := by
  unfold planLayerOwn
  frp

theorem frP_planAttentionOwn (x : AttentionRounds) : FrP (planAttentionOwn x) := by
  unfold planAttentionOwn
  frp

theorem all_append {a b : List (Planning Unit)} (ha : ∀ y ∈ a, FrP y) (hb : ∀ y ∈ b, FrP y) :
    ∀ y ∈ a ++ b, FrP y := by
  intro y hy
  rcases List.mem_append.1 hy with hy | hy
  · exact ha y hy
  · exact hb y hy

theorem all_two {x z : Planning Unit} (hx : FrP x) (hz : FrP z) : ∀ y ∈ [x, z], FrP y := by
  intro y hy
  rcases List.mem_cons.1 hy with rfl | hy
  · exact hx
  · rcases List.mem_singleton.1 hy with rfl
    exact hz

theorem all_one {x : Planning Unit} (hx : FrP x) : ∀ y ∈ [x], FrP y := by
  intro y hy
  rcases List.mem_singleton.1 hy with rfl
  exact hx

/-- **Each piece of an arm reads no round.** -/
theorem frP_armPieces : ∀ a : Arm, ∀ y ∈ armPieces a, FrP y
  | .head _ x s =>
    all_append (all_append (all_append (frP_lookPiecesP _)
      (all_two (frP_planHeadOwn x) (frP_planSmall s 0))) (frP_lookPiecesP _))
      (all_one (frP_planHeadEnd x))
  | .layer _ x s c =>
    all_append (all_append (all_append (frP_lookPiecesP _)
      (all_two (frP_planLayerOwn x) (frP_planSmall s 0))) (frP_lookPiecesP _))
      (all_one (frP_planBatSigma c))
  | .attention _ x s =>
    all_append (all_append (all_append (frP_lookPiecesP _)
      (all_two (frP_planAttentionOwn x) (frP_planSmall s 0))) (frP_lookPiecesP _))
      (all_one (frP_planBatSigma x.rows))
  | .none =>
    all_append (a := [needs false]) (all_one (frP_needs _ _))
      (all_two (frP_needs _ _) (frP_needs _ _))

/-! ## The count by the walk -/

/-- The walk over an arm's pieces, at the written setting, returns and gives the count n. -/
def countIsW (a : Arm) (n : Nat) : Bool :=
  match walkS writtenSized.proof.set (0, { set := writtenSized.proof.set }) (armPieces a) with
  | some (m, p) => (m + fieldBytes p.openBytes p.openRoots p.openAnswers) / 24 == n
  | none => false

/-- **A yes of the walk gives the planner's own count.** -/
theorem count_of_isW {a : Arm} {n : Nat} (h : countIsW a n = true) : armCount a = .ok n := by
  unfold countIsW at h
  cases e : walkS writtenSized.proof.set (0, { set := writtenSized.proof.set }) (armPieces a) with
  | none =>
    rw [e] at h
    cases h
  | some r =>
    obtain ⟨m, p⟩ := r
    rw [e] at h
    unfold armCount
    rw [arm_seq, scalars_of_walk (frP_armPieces a) e, eq_of_beq h]

/-- The equation gives a yes of ArmCount.lean's test. -/
theorem is_of_count {a : Arm} {n : Nat} (h : armCount a = .ok n) : countIs a n = true := by
  unfold countIs
  rw [h]
  exact beq_self_eq_true n

end AtFull.Rows

#print axioms AtFull.Rows.ite_bindP
#print axioms AtFull.Rows.planLookup_seq
#print axioms AtFull.Rows.planForest_seq
#print axioms AtFull.Rows.range3
#print axioms AtFull.Rows.planSmall_one
#print axioms AtFull.Rows.head_0
#print axioms AtFull.Rows.head_1
#print axioms AtFull.Rows.head_2
#print axioms AtFull.Rows.layer_0
#print axioms AtFull.Rows.layer_1
#print axioms AtFull.Rows.layer_2
#print axioms AtFull.Rows.att_0
#print axioms AtFull.Rows.att_1
#print axioms AtFull.Rows.att_2
#print axioms AtFull.Rows.arm_seq
#print axioms AtFull.Rows.frP_times
#print axioms AtFull.Rows.frP_lookHeadP
#print axioms AtFull.Rows.frP_lookEndP
#print axioms AtFull.Rows.frP_lookPiecesP
#print axioms AtFull.Rows.frP_planForest
#print axioms AtFull.Rows.frP_planSmall
#print axioms AtFull.Rows.frP_planHeadOwn
#print axioms AtFull.Rows.frP_planHeadEnd
#print axioms AtFull.Rows.frP_planLayerOwn
#print axioms AtFull.Rows.frP_planAttentionOwn
#print axioms AtFull.Rows.all_append
#print axioms AtFull.Rows.all_two
#print axioms AtFull.Rows.all_one
#print axioms AtFull.Rows.frP_armPieces
#print axioms AtFull.Rows.count_of_isW
#print axioms AtFull.Rows.is_of_count
