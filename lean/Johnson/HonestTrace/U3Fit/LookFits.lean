-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/HonestTrace/U3Fit/LookFits.lean

Under the head (the terms: Johnson/HonestTrace/U3Fit/SeatsAtHead.lean) the two clauses of "fitsSeg"
(Johnson/HonestTrace/U3Rows.lean) on the lookup's rounds hold at each of the 25 segments: the named
premise "LookFits" (Johnson/HonestTrace/U3Fit/ValsGeneral.lean) is shown, at the three kinds K4, K5
and K6, by one theorem. Two definitions; theorems. Public data alone.

Main theorems:
* "lookRounds_len": "k4LookRounds h = (entriesV (faceOf h)).length" at every shape: one call of
  "rounds_stages" (Johnson/Desc/ProofFile/Honest/K3/RowLaw.lean) at "faceOf h".
* "k3_block_at_head": the member of the lookup on the calls at link l stands at number "14 * l +
  IM.k3Ix l false + 2" of the first chain's flat list; its rounds are its place's own; the place has
  a shape hs, and the plan's entries fit at "faceOf hs" ("entriesFit").
* "lookFits_at_head": at l below 25, where every place of the lookup at l has the shape fs:
  "LookFits Zp spotsWritten l (ownOf l) fs".
* "shape_layers", "shape_att", "shape_head": that shape is "layers.y.fo", "a.fs", "HLy.fs".
* "lookFits_layers", "lookFits_att" (for "G.W.A[g]? = some a"), "lookFits_head": the three ends.

Definitions: "ownOf l": K6 at 24, K4 at an even, K5 at an odd segment. "lookPlacesW off": at off = 0
a test at written values: at each segment "placeBy" finds the places of K3 and of the own kind, and
the table of steps counts in front of them what the written rows count in front of K3's row and the
next; off = 1 holds them against the rows one further on, for the control.

Limits. The head is a premise: the full size and the format's second hash function alone. Two closed facts,
"lookPlacesW_yes" and its control "lookPlacesW_can_fail", are shown by "decide +kernel", each under
"set_option maxRecDepth 1000000", which raises the elaborator's depth of recursion. "LookFits"
speaks only of returns of "placeIn"; that "placeIn" does return at K3 and at the own kind is stated
here by no theorem: at the layers' segments "layersDeclared_at_head"
(Johnson/HonestTrace/U3Fit/Slice.lean) says it; at the other thirteen no statement of this folder
does.
Not claimed: anything on what is heard in these rounds. No property of a release, of a verifier or
of a prover is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K3.RowLaw
import Johnson.Desc.ProofFile.Honest.K4.Look
import Johnson.HonestTrace.U3Fit.Slice
import Johnson.HonestTrace.U3Fit.MatsAtHead
import Johnson.IMR.K3Seat
import Johnson.Desc.First.Look.K03PlanOf
import Johnson.Desc.First.Look.K3CallerAtPlan

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.HonestTrace.U3.Fit

open OnBytes OnBytes.Model
open ProofFile (Pub Ground Spot)
open ProofFile.Honest.K4 (k4LookRounds)
open VerifiableInference.Desc (Block KindName)
open VerifiableInference.Desc.K3 (entriesFit entriesV faceOf)
open VerifiableInference.Desc.First.Look (placeAt lookAt)
open VerifiableInference.PlanWritten (cutFirstFull)
open Johnson.AtFull.Cut (cutWritten)
open Johnson.AtFull.Desc (spotsWritten)
open P5J (AtMgA TS)

variable {W : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place}

/-- At every shape the honest side's count of the lookup's rounds is the number of the hearing's entries: the
library's "rounds_stages" at "faceOf h", which has 32 planes. -/
theorem lookRounds_len (h : Forest.Shape) : k4LookRounds h = (entriesV (faceOf h)).length :=
  ProofFile.Honest.K3.rounds_stages (faceOf h) (show 2 ≤ 32 by decide)

/-- **The member of the lookup on the calls at link l.** -/
theorem k3_block_at_head (h : AtMgA OnBytes.secondHashFunction W D r Zp Np cF x) {G : Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) {l : Nat} (hl : l < 25) :
    ∃ (b : Block TS ProofFile.Cl) (p : VerifiableInference.Desc.First.Look.P) (hs : Forest.Shape),
      cF.blocksInOrder[14 * l + IM.k3Ix l false + 2]? = some b ∧ placeAt G.W l false = some p ∧
      b.rounds = p.rounds ∧ p.shape = some hs ∧
      entriesFit (faceOf hs) (p.entries.getD []) = true := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain rfl : Bs.G₀ = G := Option.some.inj (O.blank.symm.trans hG)
  obtain ⟨Lk, b, b', h1, h2, h3, h4⟩ := IM.k3_of h.scope h.reads O l hl false
  have h5 := IM.hear_at_flat h1 h2
  rw [IM.flatIx_scope h.scope h.reads O (by omega) (IM.k3Ix l false)] at h5
  obtain ⟨b'', h3', hk⟩ :=
    VerifiableInference.OnPublicFiles.k03_const_ok h.scope h.reads O h.laid.planOk l hl false
  obtain rfl : b' = b'' := Option.some.inj (h3.symm.trans h3')
  obtain ⟨hpc, p, hp, er⟩ := K3Lot.k03_place _ _ _ _ _ l false b' h3
  obtain ⟨B₁, hB₁, -, -, -, e4⟩ := VerifiableInference.Desc.K3.theStated_is _ _ _ _ _ _ b' h3
  obtain ⟨b0, hb0, hW⟩ := VerifiableInference.Desc.K3.theWhole_is _ true _ _ _ _ B₁ hB₁
  obtain ⟨i, d, p', sent, laid, hi, hpc', hP, -, -, -, -, -, r4⟩ :=
    VerifiableInference.Desc.K3.theOwn_is _ true _ _ _ _ b0 hb0
  obtain rfl : l = i := Option.some.inj hi
  obtain rfl : false = d := VerifiableInference.Desc.K3.pieceAt_inj _ l (hpc.symm.trans hpc')
  obtain rfl : p = p' := Option.some.inj (hp.symm.trans hP)
  have hbk : b0.planOk = true := by
    rcases hW with ⟨-, rfl⟩ | ⟨f, -, rfl⟩
    · exact e4.symm.trans hk
    · have h6 : (b0.planOk && (VerifiableInference.Desc.roundlessBlock (b0.name ++ ": behind it") 1
          (IM.k3Place l false).link (IM.k3Place l false).piece f).planOk) = true :=
        e4.symm.trans hk
      exact (Eq.mp (Bool.and_eq_true _ _) h6).1
  have hf := (VerifiableInference.Desc.K3.Law.blockVia_planOk (r4 hbk)).2
  unfold VerifiableInference.Desc.K3.Law.fitsVia at hf
  cases hs : p.shape with
  | none =>
    rw [hs] at hf
    cases hf
  | some s =>
    rw [hs] at hf
    exact ⟨b, p, s, h5, hp, (IM.alone_rounds h4).trans er, hs,
      (Eq.mp (Bool.and_eq_true _ _) hf).1⟩

/-- The written rows' rounds in front of row i + 1. -/
theorem rowsBeforeW_succ {i n : Nat} (e : (cutFirstFull[i]?).map (·.2.2.1) = some n) :
    rowsBeforeW (i + 1) = rowsBeforeW i + n := by
  unfold rowsBeforeW
  cases hc : cutFirstFull[i]? with
  | none =>
    rw [hc] at e
    cases e
  | some c =>
    rw [hc] at e
    have en : c.2.2.1 = n := Option.some.inj e
    rw [List.take_add_one, hc, List.map_append, List.sum_append, ← en]
    simp

/-- The segment's own kind. -/
def ownOf (l : Nat) : KindName := if l == 24 then .K6 else if l % 2 == 0 then .K4 else .K5

/-- **A TEST AT WRITTEN VALUES**, at off = 0; off = 1 is the control's shift by one row. -/
def lookPlacesW (off : Nat) : Bool :=
  (List.range 25).all fun l =>
    match placeBy cutWritten spotsWritten l .K3, placeBy cutWritten spotsWritten l (ownOf l) with
    | .ok k3, .ok k =>
      k3.2 == rowsBeforeW (14 * l + IM.k3Ix l false + 2 + off) &&
        k.2 == rowsBeforeW (14 * l + IM.k3Ix l false + 2 + 1 + off)
    | _, _ => false

set_option maxRecDepth 1000000 in
theorem lookPlacesW_yes : lookPlacesW 0 = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- A control: against the rows one further on the test says no. -/
theorem lookPlacesW_can_fail : lookPlacesW 1 = false := by decide +kernel

/-- **UNDER THE HEAD: THE LOOKUP's TWO CLAUSES AT SEGMENT l**, at the shape fs of the lookup's place there. -/
theorem lookFits_at_head (h : AtMgA OnBytes.secondHashFunction W D r Zp Np cF x) {G : Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) {l : Nat} (hl : l < 25) {fs : Forest.Shape}
    (hfs : ∀ p, placeAt G.W l false = some p → p.shape = some fs) :
    LookFits Zp spotsWritten l (ownOf l) fs := by
  intro k3 k q3 q
  obtain ⟨b, p, hs, hb, hp, er, esh, hfit⟩ := k3_block_at_head h hG hl
  obtain rfl : hs = fs := Option.some.inj (esh.symm.trans (hfs p hp))
  -- the two places
  rw [placeIn_by, cuts_at_head h] at q3 q
  have w := List.all_eq_true.1 lookPlacesW_yes l (List.mem_range.2 hl)
  rw [q3, q] at w
  simp only [Bool.and_eq_true, beq_iff_eq, Nat.add_zero] at w
  -- the lengths
  have e1 : b.rounds.length = (p.entries.getD []).length := by
    rw [er]
    exact List.length_map _
  have e2 : (p.entries.getD []).length = (entriesV (faceOf hs)).length := by
    unfold entriesFit at hfit
    have := congrArg List.length (beq_iff_eq.1 hfit)
    rwa [List.length_map] at this
  have e3 : k4LookRounds hs = b.rounds.length := by rw [lookRounds_len, ← e2, e1]
  have e4 : declared Zp k3.2 (k4LookRounds hs) = p.entries.getD [] := by
    rw [w.1, e3, slice_at_head h hb, er]
    unfold VerifiableInference.Desc.First.Look.P.rounds
    rw [List.map_map]
    exact List.map_id _
  unfold fitsLook
  rw [e4, hfit, w.1, w.2, e3, rowsBeforeW_succ (len_at_head h hb), beq_self_eq_true]
  rfl

/-! ## The place's shape is the maker's -/

theorem shape_layers (h : AtMgA OnBytes.secondHashFunction W D r Zp Np cF x) {G : Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) {g : Nat} (hg : g < 12) :
    ∀ p, placeAt G.W (2 * g) false = some p → p.shape = some G.W.layers.y.fo := by
  intro p hp
  have hX := IM.ground_publicK h.laid.pub hG
  have M := marks_at_head h hG
  unfold placeAt at hp
  obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.1 hp
  have hn : 2 * g ≠ (if G.W.p4 then 2 else 1) * G.W.NGr := by
    rw [M.p4, M.groups]
    show 2 * g ≠ 2 * 12
    omega
  have h0 : 2 * g % (if G.W.p4 then 2 else 1) = 0 := by
    rw [M.p4]
    show 2 * g % 2 = 0
    omega
  rw [VerifiableInference.Desc.First.Look.lay_shape _ hX hy hn h0]
  obtain ⟨-, -, -, e, -⟩ := VerifiableInference.Desc.First.Look.lookAt_lay hy hn h0
  rw [e]
  rfl

theorem shape_att (h : AtMgA OnBytes.secondHashFunction W D r Zp Np cF x) {G : Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) {g : Nat}
    {a : Attention.Plan} (ea : G.W.A[g]? = some a) :
    ∀ p, placeAt G.W (2 * g + 1) false = some p → p.shape = some a.fs := by
  intro p hp
  have hX := IM.ground_publicK h.laid.pub hG
  have M := marks_at_head h hG
  unfold placeAt at hp
  obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.1 hp
  have hn : 2 * g + 1 ≠ (if G.W.p4 then 2 else 1) * G.W.NGr := by
    rw [M.p4, M.groups]
    show 2 * g + 1 ≠ 2 * 12
    omega
  have h0 : (2 * g + 1) % (if G.W.p4 then 2 else 1) ≠ 0 := by
    rw [M.p4]
    show (2 * g + 1) % 2 ≠ 0
    omega
  rw [VerifiableInference.Desc.First.Look.att_shape _ hX hy hn h0]
  obtain ⟨a', ha', -, e, -⟩ := VerifiableInference.Desc.First.Look.lookAt_att hy hn h0
  have hd : (2 * g + 1) / (if G.W.p4 then 2 else 1) = g := by
    rw [M.p4]
    show (2 * g + 1) / 2 = g
    omega
  rw [hd] at ha'
  obtain rfl : a' = a := Option.some.inj (ha'.symm.trans ea)
  rw [e]

theorem shape_head (h : AtMgA OnBytes.secondHashFunction W D r Zp Np cF x) {G : Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) :
    ∀ p, placeAt G.W 24 false = some p → p.shape = some G.W.HLy.fs := by
  intro p hp
  have hX := IM.ground_publicK h.laid.pub hG
  have M := marks_at_head h hG
  unfold placeAt at hp
  obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.1 hp
  have e24 : (if G.W.p4 then 2 else 1) * G.W.NGr = 24 := by
    rw [M.p4, M.groups]
    rfl
  rw [← e24] at hy
  rw [VerifiableInference.Desc.First.Look.head_shape _ hX hy,
    (VerifiableInference.Desc.First.Look.lookAt_head hy).2.1]

/-- **AT THE TWELVE LAYERS' SEGMENTS.** -/
theorem lookFits_layers (h : AtMgA OnBytes.secondHashFunction W D r Zp Np cF x) {G : Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) {g : Nat} (hg : g < 12) :
    LookFits Zp spotsWritten (2 * g) .K4 G.W.layers.y.fo := by
  have k := lookFits_at_head h hG (l := 2 * g) (by omega) (shape_layers h hG hg)
  have e : ownOf (2 * g) = .K4 := by
    unfold ownOf
    have a : (2 * g == 24) = false := by
      have : 2 * g ≠ 24 := by omega
      simpa using this
    have b : 2 * g % 2 = 0 := by omega
    rw [a, b]
    rfl
  rw [e] at k
  exact k

/-- **AT THE TWELVE ATTENTION SEGMENTS.** -/
theorem lookFits_att (h : AtMgA OnBytes.secondHashFunction W D r Zp Np cF x) {G : Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) {g : Nat} (hg : g < 12)
    {a : Attention.Plan} (ea : G.W.A[g]? = some a) :
    LookFits Zp spotsWritten (2 * g + 1) .K5 a.fs := by
  have k := lookFits_at_head h hG (l := 2 * g + 1) (by omega) (shape_att h hG ea)
  have e : ownOf (2 * g + 1) = .K5 := by
    unfold ownOf
    have a : (2 * g + 1 == 24) = false := by
      have : 2 * g + 1 ≠ 24 := by omega
      simpa using this
    have b : (2 * g + 1) % 2 = 1 := by omega
    rw [a, b]
    rfl
  rw [e] at k
  exact k

/-- **AT THE OUTPUT HEAD's SEGMENT.** -/
theorem lookFits_head (h : AtMgA OnBytes.secondHashFunction W D r Zp Np cF x) {G : Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) :
    LookFits Zp spotsWritten 24 .K6 G.W.HLy.fs :=
  lookFits_at_head h hG (l := 24) (by decide) (shape_head h hG)

end OnBytes.HonestTrace.U3.Fit

-- Lean's own words on each theorem of this file: its statement, and the axioms that it rests on: each line
-- «depends on axioms» should name no more than propext, Classical.choice and Quot.sound.
#check @OnBytes.HonestTrace.U3.Fit.lookRounds_len
#check @OnBytes.HonestTrace.U3.Fit.k3_block_at_head
#check @OnBytes.HonestTrace.U3.Fit.rowsBeforeW_succ
#check @OnBytes.HonestTrace.U3.Fit.lookPlacesW_yes
#check @OnBytes.HonestTrace.U3.Fit.lookPlacesW_can_fail
#check @OnBytes.HonestTrace.U3.Fit.lookFits_at_head
#check @OnBytes.HonestTrace.U3.Fit.shape_layers
#check @OnBytes.HonestTrace.U3.Fit.shape_att
#check @OnBytes.HonestTrace.U3.Fit.shape_head
#check @OnBytes.HonestTrace.U3.Fit.lookFits_layers
#check @OnBytes.HonestTrace.U3.Fit.lookFits_att
#check @OnBytes.HonestTrace.U3.Fit.lookFits_head
#print axioms OnBytes.HonestTrace.U3.Fit.lookRounds_len
#print axioms OnBytes.HonestTrace.U3.Fit.k3_block_at_head
#print axioms OnBytes.HonestTrace.U3.Fit.rowsBeforeW_succ
#print axioms OnBytes.HonestTrace.U3.Fit.lookPlacesW_yes
#print axioms OnBytes.HonestTrace.U3.Fit.lookPlacesW_can_fail
#print axioms OnBytes.HonestTrace.U3.Fit.lookFits_at_head
#print axioms OnBytes.HonestTrace.U3.Fit.shape_layers
#print axioms OnBytes.HonestTrace.U3.Fit.shape_att
#print axioms OnBytes.HonestTrace.U3.Fit.shape_head
#print axioms OnBytes.HonestTrace.U3.Fit.lookFits_layers
#print axioms OnBytes.HonestTrace.U3.Fit.lookFits_att
#print axioms OnBytes.HonestTrace.U3.Fit.lookFits_head
