-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/MergeLaw/TieThreeFour.lean: what three of the merge's ties ask of a filling of the
table of joints, gathered in one structure of premises over a letter Mg; these three ties from it;
and two of its fields paid at the form that the composed filling has. A structure, and theorems with
their proofs.

Why. `merge_seatLawsZ` (TieLawsZ.lean) takes five ties between the merge's own words and the
table's. Whoever composes the filling can show equations on its fields; the ties themselves hang on
the merge's text. Here the two are parted.

Main names:
  `MergeFill`: THE PREMISES ON THE FILLING, each an equation or an implication on one field of Mg,
    or a closed fact on the table: the table's row at the merge's place (what it closes, opens and
    reads); "ledger m" and "freeAbove m" are open at the merge's border and the filling's tests for
    them are the table's own; the table's three pins give the merge's (`Pinned`, Pin.lean);
    "weights" follows from `WeightsHere` at the numbers that the verifier's state holds; "merged"
    gives `MergedHere` and "wo" gives `WoHere` (Here.lean) behind an accepting step. The fields on
    "weights" and "merged" take `MaskAt own xM R` (MaskRow.lean) at the state in question; the field
    on "weights" takes beside it Wa, a letter: whatever else the filling's payer needs of the state
    in front (the composed meaning's sentence for "weights" must be readable at earlier borders too,
    so it is not the merge's own: the lemma that joins the two spends a fact on that state); the
    field on "wo" takes the public item `hasRow` there (the filling's sentence is an implication:
    "if the state holds a pending row, it holds of the witness") and Wb, a letter: whatever else the
    filling's payer needs of that state.
  `merge_t1_fill`: the first tie (by `merge_t1`, TieOneTwo.lean).
  `merge_t3`: the third: what the row opens and reads, behind an accepting step, gives the merge's
    relation behind. Four of its premises are NO premises on the filling: facts on the verifier's
    state behind: he: the index masks' ledger has an entry to give, inside the message; hMb:
    `MaskAt`; hRow: `hasRow`; hWb.
  `merge_t4`: the fourth: the merge's relation in front gives what the row closes; what the row
    reads stands behind the accepting step already and rides back past it: its premise hcb; hMa:
    `MaskAt` in front; hWa.
  `merged_field`, `weights_field`: TWO FIELDS, PAID, at posM := `posMask R`: at every filling whose
    "forms m 9 merged" gives the table's own sentence on linear forms (`formsQ`) at the members'
    tables, and whose "forms m 4 weights" follows from the layer's `FillP1.wtP1` at a reader of the
    mask row that is the forms' own.

Who pays the premises on the state. he, hMb, hRow: `MergeFront` (EntryFront.lean), from four facts
on the state in front; hRow with a closed test on the planner's numbers beside. hcb: `merge_hcb`
(CtxBack.lean). hMa is a field of `MergeFront`. hWa, hWb: owed with the filling at which Wa and Wb
are named.

Limits. `MergeFill` is shown at the composed meaning under premises
(Johnson/Desc/Sound/MgAt/K11.lean); at no closed value.
(Where this and lean/THEOREM.md differ, the page
holds.) The second and the fifth tie and "decodes rides" are not treated here (the merge's share of
the second: TieOneTwo.lean). Nothing on soundness.

-/
import Johnson.Top.H0.MergeLaw.TieLaws
import Johnson.Top.H0.MergeLaw.TieOneTwo
import Johnson.Top.H0.MergeLaw.MaskRow
import Johnson.Top.H0.Fill.FillP1

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.Desc.First.MergeLaw
open Iop
open OnBytes.Maker OnBytes.Flat OnBytes.Slice KObj
open OnBytes.Model (WsShape wsLayOf)
open _root_.Run (ckP)
open VerifiableInference.Desc (FileDescription Place Wit)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S ModelPart Item Pub Meaning Numbers pubSets ledgerB freeAboveB)
open Johnson.Pack (sigOf)
open Johnson.Desc.First.ForkMerge (HeadMergeP headMergeDecide)

variable (cs : OnBytes.Codes) {Xi : Type} (G : FileDescription Xi) {Cells Tok Pp : Type} (arr : ℕ → ℕ → ℕ)
  (smp : Pp → S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
  (rc : Cells → ℕ → ℕ → GE) (decT : Pp → (ℕ → Option (ℕ × List UInt64)) → S → Option Cells)
  (claims : ℕ) (lin : OnBytes.Params.LinShape) (xM xI : Mem) (posM posI : ℕ → Bool × ℕ × ℕ)
  (P : HeadMergeP) {s₀ : WsShape} {p3 : Bool} {lkW : ℕ} (h : wsLayOf s₀ p3 lkW = .ok P.lay)
  (hn : 2 * P.lay.lk + 3 ≤ P.nMsg) (ni : ℕ) (own : List (ℕ × ℕ)) (R : ℕ)
  (Wa Wb : S → Prop)

/-- **WHAT THE MERGE's THIRD AND FOURTH TIE ASK OF A FILLING OF THE TABLE**: premises over a letter
Mg, gathered in one structure. m: the head's segment's number. k: the merge's number in the list of
places. -/
structure MergeFill (Nn : Numbers) (Mg : Meaning Pp (Wit Cells Tok MsgT))
    (links : List ModelPart) (ps : List Place) (k m : ℕ) : Prop where
  /-- the table's row at the merge's place -/
  ins : (rowQ links ps k).ins = [.forms m 4 "weights"]
  outs : (rowQ links ps k).outs = [.forms m 9 "merged", .wo m]
  ctx : (rowQ links ps k).ctx = [.pinW, .pin m 0, .pinI]
  /-- two public items are open at the merge's border, and the filling's tests for them are the
table's own at the plan's number of slots -/
  ledgerOpen : Pub.ledger m ∈ (pubSets Mg.more links ps)[k]?.getD []
  freeOpen : Pub.freeAbove m ∈ (pubSets Mg.more links ps)[k]?.getD []
  ledgerIs : ∀ a, Mg.pub (.ledger m) a = ledgerB a.2
  freeIs : ∀ a, Mg.pub (.freeAbove m) a = freeAboveB P.nMsg a.2
  /-- the table's three pins give the merge's -/
  pins : ∀ (z : Pp) (a : S) (y : VerifiableInference.Desc.Strs) (w : Wit Cells Tok MsgT),
    (Mg.pinW (z, a) y w ∧ (∀ x ∈ Nn.sent m 0, Mg.pin x.1 x.2 (z, a) y w) ∧
      Mg.pin Nn.index.1 Nn.index.2 (z, a) y w) → Pinned cs G arr (smp z) (decT z) xM xI a y w
  /-- "weights" follows from the merge's own sentence at the numbers that the verifier's state holds
-/
  weights : ∀ (z : Pp) (a : S) (y : VerifiableInference.Desc.Strs) (w : Wit Cells Tok MsgT)
    (ui : Fin P.lay.U.size) (sv : ℕ) (hsv : sv < P.nMsg) (c : ℕ) (hc : c < ni),
    ReadsAt a ui.val sv → MaskAt own xM R a → Wa a →
    WeightsHere (recNums P h hn ni ui sv hsv c hc) (rc w.cells) (vecBy cs arr P.nMsg posM xM w) a →
    Mg.forms m 4 "weights" (z, a) y w
  /-- "merged" gives the merge's own sentence, behind a yes -/
  merged : ∀ (z : Pp) (b : S) (y : VerifiableInference.Desc.Strs) (w : Wit Cells Tok MsgT)
    (ui : Fin P.lay.U.size) (sv : ℕ) (hsv : sv < P.nMsg) (c : ℕ) (hc : c < ni),
    ReadsAt b ui.val sv → BehindOk (recNums P h hn ni ui sv hsv c hc) b → MaskAt own xM R b →
    Mg.forms m 9 "merged" (z, b) y w →
    MergedHere (recNums P h hn ni ui sv hsv c hc) (rc w.cells) (vecBy cs arr P.nMsg posM xM w)
      (vecBy cs arr ni posI xI w) b
  /-- "wo" gives the merge's own sentence, at the entry that the index masks' ledger gives next,
  where the state holds a pending row -/
  wo : ∀ (z : Pp) (b : S) (y : VerifiableInference.Desc.Strs) (w : Wit Cells Tok MsgT)
    (ui : Fin P.lay.U.size) (sv : ℕ) (hsv : sv < P.nMsg) (c : ℕ) (hc : c < ni),
    ReadsAt b ui.val sv → EntryAt b c → BehindOk (recNums P h hn ni ui sv hsv c hc) b →
    Johnson.Desc.First.Walk.Law.hasRow P.lay claims lin b = true → Wb b → Mg.wo m (z, b) y w →
    WoHere (recNums P h hn ni ui sv hsv c hc) claims lin (rc w.cells) (vecBy cs arr ni posI xI w) b

variable {cs G arr smp rc decT claims lin xM xI posM posI P h hn ni own R Wa Wb}
variable {Fr : Frame} {Nn : Numbers} {Mg : Meaning Pp (Wit Cells Tok MsgT)}
  {links : List ModelPart} {ps : List Place} {k m : ℕ}

/-- **THE MERGE's FIRST TIE**, from the same premises. -/
theorem merge_t1_fill
    (M : MergeFill cs G arr smp rc decT claims lin xM xI posM posI P h hn ni own R Wa Wb Nn Mg
      links ps k m)
    (z : Pp) (a : S × Fr.E.Str) (ha : onQ Nn Mg links ps (fun s => (z, s)) k a)
    (hm : ¬ a.1.failed ≠ none) : frontR P a.1 = true :=
  merge_t1 Nn Mg links ps k P m M.ledgerOpen M.freeOpen M.ledgerIs M.freeIs z a ha hm

/-- **THE MERGE's THIRD TIE**: what the row opens and reads, behind a yes, gives the merge's
relation behind. he, hMb, hRow, hWb: NO PREMISES ON THE FILLING: facts on the verifier's state
behind: the index masks' ledger has an entry to give, inside the message; `MaskAt`; the state holds
a pending row; Wb. -/
theorem merge_t3
    (M : MergeFill cs G arr smp rc decT claims lin xM xI posM posI P h hn ni own R Wa Wb Nn Mg
      links ps k m)
    (z : Pp) (b : S × Fr.E.Str) (w : Wit Cells Tok MsgT)
    (he : ∃ c, c < ni ∧ EntryAt b.1 c) (hMb : MaskAt own xM R b.1)
    (hRow : Johnson.Desc.First.Walk.Law.hasRow P.lay claims lin b.1 = true) (hWb : Wb b.1)
    (hB : BehindR P h hn ni b.1)
    (hw : relAt (meansQ Nn Mg fun s => (z, s)) (outsQ links ps k) b w) :
    RelBehindR cs G arr (smp z) rc (decT z) claims lin xM xI posM posI P h hn ni b w := by
  obtain ⟨ui, sv, hsv, c0, hc0, hr, hok⟩ := hB
  obtain ⟨c, hc, he⟩ := he
  have hok' : BehindOk (recNums P h hn ni ui sv hsv c hc) b.1 := hok
  have hi : ∀ i : Item, i ∈ [Item.forms m 9 "merged", .wo m] ++ [.pinW, .pin m 0, .pinI] →
      meansQ Nn Mg (fun s => (z, s)) i b w := fun i hi =>
    hw i (by
      unfold outsQ
      rw [M.outs, M.ctx]
      exact List.mem_append_left _ hi)
  have h1 : Mg.forms m 9 "merged" (z, b.1) (strsOf Fr b.2) w :=
    hi (.forms m 9 "merged") (by simp)
  have h2 : Mg.wo m (z, b.1) (strsOf Fr b.2) w := hi (.wo m) (by simp)
  have h3 : Mg.pinW (z, b.1) (strsOf Fr b.2) w := hi .pinW (by simp)
  have h4 : ∀ x ∈ Nn.sent m 0, Mg.pin x.1 x.2 (z, b.1) (strsOf Fr b.2) w := hi (.pin m 0) (by simp)
  have h5 : Mg.pin Nn.index.1 Nn.index.2 (z, b.1) (strsOf Fr b.2) w := hi .pinI (by simp)
  exact ⟨ui, sv, hsv, c, hc, hr, he, M.pins z b.1 _ w ⟨h3, h4, h5⟩,
    M.merged z b.1 _ w ui sv hsv c hc hr hok' hMb h1,
    M.wo z b.1 _ w ui sv hsv c hc hr he hok' hRow hWb h2⟩

/-- **THE MERGE's FOURTH TIE**: the merge's relation in front gives what the row closes; what the
row reads stands behind the yes already (hw) and rides back past it: hcb: NO PREMISE ON THE FILLING
ALONE: it hangs on the merge's yes and on the strings behind it. -/
theorem merge_t4
    (M : MergeFill cs G arr smp rc decT claims lin xM xI posM posI P h hn ni own R Wa Wb Nn Mg
      links ps k m)
    (z : Pp) (a b : S × Fr.E.Str) (w : Wit Cells Tok MsgT) (hm : ¬ a.1.failed ≠ none)
    (hMa : MaskAt own xM R a.1) (hWa : Wa a.1)
    (hw : relAt (meansQ Nn Mg fun s => (z, s)) (outsQ links ps k) b w)
    (hcb : ∀ i ∈ [Item.pinW, .pin m 0, .pinI], meansQ Nn Mg (fun s => (z, s)) i b w →
      meansQ Nn Mg (fun s => (z, s)) i a w)
    (hr : RelFrontR cs G arr (smp z) rc (decT z) xM xI posM P h hn ni a w) :
    relAt (meansQ Nn Mg fun s => (z, s)) (insQ links ps k) a w := by
  obtain ⟨ui, sv, hsv, c, hc, hra, _, hwt⟩ := hr
  have hb : ∀ i ∈ [Item.pinW, .pin m 0, .pinI], meansQ Nn Mg (fun s => (z, s)) i a w :=
    fun i hi => hcb i hi (hw i (by
      unfold outsQ
      rw [M.outs, M.ctx]
      exact List.mem_append_left _ (List.mem_append_right _ hi)))
  intro i hi
  unfold insQ at hi
  rw [M.ins, M.ctx] at hi
  rcases List.mem_append.1 hi with hi | hi
  · rcases List.mem_append.1 hi with hi | hi
    · obtain rfl := List.mem_singleton.1 hi
      exact M.weights z a.1 _ w ui sv hsv c hc hra hMa hWa hwt
    · exact hb i hi
  · obtain rfl := List.mem_singleton.1 hi
    exact not_not.1 hm

/-- **THE FIELD "merged", PAID**, at posM := `posMask R`: at every filling whose "forms m 9 merged"
gives the table's own sentence on linear forms at a run under which the merge's run of claims is
stated, read at the members' tables. ms: the list of members; xM is the first of them with its
place. -/
theorem merged_field (ms : List Mem) (states : ℕ → List (K9.RunOf S)) (pc : ℕ)
    (run name : String) (hst : ((states pc).find? fun r => r.1 == run) =
      some (name, Johnson.Desc.First.ForkMerge.headMergeClaim))
    (hx : (ms.find? fun y => decide (seatOf y = seatOf xM)) = some xM)
    (hf : ∀ (z : Pp) (b : S) (y : VerifiableInference.Desc.Strs) (w : Wit Cells Tok MsgT),
      Mg.forms m 9 "merged" (z, b) y w →
      formsQ (K9.Readers.ofStates states) own pc run b (seatTab cs arr ms w))
    (z : Pp) (b : S) (y : VerifiableInference.Desc.Strs) (w : Wit Cells Tok MsgT)
    (ui : Fin P.lay.U.size) (sv : ℕ) (hsv : sv < P.nMsg) (c : ℕ) (hc : c < ni)
    (hb : BehindOk (recNums P h hn ni ui sv hsv c hc) b) (hM : MaskAt own xM R b)
    (hm : Mg.forms m 9 "merged" (z, b) y w) :
    MergedHere (recNums P h hn ni ui sv hsv c hc) (rc w.cells)
      (vecBy cs arr P.nMsg (posMask R) xM w) (vecBy cs arr ni posI xI w) b :=
  merged_at_member (recNums P h hn ni ui sv hsv c hc) cs arr ms states own pc run name hst hb w _ _
    xM R hM hx (hf z b y w hm)

/-- **THE FIELD "weights", PAID**, at posM := `posMask R`: at every filling whose "forms m 4
weights" follows from the layer's sentence `FillP1.wtP1` at the cells' reader rc and a reader of the
mask row that is the forms' own at the open segment's part. -/
theorem weights_field (ms : List Mem)
    (hx : (ms.find? fun y => decide (seatOf y = seatOf xM)) = some xM)
    (maskOf : Pp × S → Wit Cells Tok MsgT → ℕ → GE)
    (hmask : ∀ (z : Pp) (a : S) (w : Wit Cells Tok MsgT) a9, K9.segAt? a = some a9 →
      ∀ j, maskOf (z, a) w j = (dataQ own a9 (seatTab cs arr ms w)).mask j)
    (hf : ∀ (z : Pp) (a : S) (y : VerifiableInference.Desc.Strs) (w : Wit Cells Tok MsgT),
      Wa a → FillP1.wtP1 P ni (fun w => rc w.cells) maskOf (z, a) y w →
      Mg.forms m 4 "weights" (z, a) y w)
    (z : Pp) (a : S) (y : VerifiableInference.Desc.Strs) (w : Wit Cells Tok MsgT)
    (ui : Fin P.lay.U.size) (sv : ℕ) (hsv : sv < P.nMsg) (c : ℕ) (hc : c < ni)
    (hr : ReadsAt a ui.val sv) (hM : MaskAt own xM R a) (hA : Wa a)
    (hw : WeightsHere (recNums P h hn ni ui sv hsv c hc) (rc w.cells)
      (vecBy cs arr P.nMsg (posMask R) xM w) a) :
    Mg.forms m 4 "weights" (z, a) y w :=
  hf z a y w hA ((FillP1.wtP1_iff P h hn ni _ _ (z, a) y w).2 ⟨ui, sv, hsv, c, hc, hr,
    weights_at_forms (recNums P h hn ni ui sv hsv c hc) cs arr ms own w _ xM R hM hx _
      (hmask z a w) hw⟩)

end VerifiableInference.Desc.First.MergeLaw

#print axioms VerifiableInference.Desc.First.MergeLaw.weights_field
#print axioms VerifiableInference.Desc.First.MergeLaw.merged_field
#print axioms VerifiableInference.Desc.First.MergeLaw.merge_t1_fill
#print axioms VerifiableInference.Desc.First.MergeLaw.merge_t3
#print axioms VerifiableInference.Desc.First.MergeLaw.merge_t4
