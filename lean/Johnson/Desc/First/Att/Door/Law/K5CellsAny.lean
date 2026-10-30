-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/Door/Law/K5CellsAny.lean: kind K5: THE FIELD cells OF K5Rest (K5AtMgPaid.lean: "under the smallness constraint the cells read off the pinned messages are the model's integers": the one law over witnesses), AS A THEOREM UNDER CONDITIONS ON PUBLIC DATA
ALONE: GENERAL IN THE LETTERS OF THE COMPOSED MEANING's READER OF A WITNESS (hidAtSeat, Johnson/P5J/MeansQ.lean, at the library's own sizes and the seats off the layout by the label). No closed constant is imported.

"Off the pads" stands not as PlacesOffPad (Johnson/P5J/HidBears.lean) at all segments, but as OwnNamed (Johnson/Desc/First/Look/K3CopiesRead.lean) at the two segments that the field reads: SO ALL FOUR CONDITIONS ARE FIELDS OF THE LOOKUP ARGUMENT's OWN LEDGER
(AttOwedR's tie · one · own at segment 2 g + 1; LayOwedR's own at segment 2 g: Johnson/Desc/Sound/MgAt/K3Owed.lean), text for text: one evaluation serves both kinds.

Why. A JOINING OF OTHER FILES' THEOREMS; no new mathematics: cellsAre_own (Johnson/Goal/Meaning/ReadingsOneLook.lean), maOf_ownOf (HidWord.lean) and sameArr_of_fit (HidSeat.lean) ·
symsAre_readAt (Johnson/Desc/First/Look/K3CopiesRead.lean) · readAt_offPad (Johnson/Desc/Sound/ReadAt.lean) and sizesFit_sizesOf (Johnson/P5J/HidAtPlan.lean).

Main names:
  `tlAt_att`: the meaning's record of the approximate range proof at segment 2 g + 1 is the group's plan's.
  `symAt_of_own`: under OwnNamed at a segment its symbols, as it reads them, are the symbols of the witness's shared components.
  `ownNamed_of_places`: SeatsNamed and PlacesOffPad (Johnson/P5J/HidBears.lean: ONE condition for all segments, with a test with code of its own) give OwnNamed at each segment: so whoever has that one needs no own₁ | own₀.
  `ma_is_own`: IN THE GOALS' SCOPE, under OwnNamed at segments 2 g + 1 and 2 g: the list that the hidden values hold for group g's attention sub-proof IS that sub-proof's own list, as functions (so the borrowed array qa is read alike by
    reader and owner).
  `cells_any`: **the field**, at Zof := fun w => (H.hid w).MA g · bsW := H.base, from: T (linkTieB: a test with code) · O (OneNumber at wn := id: a test with code: oneNumberB) · own₁ · own₀ (OwnNamed at the segment and at its group's segment) · hG (GroupsSeated: follows from the standing hypotheses, "the head":
    h.plan.hG, by PlanOk.hG, Johnson/P5J/PlanOk.lean). hN stands in hidAtSeat's type alone.
THE LETTER idx (where a message of a number stands in the segment's own list) IS A LETTER OF EACH SEGMENT: it is bound here behind g and x. With one idx for all segments T cannot hold at two segments.
Is it empty here? T · O · own₁ · own₀ ARE SHOWN AT NOTHING HERE. As reported, T has been evaluated true at all 25 segments of the public files of another build, at another num (numP); the other three have run nowhere.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.P5J.HidAtPlan
import Johnson.P5J.HidBears
import Johnson.Desc.First.Look.K3CopiesRead
import Johnson.Goal.Meaning.ReadingsOneLook
import Johnson.Goal.Meaning.HidWord
import Johnson.Goal.Meaning.PlanShapes
import Johnson.Desc.First.Att.K05PlanOfPublic

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace H2K5.Door
open OnBytes OnBytes.Model
open VerifiableInference.Desc VerifiableInference.Desc.First VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First.Look (Sent lookAt sigListCalls CellsAre szOf)
open VerifiableInference.Desc.First.Att.P (place_calls)
open VerifiableInference.OnPublicFiles (OneNumber OwnNamed symsAre_readAt)
open VerifiableInference.OnPublicFiles.Flat (GE)

/-- The meaning's record of the approximate range proof at segment 2 g + 1 is the group's plan's. -/
theorem tlAt_att {X : Verify.Public} {g : ℕ} {a : Attention.Plan} (hg : g < 12) (ha : X.A[g]? = some a) :
    _root_.Meaning.tlAt X (2 * g + 1) = a.seam.tl := by
  unfold _root_.Meaning.tlAt
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), show (2 * g + 1) / 2 = g by omega, ha]
  rfl

section
variable {Z : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : Option ByteArray} {X : Verify.Public} {P Cells Tok : Type} {rows cols : ℕ}
  (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp) (hX : Verify.publicOf Z.pol Z.KL lay = .ok X)
  (D : Sent) (arr : ℕ → ℕ → ℕ) (ms : List Mem) (N : Numbers) (num : ℕ → ℕ → ℕ)
  (tokV : Tok → Fin Inst.Model.ppref.V) (req : P × P5J.TS → P5J.TReq) (dec : P × P5J.TS → Strs → Option (Fin rows → Fin cols → GE))
  (hN : SeatsNamed arr N (_root_.Meaning.sizesOf X)
    (_root_.Meaning.seatBy (_root_.Meaning.fLay D.layout num) X (_root_.Meaning.sizesOf X)))
  (hG : GroupsSeated ms N)

omit hN in
include hG in
/-- Under OwnNamed at a segment its symbols, as it reads them, are the symbols of the witness's shared components. -/
theorem symAt_of_own {k : ℕ} (Own : OwnNamed X D num (_root_.Meaning.tlAt X) k arr ms N) (w : Wit Cells Tok MsgT) :
    _root_.Meaning.symAt (_root_.Meaning.sizesOf X k)
        (_root_.Meaning.seatBy (_root_.Meaning.fLay D.layout num) X (_root_.Meaning.sizesOf X) k) (readAt D.codes arr ms N k w) =
      _root_.Meaning.symAt (_root_.Meaning.sizesOf X k)
        (_root_.Meaning.seatBy (_root_.Meaning.fLay D.layout num) X (_root_.Meaning.sizesOf X) k) w.msg := by
  funext μ r c
  exact readAt_offPad D.codes arr ms N k _ _ _ w (Own μ.val r.val c.val μ.isLt r.isLt c.isLt).1 hG
    (Own μ.val r.val c.val μ.isLt r.isLt c.isLt).2

include hN in
omit hG in
/-- The two conditions at all segments (SeatsNamed · PlacesOffPad) give OwnNamed at each. -/
theorem ownNamed_of_places
    (hO : P5J.PlacesOffPad D.codes arr ms N (_root_.Meaning.sizesOf X)
      (_root_.Meaning.seatBy (_root_.Meaning.fLay D.layout num) X (_root_.Meaning.sizesOf X))) (k : ℕ) :
    OwnNamed X D num (_root_.Meaning.tlAt X) k arr ms N :=
  fun μ i c hμ hi hc => ⟨hN k ⟨μ, hμ⟩ i c hi hc, hO k ⟨μ, hμ⟩ i c hi hc⟩

include hZ hR hX in
/-- **The hidden values' list of group g's attention sub-proof is that sub-proof's own list, as functions.** -/
theorem ma_is_own {g : ℕ} (hg : g < 12) (own₁ : OwnNamed X D num (_root_.Meaning.tlAt X) (2 * g + 1) arr ms N)
    (own₀ : OwnNamed X D num (_root_.Meaning.tlAt X) (2 * g) arr ms N) (w : Wit Cells Tok MsgT) :
    ((P5J.hidAtSeat (rows := rows) (cols := cols) X D.codes arr ms N (_root_.Meaning.sizesOf X)
      (_root_.Meaning.seatBy (_root_.Meaning.fLay D.layout num) X (_root_.Meaning.sizesOf X)) tokV req dec hN hG).hid w).MA g =
      _root_.Meaning.ownL X D num (_root_.Meaning.tlAt X) (fun k => readAt D.codes arr ms N k w) (2 * g + 1) := by
  have f := P5J.sizesFit_sizesOf hZ hR hX
  have o := _root_.Meaning.seatsOne_of_planFit (s := _root_.Meaning.sizesOf X) (_root_.Meaning.fLay D.layout num)
    (_root_.Meaning.planFit_of_core hX (OnBytes.Road.Hd.core_of_scope hZ hR hX))
  have A : _root_.Meaning.SameArr (_root_.Meaning.sizesOf X (2 * g + 1))
      (_root_.Meaning.symAt (_root_.Meaning.sizesOf X (2 * g + 1))
        (_root_.Meaning.seatBy (_root_.Meaning.fLay D.layout num) X (_root_.Meaning.sizesOf X) (2 * g + 1)) (readAt D.codes arr ms N (2 * g + 1) w))
      ((OnBytes.Road.Hd.shapeA X g).cf.NAs + 3) (_root_.Meaning.sizesOf X (2 * g))
      (_root_.Meaning.symAt (_root_.Meaning.sizesOf X (2 * g))
        (_root_.Meaning.seatBy (_root_.Meaning.fLay D.layout num) X (_root_.Meaning.sizesOf X) (2 * g)) (readAt D.codes arr ms N (2 * g) w))
      (OnBytes.Model.Layer.matIx X.y).iQA := by
    rw [symAt_of_own D arr ms N num hG own₁ w, symAt_of_own D arr ms N num hG own₀ w]
    exact _root_.Meaning.sameArr_of_fit ((_root_.Meaning.sizes_of_fit f).2 g hg) (o.att g hg) w.msg
  exact _root_.Meaning.maOf_ownOf (X := X) (s := _root_.Meaning.sizesOf X)
    (y := fun k => _root_.Meaning.symAt (_root_.Meaning.sizesOf X k)
      (_root_.Meaning.seatBy (_root_.Meaning.fLay D.layout num) X (_root_.Meaning.sizesOf X) k) (readAt D.codes arr ms N k w)) A

include hZ hR hX in
/-- **THE FIELD cells, UNDER CONDITIONS ON PUBLIC DATA ALONE.** -/
theorem cells_any {g : ℕ} (hg : g < 12) {a : Attention.Plan} (ha : X.A[g]? = some a) {x : Look.Place}
    (hx : lookAt X (2 * g + 1) false = some x) (rad : OracleShape → ℕ) (idx : ℕ → ℕ)
    (seatT : Fin (sigListCalls D rad x.link).length → ℕ × ℕ)
    (T : _root_.Meaning.linkTieB X D rad num idx x.link a.seam.tl = true)
    (O : OneNumber X D rad num idx (_root_.Meaning.tlAt X) x.link seatT arr id)
    (own₁ : OwnNamed X D num (_root_.Meaning.tlAt X) x.link arr ms N) (own₀ : OwnNamed X D num (_root_.Meaning.tlAt X) (2 * g) arr ms N) :
    ∀ w : Wit Cells Tok MsgT,
      (P5J.hidAtSeat (rows := rows) (cols := cols) X D.codes arr ms N (_root_.Meaning.sizesOf X)
        (_root_.Meaning.seatBy (_root_.Meaning.fLay D.layout num) X (_root_.Meaning.sizesOf X)) tokV req dec hN hG).base (2 * g + 1) w →
      CellsAre x a.S a.seam.tl D rad (msgsOf D.codes (sigListCalls D rad x.link) seatT arr w)
        (((P5J.hidAtSeat (rows := rows) (cols := cols) X D.codes arr ms N (_root_.Meaning.sizesOf X)
          (_root_.Meaning.seatBy (_root_.Meaning.fLay D.layout num) X (_root_.Meaning.sizesOf X)) tokV req dec hN hG).hid w).MA g) := by
  intro w hb
  have h4 : X.p4 = true := (_root_.Meaning.scope_plans hZ hR hX).1
  have hxl : x.link = 2 * g + 1 := (place_calls h4 ha hx).2.2.1
  have htl : _root_.Meaning.tlAt X x.link = a.seam.tl := by
    rw [hxl]
    exact tlAt_att hg ha
  have T' : _root_.Meaning.linkTieB X D rad num idx x.link (_root_.Meaning.tlAt X x.link) = true := by
    rw [htl]
    exact T
  have hm : _root_.Meaning.SymsAre X D rad num idx (_root_.Meaning.tlAt X) (fun k => readAt D.codes arr ms N k w) x.link
      (msgsOf D.codes (sigListCalls D rad x.link) seatT arr w) := symsAre_readAt T' O own₁ hG w
  have hB : _root_.Meaning.BaseSegF (fun j => szOf (_root_.Meaning.tlAt X j))
      (_root_.Meaning.seatBy (_root_.Meaning.fLay D.layout num) X fun j => szOf (_root_.Meaning.tlAt X j))
      (fun k => readAt D.codes arr ms N k w) x.link := by
    rw [hxl]
    exact hb
  have e2 : _root_.Meaning.ownL X D num (_root_.Meaning.tlAt X) (fun k => readAt D.codes arr ms N k w) x.link =
      ((P5J.hidAtSeat (rows := rows) (cols := cols) X D.codes arr ms N (_root_.Meaning.sizesOf X)
        (_root_.Meaning.seatBy (_root_.Meaning.fLay D.layout num) X (_root_.Meaning.sizesOf X)) tokV req dec hN hG).hid w).MA g := by
    rw [hxl]
    exact (ma_is_own hZ hR hX D arr ms N num tokV req dec hN hG hg (hxl ▸ own₁) own₀ w).symm
  have R := _root_.Meaning.cellsAre_own (_root_.Meaning.tlAt X) (fun k => readAt D.codes arr ms N k w) T' (S := a.S)
    (msgsOf D.codes (sigListCalls D rad x.link) seatT arr w) hm hB
  rw [htl, e2] at R
  exact R

end

end H2K5.Door

#print axioms H2K5.Door.tlAt_att
#print axioms H2K5.Door.symAt_of_own
#print axioms H2K5.Door.ownNamed_of_places
#print axioms H2K5.Door.ma_is_own
#print axioms H2K5.Door.cells_any
