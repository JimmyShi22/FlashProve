-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/K4PinsRider.lean: THE ROAD's SENTENCE ON THE RIDER (the letter worthRider of
Johnson/Road/K4/CloseFill.lean's filling: the selectors' sums at the token point) GIVES THE LOOKUP's
OWN ITEM worth "rider" (`K3WorthRider`, Johnson/Top/H/K3Worth.lean) AT THE CALLER OF THE LOOKUP ON A
LAYERS' LINK's CALLS WITH ITS RIDER (`layRider`, Johnson/Desc/First/Look/K3CallerLay.lean), at the
filled pinned part and the seat of Johnson/Road/K4/K4PinsPlanes.lean. Theorems, by unfolding and
`rider_of_point` (Johnson/Top/H/K3RowOutRider.lean). No draw, no count.

  `cells_lay`: under `SitsIn` and `Covers`: the value's cells off the pinned part of w are the
    caller's `layCells` off `tupleW` w, where the caller's layout is the value's.
  `point_lay`: the library's token point of the lookup's point, read off what was heard
    (`zpos D (zAt g)`), is the last D.lT places of the first part of the heard key point, where g.zx
    has `Dk D` words and D.lT ≤ `Dk D`.
  **`rider_worth`**: `K3WorthRider S.fork? S.lookHeard? (layRider …) x.lm x.F.next (fun _ => ())
    (tupleW …) a.1 w`, from: the filling's promise in front · the road's sentence
    `Lt.worthRider a w` · `SitsIn` · `Covers` · `PlaceIs` · the plan's depth of a tree is the
    library's `Dk` at the reference sizes, and not below lT · "what `S.lookHeard?` finds the seat's
    reader finds". THE SEAT's LAYOUT IS THE CALLER's q.y, BY MAKE.

STANDS OVER Johnson/Top/H/K3Worth.lean, which stands in this tree.

OBJECT: none of its own. USER: Johnson/Road/K4/K4PinsKeys.lean; meant: whoever pays the line rider
of `K4Lines` (Johnson/Road/K4/CloseAtTable.lean) at a meaning whose field worth holds
`K3WorthRider`. LETTERS, filled by nobody: those of K4PinsPlanes.lean, and the caller's public
letters q.

Limits. K04_law IS NOT PROVED BY THIS. WHAT STAYS A PREMISE, AND WHO COULD PAY IT: those of
K4PinsPlanes.lean · (that q.y is the public parameters' layout is owed by whoever lays this seat
into
`RefSeat.k4_own_refS`: its premise on the layout) · p.P.y.fo.dT = Dk Dim.ref: the field
dT of `TreesFit` (Johnson/Road/FormsKeysLook.lean), which follows from the plan's public lines by
`treesFit_of_layout` (Johnson/Road/FormsKeysLookT.lean): that call is not made here. THE TABLE OF
SCALES IS NOT READ by the identity on the selectors: the caller's and the section's may differ. The
item is true of every witness where the verifier's state holds no ledger or nothing heard.

-/
import Johnson.Road.K4.K4PinsPlanes
import Johnson.Road.FormsKeysPortFits
import Johnson.Road.FormsKeysVec

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace OnBytes.Road.K4
open Johnson.Pack
open OnBytes.Model (HTailF2 Fork Reading)
open OnBytes.Model.Layer (Lay matIx)
open OnBytes.Model.Verify (Public)
open OnBytes.Desc.First.K4 (Par seatS)
open VerifiableInference.Desc (Wit)
open VerifiableInference.Desc.First (S Numbers)
open VerifiableInference.Desc.First.Look (Sent sigListCalls laySg msgLay matsOfE LayPub layCells
  layRider)
open VerifiableInference.Desc.Sound (Frame Mem MsgT)
open VerifiableInference.OnPublicFiles (K3WorthRider K3LeftAt rider_of_point)
open Inst.Model (Scl)
open Inst.Model.FFSeg (Dim Dk zpos d10)

/-- The library's token point of the lookup's point, off what was heard, is the last lT places of
the first part of the heard key point. -/
theorem point_lay (D : Dim) (g : OnBytes.Model.Forest.Heard) (hz : g.zx.size = Dk D)
    (hl : D.lT ≤ Dk D) (t : ℕ) (ht : t < D.lT) :
    zpos D (zAt g) t =
      (_root_.Fo.rdA Reading.gl g.zx ++ _root_.Fo.rdA Reading.gl g.zy).getD
        (Dk D - D.lT + t) 0 := by
  have hlt : Dk D - D.lT + t < g.zx.size := by omega
  show zOf Reading.gl g.zx g.zy (Dk D - D.lT + t) = _
  unfold zOf
  rw [if_pos hlt, List.getD_append _ _ _ _ (by
    unfold _root_.Fo.rdA
    rw [List.length_map, Array.length_toList]
    exact hlt)]
  exact _root_.Fo.rdL_getD Reading.gl g.zx _

section
variable [scl : Scl] (x : VerifiableInference.Desc.First.Look.Place) (q : LayPub) (D : Sent)
  (rad : OnBytes.OracleShape → ℕ) (seatT : Fin (sigListCalls D rad x.link).length → ℕ × ℕ)
  (posI : ℕ → Bool × ℕ × ℕ) (tl : HTailF2) (oW : Cb.OMsg Cb.Gl.E) {Cells : Type}
  (enc : Cells → oW.Msg)
  (wOf : oW.Msg → ℕ → ℕ → Cb.Gl.E) (nr nc : ℕ) {Tok : Type} {Fr : Frame} (arr : ℕ → ℕ → ℕ)
  (ms : List Mem) (N : Numbers) (m : ℕ)

/-- **The value's cells are the caller's**, under `SitsIn` and `Covers`, where the caller's layout
is the value's. -/
theorem cells_lay (hs : SitsIn (sigListCalls D rad x.link) seatT ms N m)
    (nM nR nC n0 ns nx v7 : ℕ) (hC : Covers tl nM nR nC) (X : Public) (p : Par) (hg : p.g < 12)
    (w : Wit Cells Tok MsgT) :
    (((planAt x D rad seatT (cutW enc wOf nr nc) posI).seatN x.ns N tl q.y nM nR nC n0 ns nx
        v7).atRec X p hg).plan.cells (partOf D.codes arr ms N m w) =
      layCells x q tl D rad oW wOf nr nc (tupleW x D rad seatT oW enc arr w) := by
  rw [Plan4K.cells_eq _ _ (fun _ _ _ hb => if_neg hb),
    mats_lay x D rad seatT posI tl oW enc wOf nr nc arr ms N m hs q.y nM nR nC n0 ns nx v7 hC X p hg
      w]
  rfl

/-- **THE ROAD's SENTENCE ON THE RIDER GIVES THE LOOKUP's ITEM worth "rider"**, from the filling's
promise in front, `SitsIn`, `Covers`, `PlaceIs`, the plan's depth of a tree is `Dk` at the reference
sizes and not below lT, and "what `S.lookHeard?` finds the seat's reader finds". -/
theorem rider_worth (hs : SitsIn (sigListCalls D rad x.link) seatT ms N m)
    (nM nR nC n0 ns nx v7 : ℕ) (X : Public) (p : Par) (hg : p.g < 12)
    (hC : Covers tl nM nR nC) {first : ℕ} (hP : PlaceIs x p first)
    (hdT : p.P.y.fo.dT = Dk Dim.ref) (hlT : Dim.ref.lT ≤ Dk Dim.ref)
    {Q3 : Fork → Prop} {on0 on' : S × Fr.E.Str → Prop}
    {ctx0 : S × Fr.E.Str → Wit Cells Tok MsgT → Prop} {dec : S × Fr.E.Str → PinM Cells}
    (a : S × Fr.E.Str) (w : Wit Cells Tok MsgT)
    (hl : ∀ g, a.1.lookHeard? = some g → seatS.look a.1 = some g)
    (hon : ((((planAt x D rad seatT (cutW enc wOf nr nc) posI).seatN x.ns N tl q.y nM nR nC n0 ns nx
      v7).atRec X p hg).lettersOf (partOf D.codes arr ms N m) p first p.P.y.fo Q3 on0 on' ctx0
      dec).on a)
    (hR : ((((planAt x D rad seatT (cutW enc wOf nr nc) posI).seatN x.ns N tl q.y nM nR nC n0 ns nx
      v7).atRec X p hg).lettersOf (partOf D.codes arr ms N m) p first p.P.y.fo Q3 on0 on' ctx0
      dec).worthRider a w) :
    K3WorthRider (fun s : S => s.fork?) (fun s : S => s.lookHeard?)
      (layRider x q tl D rad oW wOf nr nc Iop.extNone Unit) x.lm x.F.next (fun _ => ())
      (fun w => tupleW x D rad seatT oW enc arr w) a.1 w := by
  intro g F' _ hh
  have hlook : seatS.look a.1 = some g := hl g hh
  obtain ⟨_, F0, F1, g', rs, _, _, hK, hg', _⟩ := hon
  have eg : g' = g := Option.some.inj (hg'.symm.trans hlook)
  have hzx : g.zx.size = Dk Dim.ref := by
    rw [← eg, hK.zx, hdT]
  refine rider_of_point _ _ _ _ _ _ _ fun i => ?_
  have h0 := hR g hlook i.val i.isLt
  have hc := cells_lay x q D rad seatT posI tl oW enc wOf nr nc arr ms N m hs nM nR nC n0 ns nx v7
    hC X
    p hg w
  show Blocks.ext Dim.ref.lT
      (d10 Dim.ref (layCells x q tl D rad oW wOf nr nc (tupleW x D rad seatT oW enc arr w)) i.val)
      (fun t => (_root_.Fo.rdA Reading.gl g.zx ++ _root_.Fo.rdA Reading.gl g.zy).getD
        (x.fs.dT - Dim.ref.lT + t) 0) = 0
  rw [← hc, hP.shape, hdT,
    ← ext_congr_pt Dim.ref.lT _ (fun t ht => point_lay Dim.ref g hzx hlT t ht)]
  exact h0

end

/-- At the reference sizes the positions' bits are at most the depth of a batch: the library's two
lemmas (Johnson/Road/FormsKeysVec.lean), called. -/
theorem deep_ref : Dim.ref.lT ≤ Dk Dim.ref := OnBytes.Road.lT_le_Dk Dim.ref OnBytes.Road.ref_cap

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.deep_ref
#print axioms OnBytes.Road.K4.point_lay
#print axioms OnBytes.Road.K4.cells_lay
#print axioms OnBytes.Road.K4.rider_worth
