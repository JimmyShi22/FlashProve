-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/K4PinsRiderFirst.lean: THE LINE rider OF `K4Lines`
(Johnson/Road/K4/CloseAtTable.lean) IN THE FIRST GROUP, AT THE FILLED PINNED PART: the road's
sentence on the rider, at the first group's value and filling, gives the lookup's item worth
"rider". The twin of two theorems of Johnson/Road/K4/K4PinsRider.lean, by their proofs; `point_lay`
names no group and is taken as it stands. No draw, no count.

  `cells_layF`: the first group's value's cells are the caller's, under `SitsIn` and `Covers`, where
    the caller's layout is the value's (`Plan4KF.cells_eqF`, ValueSeatFirst.lean; `mats_layF`).
  `rider_worthF`: `K3WorthRider` at the caller's letters, from the filling's promise in front and
    its sentence worthRider.

Limits. K04_law IS NOT PROVED BY THIS. All limits of K4PinsRider.lean stand. WHAT PARTS FROM IT: the
value is `RefSeat.atRecF` (CloseRefFirst.lean), its cells are written fullF.rd (fullF.msg t), the
letters are `Plan4KF.lettersOfF` (CloseFillFirst.lean); no premise on the group is asked. USER:
`k4_own_allF` (K4PinsAllFirst.lean). The reference sizes alone.
-/
import Johnson.Road.K4.K4PinsRider
import Johnson.Road.K4.K4PinsPlanesFirst

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

section
variable [scl : Scl] (x : VerifiableInference.Desc.First.Look.Place) (q : LayPub) (D : Sent)
  (rad : OnBytes.OracleShape → ℕ) (seatT : Fin (sigListCalls D rad x.link).length → ℕ × ℕ)
  (posI : ℕ → Bool × ℕ × ℕ) (tl : HTailF2) (oW : Cb.OMsg Cb.Gl.E) {Cells : Type}
  (enc : Cells → oW.Msg)
  (wOf : oW.Msg → ℕ → ℕ → Cb.Gl.E) (nr nc : ℕ) {Tok : Type} {Fr : Frame} (arr : ℕ → ℕ → ℕ)
  (ms : List Mem) (N : Numbers) (m : ℕ)

/-- **The value's cells are the caller's**, under `SitsIn` and `Covers`, where the caller's layout
is the value's. -/
theorem cells_layF (hs : SitsIn (sigListCalls D rad x.link) seatT ms N m)
    (nM nR nC n0 ns nx v7 : ℕ) (hC : Covers tl nM nR nC) (X : Public) (p : Par)
    (w : Wit Cells Tok MsgT) :
    (((planAt x D rad seatT (cutW enc wOf nr nc) posI).seatN x.ns N tl q.y nM nR nC n0 ns nx
        v7).atRecF X p).toLF.planF.fullF.rd
        ((((planAt x D rad seatT (cutW enc wOf nr nc) posI).seatN x.ns N tl q.y nM nR nC n0 ns nx
          v7).atRecF X p).toLF.planF.fullF.msg
          (partOf D.codes arr ms N m w)) =
      layCells x q tl D rad oW wOf nr nc (tupleW x D rad seatT oW enc arr w) := by
  rw [Plan4KF.cells_eqF _ _ (fun _ _ _ hb => if_neg hb),
    mats_layF x D rad seatT posI tl oW enc wOf nr nc arr ms N m hs q.y nM nR nC n0 ns nx v7 hC X p
      w]
  rfl

/-- **THE ROAD's SENTENCE ON THE RIDER GIVES THE LOOKUP's ITEM worth "rider"**, from the filling's
promise in front, `SitsIn`, `Covers`, `PlaceIs`, the plan's depth of a tree is `Dk` at the reference
sizes and not below lT, and "what `S.lookHeard?` finds the seat's reader finds". -/
theorem rider_worthF (hs : SitsIn (sigListCalls D rad x.link) seatT ms N m)
    (nM nR nC n0 ns nx v7 : ℕ) (X : Public) (p : Par)
    (hC : Covers tl nM nR nC) {first : ℕ} (hP : PlaceIs x p first)
    (hdT : p.P.y.fo.dT = Dk Dim.ref) (hlT : Dim.ref.lT ≤ Dk Dim.ref)
    {Q3 : Fork → Prop} {on0 on' : S × Fr.E.Str → Prop}
    {ctx0 : S × Fr.E.Str → Wit Cells Tok MsgT → Prop} {dec : S × Fr.E.Str → PinM Cells}
    (a : S × Fr.E.Str) (w : Wit Cells Tok MsgT)
    (hl : ∀ g, a.1.lookHeard? = some g → seatS.look a.1 = some g)
    (hon : ((((planAt x D rad seatT (cutW enc wOf nr nc) posI).seatN x.ns N tl q.y nM nR nC n0 ns nx
      v7).atRecF X p).lettersOfF (partOf D.codes arr ms N m) p first p.P.y.fo Q3 on0 on' ctx0
      dec).on a)
    (hR : ((((planAt x D rad seatT (cutW enc wOf nr nc) posI).seatN x.ns N tl q.y nM nR nC n0 ns nx
      v7).atRecF X p).lettersOfF (partOf D.codes arr ms N m) p first p.P.y.fo Q3 on0 on' ctx0
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
  have hc := cells_layF x q D rad seatT posI tl oW enc wOf nr nc arr ms N m hs nM nR nC n0 ns nx v7
    hC X p w
  show Blocks.ext Dim.ref.lT
      (d10 Dim.ref (layCells x q tl D rad oW wOf nr nc (tupleW x D rad seatT oW enc arr w)) i.val)
      (fun t => (_root_.Fo.rdA Reading.gl g.zx ++ _root_.Fo.rdA Reading.gl g.zy).getD
        (x.fs.dT - Dim.ref.lT + t) 0) = 0
  rw [← hc, hP.shape, hdT,
    ← ext_congr_pt Dim.ref.lT _ (fun t ht => point_lay Dim.ref g hzx hlT t ht)]
  exact h0

end

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.cells_layF
#print axioms OnBytes.Road.K4.rider_worthF
