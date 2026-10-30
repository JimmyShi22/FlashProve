-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/K4PinsPlanesFirst.lean: THE LINE planes OF `K4Lines`
(Johnson/Road/K4/CloseAtTable.lean) IN THE FIRST GROUP, AT THE FILLED PINNED PART: the road's
sentence on the planes, at the first group's value and filling, gives the lookup's item worth
"planes". The twin of three theorems of Johnson/Road/K4/K4PinsPlanes.lean, by their proofs. Its
definitions (`PinPlan.maskN`, `PinPlan.seatN`, `tupleW`, `nuLay`, `Covers`, `PlaceIs`) and
`fork_lay` name no group and no value: they are taken as they stand. No draw, no count.

  `mats_layF`, `nu_layF`: the first group's value's matrices and the road's valuation are the
    caller's, under `SitsIn` and `Covers`.
  `planes_worthF`: `K3WorthPlanes` at the caller's letters, from the filling's promise in front and
    its sentence worthPlanes.

Limits. K04_law IS NOT PROVED BY THIS. All limits of K4PinsPlanes.lean stand. WHAT PARTS FROM IT:
the value is `RefSeat.atRecF` (CloseRefFirst.lean), the letters `Plan4KF.lettersOfF`
(CloseFillFirst.lean); no premise on the group is asked: these three read the matrices, the mask row
and the seat alone, which the first group's value shares with a later group's. USER: `k4_own_allF`
(K4PinsAllFirst.lean). The reference sizes alone.
-/
import Johnson.Road.K4.K4PinsPlanes
import Johnson.Road.K4.CloseRefFillFirst

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
open VerifiableInference.Desc.First.Look (Sent sigListCalls cellJ szOf finOf laySg msgLay matsOfE
  lyCell lyMask)
open VerifiableInference.Desc.Sound (Frame Mem MsgT msgsOf)
open VerifiableInference.OnPublicFiles (K3OutPlanes K3WorthPlanes K3LeftAt)
open Cb.Fo (zext)
open Inst.Model (Scl)

section
variable (x : VerifiableInference.Desc.First.Look.Place) (D : Sent)
  (rad : OnBytes.OracleShape → ℕ) (seatT : Fin (sigListCalls D rad x.link).length → ℕ × ℕ)
  (posI : ℕ → Bool × ℕ × ℕ) (tl : HTailF2) (oW : Cb.OMsg Cb.Gl.E) {Cells : Type}
  (enc : Cells → oW.Msg)
  (wOf : oW.Msg → ℕ → ℕ → Cb.Gl.E) (nr nc : ℕ)

variable [scl : Scl] {Tok : Type} (arr : ℕ → ℕ → ℕ) (ms : List Mem) (N : Numbers) (m : ℕ)

/-- **The value's matrices are the caller's**, under `SitsIn` and `Covers`. -/
theorem mats_layF (hs : SitsIn (sigListCalls D rad x.link) seatT ms N m) (y : Lay)
    (nM nR nC n0 ns nx v7 : ℕ) (hC : Covers tl nM nR nC) (X : Public) (p : Par)
    (w : Wit Cells Tok MsgT) :
    (((planAt x D rad seatT (cutW enc wOf nr nc) posI).seatN x.ns N tl y nM nR nC n0 ns nx
        v7).atRecF X p).mats (partOf D.codes arr ms N m w) =
      matsOfE (msgLay x tl D rad oW wOf nr nc (tupleW x D rad seatT oW enc arr w)) := by
  obtain ⟨h1, -⟩ := lay_part x D rad seatT (cutW enc wOf nr nc) posI tl oW wOf nr nc arr ms N m hs w
    (tupleW x D rad seatT oW enc arr w) rfl
  funext a r c
  show (if a < nM ∧ r < nR ∧ c < nC then
      (planAt x D rad seatT (cutW enc wOf nr nc) posI).raw tl (partOf D.codes arr ms N m w) a r c
      else 0) = _
  rw [h1]
  by_cases hb : a < nM ∧ r < nR ∧ c < nC
  · rw [if_pos hb]
  · rw [if_neg hb]
    have e : cellJ (szOf tl) a r c = none := by
      cases hc : cellJ (szOf tl) a r c with
      | none => rfl
      | some j => exact absurd (hC a r c (by rw [hc]; rfl)) hb
    unfold PinPlan.raw
    rw [e]
    rfl

/-- **The road's valuation is the caller's**, under `SitsIn` and `Covers`. -/
theorem nu_layF (hs : SitsIn (sigListCalls D rad x.link) seatT ms N m) (y : Lay)
    (nM nR nC n0 ns nx v7 iB : ℕ) (hC : Covers tl nM nR nC) (X : Public) (p : Par) (w : Wit Cells
        Tok MsgT) :
    (((planAt x D rad seatT (cutW enc wOf nr nc) posI).seatN x.ns N tl y nM nR nC n0 ns nx
        v7).atRecF X p).toPlan4K.nuOf (partOf D.codes arr ms N m) iB w =
      nuLay x D rad tl oW wOf nr nc iB (tupleW x D rad seatT oW enc arr w) := by
  obtain ⟨-, h2⟩ := lay_part x D rad seatT (cutW enc wOf nr nc) posI tl oW wOf nr nc arr ms N m hs w
    (tupleW x D rad seatT oW enc arr w) rfl
  funext pq
  cases pq with
  | mask j =>
    show (if j < x.ns then
        (planAt x D rad seatT (cutW enc wOf nr nc) posI).mask (partOf D.codes arr ms N m w) j else
          0) =
      msgLay x tl D rad oW wOf nr nc (tupleW x D rad seatT oW enc arr w) (lyMask x.ns tl nr nc j)
    by_cases hj : j < x.ns
    · rw [if_pos hj, h2 j hj]
    · have e : finOf x.ns j = none := dif_neg hj
      rw [if_neg hj]
      unfold lyMask
      rw [e]
      rfl
  | cell r c =>
    show (((planAt x D rad seatT (cutW enc wOf nr nc) posI).seatN x.ns N tl y nM nR nC n0 ns nx
        v7).atRecF X p).mats (partOf D.codes arr ms N m w) iB r c =
      matsOfE (msgLay x tl D rad oW wOf nr nc (tupleW x D rad seatT oW enc arr w)) iB r c
    rw [mats_layF x D rad seatT posI tl oW enc wOf nr nc arr ms N m hs y nM nR nC n0 ns nx v7 hC X p
      w]
  | key _ _ => rfl
  | zero => rfl

end

section
variable [scl : Scl] (x : VerifiableInference.Desc.First.Look.Place) (D : Sent)
  (rad : OnBytes.OracleShape → ℕ) (seatT : Fin (sigListCalls D rad x.link).length → ℕ × ℕ)
  (posI : ℕ → Bool × ℕ × ℕ) (tl : HTailF2) (oW : Cb.OMsg Cb.Gl.E) {Cells : Type}
  (enc : Cells → oW.Msg)
  (wOf : oW.Msg → ℕ → ℕ → Cb.Gl.E) (nr nc : ℕ) {Tok : Type} {Fr : Frame} (arr : ℕ → ℕ → ℕ)
  (ms : List Mem) (N : Numbers) (m : ℕ)

/-- **THE ROAD's SENTENCE ON THE PLANES GIVES THE LOOKUP's ITEM worth "planes"**, from the filling's
promise in front, `SitsIn`, `Covers`, `PlaceIs`, and "what `S.lookHeard?` finds the seat's reader
finds". -/
theorem planes_worthF (hs : SitsIn (sigListCalls D rad x.link) seatT ms N m) (y : Lay)
    (nM nR nC n0 ns nx v7 : ℕ) (X : Public) (p : Par)
    (hC : Covers tl nM nR nC) {first : ℕ} (hP : PlaceIs x p first)
    {Q3 : Fork → Prop} {on0 on' : S × Fr.E.Str → Prop}
    {ctx0 : S × Fr.E.Str → Wit Cells Tok MsgT → Prop} {dec : S × Fr.E.Str → PinM Cells}
    (a : S × Fr.E.Str) (w : Wit Cells Tok MsgT)
    (hl : ∀ g, a.1.lookHeard? = some g → seatS.look a.1 = some g)
    (hon : ((((planAt x D rad seatT (cutW enc wOf nr nc) posI).seatN x.ns N tl y nM nR nC n0 ns nx
      v7).atRecF X p).lettersOfF (partOf D.codes arr ms N m) p first p.P.y.fo Q3 on0 on' ctx0
      dec).on a)
    (hW : ((((planAt x D rad seatT (cutW enc wOf nr nc) posI).seatN x.ns N tl y nM nR nC n0 ns nx
      v7).atRecF X p).lettersOfF (partOf D.codes arr ms N m) p first p.P.y.fo Q3 on0 on' ctx0
      dec).worthPlanes a w) :
    K3WorthPlanes (fun s : S => s.fork?) (fun s : S => s.lookHeard?) x.fs x.lm x.F.next
      (fun w => nuLay x D rad tl oW wOf nr nc (matIx p.P.y).iB (tupleW x D rad seatT oW enc arr w))
      a.1 w := by
  intro g F' hf hh
  have hlook : seatS.look a.1 = some g := hl g hh
  have hfork : seatS.fork a.1 = F' := fork_lay hlook hf
  obtain ⟨_, F0, F1, g', rs, _, _, hK, hg', _⟩ := hon
  have eg : g' = g := Option.some.inj (hg'.symm.trans hlook)
  have hshape : g.shape = p.P.y.fo := eg ▸ hK.shape
  have h0 := hW g hlook
  rw [nu_layF x D rad seatT posI tl oW enc wOf nr nc arr ms N m hs y nM nR nC n0 ns nx v7 _ hC X p
    w,
    hshape] at h0
  rw [hP.shape, hP.packing, hP.first, ← hfork]
  exact h0

end

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.mats_layF
#print axioms OnBytes.Road.K4.nu_layF
#print axioms OnBytes.Road.K4.planes_worthF
