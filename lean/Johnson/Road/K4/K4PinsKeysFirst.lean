-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/K4PinsKeysFirst.lean: THE LINE keys OF `K4Lines` (Johnson/Road/K4/CloseAtTable.lean)
IN THE FIRST GROUP, AT THE FILLED PINNED PART: the road's sentence on the keys, at the first group's
value and filling, gives the lookup's item worth "keys". The twin of four theorems of
Johnson/Road/K4/K4PinsKeys.lean, by their proofs, and four lemmas more. `HeardFits`, `KeysFit`,
`join_of_keys` and what stands in front of them there name no group and no value: they are taken as
they stand; so is `Plan4K.keys_iff` (ValueSeat.lean), at the letters that the first group's value
shares with a later group's. No draw, no count.

  `Plan4.cells_f7`, `Plan4.weights_f7`, `Plan4.keys_f7`: the cells, the weights and the sentence on
    the keys read no slot number f7.
  `cells_layK`: these shared letters' cells are the caller's.
  `RefSeat.weights_eqF`, `weights_layNF`: the first group's weights are the caller's layers'
    matrices.
  `keyVec_layF`: the caller's key vector of a call is the library's at the value's cells and
    weights.
  `keys_worthF`: `K3WorthKeys` at the caller's letters, from the filling's promise in front and its
    sentence worthKeys.

Limits. K04_law IS NOT PROVED BY THIS. All limits of K4PinsKeys.lean stand. WHAT PARTS FROM IT: the
value is `RefSeat.atRecF` (CloseRefFirst.lean), the letters `Plan4KF.lettersOfF`
(CloseFillFirst.lean); the premise p.g < 12 falls, p.g = 0 comes (the value's first layer is 0 by
make; the caller's is 4 p.g). THE FIRST GROUP's SENTENCE worthKeys IS SAID OF THE PLAN WITH ONE SLOT
MORE (`Plan4LF.planF`): that it is the shared letters' sentence: `Plan4.keys_f7`. USER:
`k4_own_allF` (K4PinsAllFirst.lean). The reference sizes alone.
-/
import Johnson.Road.K4.K4PinsKeys
import Johnson.Road.K4.K4PinsRiderFirst

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace OnBytes.Road.K4
open Finset
open Johnson.Pack
open OnBytes.Model (HTailF2 Fork Reading Forest.Heard eqTab)
open OnBytes.Model.Layer (Lay matIx)
open OnBytes.Model.Verify (Public layerShape)
open OnBytes.Desc.First.K4 (Par seatS)
open VerifiableInference.Desc (Wit)
open VerifiableInference.Desc.First (S Numbers)
open VerifiableInference.Desc.First.Look (Sent sigListCalls laySg msgLay matsOfE wOfE LayPub
  layCells layLay)
open VerifiableInference.Desc.Sound (Frame Mem MsgT)
open VerifiableInference.OnPublicFiles (K3WorthKeys K3OutKeys K3LeftAt k3KeysHanded)
open Inst.Model (Scl ppref tbRef)
open Inst.Model.Layout (kRef hRef)
open Inst.Model.FFSeg (Dim Dk aC zc wc KF keyVec layerR LW)

/-- The cells read no slot number f7. -/
theorem Plan4.cells_f7 {E : Type} [Field E] [Fintype E] [scl : Scl] {M X : Type} (Q : Plan4 E M X)
    (n : ℕ) (m : M) : ({ Q with f7 := n } : Plan4 E M X).cells m = Q.cells m := by
  funext c
  unfold Plan4.cells
  cases h : Q.nameOf c with
  | some j =>
    have h' : ({ Q with f7 := n } : Plan4 E M X).nameOf c = some j := h
    rw [Plan4.rd_valid _ _ h', Plan4.rd_valid _ _ h]
    rfl
  | none =>
    have h' : ({ Q with f7 := n } : Plan4 E M X).nameOf c = none := h
    rw [Plan4.rd_invalid _ _ h', Plan4.rd_invalid _ _ h]

/-- Nor do the weights. -/
theorem Plan4.weights_f7 {E : Type} [Field E] [Fintype E] [scl : Scl] {M X : Type}
    (Q : Plan4 E M X) (n : ℕ) (m : M) :
    ({ Q with f7 := n } : Plan4 E M X).weights m = Q.weights m := by
  have e : ({ Q with f7 := n } : Plan4 E M X).Wn (({ Q with f7 := n } : Plan4 E M X).msg m) =
      Q.Wn (Q.msg m) := by
    funext r c
    rw [Plan4.Wn_msg, Plan4.Wn_msg]
  funext l
  unfold Plan4.weights
  rw [e]

/-- The sentence on the keys reads no slot number f7: at every plan. Said once, of a plan that is a
letter; by steps: the cells, the weights, then the sentence's own text. -/
theorem Plan4.keys_f7 {E : Type} [Field E] [Fintype E] [scl : Scl] {M X : Type} (Q : Plan4 E M X)
    (n : ℕ) (x : X) (m : M) : ({ Q with f7 := n } : Plan4 E M X).Keys x m ↔ Q.Keys x m := by
  unfold Plan4.Keys
  rw [Plan4.cells_f7, Plan4.weights_f7]

/-- The cells of the letters that the first group's value shares with a later group's are the
caller's, under `SitsIn` and `Covers`, where the caller's layout is the value's. -/
theorem cells_layK [scl : Scl] (x : VerifiableInference.Desc.First.Look.Place) (q : LayPub)
    (D : Sent) (rad : OnBytes.OracleShape → ℕ)
    (seatT : Fin (sigListCalls D rad x.link).length → ℕ × ℕ) (posI : ℕ → Bool × ℕ × ℕ)
    (tl : HTailF2) (oW : Cb.OMsg Cb.Gl.E) {Cells : Type} (enc : Cells → oW.Msg)
    (wOf : oW.Msg → ℕ → ℕ → Cb.Gl.E) (nr nc : ℕ) {Tok : Type} (arr : ℕ → ℕ → ℕ) (ms : List Mem)
    (N : Numbers) (m : ℕ) (hs : SitsIn (sigListCalls D rad x.link) seatT ms N m)
    (nM nR nC n0 ns nx v7 : ℕ) (hC : Covers tl nM nR nC) (X : Public) (p : Par)
    (w : Wit Cells Tok MsgT) :
    (((planAt x D rad seatT (cutW enc wOf nr nc) posI).seatN x.ns N tl q.y nM nR nC n0 ns nx
        v7).atRecF X p).toPlan4K.plan.cells (partOf D.codes arr ms N m w) =
      layCells x q tl D rad oW wOf nr nc (tupleW x D rad seatT oW enc arr w) := by
  rw [Plan4K.cells_eq _ _ (fun _ _ _ hb => if_neg hb)]
  have e := mats_layF x D rad seatT posI tl oW enc wOf nr nc arr ms N m hs q.y nM nR nC n0 ns nx v7
    hC X p w
  rw [show (((planAt x D rad seatT (cutW enc wOf nr nc) posI).seatN x.ns N tl q.y nM nR nC n0 ns nx
    v7).atRecF X p).toPlan4K.mats (partOf D.codes arr ms N m w) = _ from e]
  rfl

/-- The first group's weights that the value reads, of any matrix that agrees with matAt inside the
reference rows and columns and is 0 outside. -/
theorem RefSeat.weights_eqF [scl : Scl] {M : Type} (U : RefSeat M S) (X : Public) (p : Par)
    (eg : p.g = 0) (t : M) (Wf : ℕ → ℕ → Cb.Gl.E)
    (h : ∀ r c, r < hRef ∧ c < 2 ^ kRef → U.matAt t r c = Wf r c)
    (h0 : ∀ r c, ¬ (r < hRef ∧ c < 2 ^ kRef) → Wf r c = 0) (l : ℕ) :
    (U.atRecF X p).toPlan4K.plan.weights t l = layerR ppref kRef Wf (4 * p.g + l) := by
  have e : (U.atRecF X p).toPlan4K.plan.Wn ((U.atRecF X p).toPlan4K.plan.msg t) = Wf := by
    funext r c
    rw [Plan4.Wn_msg]
    show (if r < hRef ∧ c < 2 ^ kRef then U.matAt t r c else 0) = Wf r c
    by_cases hrc : r < hRef ∧ c < 2 ^ kRef
    · rw [if_pos hrc, h r c hrc]
    · rw [if_neg hrc, h0 r c hrc]
  unfold Plan4.weights
  rw [e, eg]
  rfl

section
variable [scl : Scl] (x : VerifiableInference.Desc.First.Look.Place) (q : LayPub) (D : Sent)
  (rad : OnBytes.OracleShape → ℕ) (seatT : Fin (sigListCalls D rad x.link).length → ℕ × ℕ)
  (posI : ℕ → Bool × ℕ × ℕ) (tl : HTailF2) (oW : Cb.OMsg Cb.Gl.E) {Cells : Type}
  (enc : Cells → oW.Msg)
  (wOf : oW.Msg → ℕ → ℕ → Cb.Gl.E) {Tok : Type} {Fr : Frame} (arr : ℕ → ℕ → ℕ)
  (ms : List Mem) (N : Numbers) (m : ℕ) (nM nR nC n0 ns nx v7 : ℕ) (X : Public) (p : Par)
  (eg : p.g = 0)
include eg

/-- the value: at the seat whose mask row is cut, the caller's layout, the reference matrix -/
local notation "𝐅" => RefSeat.atRecF (PinPlan.seatN (planAt x D rad seatT
  (cutW enc wOf hRef (2 ^ kRef)) posI) x.ns N tl q.y nM nR nC n0 ns nx v7) X p
/-- the letters that it shares with a later group's value -/
local notation "𝐐" => Plan4KF.toPlan4K (RefSeat.atRecF (PinPlan.seatN (planAt x D rad seatT
  (cutW enc wOf hRef (2 ^ kRef)) posI) x.ns N tl q.y nM nR nC n0 ns nx v7) X p)
/-- the caller's entries off a witness -/
local notation "𝛍" w => msgLay x tl D rad oW wOf hRef (2 ^ kRef)
  (tupleW x D rad seatT oW enc arr w)
/-- the caller's key vectors off a witness -/
local notation "𝐊" w => Cb.Fo.forK Cb.Gl.E (layLay q x.fs x.lm x.F.next x.ns tl hRef (2 ^ kRef)) ()
  (Cb.Fo.zext (msgLay x tl D rad oW wOf hRef (2 ^ kRef) (tupleW x D rad seatT oW enc arr w)))

/-- The value's weights off the pinned part of a witness are the caller's layers' matrices. -/
theorem weights_layNF (w : Wit Cells Tok MsgT) :
    (𝐐).plan.weights (partOf D.codes arr ms N m w) =
      fun l => layerR ppref kRef (wOfE (𝛍 w)) (4 * p.g + l) := by
  funext l
  have em := mat_lay x D rad seatT posI tl oW enc wOf hRef (2 ^ kRef)
    (tupleW x D rad seatT oW enc arr w) (partOf D.codes arr ms N m w) w.cells rfl rfl
  refine RefSeat.weights_eqF _ X p eg _ _ (fun r c _ => ?_) (fun r c hrc => ?_) l
  · rw [em]
    rfl
  · rw [em, PinPlan.mat_some _ rfl]
    show cutW enc wOf hRef (2 ^ kRef) _ r c = 0
    unfold cutW
    rw [if_neg hrc]

/-- **The caller's key vector of a call is the library's at the value's cells and weights**, under
`SitsIn`, `Covers`, "the section's table of scales is X's" and `KeysFit`. -/
theorem keyVec_layF (hs : SitsIn (sigListCalls D rad x.link) seatT ms N m)
    (hscl : scl = sclX X p.g) (hC : Covers tl nM nR nC) (Kq : KeysFit X p q)
    (w : Wit Cells Tok MsgT) (c : Fin 8) :
    (𝐊 w) c.val =
      keyVec Dim.ref ((𝐐).plan.cells (partOf D.codes arr ms N m w)) tbRef (p.g * 4)
        ((𝐐).plan.weights (partOf D.codes arr ms N m w)) c := by
  rw [weights_layNF x q D rad seatT posI tl oW enc wOf arr ms N m nM nR nC n0 ns nx v7 X p eg w,
    cells_layK x q D rad seatT posI tl oW enc wOf hRef (2 ^ kRef) arr ms N m hs nM nR nC n0 ns nx v7
      hC X p w, Nat.mul_comm p.g 4]
  have hsc : scl = sclOf q.h q.sc q.g 4 := by
    rw [hscl, Kq.shape, Kq.scales, Kq.group, ← Kq.lam]
  subst hsc
  funext Xk
  show (if hc : c.val < 8 then _ else 0) = _
  rw [dif_pos c.isLt, Kq.group]
  rfl

/-- **THE ROAD's SENTENCE ON THE KEYS GIVES THE LOOKUP's ITEM worth "keys"**, from the filling's
promise in front, "the section's table of scales is X's", `SitsIn`, `Covers`, `PlaceIs`,
`KeysFit`, "what `S.lookHeard?` finds the seat's reader finds", and the bound on the number of slots
of the ledger in hand. -/
theorem keys_worthF (hs : SitsIn (sigListCalls D rad x.link) seatT ms N m)
    (hscl : scl = sclX X p.g) (hC : Covers tl nM nR nC) {first : ℕ} (hP : PlaceIs x p first)
    (Kq : KeysFit X p q) {Q3 : Fork → Prop} {on0 on' : S × Fr.E.Str → Prop}
    {ctx0 : S × Fr.E.Str → Wit Cells Tok MsgT → Prop} {dec : S × Fr.E.Str → PinM Cells}
    (a : S × Fr.E.Str) (w : Wit Cells Tok MsgT)
    (hl : ∀ g, a.1.lookHeard? = some g → seatS.look a.1 = some g)
    (hns : (seatS.fork a.1).ns ≤ (𝐐).ns + 1)
    (hon : ((𝐅).lettersOfF (partOf D.codes arr ms N m) p first p.P.y.fo Q3 on0 on' ctx0 dec).on a)
    (hW : ((𝐅).lettersOfF (partOf D.codes arr ms N m) p first p.P.y.fo Q3 on0 on' ctx0
      dec).worthKeys a w) :
    K3WorthKeys (fun s : S => s.fork?) (fun s : S => s.lookHeard?) x.fs x.lm x.F.next
      (fun w => nuLay x D rad tl oW wOf hRef (2 ^ kRef) (matIx p.P.y).iB
        (tupleW x D rad seatT oW enc arr w)) (fun w => 𝐊 w) a.1 w := by
  intro g F' hf hh
  have hlook : seatS.look a.1 = some g := hl g hh
  have hfork : seatS.fork a.1 = F' := fork_lay hlook hf
  obtain ⟨_, F0, F1, g', rs, _, _, hK, hg', hF1⟩ := hon
  obtain rfl : g' = g := Option.some.inj (hg'.symm.trans hlook)
  have eF1 : F1 = seatS.fork a.1 := (Option.some.inj hF1).symm
  have hsh : g'.shape = p.P.y.fo := hK.shape
  have H : HeardFits g' :=
    ⟨by rw [hsh]; exact hK.zx, by rw [hsh]; exact hK.zy,
      fun c hc => by rw [hsh] at hc ⊢; exact (hK.zkRaw c hc).2, by rw [hsh]; exact hK.eRaw⟩
  have T : TreesFit g'.shape Dim.ref := by rw [hsh]; exact Kq.trees
  have h8 : g'.shape.NC = 8 := by rw [hsh]; exact Kq.calls
  have hm : (𝐐).maskAt (partOf D.codes arr ms N m w) =
      fun j => nuLay x D rad tl oW wOf hRef (2 ^ kRef) (matIx p.P.y).iB
        (tupleW x D rad seatT oW enc arr w) (.mask j) := by
    rw [← nu_layF x D rad seatT posI tl oW enc wOf hRef (2 ^ kRef) arr ms N m hs q.y nM nR nC n0 ns
      nx v7 (matIx p.P.y).iB hC X p w]
    rfl
  -- the road's sentence, as an equation on what was heard
  have hW0 : (𝐅).toLF.planF.toPlan4.Keys a.1 (partOf D.codes arr ms N m w) := hW
  have hW1 : (𝐐).plan.Keys a.1 (partOf D.codes arr ms N m w) :=
    (Plan4.keys_f7 (𝐐).plan ((𝐐).toL.slots.f7 + 1) a.1 (partOf D.codes arr ms N m w)).1 hW0
  have hk := (Plan4K.keys_iff (𝐐) hlook (partOf D.codes arr ms N m w) (fun _ _ _ => 0)
    hK.cEndEnts (fun s hs' => Nat.lt_of_lt_of_le (eF1 ▸ (hK.cEndFilled s hs').1) hns)).1 hW1
  rw [hm] at hk
  -- the caller's first layer is 4 p.g, the value's is 0
  have kv : ∀ c : Fin 8, (𝐊 w) c.val =
      keyVec Dim.ref ((𝐐).plan.cells (partOf D.codes arr ms N m w)) tbRef (0 * 4)
        ((𝐐).plan.weights (partOf D.codes arr ms N m w)) c := fun c => by
    have h := keyVec_layF x q D rad seatT posI tl oW enc wOf arr ms N m nM nR nC n0 ns nx v7 X p eg
      hs hscl hC Kq w c
    rw [eg] at h
    exact h
  -- the lookup's own door for keys that are handed in
  rw [hP.shape, ← hsh, ← hfork]
  exact k3KeysHanded Cb.Gl.E Reading.gl _ g' _ _ _ _ (fun _ _ _ => 0) _
    (by rw [hsh]; exact Kq.ok) (_root_.Fo.Later.refl _)
    (join_of_keys H T h8 OnBytes.Road.ref_cap _ _ _ _ _ kv _ _ hk)

end

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.Plan4.cells_f7
#print axioms OnBytes.Road.K4.Plan4.weights_f7
#print axioms OnBytes.Road.K4.Plan4.keys_f7
#print axioms OnBytes.Road.K4.cells_layK
#print axioms OnBytes.Road.K4.RefSeat.weights_eqF
#print axioms OnBytes.Road.K4.weights_layNF
#print axioms OnBytes.Road.K4.keyVec_layF
#print axioms OnBytes.Road.K4.keys_worthF
