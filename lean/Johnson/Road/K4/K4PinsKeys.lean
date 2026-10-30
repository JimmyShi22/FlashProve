-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/K4PinsKeys.lean: THE ROAD's SENTENCE ON THE KEYS (the letter worthKeys of
Johnson/Road/K4/CloseFill.lean's filling: the lookup's join in the library's key vectors) GIVES THE
LOOKUP's OWN ITEM worth "keys" (`K3WorthKeys`, Johnson/Top/H/K3Worth.lean) AT THE KEY VECTORS OF THE
CALLER OF THE LOOKUP ON A LAYERS' LINK's CALLS (`layLay`, Johnson/Desc/First/Look/K3CallerLay.lean),
at the filled pinned part and the seat of Johnson/Road/K4/K4PinsPlanes.lean. Theorems. No draw, no
count. NO NEW ARGUMENT: laws of the library, called.

CALLED: `k3KeysHanded` (Johnson/Top/H/K3OutPaid.lean: the item from the join's value at what was
heard) · `val_joinK` (OnBytes/Tie/Pv/Lookup/Port/FoJoin.lean) · `Plan4K.keys_iff`
(Johnson/Road/K4/ValueSeat.lean) · `wc_of_look`, `zc_of_look`, `size_of_look`
(Johnson/Road/FormsKeysLook.lean) · `ext_keyVec_KF` (Johnson/Road/FormsKeysVec.lean: the library's
KF of a call is the extension of the call's key vector at the call's point) · `extL_ofList`
(OnBytes/Tie/Pv/Lookup/Forest/FoKfDig.lean) · `weight_val`, `eqTab_val`, `padKey_val`, `rdL_getD`
(OnBytes/Tie/Pv/Lookup/Port/FoTwins.lean) · `foldl_madd_range` (Johnson/Road/FormsKeysQK.lean).

  `HeardFits g`: what a yes of the lookup leaves of the points and weights that were heard, in what
    was heard's own shape (five of the lines of `K3Left`, Johnson/Top/H/K3LeftStatement.lean).
  `e_wc`, `e_eK`: the heard weight of a call reads as the library's w_c at the lookup's point, and
    as the join's weight.
  `key_at`: the extension at the heard point of a call, as a list, is the library's extension at
    the library's point of the call.
  `pad_at`: the public number for the padding trees reads as the join's term for them.
  `RefSeat.weights_eq`: the group's weights that the value reads are `layerR` of any matrix that
    agrees with matAt inside the reference rows and columns and is 0 outside.
  `join_zero`, `keysPub_eq`, `join_of_keys`: THE ALGEBRA: the lookup's join at what was heard is 0
    where the weighted sum of the library's KF is the road's public part less the end form's
    worth, and the key vectors are the library's: at free letters.
  **`keys_worth`**: `K3WorthKeys S.fork? S.lookHeard? x.fs x.lm x.F.next (nuLay …) (the key vectors
    of layLay at tupleW) a.1 w`, from: the filling's promise in front · the road's sentence
    `Lt.worthKeys a w` · `SitsIn` · `Covers` · `PlaceIs` · `KeysFit` · "what `S.lookHeard?` finds
    the seat's reader finds" · the ledger in hand has at most the value's number of slots, and one.
  `KeysFit`: PREMISES ON PUBLIC NUMBERS AND LETTERS: `TreesFit` at the plan's shape and the
    reference sizes · eight calls · the library's bounds on the shape · the caller's public letters
    h, sc, g are the public parameters' shape, their scale file and the plan's group ·
    a group has four layers.
  `keyVec_lay`: the caller's key vector of a call is the library's `keyVec` at the value's cells and
    weights.

STANDS OVER Johnson/Top/H/K3Worth.lean, which stands in this tree. NEEDS BESIDE:
Johnson/Top/H/K3OutPaid.lean.

OBJECT: none of its own. USER: Johnson/Road/K4/K4PinsAll.lean; meant: whoever pays the line keys of
`K4Lines` (Johnson/Road/K4/CloseAtTable.lean) at a meaning whose field worth holds `K3WorthKeys`.
LETTERS, filled by nobody: those of Johnson/Road/K4/K4PinsRider.lean.

Limits. K04_law IS NOT PROVED BY THIS. WHAT STAYS A PREMISE, AND WHO COULD PAY IT: those of
K4PinsPlanes.lean · `KeysFit`: its lines trees, calls follow from the plan's public lines
(`treesFit_of_layout`, Johnson/Road/FormsKeysLookT.lean; `fo_of_layout`): those calls are not made
here; ok: `pub_ok` (Johnson/Road/K4/RefPub.lean); shape, scales, group: whoever fills the caller's
letters q: they are set to the public parameters'; lam: at the reference shape `lam_ref`
(Johnson/Road/FormsKeysRef.lean). WITH THESE THE CALLER's TABLE OF SCALES `sclOf q.h q.sc q.g 4` IS
THE ROAD's `sclX X p.g` (Johnson/Road/K4/RefValue.lean: one `sclOf`, at the layout's Lam) · the
bound on the ledger's number of slots:
the promise in front (the road's bound on Q3, and that the lookup's run leaves that number). THE
WEIGHTS ARE READ AT hRef ROWS AND 2 ^ kRef COLUMNS: the caller's letters nr, nc are set to these.
The item is true of every witness where the verifier's state holds no ledger or nothing heard.

-/
import Johnson.Road.K4.K4PinsRider
import Johnson.Road.K4.K4PinsWeights
import Johnson.Top.H.K3OutPaid
import Johnson.Road.FormsKeysVec
import Johnson.Road.FormsKeysQK
import OnBytes.Tie.Pv.Lookup.Forest.FoKfDig

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

/-! ## 1 What was heard, read -/

/-- What a yes of the lookup leaves of the points and weights that were heard, in what was heard's
own shape. -/
structure HeardFits (g : Forest.Heard) : Prop where
  zx : g.zx.size = g.shape.dT
  zy : g.zy.size = g.shape.rK
  points : ∀ c, c < g.shape.NC →
    g.zk.getD c #[] = g.zy.extract (g.shape.rK - g.shape.iota.getD c 0) g.zy.size ++ g.zx
  e : g.e = (Array.range g.shape.NC).map (OnBytes.Model.Forest.callWeight g.shape g.zy)

section Heard
variable {g : Forest.Heard} (H : HeardFits g) {D : Dim} (T : TreesFit g.shape D)
  (h8 : g.shape.NC = 8)
include H h8

theorem e_call (c : Fin 8) :
    g.e.getD c.val zeroE = OnBytes.Model.Forest.callWeight g.shape g.zy c.val := by
  rw [H.e, range_map_getD' _ _ _ (by rw [h8]; exact c.isLt)]

/-- The heard weight of a call reads as the join's weight. -/
theorem e_eK (c : Fin 8) : Reading.gl.val (g.e.getD c.val zeroE) =
    _root_.Fo.eK g.shape (_root_.Fo.rdA Reading.gl g.zy) c.val := by
  rw [e_call H h8 c]
  exact _root_.Fo.weight_val Reading.gl g.shape g.zy c.val

include T

/-- The heard weight of a call reads as the library's weight of the call at the lookup's point. -/
theorem e_wc (c : Fin 8) : Reading.gl.val (g.e.getD c.val zeroE) = wc D (zAt g) c := by
  rw [e_call H h8 c]
  exact wc_of_look T H.zx c

/-- The extension at the heard point of a call is the library's at the library's point. -/
theorem key_at (f : ℕ → Cb.Gl.E) (c : Fin 8) :
    _root_.Fo.extL f (_root_.Fo.rdA Reading.gl (g.zk.getD c.val #[])) =
      Blocks.ext (aC D c) f (zc D (zAt g) c) := by
  have ek : g.zk.getD c.val #[] = ((Array.range g.shape.NC).map fun c =>
      g.zy.extract (g.shape.rK - g.shape.iota.getD c 0) g.zy.size ++ g.zx).getD c.val #[] := by
    rw [range_map_getD' _ _ _ (by rw [h8]; exact c.isLt)]
    exact H.points c.val (by rw [h8]; exact c.isLt)
  have hlen : (_root_.Fo.rdA Reading.gl (g.zk.getD c.val #[])).length = aC D c := by
    unfold _root_.Fo.rdA
    rw [List.length_map, Array.length_toList, ek]
    exact size_of_look T h8 H.zx H.zy rfl c
  rw [_root_.Fo.extL_ofList, hlen]
  refine ext_congr_pt _ _ fun j hj => ?_
  have hz := zc_of_look (ρ := Reading.gl) T h8 H.zx H.zy rfl c j hj
  rw [← ek] at hz
  show (_root_.Fo.rdA Reading.gl (g.zk.getD c.val #[])).getD j 0 = zc D (zAt g) c j
  exact (_root_.Fo.rdL_getD Reading.gl _ j).symm.trans hz

end Heard

/-- The public number for the padding trees reads as the join's term for them. -/
theorem pad_at (g : Forest.Heard) : Reading.gl.val (padFo g) =
    ∑ i ∈ range (2 ^ g.shape.rK - g.shape.NT),
      (_root_.Fo.eqTabK (_root_.Fo.rdA Reading.gl g.zy)).getD (g.shape.NT + i) 0 *
        (Reading.gl.val g.alpha - _root_.Fo.padKeyK g.shape (Reading.gl.val g.theta) 0) := by
  unfold padFo
  refine (foldl_madd_range Reading.gl (fun t => (eqTab g.zy).getD (g.shape.NT + t) zeroE)
    (fun _ => subE g.alpha (g.padKey 0)) _).trans ?_
  refine sum_congr rfl fun t _ => ?_
  have e1 : Reading.gl.val ((eqTab g.zy).getD (g.shape.NT + t) zeroE) =
      (_root_.Fo.eqTabK (_root_.Fo.rdA Reading.gl g.zy)).getD (g.shape.NT + t) 0 := by
    rw [_root_.Fo.rdL_getD, _root_.Fo.eqTab_val]
    rfl
  have e2 : Reading.gl.val (subE g.alpha (g.padKey 0)) =
      Reading.gl.val g.alpha - _root_.Fo.padKeyK g.shape (Reading.gl.val g.theta) 0 := by
    rw [Reading.gl.sub, show g.padKey 0 = OnBytes.Model.Forest.padKeyOf g.shape g.theta 0 from rfl,
      _root_.Fo.padKey_val Reading.gl g.shape g.theta 0 (by norm_num)]
  rw [e1, e2]

/-! ## 2 The algebra -/

/-- The join's value is 0 where the weighted sum of the keys is the public part less the end form's
worth. -/
theorem join_zero (wv kv av : Fin 8 → Cb.Gl.E) (P C : Cb.Gl.E)
    (h : ∑ c, wv c * kv c = ∑ c, wv c * av c + P - C) :
    ∑ c, wv c * (av c - kv c) + P - C = 0 := by
  have e : ∑ c, wv c * (av c - kv c) = ∑ c, wv c * av c - ∑ c, wv c * kv c := by
    rw [← sum_sub_distrib]
    exact sum_congr rfl fun c _ => mul_sub _ _ _
  rw [e, h]
  ring

/-- The road's public part of the join, in the library's weights. -/
theorem keysPub_eq {g : Forest.Heard} (H : HeardFits g) {D : Dim} (T : TreesFit g.shape D)
    (h8 : g.shape.NC = 8) : keysPub g = ∑ c : Fin 8, wc D (zAt g) c *
      (Reading.gl.val g.alpha - ((c.val : ℕ) : Cb.Gl.E) * Reading.gl.val g.theta) +
        Reading.gl.val (padFo g) := by
  have hes : g.e.size = 8 := by rw [H.e, Array.size_map, Array.size_range, h8]
  unfold keysPub
  rw [hes, Finset.sum_range]
  exact congrArg (· + Reading.gl.val (padFo g))
    (sum_congr rfl fun c _ => by rw [e_wc H T h8 c])

/-- **The lookup's join at what was heard is 0**, where the weighted sum of the library's KF is the
road's public part less the end form's worth, and the key vectors are the library's. All letters
free: cells t, tables tb, first layer L0, weights wts, key vectors Kv, valuation nu, ledger F. -/
theorem join_of_keys [scl : Scl] {g : Forest.Heard} (H : HeardFits g) {D : Dim}
    (T : TreesFit g.shape D) (h8 : g.shape.NC = 8) (hcap : D.lT ≤ D.cap)
    (t : Inst.Model.FFSeg.Cell → Cb.Gl.E) (tb : Inst.Model.Tables) (L0 : ℕ)
    (wts : ℕ → LW Cb.Gl.E) (Kv : ℕ → ℕ → Cb.Gl.E)
    (hKv : ∀ c : Fin 8, Kv c.val = keyVec D t tb L0 wts c) (nu : _root_.Fo.Pl → Cb.Gl.E)
    (C : Cb.Gl.E)
    (hk : ∑ c, wc D (zAt g) c * KF D t tb L0 wts (zAt g) c = keysPub g - C) :
    _root_.Fo.AffK.val (_root_.Fo.joinK g.shape (Reading.gl.val g.theta) (Reading.gl.val g.alpha)
      (_root_.Fo.eK g.shape (_root_.Fo.rdA Reading.gl g.zy)) (_root_.Fo.rdA Reading.gl g.zy)
      (fun c => _root_.Fo.AffK.ofConst
        (_root_.Fo.extL (Kv c) (_root_.Fo.rdA Reading.gl (g.zk.getD c #[]))))
      (_root_.Fo.AffK.ofConst C)) nu = 0 := by
  rw [_root_.Fo.val_joinK]
  simp only [_root_.Fo.AffK.val_ofConst]
  rw [← pad_at g, h8, Finset.sum_range]
  have e : ∀ c : Fin 8, _root_.Fo.eK g.shape (_root_.Fo.rdA Reading.gl g.zy) c.val *
        (Reading.gl.val g.alpha - ((c.val : ℕ) : Cb.Gl.E) * Reading.gl.val g.theta -
          _root_.Fo.extL (Kv c.val) (_root_.Fo.rdA Reading.gl (g.zk.getD c.val #[]))) =
      wc D (zAt g) c *
        (Reading.gl.val g.alpha - ((c.val : ℕ) : Cb.Gl.E) * Reading.gl.val g.theta -
          KF D t tb L0 wts (zAt g) c) := fun c => by
    rw [← e_eK H h8 c, e_wc H T h8 c, key_at H T h8 _ c, hKv c, ext_keyVec_KF D t tb L0 wts hcap]
  rw [sum_congr rfl fun c _ => e c]
  exact join_zero _ _ _ _ _ (hk.trans (by rw [keysPub_eq H T h8]))

/-! ## 3 The weights, at any seat -/

/-- The group's weights that the value reads, of any matrix that agrees with matAt inside the
reference rows and columns and is 0 outside. -/
theorem RefSeat.weights_eq [scl : Scl] {M : Type} (U : RefSeat M S) (X : Public) (p : Par)
    (hg : p.g < 12) (t : M) (Wf : ℕ → ℕ → Cb.Gl.E)
    (h : ∀ r c, r < hRef ∧ c < 2 ^ kRef → U.matAt t r c = Wf r c)
    (h0 : ∀ r c, ¬ (r < hRef ∧ c < 2 ^ kRef) → Wf r c = 0) (l : ℕ) :
    (U.atRec X p hg).plan.weights t l = layerR ppref kRef Wf (4 * p.g + l) := by
  have e : (U.atRec X p hg).plan.Wn ((U.atRec X p hg).plan.msg t) = Wf := by
    funext r c
    rw [Plan4.Wn_msg]
    show (if r < hRef ∧ c < 2 ^ kRef then U.matAt t r c else 0) = Wf r c
    by_cases hrc : r < hRef ∧ c < 2 ^ kRef
    · rw [if_pos hrc, h r c hrc]
    · rw [if_neg hrc, h0 r c hrc]
  unfold Plan4.weights
  rw [e, Nat.mul_comm 4 p.g]
  rfl

/-! ## 4 The line -/

/-- **Premises on public numbers and letters.** -/
structure KeysFit (X : Public) (p : Par) (q : LayPub) : Prop where
  /-- the numbers of the plan's trees are the library's at the reference sizes -/
  trees : TreesFit p.P.y.fo Dim.ref
  calls : p.P.y.fo.NC = 8
  ok : FoNums.ok p.P.y.fo = true
  /-- the caller's public letters are the public parameters' -/
  shape : q.h = layerShape X.P
  scales : q.sc = X.layers.sc
  group : q.g = p.g
  /-- a group has four layers -/
  lam : X.layers.y.Lam = 4

section
variable [scl : Scl] (x : VerifiableInference.Desc.First.Look.Place) (q : LayPub) (D : Sent)
  (rad : OnBytes.OracleShape → ℕ) (seatT : Fin (sigListCalls D rad x.link).length → ℕ × ℕ)
  (posI : ℕ → Bool × ℕ × ℕ) (tl : HTailF2) (oW : Cb.OMsg Cb.Gl.E) {Cells : Type}
  (enc : Cells → oW.Msg)
  (wOf : oW.Msg → ℕ → ℕ → Cb.Gl.E) {Tok : Type} {Fr : Frame} (arr : ℕ → ℕ → ℕ)
  (ms : List Mem) (N : Numbers) (m : ℕ) (nM nR nC n0 ns nx v7 : ℕ) (X : Public) (p : Par)
  (hg : p.g < 12)

/-- the value: at the seat whose mask row is cut, the caller's layout, the reference matrix -/
local notation "𝐐" => RefSeat.atRec (PinPlan.seatN (planAt x D rad seatT
  (cutW enc wOf hRef (2 ^ kRef)) posI) x.ns N tl q.y nM nR nC n0 ns nx v7) X p hg
/-- the caller's entries off a witness -/
local notation "𝛍" w => msgLay x tl D rad oW wOf hRef (2 ^ kRef)
  (tupleW x D rad seatT oW enc arr w)
/-- the caller's key vectors off a witness -/
local notation "𝐊" w => Cb.Fo.forK Cb.Gl.E (layLay q x.fs x.lm x.F.next x.ns tl hRef (2 ^ kRef)) ()
  (Cb.Fo.zext (msgLay x tl D rad oW wOf hRef (2 ^ kRef) (tupleW x D rad seatT oW enc arr w)))

/-- The value's weights off the pinned part of a witness are the caller's layers' matrices. -/
theorem weights_layN (w : Wit Cells Tok MsgT) :
    (𝐐).plan.weights (partOf D.codes arr ms N m w) =
      fun l => layerR ppref kRef (wOfE (𝛍 w)) (4 * p.g + l) := by
  funext l
  have em := mat_lay x D rad seatT posI tl oW enc wOf hRef (2 ^ kRef)
    (tupleW x D rad seatT oW enc arr w) (partOf D.codes arr ms N m w) w.cells rfl rfl
  refine RefSeat.weights_eq _ X p hg _ _ (fun r c _ => ?_) (fun r c hrc => ?_) l
  · rw [em]
    rfl
  · rw [em, PinPlan.mat_some _ rfl]
    show cutW enc wOf hRef (2 ^ kRef) _ r c = 0
    unfold cutW
    rw [if_neg hrc]

/-- **The caller's key vector of a call is the library's at the value's cells and weights**, under
`SitsIn`, `Covers`, "the section's table of scales is the public parameters'" and `KeysFit`. -/
theorem keyVec_lay (hs : SitsIn (sigListCalls D rad x.link) seatT ms N m)
    (hscl : scl = sclX X p.g) (hC : Covers tl nM nR nC) (Kq : KeysFit X p q)
    (w : Wit Cells Tok MsgT) (c : Fin 8) :
    (𝐊 w) c.val =
      keyVec Dim.ref ((𝐐).plan.cells (partOf D.codes arr ms N m w)) tbRef (p.g * 4)
        ((𝐐).plan.weights (partOf D.codes arr ms N m w)) c := by
  rw [weights_layN x q D rad seatT posI tl oW enc wOf arr ms N m nM nR nC n0 ns nx v7 X p hg w,
    cells_lay x q D rad seatT posI tl oW enc wOf hRef (2 ^ kRef) arr ms N m hs nM nR nC n0 ns nx v7
      hC
      X p hg w, Nat.mul_comm p.g 4]
  have hsc : scl = sclOf q.h q.sc q.g 4 := by
    rw [hscl, Kq.shape, Kq.scales, Kq.group, ← Kq.lam]
  subst hsc
  funext Xk
  show (if hc : c.val < 8 then _ else 0) = _
  rw [dif_pos c.isLt, Kq.group]
  rfl

/-- **THE ROAD's SENTENCE ON THE KEYS GIVES THE LOOKUP's ITEM worth "keys"**, from the filling's
promise in front, "the section's table of scales is the public parameters'", `SitsIn`, `Covers`,
  `PlaceIs`,
`KeysFit`, "what `S.lookHeard?` finds the seat's reader finds", and the bound on the number of slots
of the ledger in hand. -/
theorem keys_worth (hs : SitsIn (sigListCalls D rad x.link) seatT ms N m)
    (hscl : scl = sclX X p.g) (hC : Covers tl nM nR nC) {first : ℕ} (hP : PlaceIs x p first)
    (Kq : KeysFit X p q) {Q3 : Fork → Prop} {on0 on' : S × Fr.E.Str → Prop}
    {ctx0 : S × Fr.E.Str → Wit Cells Tok MsgT → Prop} {dec : S × Fr.E.Str → PinM Cells}
    (a : S × Fr.E.Str) (w : Wit Cells Tok MsgT)
    (hl : ∀ g, a.1.lookHeard? = some g → seatS.look a.1 = some g)
    (hns : (seatS.fork a.1).ns ≤ (𝐐).ns + 1)
    (hon : ((𝐐).lettersOf (partOf D.codes arr ms N m) p first p.P.y.fo Q3 on0 on' ctx0 dec).on a)
    (hW : ((𝐐).lettersOf (partOf D.codes arr ms N m) p first p.P.y.fo Q3 on0 on' ctx0
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
    rw [← nu_lay x D rad seatT posI tl oW enc wOf hRef (2 ^ kRef) arr ms N m hs q.y nM nR nC n0 ns
      nx
      v7 (matIx p.P.y).iB hC X p hg w]
    rfl
  -- the road's sentence, as an equation on what was heard
  have hk := (Plan4K.keys_iff (𝐐) hlook (partOf D.codes arr ms N m w) (fun _ _ _ => 0)
    hK.cEndEnts (fun s hs' => Nat.lt_of_lt_of_le (eF1 ▸ (hK.cEndFilled s hs').1) hns)).1 hW
  rw [hm] at hk
  -- the lookup's own door for keys that are handed in
  rw [hP.shape, ← hsh, ← hfork]
  exact k3KeysHanded Cb.Gl.E Reading.gl _ g' _ _ _ _ (fun _ _ _ => 0) _
    (by rw [hsh]; exact Kq.ok) (_root_.Fo.Later.refl _)
    (join_of_keys H T h8 OnBytes.Road.ref_cap _ _ _ _ _
      (keyVec_lay x q D rad seatT posI tl oW enc wOf arr ms N m nM nR nC n0 ns nx v7 X p hg hs hscl
        hC
        Kq w) _ _ hk)

end

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.e_eK
#print axioms OnBytes.Road.K4.e_wc
#print axioms OnBytes.Road.K4.key_at
#print axioms OnBytes.Road.K4.pad_at
#print axioms OnBytes.Road.K4.join_zero
#print axioms OnBytes.Road.K4.keysPub_eq
#print axioms OnBytes.Road.K4.join_of_keys
#print axioms OnBytes.Road.K4.RefSeat.weights_eq
#print axioms OnBytes.Road.K4.weights_layN
#print axioms OnBytes.Road.K4.keyVec_lay
#print axioms OnBytes.Road.K4.keys_worth
