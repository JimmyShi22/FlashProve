-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/K4PinsPlanes.lean: THE ROAD's SENTENCE ON THE PLANES (the letter worthPlanes of
Johnson/Road/K4/CloseFill.lean's filling) GIVES THE LOOKUP's OWN ITEM worth "planes"
(`K3WorthPlanes`, Johnson/Top/H/K3Worth.lean) AT THE LETTERS OF THE CALLER OF THE LOOKUP ON A
LAYERS' LINK's CALLS, at the filled pinned part (Johnson/Road/K4/K4Pins.lean) and a seat whose mask
row is cut at the place's number of slots. Definitions and theorems, by unfolding. No draw, no
count.

  `PinPlan.maskN n`, `PinPlan.seatN n`: `PinPlan.mask` read as 0 from entry n on; `PinPlan.seat`
    (Johnson/Road/K4/K4PinsRead.lean) with that mask row.
  `tupleW`: the caller's tuple of messages off a witness: the external member is the image of the
    witness's cells under the letter enc, the first chain's part the witness's own messages
    (`msgsOf`).
  `nuLay`: the caller's reading of the lookup's places off such a tuple: a mask ↦ the mask row's
    entry, a cell ↦ the cell of the list's matrix number iB, every other place ↦ 0.
  `Covers tl nM nR nC`: A CONDITION ON NUMBERS: every cell that the smallness test's record tl has
    lies inside the value's bounds.
  `mats_lay`, `nu_lay`: under `SitsIn` and `Covers`: the value's matrices at `seatN x.ns` and the
    pinned part of w ARE the caller's `matsOfE` at `tupleW` w; the road's valuation `Plan4K.nuOf`
    there IS `nuLay`.
  `fork_lay`: where the seat's reader finds what the lookup returned, what the record's own reader
    of the ledger finds is the seat's ledger.
  `PlaceIs`: EQUATIONS ON THE PLAN: the caller's place has the plan's shape, packing and first
    slot.
  **`planes_worth`**: `K3WorthPlanes S.fork? S.lookHeard? x.fs x.lm x.F.next (nuLay …) a.1 w`,
    from: the filling's promise in front `Lt.on a` · the road's sentence `Lt.worthPlanes a w` ·
    `SitsIn` · `Covers` · `PlaceIs` · "what `S.lookHeard?` finds at a.1 the seat's reader finds".

STANDS OVER Johnson/Top/H/K3Worth.lean, which stands in this tree. `nuLay` and `tupleW` ARE MEANT AS
THE BODIES OF THAT KIND's `layNu` AND `layMs` (Johnson/Desc/First/Look/K3LayGoodIn.lean) at msgW w
:= enc w.cells: BY READING: that file is not imported here.

OBJECT: none of its own. USER: Johnson/Road/K4/K4PinsRider.lean; meant: whoever pays the line planes
of `K4Lines` (Johnson/Road/K4/CloseAtTable.lean) at a meaning whose field worth holds
`K3WorthPlanes`. LETTERS, filled by nobody: those of Johnson/Road/K4/K4PinsW.lean, the bounds, what
the seat hands through, first, Q3, on0, on', ctx0, dec.

Limits. K04_law IS NOT PROVED BY THIS. WHAT STAYS A PREMISE, AND WHO COULD PAY IT: `SitsIn`,
`Covers`: runs on the plan · `PlaceIs`: the authors of the kind "lookup" (their place's letters at
a layers' link) · the two readers of what the lookup returned agree: the table's public item
look m. FROM ENTRY x.ns ON THE CUT MASK ROW READS 0: K4's value reads slots up to its own number
ns: THAT THIS NUMBER LIES BELOW x.ns IS NOT ASKED AND NOT SHOWN HERE: where it does not, the value
speaks of zeros there. That the field worth of a meaning holds `K3WorthPlanes` at these letters is
its filler's word. The item is true of every witness where the record holds no ledger or nothing
heard (K3Worth.lean's Limits).
-/
import Johnson.Road.K4.K4PinsW
import Johnson.Top.H.K3Worth

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

/-! ## 1 A seat whose mask row is cut -/

/-- The own mask row, read as 0 from entry n on. -/
def PinPlan.maskN {Cells : Type} (A : PinPlan Cells) (n : ℕ) (t : PinM Cells) (j : ℕ) : Cb.Gl.E :=
  if j < n then A.mask t j else 0

/-- `PinPlan.seat` with that mask row. -/
def PinPlan.seatN {Cells : Type} (A : PinPlan Cells) (n : ℕ) (N : Numbers) (tl : HTailF2) (y : Lay)
    (nM nR nC n0 ns nx v7 : ℕ) : RefSeat (PinM Cells) S :=
  { A.seat N tl y nM nR nC n0 ns nx v7 with maskAt := A.maskN n }

/-! ## 2 The caller's readings -/

section
variable (x : VerifiableInference.Desc.First.Look.Place) (D : Sent)
  (rad : OnBytes.OracleShape → ℕ) (seatT : Fin (sigListCalls D rad x.link).length → ℕ × ℕ)
  (posI : ℕ → Bool × ℕ × ℕ) (tl : HTailF2) (oW : Cb.OMsg Cb.Gl.E) {Cells : Type}
  (enc : Cells → oW.Msg)
  (wOf : oW.Msg → ℕ → ℕ → Cb.Gl.E) (nr nc : ℕ)

/-- The caller's tuple of messages, off a witness. -/
def tupleW {Tok : Type} (arr : ℕ → ℕ → ℕ) (w : Wit Cells Tok MsgT) : (laySg x D rad oW).Msg :=
  (sigOf D.codes (sigListCalls D rad x.link)).cons (T := fun o => o.Msg) oW (enc w.cells)
    (msgsOf D.codes (sigListCalls D rad x.link) seatT arr w)

/-- The caller's reading of the lookup's places. -/
def nuLay (iB : ℕ) (mm : (laySg x D rad oW).Msg) (pq : _root_.Fo.Pl) : Cb.Gl.E :=
  zext (msgLay x tl D rad oW wOf nr nc mm)
    (Cb.Fo.NumsEq.placeOf (lyMask x.ns tl nr nc) (lyCell x.ns tl nr nc iB) pq)

/-- **A condition on numbers**: every cell that the record tl has lies inside the bounds. -/
def Covers (nM nR nC : ℕ) : Prop :=
  ∀ a r c, (cellJ (szOf tl) a r c).isSome = true → a < nM ∧ r < nR ∧ c < nC

variable [scl : Scl] {Tok : Type} (arr : ℕ → ℕ → ℕ) (ms : List Mem) (N : Numbers) (m : ℕ)

/-- **The value's matrices are the caller's**, under `SitsIn` and `Covers`. -/
theorem mats_lay (hs : SitsIn (sigListCalls D rad x.link) seatT ms N m) (y : Lay)
    (nM nR nC n0 ns nx v7 : ℕ) (hC : Covers tl nM nR nC) (X : Public) (p : Par) (hg : p.g < 12)
    (w : Wit Cells Tok MsgT) :
    (((planAt x D rad seatT (cutW enc wOf nr nc) posI).seatN x.ns N tl y nM nR nC n0 ns nx v7).atRec
      X
        p hg).mats (partOf D.codes arr ms N m w) =
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
theorem nu_lay (hs : SitsIn (sigListCalls D rad x.link) seatT ms N m) (y : Lay)
    (nM nR nC n0 ns nx v7 iB : ℕ) (hC : Covers tl nM nR nC) (X : Public) (p : Par)
    (hg : p.g < 12) (w : Wit Cells Tok MsgT) :
    (((planAt x D rad seatT (cutW enc wOf nr nc) posI).seatN x.ns N tl y nM nR nC n0 ns nx v7).atRec
      X
        p hg).nuOf (partOf D.codes arr ms N m) iB w =
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
        v7).atRec X p hg).mats (partOf D.codes arr ms N m w) iB r c =
      matsOfE (msgLay x tl D rad oW wOf nr nc (tupleW x D rad seatT oW enc arr w)) iB r c
    rw [mats_lay x D rad seatT posI tl oW enc wOf nr nc arr ms N m hs y nM nR nC n0 ns nx v7 hC X p
      hg
      w]
  | key _ _ => rfl
  | zero => rfl

end

/-! ## 3 The record's readers and the seat's -/

/-- Where the seat's reader finds what the lookup returned, the record's own reader of the ledger
finds the seat's ledger, and no other. -/
theorem fork_lay {s : S} {g : OnBytes.Model.Forest.Heard} (h : seatS.look s = some g) {F' : Fork}
    (hf : s.fork? = some F') : seatS.fork s = F' := by
  unfold VerifiableInference.Desc.First.S.fork? at hf
  cases hh : s.here with
  | lay a =>
    rw [hh] at hf
    have e : seatS.fork s = a.F := by
      show (match s.here with
        | .lay a => a.F
        | _ => {}) = a.F
      rw [hh]
    rw [e]
    exact Option.some.inj hf
  | between | att _ | head _ | fin _ | mem _ =>
    have e : seatS.look s = none := by
      show (match s.here with
        | .lay a => a.fo
        | _ => none) = none
      rw [hh]
    rw [e] at h
    cases h

/-! ## 4 The line -/

/-- **Equations on the plan**: the caller's place against the layers' plan. -/
structure PlaceIs (x : VerifiableInference.Desc.First.Look.Place) (p : Par) (first : ℕ) : Prop where
  shape : x.fs = p.P.y.fo
  packing : x.lm = p.P.y.h.lmb
  first : x.F.next = first

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
theorem planes_worth (hs : SitsIn (sigListCalls D rad x.link) seatT ms N m) (y : Lay)
    (nM nR nC n0 ns nx v7 : ℕ) (X : Public) (p : Par) (hg : p.g < 12)
    (hC : Covers tl nM nR nC) {first : ℕ} (hP : PlaceIs x p first)
    {Q3 : Fork → Prop} {on0 on' : S × Fr.E.Str → Prop}
    {ctx0 : S × Fr.E.Str → Wit Cells Tok MsgT → Prop} {dec : S × Fr.E.Str → PinM Cells}
    (a : S × Fr.E.Str) (w : Wit Cells Tok MsgT)
    (hl : ∀ g, a.1.lookHeard? = some g → seatS.look a.1 = some g)
    (hon : ((((planAt x D rad seatT (cutW enc wOf nr nc) posI).seatN x.ns N tl y nM nR nC n0 ns nx
      v7).atRec X p hg).lettersOf (partOf D.codes arr ms N m) p first p.P.y.fo Q3 on0 on' ctx0
      dec).on a)
    (hW : ((((planAt x D rad seatT (cutW enc wOf nr nc) posI).seatN x.ns N tl y nM nR nC n0 ns nx
      v7).atRec X p hg).lettersOf (partOf D.codes arr ms N m) p first p.P.y.fo Q3 on0 on' ctx0
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
  rw [nu_lay x D rad seatT posI tl oW enc wOf nr nc arr ms N m hs y nM nR nC n0 ns nx v7 _ hC X p hg
    w,
    hshape] at h0
  rw [hP.shape, hP.packing, hP.first, ← hfork]
  exact h0

end

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.nu_lay
#print axioms OnBytes.Road.K4.fork_lay
#print axioms OnBytes.Road.K4.planes_worth
