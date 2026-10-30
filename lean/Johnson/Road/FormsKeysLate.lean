-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/FormsKeysLate.lean: the eight kinds of the verifier's panels that hold a value which
the prover has sent, against the library's panels.

The panels of the batched sumcheck that belong to the second token sumcheck prove products of two
values at that sumcheck's end point. In eight kinds of them one factor is a value that the prover
sent at the end of that sumcheck: the reciprocal of a norm (the panels of the segments N1, N2), the
score of a layer with routed experts (XR), an entry of its selector (DD, MR, and the panels with the
selector of G, U and D). This file compares each kind with the library's panel N1, N2, XR, DD, MR,
Gr, Ur, Dr (Inst/Model/FF/Objects.lean).

What is compared with what: the verifier's Lean text (panelT, plain, tri in
OnBytes/Model/LayerPanels.lean), through the definitions of Johnson/Road/FormsKeysPort.lean and
Johnson/Road/FormsKeysEnd.lean, against the library's Pan.wt, Pan.A, Pan.B.

Main statements.
 - blkPlain, blkTri, plain_push, tri_push: the panel that plain or tri appends, written out.
 - panelT_N1_eq, _N2_eq, _DD_eq, _MR_eq: what panelT appends for a segment, written out; each holds
   by definition. That of XR is in Johnson/Road/FormsKeysXR.lean; for G, U and D the step for one
   layer is triStep in Johnson/Road/FormsKeysFold.lean.
 - shareP_N1, _N2, _XR, _DD, _MR, _Gr, _Ur, _Dr: the share (shareP) of that panel is the reading of
   the call's weight times the library's share without the call's weight (shareL), at the record
   rPort.
 - panelP_N1, _N2, _XR, _DD, _MR: the same for the panel that panelT has appended, from "panelT
   returns" and Returns; panelP_Gr, _Ur, _Dr: for the panel that triStep has appended.

Sent and hidden. The values in question stand in the verifier's panels as constants: entries of the
array shownT, which by the text of hearStack (OnBytes/Model/Layer.lean) holds what was SENT. rPort
has the readings of the same entries in the fields R2, sc2 and sel2. So each statement here holds
for any array shownT, and says nothing on what its entries are: not that they are the hidden end
values, which differ from them by a factor times a mask entry, and not that these are true. Past the
array's end both sides read 0.

What is asked. The record PortFits: the tables at the lookup's point and at the end point of the
second token sumcheck are true. The ties of the panel's own call and family, and of no other: that
the layers' weights in the point of call number q, from which the panel's rows' weights are made,
are the library's for the family's call (ElTie; q is free); where the panel reads the weights of the
segment's entries or blocks, that these are the library's (EwTie, WtsTie). That the forms of a B
side are there; Johnson/Road/FormsKeysRet.lean has that from "stackEnd returns". For a panel with
the selector: that the vector of its weight claim holds the library's B side (WvTri). The never-sent
vectors, the weights w, the tables tb and L0 are free.

What is not claimed. That PortFits and the ties can be met is not shown here. The call's weight is
not compared with the library's wc. Nothing is said on the order of the panels in the verifier's
list, on the other seven kinds, on masks, or on what makes a sent value right. The program does not
import this file.
-/
import Johnson.Road.FormsKeysPort
import Johnson.Road.FormsKeysFold
import Johnson.Road.FormsKeysW
import Johnson.Road.FormsKeysXR

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road

open Finset
open OnBytes.Model (Reading World Aff eqTab tenCell)
open OnBytes.Model.Layer (Env Lay SBlk Ten Panels PanelEnv plain tri panelT kT kTM sumE)
open Inst.Model (Scl Tables)
open Inst.Model.FFSeg (Dim Cell Fam Arr LW Pan Rd rdTrue zpos call len valU xU xS)

variable {K : Type} [Field K]

/-! ## Tools -/

/-- A sum over a longer range of a function that is cut at n. -/
theorem sum_upto {n m : ℕ} (h : n ≤ m) (f : ℕ → K) :
    ∑ y ∈ range m, (if y < n then f y else 0) = ∑ y ∈ range n, f y := by
  rw [← Finset.sum_filter]
  congr 1
  ext y
  simp only [mem_filter, mem_range]
  omega

/-- If a function that may refuse returns on every member of a list, the results are as many as the
members, and each is the function's on its member. -/
theorem mapM_get {α β : Type} {f : α → Option β} : ∀ (l : List α) (r : List β),
    l.mapM f = some r → ∀ (i : ℕ) (a : α), l[i]? = some a → ∃ y, r[i]? = some y ∧ f a = some y
  | [], r, _, i, a, hi => by simp at hi
  | x :: l, r, h, i, a, hi => by
    rw [List.mapM_cons] at h
    cases hx : f x with
    | none => rw [hx] at h; cases h
    | some y =>
      cases hl : l.mapM f with
      | none => rw [hx, hl] at h; cases h
      | some ys =>
        rw [hx, hl] at h
        have e : y :: ys = r := Option.some.inj h
        subst e
        cases i with
        | zero =>
          have e2 : x = a := by simpa using hi
          subst e2
          exact ⟨y, rfl, hx⟩
        | succ i =>
          have hi' : l[i]? = some a := by simpa using hi
          obtain ⟨y', h1, h2⟩ := mapM_get l ys hl i a hi'
          exact ⟨y', by simpa using h1, h2⟩

/-- The same for the array of the numbers below n: member k of the result is the function's at k. -/
theorem range_mapM_get {β : Type} [Inhabited β] {f : ℕ → Option β} {n : ℕ} {r : Array β} (d : β)
    (h : (Array.range n).mapM f = some r) {k : ℕ} (hk : k < n) : f k = some (r.getD k d) := by
  rw [Array.mapM_eq_mapM_toList] at h
  cases hl : (Array.range n).toList.mapM f with
  | none => rw [hl] at h; cases h
  | some ys =>
    rw [hl] at h
    have e : ys.toArray = r := Option.some.inj h
    subst e
    have hk' : (Array.range n).toList[k]? = some k := by simp [hk]
    obtain ⟨y, h1, h2⟩ := mapM_get _ ys hl k k hk'
    rw [h2]
    congr 1
    simp [Array.getD, List.getElem?_eq_some_iff.mp h1 |>.1, (List.getElem?_eq_some_iff.mp h1).2]

/-! ## The panels that plain and tri append -/

/-- The panel that plain appends to a list whose next weight claim has the number nv. -/
def blkPlain (y : Lay) (ec : E) (claim : ℕ) (moeSet : Bool) (ny : ℕ)
    (A B : Option (ℕ → ℕ → Option Aff)) (wt : ℕ → E) (virt : Option ℕ) (nv : ℕ) : SBlk :=
  { claim := claim, ec := ec, ni := if moeSet then y.LamM else y.Lam, ny := ny,
    wy := ceilLog2 ny, w := ceilLog2 (if moeSet then y.LamM else y.Lam) + ceilLog2 ny,
    A := A.map fun f => fun i yv => f (if moeSet then 2 * i + 1 else i) yv
    B := B.map fun f => fun i yv => f (if moeSet then 2 * i + 1 else i) yv
    wt := (Array.range (if moeSet then y.LamM else y.Lam)).map fun i =>
      wt (if moeSet then 2 * i + 1 else i)
    v0 := if B.isNone then some nv else none
    virt := virt }

/-- plain appends blkPlain. -/
theorem plain_push (y : Lay) (ec : E) (claim : ℕ) (moeSet : Bool) (ny : ℕ)
    (A B : Option (ℕ → ℕ → Option Aff)) (wt : ℕ → E) (virt : Option ℕ) (s : Panels) :
    plain y ec claim moeSet ny A B wt virt s =
      { bl := s.bl.push (blkPlain y ec claim moeSet ny A B wt virt s.nextV),
        nextV := if B.isNone then s.nextV + (if moeSet then y.LamM else y.Lam) else s.nextV } :=
  rfl

/-- The panel that tri appends to a list whose next weight claim has the number nv. -/
def blkTri (y : Lay) (ec : E) (claim nk : ℕ) (sl : Array E) (xx : Array Aff) (virt : Option ℕ)
    (wt : E) (nv : ℕ) : SBlk :=
  { tri := true, claim := claim, ec := ec, ni := y.h.NE, ny := nk, wy := ceilLog2 nk,
    w := ceilLog2 (max y.h.NE 1) + ceilLog2 nk, sl := sl, xx := xx, virt := virt, wt := #[wt],
    v0 := some nv }

/-- tri appends blkTri. -/
theorem tri_push (y : Lay) (ec : E) (claim nk : ℕ) (sl : Array E) (xx : Array Aff)
    (virt : Option ℕ) (wt : E) (s : Panels) :
    tri y ec claim nk sl xx virt wt s =
      { bl := s.bl.push (blkTri y ec claim nk sl xx virt wt s.nextV), nextV := s.nextV + 1 } :=
  rfl

/-! ## The share of a panel whose two sides are forms -/

/-- The share of a panel without selector whose two sides are given as forms: if at every row and
column of the panel the two forms are there and are worth a and bb, the share is the call's weight
times the sum over the rows of the row's weight times the inner product of a and bb. -/
theorem share_forms (ρ : Reading K) (W : World K) (y : Lay) (hv wv : ℕ → ℕ → K) (ec : E)
    (claim : ℕ) (moeSet : Bool) (ny : ℕ) (A B : ℕ → ℕ → Option Aff) (wt : ℕ → E) (nv : ℕ)
    (a bb : ℕ → ℕ → K)
    (ha : ∀ i, i < (if moeSet then y.LamM else y.Lam) → ∀ yv, yv < ny →
      ∃ f, A (if moeSet then 2 * i + 1 else i) yv = some f ∧ f.value ρ W = a i yv)
    (hb : ∀ i, i < (if moeSet then y.LamM else y.Lam) → ∀ yv, yv < ny →
      ∃ f, B (if moeSet then 2 * i + 1 else i) yv = some f ∧ f.value ρ W = bb i yv) :
    shareP ρ W y hv wv (blkPlain y ec claim moeSet ny (some A) (some B) wt none nv) =
      ρ.val ec * ∑ i ∈ range (if moeSet then y.LamM else y.Lam),
        ρ.val (wt (if moeSet then 2 * i + 1 else i)) * ∑ yv ∈ range ny, a i yv * bb i yv := by
  show ρ.val ec * ∑ i ∈ range (if moeSet then y.LamM else y.Lam),
      ρ.val (((Array.range (if moeSet then y.LamM else y.Lam)).map fun i =>
        wt (if moeSet then 2 * i + 1 else i)).getD i zeroE) *
      ∑ yv ∈ range (2 ^ ceilLog2 ny),
        (if yv < ny then ov ρ W (A (if moeSet then 2 * i + 1 else i) yv) else 0) *
          (if yv < ny then ov ρ W (B (if moeSet then 2 * i + 1 else i) yv) else 0) = _
  congr 1
  refine sum_congr rfl fun i hi => ?_
  have hi' := mem_range.mp hi
  rw [range_map_getD _ _ hi', ← sum_upto (le_two_pow_ceilLog2 ny)]
  congr 1
  refine sum_congr rfl fun yv _ => ?_
  by_cases hy : yv < ny
  · obtain ⟨f, h1, h2⟩ := ha i hi' yv hy
    obtain ⟨g, h3, h4⟩ := hb i hi' yv hy
    rw [if_pos hy, if_pos hy, if_pos hy, h1, h3]
    show f.value ρ W * g.value ρ W = _
    rw [h2, h4]
  · rw [if_neg hy, if_neg hy, if_neg hy, zero_mul]

/-! ## The residual stream at another point than the lookup's -/

/-- A weighted sum over the blocks of the residual stream after write number sg of the group, for a
write that is not the last: read from true long tables at any point's name Z. The stream that goes
out is not read. -/
theorem SxsA_inner {ρ : Reading K} {W : World K} (hρ : Numerals ρ) {v : Env} {lt : ℕ} {c : Cells K}
    {t : Cell → K} {low u : ℕ → K} (D : Dim) (hlast : v.y.NW * v.y.Lam = 2 * D.nl) {Z : String}
    {bI bF : ℕ} {txs : Ten} (hI : v.tabAt ("xbI" ++ "@" ++ Z) = some bI)
    (hF : v.tabAt ("af" ++ "@" ++ Z) = some bF) (hxs : v.y.T_ "xs" = some txs)
    (T0 : Tied c t .x0 4 v.y.xb) (Ts : Tied c t .xs txs.mat txs.place)
    (R0 : LongTrue ρ W v bI 4 v.y.ls lt c low u)
    (Rs : LongTrue ρ W v bF txs.mat v.y.ls lt c low u)
    (hS2 : v.y.S2 = 2 ^ v.y.ls) (halb : ∀ l, v.y.S2 ∣ tenCell v.y.xb l 0 0)
    (hals : ∀ i l, v.y.S2 ∣ tenCell txs.place l i 0)
    {ew wh : Array E} (hB : Blocked ρ ew wh v.y.ls low) {sg : ℕ} (h1 : sg ≠ 2 * D.nl) {a : Aff}
    (h : v.SxsA wh Z sg = some a) :
    a.value ρ W = wsum (fun x => ρ.val (ew.getD x zeroE)) lt u
      (v.y.h.d / v.y.S2 * 2 ^ v.y.ls) (fun x i => xS D t sg x i) := by
  have z : ∀ k : ℕ, k = 0 + k := fun k => (Nat.zero_add k).symm
  unfold Env.SxsA at h
  by_cases h0 : sg = 0
  · subst h0
    simp only [beq_self_eq_true, Bool.true_or, if_true, hI, hxs] at h
    have h' : Model.Layer.sumForms (v.y.h.d / v.y.S2) (fun k =>
        (v.limbs bI v.y.xb.nl (fun l => tenCell v.y.xb l 0 0 / v.y.S2 + k)).map
          fun f => (f, wh.getD k zeroE)) = some a := h
    have e := blocks_true hρ T0 R0 hS2 halb hB _ (fun k => k) (fun k => k) 0 0 z z h'
    simp only [Nat.zero_mul, Nat.zero_add] at e
    rw [e]
    exact wsum_congr _ _ _ _ fun x _ i => (xS_first D t x i).symm
  · have b0 : (sg == 0) = false := by simp [h0]
    have b1 : (sg == v.y.NW * v.y.Lam) = false := by simp [hlast, h1]
    simp only [b0, b1, Bool.or_false, Bool.false_eq_true, if_false, hF, hxs] at h
    have h' : Model.Layer.sumForms (v.y.h.d / v.y.S2) (fun k =>
        (v.limbs bF txs.place.nl (fun l => tenCell txs.place l (sg - 1) 0 / v.y.S2 + k)).map
          fun f => (f, wh.getD k zeroE)) = some a := h
    have e := blocks_true hρ Ts Rs hS2 (hals (sg - 1)) hB _ (fun k => k) (fun k => k) 0 0 z z h'
    simp only [Nat.zero_mul, Nat.zero_add] at e
    rw [e]
    exact wsum_congr _ _ _ _ fun x _ i => (xS_mid D t h0 h1 x i).symm

/-- A segment whose blocks have weights has weights for its entries. -/
theorem ewOf_of_ewh {v : Env} {sn : String} {wh : Array E} (h : v.ewh sn = some wh) :
    ∃ a, v.ewOf sn = some a := by
  unfold Env.ewh at h
  unfold Env.ewOf
  cases hc : v.callOf sn with
  | none => rw [hc] at h; cases h
  | some x => exact ⟨_, rfl⟩

section Kinds

variable [scl : Scl] {ρ : Reading K} {W : World K} {v : Env} {D : Dim} {c : Cells K}
  {t : Cell → K} {low z zh : ℕ → K}

/-- The same from the record, at the end point of the second token sumcheck. -/
theorem PortFits.Sxs2 (P : PortFits ρ W v D c t low z zh) {ew wh : Array E}
    (hw : Wts ρ ew wh v.y.ls low D.d) {sg : ℕ} (hsg : sg < 2 * D.nl) {a : Aff}
    (h : v.SxsA wh "Y" sg = some a) :
    a.value ρ W = ∑ x ∈ range D.d, wt ρ ew x * xU D t sg x zh := by
  obtain ⟨bI, bF, txs, hI, hF, hxs, _, T0, Ts, R0, Rs, halb, hals⟩ := P.stream2
  obtain ⟨n, hn⟩ := P.fits.bd
  have hpos : 0 < 2 ^ v.y.ls := by positivity
  have hd : v.y.h.d / v.y.S2 * 2 ^ v.y.ls = D.d := by
    rw [P.fits.d, P.fits.S2, hn, Nat.mul_div_cancel _ hpos]
  rw [SxsA_inner P.fits.num D P.fits.last hI hF hxs T0 Ts R0 Rs P.fits.S2 halb hals hw.blocked
    (Nat.ne_of_lt hsg) h, hd]
  rfl

/-- One entry of an array that is read entry by entry, at that end point. -/
theorem PortFits.shA2 (P : PortFits ρ W v D c t low z zh) (X : Arr) (hX : readShort X = true)
    (h0 : X.off = 0) {i j : ℕ} {a : Aff} (h : v.shA (arrName X) "rt" i j = some a) :
    a.value ρ W = valU D t X i j zh := by
  obtain ⟨ten, b, h1, T, R⟩ := P.short2 X hX
  rw [shA_true P.fits.num T R h1 h, ext_raw D t zh h0]

omit [Field K] scl in
/-- What the verifier appends as the panel of the segment N1: one column; the A side of the row of
layer lam is the value that was sent for the reciprocal of norm number 2 lam + 0; the B side is the
weighted sum over the blocks of the stream after write number 2 lam + 0, read at the point named
Y. -/
theorem panelT_N1_eq (p : PanelEnv) (ec : E) (el : Array E) (s : Panels) :
    panelT p ec el "N1" s =
      (p.v.ewh "N1").bind fun wh =>
        some (plain p.v.y ec 1 false 1
          (some fun lam _ => some (Aff.ofConst (p.shownT.getD (2 * lam + 0) zeroE)))
          (some fun lam _ => p.v.SxsA wh "Y" (2 * lam + 0))
          (fun lam => el.getD lam zeroE) none s) := by
  rfl

/-- The share of that panel is the call's weight times the library's share of the panel N1, at the
record rPort. hr: the forms of the B side are there. -/
theorem shareP_N1 (P : PortFits ρ W v D c t low z zh) {q : ℕ}
    (hel : ElTie ρ v D z q (call Fam.N1)) (hE : EwTie ρ v D z Fam.N1)
    (hT : WtsTie ρ v D low Fam.N1)
    (shownT : Array E) (ec : E) {wh : Array E}
    (hwh : v.ewh "N1" = some wh) (nv : ℕ)
    (hr : ∀ lam, lam < v.y.Lam → ∃ a, v.SxsA wh "Y" (2 * lam + 0) = some a)
    (hv wv : ℕ → ℕ → K) (tb : Tables) (L0 : ℕ) (w : ℕ → LW K) :
    shareP ρ W v.y hv wv (blkPlain v.y ec 1 false 1
        (some fun lam _ => some (Aff.ofConst (shownT.getD (2 * lam + 0) zeroE)))
        (some fun lam _ => v.SxsA wh "Y" (2 * lam + 0))
        (fun lam => (eqTab (v.zl q)).getD lam zeroE) none nv) =
      ρ.val ec * shareL D (rPort ρ v.y shownT hv D t z zh) tb L0 w z zh Pan.N1 := by
  obtain ⟨ew, hew⟩ := ewOf_of_ewh hwh
  have hW : Wts ρ ew wh v.y.ls low D.d := hT ew wh hew hwh
  rw [share_forms ρ W v.y hv wv ec 1 false 1 _ _ _ nv
    (fun i _ => sentAt ρ shownT (2 * i + 0))
    (fun i _ => ∑ x ∈ range D.d, Inst.Model.FFSeg.ew D z Fam.N1 x * xU D t (2 * i + 0) x zh)
    (fun i _ yv _ => ⟨_, rfl, Aff.value_ofConst ρ W _⟩)
    (fun i hi yv _ => by
      have hi' : i < v.y.Lam := hi
      obtain ⟨a, ha⟩ := hr i hi'
      refine ⟨a, ha, ?_⟩
      rw [P.Sxs2 hW (by rw [← P.fits.Lam]; omega) ha]
      exact sum_congr rfl fun x hx => by rw [← (hE ew hew).2 x (mem_range.mp hx)])]
  show ρ.val ec * ∑ i ∈ range v.y.Lam,
      ρ.val ((eqTab (v.zl q)).getD i zeroE) * ∑ _yv ∈ range 1,
        sentAt ρ shownT (2 * i + 0) *
          ∑ x ∈ range D.d, Inst.Model.FFSeg.ew D z Fam.N1 x * xU D t (2 * i + 0) x zh =
    ρ.val ec * ∑ l ∈ range D.nl, Inst.Model.FFSeg.el D z (call Fam.N1) l * ∑ _ι ∈ range 1,
      sentAt ρ shownT (2 * l) * ∑ x ∈ range D.d,
        Inst.Model.FFSeg.ew D z (if (2 * l) % 2 = 0 then Fam.N1 else Fam.N2) x *
          xU D t (2 * l) x zh
  rw [P.fits.Lam]
  congr 1
  refine sum_congr rfl fun l hl => ?_
  rw [hel l (mem_range.mp hl), if_pos (by omega)]
  rfl

omit [Field K] scl in
/-- What the verifier appends as the panel of the segment N2: one column; the A side of the row of
layer lam is the value that was sent for the reciprocal of norm number 2 lam + 1; the B side is the
weighted sum over the blocks of the stream after write number 2 lam + 1, read at the point named
Y. -/
theorem panelT_N2_eq (p : PanelEnv) (ec : E) (el : Array E) (s : Panels) :
    panelT p ec el "N2" s =
      (p.v.ewh "N2").bind fun wh =>
        some (plain p.v.y ec 1 false 1
          (some fun lam _ => some (Aff.ofConst (p.shownT.getD (2 * lam + 1) zeroE)))
          (some fun lam _ => p.v.SxsA wh "Y" (2 * lam + 1))
          (fun lam => el.getD lam zeroE) none s) := by
  rfl

/-- The share of that panel is the call's weight times the library's share of the panel N2, at the
record rPort. hr: the forms of the B side are there. -/
theorem shareP_N2 (P : PortFits ρ W v D c t low z zh) {q : ℕ}
    (hel : ElTie ρ v D z q (call Fam.N2)) (hE : EwTie ρ v D z Fam.N2)
    (hT : WtsTie ρ v D low Fam.N2)
    (shownT : Array E) (ec : E) {wh : Array E}
    (hwh : v.ewh "N2" = some wh) (nv : ℕ)
    (hr : ∀ lam, lam < v.y.Lam → ∃ a, v.SxsA wh "Y" (2 * lam + 1) = some a)
    (hv wv : ℕ → ℕ → K) (tb : Tables) (L0 : ℕ) (w : ℕ → LW K) :
    shareP ρ W v.y hv wv (blkPlain v.y ec 1 false 1
        (some fun lam _ => some (Aff.ofConst (shownT.getD (2 * lam + 1) zeroE)))
        (some fun lam _ => v.SxsA wh "Y" (2 * lam + 1))
        (fun lam => (eqTab (v.zl q)).getD lam zeroE) none nv) =
      ρ.val ec * shareL D (rPort ρ v.y shownT hv D t z zh) tb L0 w z zh Pan.N2 := by
  obtain ⟨ew, hew⟩ := ewOf_of_ewh hwh
  have hW : Wts ρ ew wh v.y.ls low D.d := hT ew wh hew hwh
  rw [share_forms ρ W v.y hv wv ec 1 false 1 _ _ _ nv
    (fun i _ => sentAt ρ shownT (2 * i + 1))
    (fun i _ => ∑ x ∈ range D.d, Inst.Model.FFSeg.ew D z Fam.N2 x * xU D t (2 * i + 1) x zh)
    (fun i _ yv _ => ⟨_, rfl, Aff.value_ofConst ρ W _⟩)
    (fun i hi yv _ => by
      have hi' : i < v.y.Lam := hi
      obtain ⟨a, ha⟩ := hr i hi'
      refine ⟨a, ha, ?_⟩
      rw [P.Sxs2 hW (by rw [← P.fits.Lam]; omega) ha]
      exact sum_congr rfl fun x hx => by rw [← (hE ew hew).2 x (mem_range.mp hx)])]
  show ρ.val ec * ∑ i ∈ range v.y.Lam,
      ρ.val ((eqTab (v.zl q)).getD i zeroE) * ∑ _yv ∈ range 1,
        sentAt ρ shownT (2 * i + 1) *
          ∑ x ∈ range D.d, Inst.Model.FFSeg.ew D z Fam.N2 x * xU D t (2 * i + 1) x zh =
    ρ.val ec * ∑ l ∈ range D.nl, Inst.Model.FFSeg.el D z (call Fam.N2) l * ∑ _ι ∈ range 1,
      sentAt ρ shownT (2 * l + 1) * ∑ x ∈ range D.d,
        Inst.Model.FFSeg.ew D z (if (2 * l + 1) % 2 = 0 then Fam.N1 else Fam.N2) x *
          xU D t (2 * l + 1) x zh
  rw [P.fits.Lam]
  congr 1
  refine sum_congr rfl fun l hl => ?_
  rw [hel l (mem_range.mp hl), if_neg (by omega)]

omit [Field K] scl in
/-- Row i of a panel over the layers with routed experts is below the group's layers. -/
theorem odd_lt (D : Dim) {i : ℕ} (hi : i < D.ne) : 2 * i + 1 < D.nl := by
  unfold Inst.Model.FFSeg.Dim.ne at hi
  omega

/-- The share of the panel that the verifier appends for the segment XR (panelT_XR_eq in
Johnson/Road/FormsKeysXR.lean) is the call's weight times the library's share of the panel XR, at
the record rPort. hr: the forms of the B side are there. -/
theorem shareP_XR (P : PortFits ρ W v D c t low z zh) {q : ℕ}
    (hel : ElTie ρ v D z q (call Fam.XR)) (hE : EwTie ρ v D z Fam.XR)
    (shownT : Array E) (ec : E) {ew : Array E}
    (hew : v.ewOf "XR" = some ew) (nv : ℕ)
    (hr : ∀ i, i < v.y.LamM → ∃ a, v.shSum ew v.y.h.d "m" "rt" (2 * i + 1) = some a)
    (hv wv : ℕ → ℕ → K) (tb : Tables) (L0 : ℕ) (w : ℕ → LW K) :
    shareP ρ W v.y hv wv (blkPlain v.y ec 1 true 1
        (some fun lam _ => some (Aff.ofConst (shownT.getD (v.y.NN * v.y.Lam + lam / 2) zeroE)))
        (some fun lam _ => v.shSum ew v.y.h.d "m" "rt" lam)
        (fun lam => (eqTab (v.zl q)).getD lam zeroE) none nv) =
      ρ.val ec * shareL D (rPort ρ v.y shownT hv D t z zh) tb L0 w z zh Pan.XR := by
  obtain ⟨ten, b, hX, T, R⟩ := P.short2 .m rfl
  rw [share_forms ρ W v.y hv wv ec 1 true 1 _ _ _ nv
    (fun i _ => sentAt ρ shownT (v.y.NN * v.y.Lam + i))
    (fun i _ => ∑ x ∈ range D.d, Inst.Model.FFSeg.ew D z Fam.XR x * valU D t .m (2 * i + 1) x zh)
    (fun i _ yv _ => ⟨_, rfl, by
      rw [Aff.value_ofConst]
      show ρ.val (shownT.getD (v.y.NN * v.y.Lam + (2 * i + 1) / 2) zeroE) = _
      rw [show (2 * i + 1) / 2 = i by omega]
      rfl⟩)
    (fun i hi yv _ => by
      have hi' : i < v.y.LamM := hi
      obtain ⟨a, ha⟩ := hr i hi'
      refine ⟨a, ha, ?_⟩
      rw [rowXR_value P.fits.num hX T R P.fits.d (2 * i + 1) ha]
      exact sum_congr rfl fun x hx => by rw [← (hE ew hew).2 x (mem_range.mp hx)])]
  show ρ.val ec * ∑ i ∈ range v.y.LamM,
      ρ.val ((eqTab (v.zl q)).getD (2 * i + 1) zeroE) * ∑ _yv ∈ range 1,
        sentAt ρ shownT (v.y.NN * v.y.Lam + i) *
          ∑ x ∈ range D.d, Inst.Model.FFSeg.ew D z Fam.XR x * valU D t .m (2 * i + 1) x zh =
    ρ.val ec * ∑ l ∈ range D.ne, Inst.Model.FFSeg.el D z (call Fam.XR) (2 * l + 1) *
      ∑ _ι ∈ range 1, sentAt ρ shownT (v.y.NN * v.y.Lam + l) *
        ∑ x ∈ range D.d, Inst.Model.FFSeg.ew D z Fam.XR x * valU D t .m (2 * l + 1) x zh
  rw [P.fits.LamM]
  congr 1
  refine sum_congr rfl fun l hl => ?_
  rw [hel (2 * l + 1) (odd_lt D (mem_range.mp hl))]

omit [Field K] scl in
/-- What the verifier appends as the panel of the segment DD, with routed experts: NE columns; the A
side at (layer lam, expert e) is the value that was sent for entry e of the selector of layer lam;
the B side is entry e of the router's output, read at the point named rt; the weight of a row is the
layer's weight times the sum of the weights of the segment's entries. -/
theorem panelT_DD_eq (p : PanelEnv) (ec : E) (el : Array E) (s : Panels) :
    panelT p ec el "DD" s =
      (if !p.v.y.h.p3 then pure s
      else (p.v.ewOf "DD").bind fun ew =>
        some (plain p.v.y ec 1 true p.v.y.h.NE
          (some fun lam e => some (Aff.ofConst (p.shownT.getD
            (p.v.y.NN * p.v.y.Lam + p.v.y.LamM + (lam / 2) * p.v.y.h.NE + e) zeroE)))
          (some fun lam e => p.v.shA "lr" "rt" (lam / 2) e)
          (fun lam => mulE (el.getD lam zeroE) (sumE ew)) none s)) := by
  rfl

omit [Field K] scl in
/-- The same for the segment MR; the weight of a row is the layer's weight times the weight of the
segment's one entry. -/
theorem panelT_MR_eq (p : PanelEnv) (ec : E) (el : Array E) (s : Panels) :
    panelT p ec el "MR" s =
      (if !p.v.y.h.p3 then pure s
      else (p.v.ewOf "MR").bind fun ew =>
        some (plain p.v.y ec 1 true p.v.y.h.NE
          (some fun lam e => some (Aff.ofConst (p.shownT.getD
            (p.v.y.NN * p.v.y.Lam + p.v.y.LamM + (lam / 2) * p.v.y.h.NE + e) zeroE)))
          (some fun lam e => p.v.shA "lr" "rt" (lam / 2) e)
          (fun lam => mulE (el.getD lam zeroE) (ew.getD 0 zeroE)) none s)) := by
  rfl

/-- The share of a panel with the sides of DD and MR, for any factor wS in the rows' weights and any
layers' weights: the common part of shareP_DD and shareP_MR. -/
theorem share_sel (P : PortFits ρ W v D c t low z zh) (shownT : Array E) (ec wS : E)
    (el : Array E) (nv : ℕ)
    (hr : ∀ i, i < v.y.LamM → ∀ e, e < v.y.h.NE → ∃ a, v.shA "lr" "rt" ((2 * i + 1) / 2) e = some a)
    (hv wv : ℕ → ℕ → K) :
    shareP ρ W v.y hv wv (blkPlain v.y ec 1 true v.y.h.NE
        (some fun lam e => some (Aff.ofConst (shownT.getD
          (v.y.NN * v.y.Lam + v.y.LamM + (lam / 2) * v.y.h.NE + e) zeroE)))
        (some fun lam e => v.shA "lr" "rt" (lam / 2) e)
        (fun lam => mulE (el.getD lam zeroE) wS) none nv) =
      ρ.val ec * ∑ l ∈ range D.ne, (ρ.val (el.getD (2 * l + 1) zeroE) * ρ.val wS) *
        ∑ e ∈ range D.nx, sentAt ρ shownT (v.y.NN * v.y.Lam + v.y.LamM + l * v.y.h.NE + e) *
          valU D t .lr l e zh := by
  rw [share_forms ρ W v.y hv wv ec 1 true v.y.h.NE _ _ _ nv
    (fun i e => sentAt ρ shownT (v.y.NN * v.y.Lam + v.y.LamM + i * v.y.h.NE + e))
    (fun i e => valU D t .lr i e zh)
    (fun i _ e _ => ⟨_, rfl, by
      rw [Aff.value_ofConst]
      show ρ.val (shownT.getD
        (v.y.NN * v.y.Lam + v.y.LamM + (2 * i + 1) / 2 * v.y.h.NE + e) zeroE) = _
      rw [show (2 * i + 1) / 2 = i by omega]
      rfl⟩)
    (fun i hi e he => by
      have hi' : i < v.y.LamM := hi
      obtain ⟨a, ha⟩ := hr i hi' e he
      refine ⟨a, ha, ?_⟩
      rw [P.shA2 .lr rfl rfl ha, show (2 * i + 1) / 2 = i by omega])]
  show ρ.val ec * ∑ i ∈ range v.y.LamM, ρ.val (mulE (el.getD (2 * i + 1) zeroE) wS) *
      ∑ e ∈ range v.y.h.NE, sentAt ρ shownT (v.y.NN * v.y.Lam + v.y.LamM + i * v.y.h.NE + e) *
        valU D t .lr i e zh = _
  rw [P.fits.LamM, P.fits.NE]
  congr 1
  refine sum_congr rfl fun l _ => ?_
  rw [ρ.mul]

/-- The share of the panel of the segment DD is the call's weight times the library's share of the
panel DD, at the record rPort. -/
theorem shareP_DD (P : PortFits ρ W v D c t low z zh) {q : ℕ}
    (hel : ElTie ρ v D z q (call Fam.DD)) (hE : EwTie ρ v D z Fam.DD)
    (shownT : Array E) (ec : E) {ew : Array E}
    (hew : v.ewOf "DD" = some ew) (nv : ℕ)
    (hr : ∀ i, i < v.y.LamM → ∀ e, e < v.y.h.NE → ∃ a, v.shA "lr" "rt" ((2 * i + 1) / 2) e = some a)
    (hv wv : ℕ → ℕ → K) (tb : Tables) (L0 : ℕ) (w : ℕ → LW K) :
    shareP ρ W v.y hv wv (blkPlain v.y ec 1 true v.y.h.NE
        (some fun lam e => some (Aff.ofConst (shownT.getD
          (v.y.NN * v.y.Lam + v.y.LamM + (lam / 2) * v.y.h.NE + e) zeroE)))
        (some fun lam e => v.shA "lr" "rt" (lam / 2) e)
        (fun lam => mulE ((eqTab (v.zl q)).getD lam zeroE) (sumE ew)) none nv) =
      ρ.val ec * shareL D (rPort ρ v.y shownT hv D t z zh) tb L0 w z zh Pan.DD := by
  rw [share_sel P shownT ec (sumE ew) _ nv hr hv wv]
  show _ = ρ.val ec * ∑ l ∈ range D.ne,
    (Inst.Model.FFSeg.el D z (call Fam.DD) (2 * l + 1) * Inst.Model.FFSeg.sw D z Fam.DD) *
      ∑ e ∈ range D.nx, sentAt ρ shownT (v.y.NN * v.y.Lam + v.y.LamM + l * v.y.h.NE + e) *
        valU D t .lr l e zh
  have hs : ρ.val (sumE ew) = Inst.Model.FFSeg.sw D z Fam.DD := by
    rw [sumE_value, (hE ew hew).1]
    exact sum_congr rfl fun x hx => (hE ew hew).2 x (mem_range.mp hx)
  congr 1
  refine sum_congr rfl fun l hl => ?_
  rw [hel (2 * l + 1) (odd_lt D (mem_range.mp hl)), hs]

/-- The share of the panel of the segment MR is the call's weight times the library's share of the
panel MR, at the record rPort. -/
theorem shareP_MR (P : PortFits ρ W v D c t low z zh) {q : ℕ}
    (hel : ElTie ρ v D z q (call Fam.MR)) (hE : EwTie ρ v D z Fam.MR)
    (shownT : Array E) (ec : E) {ew : Array E}
    (hew : v.ewOf "MR" = some ew) (nv : ℕ)
    (hr : ∀ i, i < v.y.LamM → ∀ e, e < v.y.h.NE → ∃ a, v.shA "lr" "rt" ((2 * i + 1) / 2) e = some a)
    (hv wv : ℕ → ℕ → K) (tb : Tables) (L0 : ℕ) (w : ℕ → LW K) :
    shareP ρ W v.y hv wv (blkPlain v.y ec 1 true v.y.h.NE
        (some fun lam e => some (Aff.ofConst (shownT.getD
          (v.y.NN * v.y.Lam + v.y.LamM + (lam / 2) * v.y.h.NE + e) zeroE)))
        (some fun lam e => v.shA "lr" "rt" (lam / 2) e)
        (fun lam => mulE ((eqTab (v.zl q)).getD lam zeroE) (ew.getD 0 zeroE))
        none nv) =
      ρ.val ec * shareL D (rPort ρ v.y shownT hv D t z zh) tb L0 w z zh Pan.MR := by
  rw [share_sel P shownT ec (ew.getD 0 zeroE) _ nv hr hv wv]
  show _ = ρ.val ec * ∑ l ∈ range D.ne,
    (Inst.Model.FFSeg.el D z (call Fam.MR) (2 * l + 1) * Inst.Model.FFSeg.ew D z Fam.MR 0) *
      ∑ e ∈ range D.nx, sentAt ρ shownT (v.y.NN * v.y.Lam + v.y.LamM + l * v.y.h.NE + e) *
        valU D t .lr l e zh
  have hs : ρ.val (ew.getD 0 zeroE) = Inst.Model.FFSeg.ew D z Fam.MR 0 :=
    (hE ew hew).2 0 Nat.one_pos
  congr 1
  refine sum_congr rfl fun l hl => ?_
  rw [hel (2 * l + 1) (odd_lt D (mem_range.mp hl)), hs]

/-! ## The share of a panel with the selector -/

end Kinds

/-- The share of a panel with the selector whose column factor is given as forms: if the form of
each column is worth a, and the vector of the panel's weight claim holds B, the share is the call's
weight times the sum over the rows of the panel's weight times the selector's factor times the inner
product of a and the row of B. -/
theorem share_tri_forms (ρ : Reading K) (W : World K) (y : Lay) (hv wv : ℕ → ℕ → K) (ec : E)
    (claim nk : ℕ) (sl : Array E) (xx : Array Aff) (wt : E) (nv : ℕ) (a : ℕ → K)
    (B : ℕ → ℕ → K) (ha : ∀ yv, yv < nk → (xx.getD yv {}).value ρ W = a yv)
    (hw : WvTri wv nv y.h.NE (ceilLog2 nk) nk B) :
    shareP ρ W y hv wv (blkTri y ec claim nk sl xx none wt nv) =
      ρ.val ec * ∑ e ∈ range y.h.NE, (ρ.val wt * ρ.val (sl.getD e zeroE)) *
        ∑ yv ∈ range nk, a yv * B e yv := by
  show ρ.val ec * ∑ e ∈ range y.h.NE, (ρ.val wt * ρ.val (sl.getD e zeroE)) *
      ∑ yv ∈ range (2 ^ ceilLog2 nk),
        (if yv < nk then (xx.getD yv {}).value ρ W else 0) * wv nv (e * 2 ^ ceilLog2 nk + yv) = _
  congr 1
  refine sum_congr rfl fun e he => ?_
  rw [← sum_upto (le_two_pow_ceilLog2 nk)]
  congr 1
  refine sum_congr rfl fun yv hy => ?_
  rw [hw e (mem_range.mp he) yv (mem_range.mp hy)]
  by_cases h : yv < nk
  · rw [if_pos h, if_pos h, if_pos h, ha yv h]
  · rw [if_neg h, if_neg h, if_neg h, zero_mul]

/-- The same for a panel whose column factor is the never-sent vector number k. -/
theorem share_tri_virt (ρ : Reading K) (W : World K) (y : Lay) (hv wv : ℕ → ℕ → K) (ec : E)
    (claim nk : ℕ) (sl : Array E) (xx : Array Aff) (k : ℕ) (wt : E) (nv : ℕ) (B : ℕ → ℕ → K)
    (hw : WvTri wv nv y.h.NE (ceilLog2 nk) nk B) :
    shareP ρ W y hv wv (blkTri y ec claim nk sl xx (some k) wt nv) =
      ρ.val ec * ∑ e ∈ range y.h.NE, (ρ.val wt * ρ.val (sl.getD e zeroE)) *
        ∑ yv ∈ range nk, hv k yv * B e yv := by
  show ρ.val ec * ∑ e ∈ range y.h.NE, (ρ.val wt * ρ.val (sl.getD e zeroE)) *
      ∑ yv ∈ range (2 ^ ceilLog2 nk), hv k yv * wv nv (e * 2 ^ ceilLog2 nk + yv) = _
  congr 1
  refine sum_congr rfl fun e he => ?_
  rw [← sum_upto (le_two_pow_ceilLog2 nk)]
  congr 1
  refine sum_congr rfl fun yv hy => ?_
  rw [hw e (mem_range.mp he) yv (mem_range.mp hy)]
  by_cases h : yv < nk
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h, mul_zero]

section Routed

variable [scl : Scl] {ρ : Reading K} {W : World K} {v : Env} {D : Dim} {c : Cells K}
  {t : Cell → K} {low z zh : ℕ → K}

/-- The panel with the selector that the verifier appends for the segment G and layer 2 lm + 1
(triStep in Johnson/Road/FormsKeysFold.lean): d columns; the selector's factors are the values that
were sent for the entries of that layer's selector; the column factor is the routed experts' input
xr, read at the point named rt. Its share is the call's weight times the library's share of the
panel Gr lm, at the record rPort. hw: the vector of the panel's weight claim is the library's B
side. -/
theorem shareP_Gr (P : PortFits ρ W v D c t low z zh) {q : ℕ}
    (hel : ElTie ρ v D z q (call Fam.G))
    (shownT : Array E) (ec : E) {lm : ℕ}
    (hlm : lm < D.ne) {xx : Array Aff}
    (hxx : ((Array.range v.y.h.d).mapM fun k2 => v.shIn (v.tensorAt "xr" "rt") lm k2) = some xx)
    (nv : ℕ) (hv wv : ℕ → ℕ → K) (tb : Tables) (L0 : ℕ) (w : ℕ → LW K)
    (hw : WvTri wv nv v.y.h.NE (ceilLog2 v.y.h.d) ((Pan.Gr lm).nc D)
      ((Pan.Gr lm).B D (rPort ρ v.y shownT hv D t z zh) tb L0 w z zh)) :
    shareP ρ W v.y hv wv (blkTri v.y ec 1 v.y.h.d
        ((Array.range v.y.h.NE).map fun e => shownT.getD
          (v.y.NN * v.y.Lam + v.y.LamM + lm * v.y.h.NE + e) zeroE)
        xx none
        (mulE ((eqTab (v.zl q)).getD (2 * lm + 1) zeroE)
          (kTM v.sc (v.lay (2 * lm + 1)) 1)) nv) =
      ρ.val ec * shareL D (rPort ρ v.y shownT hv D t z zh) tb L0 w z zh (Pan.Gr lm) := by
  have hw' : WvTri wv nv v.y.h.NE (ceilLog2 v.y.h.d) v.y.h.d
      ((Pan.Gr lm).B D (rPort ρ v.y shownT hv D t z zh) tb L0 w z zh) := by
    intro e he yv hy
    rw [hw e he yv hy, P.fits.d]
    rfl
  rw [share_tri_forms ρ W v.y hv wv ec 1 v.y.h.d _ xx _ nv (fun yv => valU D t .xr lm yv zh) _
    (fun yv hy => P.shA2 .xr rfl rfl
      (show v.shA (arrName Arr.xr) "rt" lm yv = some (xx.getD yv {}) from
        range_mapM_get ({} : Aff) hxx hy)) hw']
  show ρ.val ec * ∑ e ∈ range v.y.h.NE,
      (ρ.val (mulE ((eqTab (v.zl q)).getD (2 * lm + 1) zeroE)
          (Model.Layer.pw (Model.Layer.tOf (v.sc.klM (v.lay (2 * lm + 1)) 1)))) *
        ρ.val (((Array.range v.y.h.NE).map fun e => shownT.getD
          (v.y.NN * v.y.Lam + v.y.LamM + lm * v.y.h.NE + e) zeroE).getD e zeroE)) *
      ∑ yv ∈ range v.y.h.d, valU D t .xr lm yv zh *
        (Pan.Gr lm).B D (rPort ρ v.y shownT hv D t z zh) tb L0 w z zh e yv =
    ρ.val ec * ∑ e ∈ range D.nx,
      Inst.Model.Site.scl (D.Pl (2 * lm + 1)).kg'
          (Inst.Model.FFSeg.el D z (call Fam.G) (2 * lm + 1)) *
        ∑ j ∈ range D.d,
          (sentAt ρ shownT (v.y.NN * v.y.Lam + v.y.LamM + lm * v.y.h.NE + e) *
            valU D t .xr lm j zh) *
          (Pan.Gr lm).B D (rPort ρ v.y shownT hv D t z zh) tb L0 w z zh e j
  have hl := odd_lt D hlm
  rw [P.fits.kgR (2 * lm + 1) hl (by omega), scl_weight P.fits.num, hel _ hl, P.fits.d]
  congr 1
  rw [← P.fits.NE]
  refine sum_congr rfl fun e he => ?_
  rw [range_map_getD _ _ (mem_range.mp he), mul_assoc, mul_sum]
  congr 1
  refine sum_congr rfl fun j _ => ?_
  unfold sentAt
  ring

/-- The panel with the selector that the verifier appends for the segment U and layer 2 lm + 1
(triStep in Johnson/Road/FormsKeysFold.lean): d columns; the selector's factors are the values that
were sent for the entries of that layer's selector; the column factor is the routed experts' input
xr, read at the point named rt. Its share is the call's weight times the library's share of the
panel Ur lm, at the record rPort. hw: the vector of the panel's weight claim is the library's B
side. -/
theorem shareP_Ur (P : PortFits ρ W v D c t low z zh) {q : ℕ}
    (hel : ElTie ρ v D z q (call Fam.U))
    (shownT : Array E) (ec : E) {lm : ℕ}
    (hlm : lm < D.ne) {xx : Array Aff}
    (hxx : ((Array.range v.y.h.d).mapM fun k2 => v.shIn (v.tensorAt "xr" "rt") lm k2) = some xx)
    (nv : ℕ) (hv wv : ℕ → ℕ → K) (tb : Tables) (L0 : ℕ) (w : ℕ → LW K)
    (hw : WvTri wv nv v.y.h.NE (ceilLog2 v.y.h.d) ((Pan.Ur lm).nc D)
      ((Pan.Ur lm).B D (rPort ρ v.y shownT hv D t z zh) tb L0 w z zh)) :
    shareP ρ W v.y hv wv (blkTri v.y ec 1 v.y.h.d
        ((Array.range v.y.h.NE).map fun e => shownT.getD
          (v.y.NN * v.y.Lam + v.y.LamM + lm * v.y.h.NE + e) zeroE)
        xx none
        (mulE ((eqTab (v.zl q)).getD (2 * lm + 1) zeroE)
          (kTM v.sc (v.lay (2 * lm + 1)) 2)) nv) =
      ρ.val ec * shareL D (rPort ρ v.y shownT hv D t z zh) tb L0 w z zh (Pan.Ur lm) := by
  have hw' : WvTri wv nv v.y.h.NE (ceilLog2 v.y.h.d) v.y.h.d
      ((Pan.Ur lm).B D (rPort ρ v.y shownT hv D t z zh) tb L0 w z zh) := by
    intro e he yv hy
    rw [hw e he yv hy, P.fits.d]
    rfl
  rw [share_tri_forms ρ W v.y hv wv ec 1 v.y.h.d _ xx _ nv (fun yv => valU D t .xr lm yv zh) _
    (fun yv hy => P.shA2 .xr rfl rfl
      (show v.shA (arrName Arr.xr) "rt" lm yv = some (xx.getD yv {}) from
        range_mapM_get ({} : Aff) hxx hy)) hw']
  show ρ.val ec * ∑ e ∈ range v.y.h.NE,
      (ρ.val (mulE ((eqTab (v.zl q)).getD (2 * lm + 1) zeroE)
          (Model.Layer.pw (Model.Layer.tOf (v.sc.klM (v.lay (2 * lm + 1)) 2)))) *
        ρ.val (((Array.range v.y.h.NE).map fun e => shownT.getD
          (v.y.NN * v.y.Lam + v.y.LamM + lm * v.y.h.NE + e) zeroE).getD e zeroE)) *
      ∑ yv ∈ range v.y.h.d, valU D t .xr lm yv zh *
        (Pan.Ur lm).B D (rPort ρ v.y shownT hv D t z zh) tb L0 w z zh e yv =
    ρ.val ec * ∑ e ∈ range D.nx,
      Inst.Model.Site.scl (D.Pl (2 * lm + 1)).ku'
          (Inst.Model.FFSeg.el D z (call Fam.U) (2 * lm + 1)) *
        ∑ j ∈ range D.d,
          (sentAt ρ shownT (v.y.NN * v.y.Lam + v.y.LamM + lm * v.y.h.NE + e) *
            valU D t .xr lm j zh) *
          (Pan.Ur lm).B D (rPort ρ v.y shownT hv D t z zh) tb L0 w z zh e j
  have hl := odd_lt D hlm
  rw [P.fits.kuR (2 * lm + 1) hl (by omega), scl_weight P.fits.num, hel _ hl, P.fits.d]
  congr 1
  rw [← P.fits.NE]
  refine sum_congr rfl fun e he => ?_
  rw [range_map_getD _ _ (mem_range.mp he), mul_assoc, mul_sum]
  congr 1
  refine sum_congr rfl fun j _ => ?_
  unfold sentAt
  ring

/-- The panel with the selector that the verifier appends for the segment D and layer 2 lm + 1
(triStep): fe columns; the selector's factors as before; the column factor is the never-sent vector
number 1 + lm. Its share is the call's weight times the library's share of the panel Dr lm, at the
record rPort. hw: the vector of the panel's weight claim is the library's B side. The never-sent
vector stays free: rPort has it for Hh2. -/
theorem shareP_Dr (P : PortFits ρ W v D c t low z zh) {q : ℕ}
    (hel : ElTie ρ v D z q (call Fam.D))
    (shownT : Array E) (ec : E) {lm : ℕ}
    (hlm : lm < D.ne) (nv : ℕ) (hv wv : ℕ → ℕ → K) (tb : Tables) (L0 : ℕ) (w : ℕ → LW K)
    (hw : WvTri wv nv v.y.h.NE (ceilLog2 v.y.h.fe) ((Pan.Dr lm).nc D)
      ((Pan.Dr lm).B D (rPort ρ v.y shownT hv D t z zh) tb L0 w z zh)) :
    shareP ρ W v.y hv wv (blkTri v.y ec 1 v.y.h.fe
        ((Array.range v.y.h.NE).map fun e => shownT.getD
          (v.y.NN * v.y.Lam + v.y.LamM + lm * v.y.h.NE + e) zeroE)
        #[] (some (1 + lm))
        (mulE ((eqTab (v.zl q)).getD (2 * lm + 1) zeroE)
          (kT v.sc (v.lay (2 * lm + 1)) Model.Layer.Lkd)) nv) =
      ρ.val ec * shareL D (rPort ρ v.y shownT hv D t z zh) tb L0 w z zh (Pan.Dr lm) := by
  have hw' : WvTri wv nv v.y.h.NE (ceilLog2 v.y.h.fe) v.y.h.fe
      ((Pan.Dr lm).B D (rPort ρ v.y shownT hv D t z zh) tb L0 w z zh) := by
    intro e he yv hy
    rw [hw e he yv hy, P.fits.fe]
    rfl
  rw [share_tri_virt ρ W v.y hv wv ec 1 v.y.h.fe _ #[] (1 + lm) _ nv _ hw']
  show ρ.val ec * ∑ e ∈ range v.y.h.NE,
      (ρ.val (mulE ((eqTab (v.zl q)).getD (2 * lm + 1) zeroE)
          (Model.Layer.pw (Model.Layer.tOf (v.sc.kl (v.lay (2 * lm + 1)) Model.Layer.Lkd)))) *
        ρ.val (((Array.range v.y.h.NE).map fun e => shownT.getD
          (v.y.NN * v.y.Lam + v.y.LamM + lm * v.y.h.NE + e) zeroE).getD e zeroE)) *
      ∑ yv ∈ range v.y.h.fe, hv (1 + lm) yv *
        (Pan.Dr lm).B D (rPort ρ v.y shownT hv D t z zh) tb L0 w z zh e yv =
    ρ.val ec * ∑ e ∈ range D.nx,
      Inst.Model.Site.scl (D.Pl (2 * lm + 1)).kd
          (Inst.Model.FFSeg.el D z (call Fam.D) (2 * lm + 1)) *
        ∑ j ∈ range D.fe,
          (sentAt ρ shownT (v.y.NN * v.y.Lam + v.y.LamM + lm * v.y.h.NE + e) * hv (1 + lm) j) *
          (Pan.Dr lm).B D (rPort ρ v.y shownT hv D t z zh) tb L0 w z zh e j
  have hl := odd_lt D hlm
  rw [P.fits.kd (2 * lm + 1) hl, scl_weight P.fits.num, hel _ hl, P.fits.fe]
  congr 1
  rw [← P.fits.NE]
  refine sum_congr rfl fun e he => ?_
  rw [range_map_getD _ _ (mem_range.mp he), mul_assoc, mul_sum]
  congr 1
  refine sum_congr rfl fun j _ => ?_
  unfold sentAt
  ring

end Routed

/-! ## The same on what panelT returns -/

/-- Two arrays that arise from one by appending a member are equal only if the members are. -/
theorem push_same {α : Type} {a : Array α} {x y : α} (h : a.push x = a.push y) : x = y := by
  have h2 := congrArg Array.back? h
  simpa using h2

/-- A step that may refuse and then returns a value. -/
theorem of_bind_some {α β : Type} {o : Option α} {F : α → β} {r : β}
    (h : (o.bind fun x => some (F x)) = some r) : ∃ x, o = some x ∧ r = F x := by
  cases o with
  | none => cases h
  | some x => exact ⟨x, rfl, (Option.some.inj h).symm⟩

section Whole

variable [scl : Scl] {ρ : Reading K} {W : World K} {v : Env} {D : Dim} {c : Cells K}
  {t : Cell → K} {low z zh : ℕ → K}

/-- THE PANEL OF N1. If panelT returns for the segment N1, with the layers' weights in the point of
call number q, and b is the panel that it has appended, whose forms are there, then the share of b
is the call's weight times the library's share of the panel N1 at the record rPort. -/
theorem panelP_N1 (P : PortFits ρ W v D c t low z zh) {q : ℕ}
    (hel : ElTie ρ v D z q (call Fam.N1)) (hE : EwTie ρ v D z Fam.N1)
    (hT : WtsTie ρ v D low Fam.N1)
    (p : PanelEnv) (hp : p.v = v) (ec : E)
    (s : Panels) (hv wv : ℕ → ℕ → K) (tb : Tables) (L0 : ℕ) (w : ℕ → LW K) {s' : Panels} {b : SBlk}
    (hs : panelT p ec (eqTab (v.zl q)) "N1" s = some s')
    (hb : s'.bl = s.bl.push b) (hr : Returns b) :
    shareP ρ W v.y hv wv b =
      ρ.val ec * shareL D (rPort ρ v.y p.shownT hv D t z zh) tb L0 w z zh Pan.N1 := by
  subst hp
  rw [panelT_N1_eq] at hs
  obtain ⟨wh, hwh, e⟩ := of_bind_some hs
  rw [e, plain_push] at hb
  have eb := push_same hb
  subst eb
  exact shareP_N1 P hel hE hT p.shownT ec hwh s.nextV
    (fun lam hlam => hr.2 _ rfl lam hlam 0 Nat.one_pos) hv wv tb L0 w

/-- THE PANEL OF N2: as panelP_N1. -/
theorem panelP_N2 (P : PortFits ρ W v D c t low z zh) {q : ℕ}
    (hel : ElTie ρ v D z q (call Fam.N2)) (hE : EwTie ρ v D z Fam.N2)
    (hT : WtsTie ρ v D low Fam.N2)
    (p : PanelEnv) (hp : p.v = v) (ec : E)
    (s : Panels) (hv wv : ℕ → ℕ → K) (tb : Tables) (L0 : ℕ) (w : ℕ → LW K) {s' : Panels} {b : SBlk}
    (hs : panelT p ec (eqTab (v.zl q)) "N2" s = some s')
    (hb : s'.bl = s.bl.push b) (hr : Returns b) :
    shareP ρ W v.y hv wv b =
      ρ.val ec * shareL D (rPort ρ v.y p.shownT hv D t z zh) tb L0 w z zh Pan.N2 := by
  subst hp
  rw [panelT_N2_eq] at hs
  obtain ⟨wh, hwh, e⟩ := of_bind_some hs
  rw [e, plain_push] at hb
  have eb := push_same hb
  subst eb
  exact shareP_N2 P hel hE hT p.shownT ec hwh s.nextV
    (fun lam hlam => hr.2 _ rfl lam hlam 0 Nat.one_pos) hv wv tb L0 w

/-- THE PANEL OF XR: as panelP_N1. -/
theorem panelP_XR (P : PortFits ρ W v D c t low z zh) {q : ℕ}
    (hel : ElTie ρ v D z q (call Fam.XR)) (hE : EwTie ρ v D z Fam.XR)
    (p : PanelEnv) (hp : p.v = v) (ec : E)
    (s : Panels) (hv wv : ℕ → ℕ → K) (tb : Tables) (L0 : ℕ) (w : ℕ → LW K) {s' : Panels} {b : SBlk}
    (hs : panelT p ec (eqTab (v.zl q)) "XR" s = some s')
    (hb : s'.bl = s.bl.push b) (hr : Returns b) :
    shareP ρ W v.y hv wv b =
      ρ.val ec * shareL D (rPort ρ v.y p.shownT hv D t z zh) tb L0 w z zh Pan.XR := by
  subst hp
  rw [panelT_XR_eq, P.fits.p3] at hs
  obtain ⟨ew, hew, e⟩ := of_bind_some (o := p.v.ewOf "XR") hs
  rw [e, plain_push] at hb
  have eb := push_same hb
  subst eb
  exact shareP_XR P hel hE p.shownT ec hew s.nextV
    (fun i hi => hr.2 _ rfl i hi 0 Nat.one_pos) hv wv tb L0 w

/-- THE PANEL OF DD: as panelP_N1. -/
theorem panelP_DD (P : PortFits ρ W v D c t low z zh) {q : ℕ}
    (hel : ElTie ρ v D z q (call Fam.DD)) (hE : EwTie ρ v D z Fam.DD)
    (p : PanelEnv) (hp : p.v = v) (ec : E)
    (s : Panels) (hv wv : ℕ → ℕ → K) (tb : Tables) (L0 : ℕ) (w : ℕ → LW K) {s' : Panels} {b : SBlk}
    (hs : panelT p ec (eqTab (v.zl q)) "DD" s = some s')
    (hb : s'.bl = s.bl.push b) (hr : Returns b) :
    shareP ρ W v.y hv wv b =
      ρ.val ec * shareL D (rPort ρ v.y p.shownT hv D t z zh) tb L0 w z zh Pan.DD := by
  subst hp
  rw [panelT_DD_eq, P.fits.p3] at hs
  obtain ⟨ew, hew, e⟩ := of_bind_some (o := p.v.ewOf "DD") hs
  rw [e, plain_push] at hb
  have eb := push_same hb
  subst eb
  exact shareP_DD P hel hE p.shownT ec hew s.nextV
    (fun i hi e he => hr.2 _ rfl i hi e he) hv wv tb L0 w

/-- THE PANEL OF MR: as panelP_N1. -/
theorem panelP_MR (P : PortFits ρ W v D c t low z zh) {q : ℕ}
    (hel : ElTie ρ v D z q (call Fam.MR)) (hE : EwTie ρ v D z Fam.MR)
    (p : PanelEnv) (hp : p.v = v) (ec : E)
    (s : Panels) (hv wv : ℕ → ℕ → K) (tb : Tables) (L0 : ℕ) (w : ℕ → LW K) {s' : Panels} {b : SBlk}
    (hs : panelT p ec (eqTab (v.zl q)) "MR" s = some s')
    (hb : s'.bl = s.bl.push b) (hr : Returns b) :
    shareP ρ W v.y hv wv b =
      ρ.val ec * shareL D (rPort ρ v.y p.shownT hv D t z zh) tb L0 w z zh Pan.MR := by
  subst hp
  rw [panelT_MR_eq, P.fits.p3] at hs
  obtain ⟨ew, hew, e⟩ := of_bind_some (o := p.v.ewOf "MR") hs
  rw [e, plain_push] at hb
  have eb := push_same hb
  subst eb
  exact shareP_MR P hel hE p.shownT ec hew s.nextV
    (fun i hi e he => hr.2 _ rfl i hi e he) hv wv tb L0 w

/-- THE PANEL GR OF LAYER 2 lm + 1. If the step of panelT for the segment G and that layer returns
(triStep), and b is the panel that it has appended, whose weight claim's vector holds the library's
B side, then the share of b is the call's weight times the library's share of the panel Gr lm at
the record rPort. -/
theorem panelP_Gr (P : PortFits ρ W v D c t low z zh) {q : ℕ}
    (hel : ElTie ρ v D z q (call Fam.G)) (p : PanelEnv) (hp : p.v = v) (ec : E) (s : Panels)
    (hv wv : ℕ → ℕ → K) (tb : Tables) (L0 : ℕ) (w : ℕ → LW K) {s' : Panels} {b : SBlk} {lm : ℕ}
    (hlm : lm < D.ne) (hs : triStep p ec (eqTab (v.zl q)) "G" s lm = some s')
    (hb : s'.bl = s.bl.push b)
    (hw : WvTri wv s.nextV b.ni b.wy ((Pan.Gr lm).nc D)
      ((Pan.Gr lm).B D (rPort ρ v.y p.shownT hv D t z zh) tb L0 w z zh)) :
    shareP ρ W v.y hv wv b =
      ρ.val ec * shareL D (rPort ρ v.y p.shownT hv D t z zh) tb L0 w z zh (Pan.Gr lm) := by
  subst hp
  obtain ⟨xx, hxx, e⟩ := of_bind_some
    (o := (Array.range p.v.y.h.d).mapM fun k2 => p.v.shIn (p.v.tensorAt "xr" "rt") lm k2) hs
  rw [e, tri_push] at hb
  have eb := push_same hb
  subst eb
  exact shareP_Gr P hel p.shownT ec hlm hxx s.nextV hv wv tb L0 w hw

/-- THE PANEL UR OF LAYER 2 lm + 1. If the step of panelT for the segment U and that layer returns
(triStep), and b is the panel that it has appended, whose weight claim's vector holds the library's
B side, then the share of b is the call's weight times the library's share of the panel Ur lm at
the record rPort. -/
theorem panelP_Ur (P : PortFits ρ W v D c t low z zh) {q : ℕ}
    (hel : ElTie ρ v D z q (call Fam.U)) (p : PanelEnv) (hp : p.v = v) (ec : E) (s : Panels)
    (hv wv : ℕ → ℕ → K) (tb : Tables) (L0 : ℕ) (w : ℕ → LW K) {s' : Panels} {b : SBlk} {lm : ℕ}
    (hlm : lm < D.ne) (hs : triStep p ec (eqTab (v.zl q)) "U" s lm = some s')
    (hb : s'.bl = s.bl.push b)
    (hw : WvTri wv s.nextV b.ni b.wy ((Pan.Ur lm).nc D)
      ((Pan.Ur lm).B D (rPort ρ v.y p.shownT hv D t z zh) tb L0 w z zh)) :
    shareP ρ W v.y hv wv b =
      ρ.val ec * shareL D (rPort ρ v.y p.shownT hv D t z zh) tb L0 w z zh (Pan.Ur lm) := by
  subst hp
  obtain ⟨xx, hxx, e⟩ := of_bind_some
    (o := (Array.range p.v.y.h.d).mapM fun k2 => p.v.shIn (p.v.tensorAt "xr" "rt") lm k2) hs
  rw [e, tri_push] at hb
  have eb := push_same hb
  subst eb
  exact shareP_Ur P hel p.shownT ec hlm hxx s.nextV hv wv tb L0 w hw

/-- THE PANEL DR OF LAYER 2 lm + 1. If the step of panelT for the segment D and that layer returns
(triStep), and b is the panel that it has appended, whose weight claim's vector holds the library's
B side, then the share of b is the call's weight times the library's share of the panel Dr lm at
the record rPort. -/
theorem panelP_Dr (P : PortFits ρ W v D c t low z zh) {q : ℕ}
    (hel : ElTie ρ v D z q (call Fam.D)) (p : PanelEnv) (hp : p.v = v) (ec : E) (s : Panels)
    (hv wv : ℕ → ℕ → K) (tb : Tables) (L0 : ℕ) (w : ℕ → LW K) {s' : Panels} {b : SBlk} {lm : ℕ}
    (hlm : lm < D.ne) (hs : triStep p ec (eqTab (v.zl q)) "D" s lm = some s')
    (hb : s'.bl = s.bl.push b)
    (hw : WvTri wv s.nextV b.ni b.wy ((Pan.Dr lm).nc D)
      ((Pan.Dr lm).B D (rPort ρ v.y p.shownT hv D t z zh) tb L0 w z zh)) :
    shareP ρ W v.y hv wv b =
      ρ.val ec * shareL D (rPort ρ v.y p.shownT hv D t z zh) tb L0 w z zh (Pan.Dr lm) := by
  subst hp
  have e : tri p.v.y ec 1 p.v.y.h.fe
      ((Array.range p.v.y.h.NE).map fun e => p.shownT.getD
        (p.v.y.NN * p.v.y.Lam + p.v.y.LamM + lm * p.v.y.h.NE + e) zeroE)
      #[] (some (1 + lm))
      (mulE ((eqTab (p.v.zl q)).getD (2 * lm + 1) zeroE)
        (kT p.v.sc (p.v.lay (2 * lm + 1)) Model.Layer.Lkd)) s = s' := Option.some.inj hs
  rw [← e, tri_push] at hb
  have eb := push_same hb
  subst eb
  exact shareP_Dr P hel p.shownT ec hlm s.nextV hv wv tb L0 w hw

end Whole

#print axioms shareP_N1
#print axioms shareP_N2
#print axioms shareP_XR
#print axioms shareP_DD
#print axioms shareP_MR
#print axioms shareP_Gr
#print axioms shareP_Ur
#print axioms shareP_Dr
#print axioms panelP_N1
#print axioms panelP_N2
#print axioms panelP_XR
#print axioms panelP_DD
#print axioms panelP_MR
#print axioms panelP_Gr
#print axioms panelP_Ur
#print axioms panelP_Dr

end OnBytes.Road
