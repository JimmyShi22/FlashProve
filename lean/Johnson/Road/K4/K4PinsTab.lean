-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/K4PinsTab.lean: THE TWO READINGS OF THE MASK ROW AND OF THE CELLS
(Johnson/Road/K4/K4PinsMaskQ.lean, K4PinsCellQ.lean) ONCE MORE, AT THE READER THAT THE TABLE's ITEM
ON FORMS ITSELF USES: `seatTab cs arr ms w` (Johnson/Desc/Sound/BordersFill.lean: the witness's
table at a seat, UNCUT). The elder theorems speak at the pinned part's own tables, `(partOf … w).1`,
which are CUT to the members' ranges and are 0 off `pinSeats`: two functions: the table's authors'
`dataQ_congr` cannot be called between them. They agree where `dataQ` reads them under `MaskOne` and
`CellOne`: that is what is proved. By unfolding, and `partOf_in`. No draw, no count.

  `mask_rd`, `cell_rd`: under `MaskOne` | `CellOne`, AT ANY READER rd: `dataQ`'s mask entry | cell
    is rd at the member's seat, at the one row and place.
  `part_tab`: under `SitsIn`, inside a member's ranges: the pinned part's table at the member's seat
    is `seatTab` there.
  **`mask_tab`**, **`cell_tab`**, **`mats_tab`**: `dataQ` at `(partOf … w).1` and at `seatTab … w`
    have the same mask entry (inside the member's mask row), the same cell, and make the same
    matrices (`matsOfB`).
  **`mask_dataQ_tab`**, **`raw_dataQ_tab`**: the value's readers at the pinned part of a witness are
    `dataQ`'s at `seatTab … w`.

OBJECT: none of its own. USER: none yet; meant: the payer of the line forms of `K4Lines`. LETTERS:
those of K4PinsMaskQ.lean and K4PinsCellQ.lean; arr, ms, N, m, w.

Limits. K04_law IS NOT PROVED BY THIS. `SitsIn`, `MaskOne`, `CellOne` (at every symbol of tl's
sizes, for the matrices) STAY PREMISES. Outside what `dataQ` reads under them the two readers may
part: nothing is said there.
-/
import Johnson.Road.K4.K4PinsMaskQ
import Johnson.Road.K4.K4PinsCellQ

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace OnBytes.Road.K4
open Johnson.Pack
open OnBytes.Model (HTailF2)
open VerifiableInference.Desc (Wit)
open VerifiableInference.Desc.First (Numbers)
open VerifiableInference.Desc.First.Look (sigListCalls cellJ szOf)
open VerifiableInference.Desc.Sound (Mem MsgT InMsg dataQ tabQ seatTab)
open VerifiableInference.Desc.K9L (maskOracle cellOfBlock)
open Cb.Pv.Tail (cellValS)

variable {Cells : Type} (A : PinPlan Cells) (own : List (ℕ × ℕ))
  (a : VerifiableInference.Desc.K9.Part)

/-- Under `MaskOne`, at any reader: the mask entry is the reader at the member's seat. -/
theorem mask_rd (H : MaskOne A own a) (rd : ℕ × ℕ → Bool → ℕ → ℕ → Cb.Gl.E) (j : ℕ) :
    (dataQ own a rd).mask j = rd (A.seatT ⟨_, H.member⟩) true 0 j := by
  show (match maskOracle a.L.check.frame with
    | some o => tabQ own a.d.st a.d.book rd o .mask j
    | none => 0) = _
  rw [H.oracle]
  show tabQ own a.d.st a.d.book rd H.o .mask j = _
  unfold tabQ
  rw [H.seated, H.oneRow, Nat.pow_zero, Nat.mod_one, Nat.div_one]
  rfl

/-- Under `CellOne`, at any reader: the cell is the reader at the member's seat. -/
theorem cell_rd {T r c : ℕ} (H : CellOne A own a T r c)
    (rd : ℕ × ℕ → Bool → ℕ → ℕ → Cb.Gl.E) :
    (dataQ own a rd).cell H.bn.1 H.bn.2 r c =
      rd (A.seatT ⟨H.k, H.member⟩) false H.rp.1 H.rp.2 := by
  show (match OnBytes.reqArray a.L.check.rows.layout H.bn.1 H.bn.2 with
    | none => (0 : Cb.Gl.E)
    | some ar =>
      match a.L.check.frame.whereIs H.bn.1 ar.message with
      | none => (0 : Cb.Gl.E)
      | some o =>
        (ar.blocks.map fun b =>
          cellOfBlock b (a.d.st.rowBits o .main) (a.d.st.placeBits o .main)
            (tabQ own a.d.st a.d.book rd o .main) r c).sum) = _
  rw [H.layout, H.laid]
  show (match a.L.check.frame.whereIs H.bn.1 H.ar.message with
      | none => (0 : Cb.Gl.E)
      | some o =>
        (H.ar.blocks.map fun b =>
          cellOfBlock b (a.d.st.rowBits o .main) (a.d.st.placeBits o .main)
            (tabQ own a.d.st a.d.book rd o .main) r c).sum) = _
  rw [H.oracle]
  show (H.ar.blocks.map fun b =>
    cellOfBlock b (a.d.st.rowBits H.o .main) (a.d.st.placeBits H.o .main)
      (tabQ own a.d.st a.d.book rd H.o .main) r c).sum = _
  rw [H.blocks _ r c H.rp H.place]
  unfold tabQ
  rw [H.seated]
  show rd (A.seatT ⟨H.k, H.member⟩) false
    ((H.rp.1 + H.rp.2 * 2 ^ a.d.st.rowBits H.o .main) % 2 ^ a.d.st.rowBits H.o .main)
    ((H.rp.1 + H.rp.2 * 2 ^ a.d.st.rowBits H.o .main) / 2 ^ a.d.st.rowBits H.o .main) = _
  rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt H.rowBelow,
    Nat.add_mul_div_right _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt H.rowBelow, Nat.zero_add]

variable {Tok : Type} (arr : ℕ → ℕ → ℕ) (ms : List Mem) (N : Numbers) (m : ℕ)
  (hs : SitsIn (sigListCalls A.D A.rad A.link) A.seatT ms N m)
include hs

/-- Under `SitsIn`, inside a member's ranges, the pinned part's table is `seatTab`. -/
theorem part_tab (w : Wit Cells Tok MsgT) (i : Fin (sigListCalls A.D A.rad A.link).length)
    (mask : Bool) (row place : ℕ)
    (hin : InMsg A.D.codes ((sigListCalls A.D A.rad A.link).get i).1 mask row place) :
    (partOf A.D.codes arr ms N m w).1 (A.seatT i) mask row place =
      seatTab A.D.codes arr ms w (A.seatT i) mask row place := by
  obtain ⟨hx, u, hu, hsh⟩ := hs i
  rw [partOf_in A.D.codes arr ms N m w hx hu mask row place (by rw [hsh]; exact hin)]
  unfold seatTab
  rw [show (ms.find? fun y => decide (VerifiableInference.Desc.Sound.seatOf y = A.seatT i)) =
    some u from hu]

/-- **The mask entries are one.** -/
theorem mask_tab (H : MaskOne A own a) (w : Wit Cells Tok MsgT) (j : ℕ)
    (hj : j < (pMask A.D.codes ((sigListCalls A.D A.rad A.link).get ⟨_, H.member⟩).1).ell) :
    (dataQ own a (partOf A.D.codes arr ms N m w).1).mask j =
      (dataQ own a (seatTab A.D.codes arr ms w)).mask j := by
  rw [mask_rd A own a H, mask_rd A own a H]
  refine part_tab A arr ms N m hs w _ true 0 j ?_
  unfold InMsg
  rw [if_pos rfl]
  exact ⟨H.rows, hj⟩

/-- **The value's mask row at the pinned part of a witness is `dataQ`'s at `seatTab`.** -/
theorem mask_dataQ_tab (H : MaskOne A own a) (w : Wit Cells Tok MsgT) (j : ℕ)
    (hj : j < (pMask A.D.codes ((sigListCalls A.D A.rad A.link).get ⟨_, H.member⟩).1).ell) :
    A.mask (partOf A.D.codes arr ms N m w) j =
      (dataQ own a (seatTab A.D.codes arr ms w)).mask j :=
  (mask_dataQ A own a H _ j hj).trans (mask_tab A own a arr ms N m hs H w j hj)

/-- **The cells are one.** -/
theorem cell_tab {T r c : ℕ} (H : CellOne A own a T r c) (w : Wit Cells Tok MsgT) :
    (dataQ own a (partOf A.D.codes arr ms N m w).1).cell H.bn.1 H.bn.2 r c =
      (dataQ own a (seatTab A.D.codes arr ms w)).cell H.bn.1 H.bn.2 r c := by
  rw [cell_rd A own a H, cell_rd A own a H]
  refine part_tab A arr ms N m hs w _ false H.rp.1 H.rp.2 ?_
  unfold InMsg
  rw [if_neg (by decide)]
  exact ⟨H.rowIn, H.placeIn⟩

/-- **The matrices are one.** -/
theorem mats_tab (tl : HTailF2)
    (H : ∀ (μ : Fin (szOf tl).NM) (i : Fin (Alg.symRows ((szOf tl).m μ)))
      (c' : Fin ((szOf tl).k μ)), CellOne A own a (tl.gtTree.getD μ.val 0) i.val c'.val)
    (w : Wit Cells Tok MsgT) :
    matsOfB A tl (dataQ own a (partOf A.D.codes arr ms N m w).1) =
      matsOfB A tl (dataQ own a (seatTab A.D.codes arr ms w)) := by
  funext x r c
  have e : (fun (μ : Fin (szOf tl).NM) (i : Fin (Alg.symRows ((szOf tl).m μ)))
      (c' : Fin ((szOf tl).k μ)) => (dataQ own a (partOf A.D.codes arr ms N m w).1).cell
        (((A.D.arrayOf.getD A.link #[])[tl.gtTree.getD μ.val 0]?).getD (0, "")).1
        (((A.D.arrayOf.getD A.link #[])[tl.gtTree.getD μ.val 0]?).getD (0, "")).2 i.val c'.val) =
      fun μ i c' => (dataQ own a (seatTab A.D.codes arr ms w)).cell
        (((A.D.arrayOf.getD A.link #[])[tl.gtTree.getD μ.val 0]?).getD (0, "")).1
        (((A.D.arrayOf.getD A.link #[])[tl.gtTree.getD μ.val 0]?).getD (0, "")).2 i.val c'.val :=
    funext fun μ => funext fun i => funext fun c' => by
      rw [(H μ i c').named, Option.getD_some]
      exact cell_tab A own a arr ms N m hs (H μ i c') w
  unfold matsOfB
  rw [e]

/-- **The value's raw matrices at the pinned part of a witness are made of `dataQ`'s cells at
`seatTab`.** -/
theorem raw_dataQ_tab (tl : HTailF2)
    (H : ∀ (μ : Fin (szOf tl).NM) (i : Fin (Alg.symRows ((szOf tl).m μ)))
      (c' : Fin ((szOf tl).k μ)), CellOne A own a (tl.gtTree.getD μ.val 0) i.val c'.val)
    (w : Wit Cells Tok MsgT) :
    A.raw tl (partOf A.D.codes arr ms N m w) =
      matsOfB A tl (dataQ own a (seatTab A.D.codes arr ms w)) :=
  (raw_dataQ A tl own a H _).trans (mats_tab A own a arr ms N m hs tl H w)

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.mask_rd
#print axioms OnBytes.Road.K4.cell_rd
#print axioms OnBytes.Road.K4.part_tab
#print axioms OnBytes.Road.K4.mask_tab
#print axioms OnBytes.Road.K4.mask_dataQ_tab
#print axioms OnBytes.Road.K4.cell_tab
#print axioms OnBytes.Road.K4.mats_tab
#print axioms OnBytes.Road.K4.raw_dataQ_tab
