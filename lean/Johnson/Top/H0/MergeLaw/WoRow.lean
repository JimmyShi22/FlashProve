-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/MergeLaw/WoRow.lean: the merge's law with the pending row read off the record: the
return of `wsPending` leaves the statement. Definitions, and theorems with their proofs.

In `merge_table_of` (Johnson/Top/H0/MergeLaw/FrontOf.lean) "what the merge left holds" is `WoSays`:
a
sentence on the return of `wsPending`, a routine of `verify-on-bytes`. The row that a link's end
lays
on the pile is another text's: `pendingRowO`; its reader off the record is `rowBy` | `rowAt`
(Johnson/Top/H0/Walk/FrameRow.lean). Here the two are tied, by `pend_inv`
(Johnson/Top/H0/MergeLaw/PendRow.lean).

Main names:
  `row_tie`: THE TIE, at any reader "left" of what a link's sub-proof has left, so at a layers' link
    too: where `rowBy left lay n lin s` gives a row r: something is left; `wsPending` returns on it;
    the
    index masks' ledger at s gives an entry c; and r is made of that return at c.
  `RowSays`: "a row on the committed matrix holds of the cells and of the index masks' entries",
  said
    plainly, of the row's own four fields. A stand-in for the notion that the pile's law will have.
  `woSays_of_row`: where the reader gives r at a record whose "left" is wo and whose ledger's next
    entry is N.c: `RowSays` of r gives `WoSays`.
  `ItemsRow`, `items_row`: `ItemsSay` with `WoSays` replaced so: see its docstring.
  `merge_table_row`: `merge_table_of` towards `ItemsRow`.

WHERE THE ROW IS READ. At ANY record sr with three properties, which are premises inside `ItemsRow`:
what is left there is still what the merge left; the reader gives a row there; the entry that the
ledger gives next there is N.c. The record in front of the link's end is meant. None of the three is
shown here. The first is owed of each block and run between the merge and the link's end. The third
is asked once, at sr, against N.c, a number of the place that is fixed before the game: it holds
there only if no block between has taken an entry beyond the plan's count; who shows it is open.

What stays a premise beside that: as FrontOf.lean's, ItemsFront.lean's and AtItems.lean's heads
list it, `WoSays` and "wsPending returns" apart. `MergedSays` still speaks of a ledger's world
(`Fork.worldOf`), and `shape_of_yes` of `wsClaimShape`: `verify-on-bytes`'s.

Limits. It is no soundness of the protocol. `RowSays` has been held against no other notion of
"a row holds". Nothing on hiding.

-/
import Johnson.Top.H0.MergeLaw.PendRow
import Johnson.Top.H0.MergeLaw.FrontOf
import Johnson.Top.H0.Walk.FrameRow

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.MergeLaw
open Iop IOR Cb Cb.Pv.Lay Johnson.L5.Layers TWhole
open OnBytes (E zeroE TensorRow)
open OnBytes.Flat OnBytes.Maker OnBytes.Slice
open OnBytes.Model (Reading Fork WsLay WsForkOut wsPending)
open OnBytes.PscRun (Later)
open OnBytes.Road.Rows (pendWeight)
open VerifiableInference.Desc (Claim)
open VerifiableInference.Desc.Sound (Frame Piece below)
open VerifiableInference.Desc.First.Pend (takeEntry)
open VerifiableInference.Desc.First.Close (leftHead)
open Johnson.Desc.First.ForkMerge (HeadMergeP headMergeClaim mergeEntries)
open Johnson.Desc.First.Walk.Law (leftOf rowBy hasRow rowBy_some leftOf_of_head ledgerAt)
open K11Caller (MergeIn GS noRd WeightsSays MergedSays WoSays cellsIn)
open _root_.Run (ckP)
open scoped ENNReal

/-- **THE TIE**, at any reader of what a link's sub-proof has left: the row that the reader gives is
made of the return of `wsPending`, at the entry that the index masks' ledger gives. -/
theorem row_tie {left : S → Option WsForkOut} {lay : WsLay} {n : ℕ} {lin : OnBytes.Params.LinShape}
    {s : S} {r : TensorRow} (h : rowBy left lay n lin s = some r) :
    ∃ w0 w l c l', left s = some w0 ∧ wsPending lay w0 n lin = .ok w ∧ ledgerAt s = some l ∧
      takeEntry l = some (c, l') ∧
      r = { g := w.g, psi := w.psi, masks := [(⟨s.out.indexMasks, c⟩, w.beta)],
            target := w.target } ∧
      w.psi = w0.rm.toList.reverse ∧ w.beta = w0.beta ∧ w.target = w0.fvp := by
  obtain ⟨w0, os, hl, hp⟩ := rowBy_some.1 h
  obtain ⟨w, l, c, l', a1, a2, a3, a4, _, a6, a7, a8⟩ := pend_inv hp
  exact ⟨w0, w, l, c, l', hl, a1, a2, a3, a4, a6, a7, a8⟩

/-- A row on the committed matrix holds of the cells and of the index masks' entries, said plainly:
the sum over the cube's rows of (the row's weights) * (the matrix's row read at the row's point),
and
each named mask entry times its factor, is the target. -/
def RowSays (lk kRow : ℕ) (cells : OnBytes.Road.Wm GE) (idx : ℕ → GE) (r : TensorRow) : Prop :=
  ∑ j ∈ Finset.range (2 ^ kRow),
      pendWeight Reading.gl r.g j * OnBytes.Road.rowAt Reading.gl lk r.psi.reverse.toArray cells j +
    (r.masks.map fun x => idx x.1.index * Reading.gl.val x.2).sum = Reading.gl.val r.target

variable {Pl : K11Caller.Place} (N : K11Caller.Nums Pl)

/-- **From the row that the reader gives to `WoSays`.** -/
theorem woSays_of_row {left : S → Option WsForkOut} {n : ℕ} {lin : OnBytes.Params.LinShape} {s : S}
    {r : TensorRow} {wo : WsForkOut} (cell : ℕ → ℕ → GE) (idx : ℕ → GE)
    (hr : rowBy left Pl.lay n lin s = some r) (hleft : left s = some wo)
    (hc : ∀ l c l', ledgerAt s = some l → takeEntry l = some (c, l') → N.c = c)
    (hrow : RowSays Pl.lay.lk lin.kRow (cellsIn Pl cell) idx r) :
    WoSays Reading.gl N wo n lin cell idx := by
  obtain ⟨w0, w, l, c, l', b1, b2, b3, b4, b5, b6, _, _⟩ := row_tie hr
  have e0 : w0 = wo := by
    rw [hleft] at b1
    exact (Option.some.inj b1).symm
  subst e0
  intro w' hw'
  have e1 : w' = w := by
    rw [b2] at hw'
    exact (Except.ok.inj hw').symm
  subst e1
  unfold RowSays at hrow
  rw [b5] at hrow
  rw [hc l c l' b3 b4]
  simpa [b6] using hrow

/-- **What the merge's yes says, with the pending row read off the record**: `ItemsSay`
(Johnson/Top/H0/MergeLaw/AtItems.lean) with `WoSays`, which speaks of the return of `wsPending`,
replaced: at every record sr at which what the link's sub-proof has left is still what the merge
left, at which the reader `rowAt` (Johnson/Top/H0/Walk/FrameRow.lean) gives a row r, and at which
the
entry that the index masks' ledger gives next is the number N.c: if the form that the merge's
sumcheck leaves is worth 0 (`MergedSays`) and r holds of the cells and that entry (`RowSays`), then
`WeightsSays`. -/
def ItemsRow (cell : ℕ → ℕ → GE) (mask idx : ℕ → GE) (st : MergeIn Pl.n) (s' : S) : Prop :=
  ∃ (a' : HeadOwn) (wo : WsForkOut), s'.here = .head a' ∧ a'.wo = some wo ∧ leftOf s' = some wo ∧
    ∀ (n : ℕ) (s₂ s₃ : S) (a₂ a₃ : HeadOwn) (cls : List Claim) (Fl : Fork) (entry : ℕ → ℕ → ℕ → GE),
      s₂.here = .head a₂ → a₂.wo = a'.wo → Later a'.F a₂.F → headMergeClaim n s₂ = .ok (cls, s₃) →
      s₃.here = .head a₃ → Later a₃.F Fl →
      cls = [{ form := wo.p.rowForm wo.fvp {} }] ∧
      ∀ (sr : S) (claims : ℕ) (lin : OnBytes.Params.LinShape) (r : TensorRow),
        leftOf sr = some wo → Johnson.Desc.First.Walk.Law.rowAt Pl.lay claims lin sr = some r →
        (∀ l c l', ledgerAt sr = some l → takeEntry l = some (c, l') → N.c = c) →
        MergedSays Reading.gl wo Fl mask entry →
        RowSays Pl.lay.lk lin.kRow (cellsIn Pl cell) idx r → WeightsSays Reading.gl N st cell mask

theorem items_row {cell : ℕ → ℕ → GE} {mask idx : ℕ → GE} {st : MergeIn Pl.n} {s' : S}
    (h : ItemsSay N cell mask idx st s') : ItemsRow N cell mask idx st s' := by
  obtain ⟨a', wo, e1, e2, hall⟩ := h
  have hl : leftOf s' = some wo := leftOf_of_head (by
    unfold leftHead
    rw [e1]
    exact e2)
  refine ⟨a', wo, e1, e2, hl, ?_⟩
  intro n s₂ s₃ a₂ a₃ cls Fl entry p1 p2 p3 p4 p5 p6
  obtain ⟨hcls, hin⟩ := hall n s₂ s₃ a₂ a₃ cls Fl entry p1 p2 p3 p4 p5 p6
  refine ⟨hcls, ?_⟩
  intro sr claims lin r hleft hr hc hm hrow
  obtain ⟨w0, w, _, _, _, b1, b2, _⟩ := row_tie (left := leftOf) hr
  have e0 : w0 = wo := by
    rw [hleft] at b1
    exact (Option.some.inj b1).symm
  subst e0
  exact hin claims lin w b2 hm (woSays_of_row N (left := leftOf) cell idx hr hleft hc hrow)

variable {F : Frame} {W : Type}

/-- **THE MERGE's LAW AT A PIECE, WITH THE PENDING ROW READ OFF THE RECORD.** -/
theorem merge_table_row (P : HeadMergeP) (hlay : Pl.lay = P.lay) (h1 : Pl.n = 1)
    (hk0 : 0 < Pl.lay.lk) (hnum : N.first + 1 + 2 * P.lay.lk + 2 = P.nMsg)
    (hunit : ∀ a u, Pl.lay.U[Pl.ui a]? = some u → OnBytes.Road.UnitOK Pl.lay.lk u) (L : List RDT)
    (he : L.map (·.entry) = mergeEntries P.lay.lk 1 P.work)
    (hkd : ∀ d ∈ L, Fmt.kindOf d.entry.name = some d.kind) :
    ∃ (dZ d0 : RDT) (ds : List RDT) (dY dV : RDT) (hk : ds.length = (GS Reading.gl N (noRd N)).k),
      L = dZ :: d0 :: (ds ++ [dY, dV]) ∧
      ∀ (base : ℕ) (ext : S × F.E.Str → Tr (uLT (ckP .two) (dZ :: d0 :: (ds ++ [dY, dV]))) → W → W)
        (cellOf : S × F.E.Str → ℕ → ℕ → GE) (maskOf idxOf : S × F.E.Str → ℕ → GE),
        (mergePiece F W P (GS Reading.gl N (noRd N)) dZ d0 ds dY dV hk base ext).ior.red.Leads
          (fun a => frontB N a.1 = true)
          (fun a a' => ItemsRow N (cellOf a) (maskOf a) (idxOf a) (frontIn Pl.n a.1) a'.1)
          (mergePiece F W P (GS Reading.gl N (noRd N)) dZ d0 ds dY dV hk base ext).err ∧
        Err.Below (mergePiece F W P (GS Reading.gl N (noRd N)) dZ d0 ds dY dV hk base ext).err
          ((2 : ℝ≥0∞)⁻¹ ^ 128) := by
  obtain ⟨dZ, d0, ds, dY, dV, hk, hL, hall⟩ :=
    merge_table_of (F := F) (W := W) N P hlay h1 hk0 hnum hunit L he hkd
  refine ⟨dZ, d0, ds, dY, dV, hk, hL, fun base ext cellOf maskOf idxOf => ?_⟩
  obtain ⟨hleads, hbelow⟩ := hall base ext cellOf maskOf idxOf
  exact ⟨hleads.conseq (fun _ h => h) fun _ _ _ _ _ hq => items_row N hq, hbelow⟩

end VerifiableInference.Desc.First.MergeLaw

#print axioms VerifiableInference.Desc.First.MergeLaw.merge_table_row
#print axioms VerifiableInference.Desc.First.MergeLaw.items_row
#print axioms VerifiableInference.Desc.First.MergeLaw.row_tie
#print axioms VerifiableInference.Desc.First.MergeLaw.woSays_of_row
