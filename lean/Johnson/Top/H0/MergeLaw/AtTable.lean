-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/MergeLaw/AtTable.lean: the merge's law in the form that the rule of composition
takes (`Piece.GoodIn`, Johnson/Desc/Sound/GoodIn.lean). Definitions, and theorems with their proofs.

What is said.
  `pinned_back`: the three pins (`Pinned`, Pin.lean: the cells; the mask row's member; the index
    masks' member) ride back past the merge's block.
  `RelFront`: the merge's relation in front: the three pins, and "weights" (`WeightsHere`,
    Here.lean) at the witness's own readings.
  `RelBehind`: behind: the three pins, "merged" and "wo".
  `merge_goodIn`: the merge's piece, at the extractor that leaves the witness as it is, has
    `GoodIn` from `frontW`'s yes to `BehindOk`, between `RelFront` and `RelBehind`; each error at
    most a share of 2⁻¹ ^ 128. It is `merge_table_hereW` at the library's decoders, with the pins.

It stands BESIDE `merge_head` (HeadLaw.lean [not in this library]): one law at two storeys: see
Here.lean's head.

Limits. The letters of Pin.lean's head stay letters: cs, G, arr, smp; rc and THE CELLS' DECODER decT
(a free function under hdec); xM, xI, posM, posI: which member and which place bears a slot or an
entry is said by no theorem here. The door at the table (`ownAtTable`,
Johnson/Desc/Sound/BordersQ.lean) is NOT called here: its four implications between these relations
and the table's own terms are not typed. No member. Nothing on hiding.

-/
import Johnson.Top.H0.MergeLaw.Here
import Johnson.Top.H0.MergeLaw.Pin
import Johnson.Desc.Sound.GoodIn

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.First.MergeLaw
open Iop IOR Cb Cb.Pv.Lay Johnson.L5.Layers TWhole
open OnBytes.Flat OnBytes.Maker OnBytes.Slice
open OnBytes.Model (Reading)
open VerifiableInference.Desc (FileDescription Wit Strs)
open VerifiableInference.Desc.Sound (Frame Piece Mem MsgT InMsg PinAt pinWOf rides Fenced SmpStays
  strsOf Sending out_behind)
open Johnson.Pack (sigOf)
open Johnson.Desc.First.ForkMerge (HeadMergeP mergeEntries)
open K11Caller (GS noRd)
open _root_.Run (ckP)
open scoped ENNReal

variable (cs : OnBytes.Codes) {Xi : Type} (G : FileDescription Xi) {Cells Tok : Type} (arr : ℕ → ℕ → ℕ)
  (smp : S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
  (rc : Cells → ℕ → ℕ → GE) (decT : (ℕ → Option (ℕ × List UInt64)) → S → Option Cells)
  {Pl : K11Caller.Place} (N : K11Caller.Nums Pl) {F : Frame} {W : Type}

/-- **The three pins ride back past the merge's block.** -/
theorem pinned_back (P : HeadMergeP) (Gw : WeightsL GE) {dZ d0 : RDT} {ds : List RDT} {dY dV : RDT}
    (hk : ds.length = Gw.k) (base : ℕ)
    (ext : S × F.E.Str → Tr (uLT (ckP .two) (dZ :: d0 :: (ds ++ [dY, dV]))) → W → W)
    (xM xI : Mem) (hF : Fenced base [xM, xI])
    (hsmp : ∀ (s : S) (a' : HeadOwn), smp { s with rowsOwed := none, here := .head a' } = smp s)
    (hdec : ∀ c (s : S) (a' : HeadOwn),
      decT c { s with rowsOwed := none, here := .head a' } = decT c s)
    (a b : S × F.E.Str) (τ : Tr (uLT (ckP .two) (dZ :: d0 :: (ds ++ [dY, dV]))))
    (hout : (mergePiece F W P Gw dZ d0 ds dY dV hk base ext).ior.red.out a τ = some b)
    (w : Wit Cells Tok MsgT) (hw : Pinned cs G arr smp decT xM xI b.1 (strsOf F b.2) w) :
    Pinned cs G arr smp decT xM xI a.1 (strsOf F a.2) w := by
  obtain ⟨pw, pm, pi⟩ := hw
  have hS : SmpStays cs smp (mergePiece F W P Gw dZ d0 ds dY dV hk base ext) [xM, xI] := by
    intro a τ b hout x _
    obtain ⟨a', e⟩ := piece_local P _ hk base ext a b τ hout
    rw [e, hsmp]
  have hT : decT (strsOf F b.2).cell b.1 = decT (strsOf F a.2).cell a.1 := by
    obtain ⟨a', e⟩ := piece_local P _ hk base ext a b τ hout
    rw [e, hdec, out_behind (mergePiece F W P Gw dZ d0 ds dY dV hk base ext) a b τ hout]
    rfl
  refine ⟨?_, ((rides cs G arr smp _ [xM, xI] hF hS a b τ hout xM (by simp)).1 w).1 pm,
    ((rides cs G arr smp _ [xM, xI] hF hS a b τ hout xI (by simp)).1 w).1 pi⟩
  unfold pinWOf at pw ⊢
  rw [← hT]
  exact pw

variable (claims : ℕ) (lin : OnBytes.Params.LinShape) (xM xI : Mem)
  (posM posI : ℕ → Bool × ℕ × ℕ)

/-- **The merge's relation in front of its block**: the three pins, and "weights", at the witness's
own readings. -/
def RelFront (a : S × F.E.Str) (w : Wit Cells Tok MsgT) : Prop :=
  Pinned cs G arr smp decT xM xI a.1 (strsOf F a.2) w ∧
    WeightsHere N (rc w.cells) (vecBy cs arr N.ns posM xM w) a.1

/-- **The merge's relation behind its block**: the three pins, "merged" and "wo", at the witness's
own readings. -/
def RelBehind (b : S × F.E.Str) (w : Wit Cells Tok MsgT) : Prop :=
  Pinned cs G arr smp decT xM xI b.1 (strsOf F b.2) w ∧
    MergedHere N (rc w.cells) (vecBy cs arr N.ns posM xM w) (vecBy cs arr N.ni posI xI w) b.1 ∧
    WoHere N claims lin (rc w.cells) (vecBy cs arr N.ni posI xI w) b.1

/-- **THE MERGE's LAW IN THE FORM THAT THE RULE OF COMPOSITION TAKES** (`Piece.GoodIn`), at the
extractor that leaves the witness as it is. -/
theorem merge_goodIn (P : HeadMergeP) (hlay : Pl.lay = P.lay) (h1 : Pl.n = 1)
    (hk0 : 0 < Pl.lay.lk) (hnum : N.first + 1 + 2 * P.lay.lk + 2 = P.nMsg)
    (hunit : ∀ a u, Pl.lay.U[Pl.ui a]? = some u → OnBytes.Road.UnitOK Pl.lay.lk u) (L : List RDT)
    (he : L.map (·.entry) = mergeEntries P.lay.lk 1 P.work)
    (hkd : ∀ d ∈ L, Fmt.kindOf d.entry.name = some d.kind)
    (hinM : ∀ j, j < N.ns → InMsg cs (xM.1.l.get xM.2).1 (posM j).1 (posM j).2.1 (posM j).2.2)
    (hinI : ∀ j, j < N.ni → InMsg cs (xI.1.l.get xI.2).1 (posI j).1 (posI j).2.1 (posI j).2.2)
    (hsmp : ∀ (s : S) (a' : HeadOwn), smp { s with rowsOwed := none, here := .head a' } = smp s)
    (hdec : ∀ c (s : S) (a' : HeadOwn),
      decT c { s with rowsOwed := none, here := .head a' } = decT c s) :
    ∃ (dZ d0 : RDT) (ds : List RDT) (dY dV : RDT) (hk : ds.length = (GS Reading.gl N (noRd N)).k),
      L = dZ :: d0 :: (ds ++ [dY, dV]) ∧
      ∀ (base : ℕ), Fenced base [xM, xI] →
        (mergePiece F (Wit Cells Tok MsgT) P (GS Reading.gl N (noRd N)) dZ d0 ds dY dV hk base
            fun _ _ w => w).GoodIn
          (fun a => frontW N a.1 = true) (fun b => BehindOk N b.1)
          (RelFront cs G arr smp rc decT N xM xI posM)
          (RelBehind cs G arr smp rc decT N claims lin xM xI posM posI) ∧
        Err.Below (mergePiece F (Wit Cells Tok MsgT) P (GS Reading.gl N (noRd N)) dZ d0 ds dY dV hk
            base fun _ _ w => w).err ((2 : ℝ≥0∞)⁻¹ ^ 128) := by
  obtain ⟨dZ, d0, ds, dY, dV, hk, hL, hall⟩ :=
    merge_table_hereW (F := F) (W := Wit Cells Tok MsgT) N P hlay h1 hk0 hnum hunit L he hkd claims
      lin
  refine ⟨dZ, d0, ds, dY, dV, hk, hL, fun base hF => ?_⟩
  obtain ⟨hleads, hbelow⟩ := hall base (fun _ _ w => w)
    (fun a => cellAt rc decT a.1 (strsOf F a.2))
    (fun a => vecAt cs G smp N.ns posM xM a.1 (strsOf F a.2))
    (fun a => vecAt cs G smp N.ni posI xI a.1 (strsOf F a.2))
  refine ⟨fun a ha => Doomed.mono _ _ ?_ (hleads a ha), hbelow⟩
  intro τ hτ b hb
  refine ⟨(hτ b hb).1, fun w hw => ?_⟩
  obtain ⟨hp, hm, hwo⟩ := hw
  have hpa := pinned_back cs G arr smp decT P _ hk base (fun _ _ w => w) xM xI hF hsmp hdec a b τ hb
    w hp
  have hq : HereSay N claims lin (cellAt rc decT a.1 (strsOf F a.2))
      (vecAt cs G smp N.ns posM xM a.1 (strsOf F a.2))
      (vecAt cs G smp N.ni posI xI a.1 (strsOf F a.2)) a.1 b.1 := (hτ b hb).2
  rw [← cell_of_pin rc decT a.1 (strsOf F a.2) w hpa.1,
    ← vec_of_pin cs G arr smp N.ns posM xM hinM a.1 (strsOf F a.2) w hpa.2.1,
    ← vec_of_pin cs G arr smp N.ni posI xI hinI a.1 (strsOf F a.2) w hpa.2.2] at hq
  exact ⟨hpa, hq hm hwo⟩

end VerifiableInference.Desc.First.MergeLaw

#print axioms VerifiableInference.Desc.First.MergeLaw.pinned_back
#print axioms VerifiableInference.Desc.First.MergeLaw.merge_goodIn
