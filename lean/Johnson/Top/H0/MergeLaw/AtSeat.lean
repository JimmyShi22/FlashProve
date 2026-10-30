-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/MergeLaw/AtSeat.lean: the merge's law under guards: at every block that narrows the
merge's. Theorems with their proofs.

Why. A written description does not lay the kind's block `headClaimMergeKind P` itself: it lays it under
guards (no mark behind; the heard reply as it was), and the rule for a file holds the strict reading
of that guarded block. Each such block has the kind's rounds and says yes only where the kind's
block does, with the same record (`Block.Narrows`, Johnson/Desc/Sound/MergeNarrow.lean). What a
kind's authors owe where a description lays their block is asked over every such block.

Main names:
  `below_mono`: narrowing passes the strict reading `below`.
  `seat_yes`: at a piece that holds `below B'`, B' a block that narrows `headClaimMergeKind P`: where the
    piece puts out, the merge's own decision has said yes with that record.
  `seat_mark`: so the mark behind is the mark in front.
  `merge_goodIn_seat`: `merge_goodIn` (AtTable.lean) at the merge's piece with `below B'` in the
    place of its block: the same rounds, errors, conditions and relations. By `out_narrow`.
  `merge_goodIn_cap`: the same at ANY list of written rounds that has the block's own entries, with
    the cap as the piece's errors (`Err.cap 128`, Iop/ErrCap.lean: at each round the number of the
    round's challenges / 2 ^ 128): the merge's own errors are no larger.

Limits. That a description's piece at the merge's place has written rounds with the block's own
entries, no round shown behind, and the cap as its errors is not said here. The rest as
AtTable.lean's head says. Nothing on hiding.

-/
import Johnson.Top.H0.MergeLaw.AtTable
import Johnson.Desc.Sound.MergeNarrow
import Iop.ErrCap

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.First.MergeLaw
open Iop IOR Cb Cb.Pv.Lay Johnson.L5.Layers TWhole
open OnBytes.Flat OnBytes.Maker OnBytes.Slice
open OnBytes.Model (Reading)
open VerifiableInference.Desc (FileDescription Wit Strs Block Claim)
open VerifiableInference.Desc.Sound (Frame Piece Mem MsgT InMsg Fenced strsOf Sending below
  out_narrow out_yes below_narrows)
open Johnson.Pack (sigOf)
open Johnson.Desc.First.ForkMerge (HeadMergeP mergeEntries headClaimMergeKind headMergeDecide)
open K11Caller (GS noRd)
open _root_.Run (ckP)
open _root_.Run.PQ (CK)
open scoped ENNReal

/-- Narrowing passes the strict reading. -/
theorem below_mono {T Cl : Type} {b' b : Block T Cl} (h : b'.Narrows b) :
    (below b').Narrows (below b) := by
  refine ⟨h.1, fun s rs gs s' e => ?_⟩
  have e' : (if viewWordsBelowPrime ⟨rs, (gs.flatMap id).map fun c => (0, c.1, c.2)⟩ then b'.decide s rs gs
      else .error "a word is not below the prime") = .ok s' := e
  show (if viewWordsBelowPrime ⟨rs, (gs.flatMap id).map fun c => (0, c.1, c.2)⟩ then b.decide s rs gs
      else .error "a word is not below the prime") = .ok s'
  split at e'
  · rename_i hv
    rw [if_pos hv]
    exact h.2 _ _ _ _ e'
  · cases e'

/-- **At a piece that holds the strict reading of a block that narrows the merge's: where it puts
out, the merge's own decision has said yes with that record.** -/
theorem seat_yes {C : CK} {F : Frame} {W : Type} (P : HeadMergeP) (p : Piece C F S Claim W)
    (B' : Block S Claim) (hB : B'.Narrows (headClaimMergeKind P)) (hp : p.b = below B')
    (a b : S × F.E.Str) (τ : Iop.Tr (uLT C p.ds)) (h : p.ior.red.out a τ = some b) :
    ∃ rs, headMergeDecide P a.1 rs = .ok b.1 := by
  obtain ⟨rs, gs, hd⟩ := out_yes p a b τ h
  rw [hp] at hd
  exact ⟨rs, hB.2 _ _ _ _ ((below_narrows B').2 _ _ _ _ hd)⟩

/-- **A mark stays there**; so does "no mark". -/
theorem seat_mark {C : CK} {F : Frame} {W : Type} (P : HeadMergeP) (p : Piece C F S Claim W)
    (B' : Block S Claim) (hB : B'.Narrows (headClaimMergeKind P)) (hp : p.b = below B')
    (a b : S × F.E.Str) (τ : Iop.Tr (uLT C p.ds)) (h : p.ior.red.out a τ = some b) :
    b.1.failed = a.1.failed := by
  obtain ⟨rs, hd⟩ := seat_yes P p B' hB hp a b τ h
  exact (leavesSeven P a.1 rs [] b.1 hd).2.2.2.1

variable (cs : OnBytes.Codes) {Xi : Type} (G : FileDescription Xi) {Cells Tok : Type} (arr : ℕ → ℕ → ℕ)
  (smp : S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
  (rc : Cells → ℕ → ℕ → GE) (decT : (ℕ → Option (ℕ × List UInt64)) → S → Option Cells)
  {Pl : K11Caller.Place} (N : K11Caller.Nums Pl) {F : Frame}
  (claims : ℕ) (lin : OnBytes.Params.LinShape) (xM xI : Mem) (posM posI : ℕ → Bool × ℕ × ℕ)

/-- **THE MERGE's LAW UNDER GUARDS**: `merge_goodIn` at the piece that holds, in the place of the
merge's block, the strict reading of ANY block that narrows it. -/
theorem merge_goodIn_seat (P : HeadMergeP) (hlay : Pl.lay = P.lay) (h1 : Pl.n = 1)
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
      ∀ (base : ℕ), Fenced base [xM, xI] → ∀ B' : Block S Claim, B'.Narrows (headClaimMergeKind P) →
        ({ mergePiece F (Wit Cells Tok MsgT) P (GS Reading.gl N (noRd N)) dZ d0 ds dY dV hk base
            (fun _ _ w => w) with b := below B' } :
          Piece (ckP .two) F S Claim (Wit Cells Tok MsgT)).GoodIn
          (fun a => frontW N a.1 = true) (fun b => BehindOk N b.1)
          (RelFront cs G arr smp rc decT N xM xI posM)
          (RelBehind cs G arr smp rc decT N claims lin xM xI posM posI) := by
  obtain ⟨dZ, d0, ds, dY, dV, hk, hL, hall⟩ :=
    merge_goodIn (F := F) cs G arr smp rc decT N claims lin xM xI posM posI P hlay h1 hk0 hnum hunit
      L he hkd hinM hinI hsmp hdec
  refine ⟨dZ, d0, ds, dY, dV, hk, hL, fun base hF B' hB a ha => ?_⟩
  refine Doomed.mono _ _ ?_ ((hall base hF).1 a ha)
  intro τ hτ b hb
  exact hτ b (out_narrow (mergePiece F (Wit Cells Tok MsgT) P (GS Reading.gl N (noRd N)) dZ d0 ds dY
      dV
    hk base fun _ _ w => w) (below B') (below_mono hB) a b τ hb)

/-- **THE SAME AT THE CAP**: at any list L of written rounds that has the block's own entries, at
the piece that holds `below B'`, no round behind, the extractor that leaves the witness, and AS ITS
ERRORS THE CAP: at each round the number of the round's challenges / 2 ^ 128. -/
theorem merge_goodIn_cap (P : HeadMergeP) (hlay : Pl.lay = P.lay) (h1 : Pl.n = 1)
    (hk0 : 0 < Pl.lay.lk) (hnum : N.first + 1 + 2 * P.lay.lk + 2 = P.nMsg)
    (hunit : ∀ a u, Pl.lay.U[Pl.ui a]? = some u → OnBytes.Road.UnitOK Pl.lay.lk u) (L : List RDT)
    (he : L.map (·.entry) = mergeEntries P.lay.lk 1 P.work)
    (hkd : ∀ d ∈ L, Fmt.kindOf d.entry.name = some d.kind)
    (hinM : ∀ j, j < N.ns → InMsg cs (xM.1.l.get xM.2).1 (posM j).1 (posM j).2.1 (posM j).2.2)
    (hinI : ∀ j, j < N.ni → InMsg cs (xI.1.l.get xI.2).1 (posI j).1 (posI j).2.1 (posI j).2.2)
    (hsmp : ∀ (s : S) (a' : HeadOwn), smp { s with rowsOwed := none, here := .head a' } = smp s)
    (hdec : ∀ c (s : S) (a' : HeadOwn),
      decT c { s with rowsOwed := none, here := .head a' } = decT c s)
    (base : ℕ) (hF : Fenced base [xM, xI]) (B' : Block S Claim)
    (hB : B'.Narrows (headClaimMergeKind P)) :
    (⟨below B', base, L, [], fun _ _ w => w, Err.cap 128 (uLT (ckP .two) L)⟩ :
      Piece (ckP .two) F S Claim (Wit Cells Tok MsgT)).GoodIn
      (fun a => frontW N a.1 = true) (fun b => BehindOk N b.1)
      (RelFront cs G arr smp rc decT N xM xI posM)
      (RelBehind cs G arr smp rc decT N claims lin xM xI posM posI) := by
  obtain ⟨dZ, d0, ds, dY, dV, hk, hL, hall⟩ :=
    merge_goodIn (F := F) cs G arr smp rc decT N claims lin xM xI posM posI P hlay h1 hk0 hnum hunit
      L he hkd hinM hinI hsmp hdec
  subst hL
  intro a ha
  refine Doomed.mono_err _ (Err.le_cap_of_below_inv 128 _ (hall base hF).2) ?_
  refine Doomed.mono _ _ ?_ ((hall base hF).1 a ha)
  intro τ hτ b hb
  exact hτ b (out_narrow (mergePiece F (Wit Cells Tok MsgT) P (GS Reading.gl N (noRd N)) dZ d0 ds dY
    dV hk base fun _ _ w => w) (below B') (below_mono hB) a b τ hb)

end VerifiableInference.Desc.First.MergeLaw

#print axioms VerifiableInference.Desc.First.MergeLaw.merge_goodIn_cap
#print axioms VerifiableInference.Desc.First.MergeLaw.below_mono
#print axioms VerifiableInference.Desc.First.MergeLaw.seat_mark
#print axioms VerifiableInference.Desc.First.MergeLaw.merge_goodIn_seat
