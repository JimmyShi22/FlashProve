-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/MergeLaw/ItemsFront.lean: the merge's law in the three items, with one premise in
front fewer: the older test on the claim's sizes follows from the yes. Theorems with their proofs.

Main names:
  `shape_of_yes`: where the merge says yes, the claim in the record passes `wsClaimShape`: by
    `hear_tests` (Pinned.lean) and `claimFits_eq` (Fits.lean).
  `merge_table`: `merge_law_items` (Johnson/Top/H0/MergeLaw/AtItems.lean) with `ClaimsFit` taken
    apart: its clause on the sizes is paid by the yes; its clause "each named unit is in order"
    stands among the premises on public numbers; its clause "the claim is on the place's unit" stays
    in front.

What stays a premise: as AtItems.lean's head lists it, with that one change. The typed record is
`GS`
at `noRd`: what rides is set to nothing. The two numbers that `wsPending` takes are bound inside
`ItemsSay` by "for all" and tied to no plan.

Limits. It is no soundness of the protocol. Nothing on hiding.

-/
import Johnson.Top.H0.MergeLaw.AtItems
import Johnson.Top.H0.MergeLaw.Pinned
import Johnson.Top.H0.MergeLaw.Fits

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.MergeLaw
open Iop IOR Cb Cb.Pv.Lay Johnson.L5.Layers TWhole
open OnBytes (E zeroE)
open OnBytes.Flat OnBytes.Maker OnBytes.Slice
open OnBytes.Model (Reading wsClaimShape)
open VerifiableInference.Desc.Sound (Frame Piece below)
open Johnson.Desc.First.ForkMerge (HeadMergeP headMergeDecide headClaimMergeKind mergeEntries claimFits)
open K11Caller (MergeIn GS noRd entries ClaimsFit)
open _root_.Run (ckP)
open scoped ENNReal

/-- **Where the merge says yes, the claim in the record passes the older test on its sizes.** -/
theorem shape_of_yes {P : HeadMergeP} {s s' : S} {rs : List Fmt.RoundView} (h : headMergeDecide P s rs =
           .ok s')
    (a : HeadOwn) (claim : OnBytes.Model.WsClaim) (ha : s.here = .head a) (hcl : a.claim = some
        claim) :
    wsClaimShape P.lay claim = .ok () := by
  obtain ⟨a0, _, _, _, claim0, _, _, ha0, _, hcl0, _, _, _, hm, _⟩ := decide_inv h
  have e : a0 = a := by
    rw [ha] at ha0
    exact (Here.head.inj ha0).symm
  subst e
  have ec : claim0 = claim := by
    rw [hcl] at hcl0
    exact (Option.some.inj hcl0).symm
  subst ec
  have h3 : claimFits P.lay claim0 = true := by simpa using (hear_tests hm).2.2
  rw [claimFits_eq] at h3
  cases hs : wsClaimShape P.lay claim0 with
  | ok u => rfl
  | error e => rw [hs] at h3; exact absurd h3 (by simp [Except.isOk, Except.toBool])

variable {Pl : K11Caller.Place} (N : K11Caller.Nums Pl) {F : Frame} {W : Type}

/-- **THE MERGE's LAW AT A PIECE, IN THE THREE ITEMS, the test on the claim's sizes paid by the
yes.** -/
theorem merge_table (P : HeadMergeP) (hlay : Pl.lay = P.lay) (h1 : Pl.n = 1) (hk0 : 0 < Pl.lay.lk)
    (hnum : N.first + 1 + 2 * P.lay.lk + 2 = P.nMsg)
    (hunit : ∀ a u, Pl.lay.U[Pl.ui a]? = some u → OnBytes.Road.UnitOK Pl.lay.lk u) (L : List RDT)
    (he : L.map (·.entry) = mergeEntries P.lay.lk 1 P.work)
    (hkd : ∀ d ∈ L, Fmt.kindOf d.entry.name = some d.kind) :
    ∃ (dZ d0 : RDT) (ds : List RDT) (dY dV : RDT) (hk : ds.length = (GS Reading.gl N (noRd N)).k),
      L = dZ :: d0 :: (ds ++ [dY, dV]) ∧
      ∀ (base : ℕ) (ext : S × F.E.Str → Tr (uLT (ckP .two) (dZ :: d0 :: (ds ++ [dY, dV]))) → W → W)
        (rd : S × F.E.Str → MergeIn Pl.n) (cellOf : S × F.E.Str → ℕ → ℕ → GE)
        (maskOf idxOf : S × F.E.Str → ℕ → GE),
        (mergePiece F W P (GS Reading.gl N (noRd N)) dZ d0 ds dY dV hk base ext).ior.red.Leads
          (fun a => FrontReads N (rd a) a.1 ∧ (∀ b, a.1.here = .head b → OnBytes.PscRun.Sized b.F) ∧
            ∀ i, ((rd a).cl i).ui = Pl.ui i)
          (fun a a' => ItemsSay N (cellOf a) (maskOf a) (idxOf a) (rd a) a'.1)
          (mergePiece F W P (GS Reading.gl N (noRd N)) dZ d0 ds dY dV hk base ext).err ∧
        Err.Below (mergePiece F W P (GS Reading.gl N (noRd N)) dZ d0 ds dY dV hk base ext).err
          ((2 : ℝ≥0∞)⁻¹ ^ 128) := by
  obtain ⟨dZ, d0, ds, dY, dV, hk, hL, hall⟩ := merge_law (F := F) (W := W) N (noRd N) P hlay h1 hnum
      L he hkd
  refine ⟨dZ, d0, ds, dY, dV, hk, hL, fun base ext rd cellOf maskOf idxOf => ?_⟩
  obtain ⟨hleads, hbelow⟩ := hall base ext rd fun a => entries N (cellOf a) (maskOf a) (idxOf a)
  refine ⟨hleads.conseq (fun a h => ⟨h.1, h.2.1⟩) ?_, hbelow⟩
  intro a τ a' ha hout hq
  obtain ⟨_, _, _, gs, hdec⟩ := piece_yes (headClaimMergeKind P)
    (mergePiece F W P (GS Reading.gl N (noRd N)) dZ d0 ds dY dV hk base ext) rfl rfl a a' τ hout
  obtain ⟨b, _, claim, x0, _, _, _, _, _, _, _, _, _, e1, _, e3, e4, _⟩ := hq.1
  obtain ⟨_, fcl, _⟩ := ha.1 b claim x0 e1 e3 e4
  have hfit : ClaimsFit Pl (rd a) := ⟨ha.2.2, fun i => by
    rw [fcl i, hlay]
    exact shape_of_yes hdec b claim e1 e3, hunit⟩
  exact merge_items N P hlay h1 hk0 _ _ _ (rd a) (frontIs_of_yes N hnum ha.1 hdec) hq.1 ha.2.1 hfit

end VerifiableInference.Desc.First.MergeLaw

#print axioms VerifiableInference.Desc.First.MergeLaw.shape_of_yes
#print axioms VerifiableInference.Desc.First.MergeLaw.merge_table
