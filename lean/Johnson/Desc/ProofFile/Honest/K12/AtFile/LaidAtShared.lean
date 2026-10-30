-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/LaidAtShared.lean: `lettersShared` with the kind's makers laid is
`LaidU` (FiveNine.lean): the thread at which `five_nine` holds is a thread of the proof file, with nothing left
but the half at the prover's list and the two letters that the test on G_omega shares.

  `fixed_zero`, `fixed_seed`   the count at own 0 and at own 3 to 6, by the kernel
  `front_at`     the first nine members are like the front block and the eight
  `keeps_nine`   what the field keeps says at member 9, at the kind's makers
  `laidU_head`   the statement

Limits.
- hf is at the prover H: `half_found` (HalfAtBase.lean) pays it at the base list.
- A laying, not a run: nothing on whether a stand is reached.
- Nothing on completeness, on soundness or on what is hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.FiveNine
import Johnson.Desc.ProofFile.Honest.K12.AtFile.TableLines
import Johnson.Desc.ProofFile.Honest.K14.OmegaAtShared
import Johnson.Desc.ProofFile.Honest.K14.AskedAtShared

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace ProofFile.Honest.K12.AtFile
open OnBytes (TableKey)
open OnBytes.Means (InOrder)
open VerifiableInference.Desc (Block Place)
open VerifiableInference.Desc (K1.qAt)
open VerifiableInference.Desc.Shared (MeaningS NumbersS)
open VerifiableInference.Desc.K12 (T12 proximityTestKind guardedProximityTestParts)
open Desc.K14 (St blocks frontBlock first)
open Desc.K14.Honest (Like flatOf_carried)
open ProofFile.Honest
open ProofFile.Honest.K14 (mgWords form2 WitLens holds2 witL get_witL kp2 shared_flat_at tailLike_shared)
open ProofFile.Honest.K12
open ProofFile.Honest.K12.Light
open ProofFile.Honest.SharedThread (lettersShared)
open ProofFile.Honest.K12.AtProof (fourOf placeU)
open H2K.Member (piUFull)
open P2Law.ProofPlan (declProofFull)

/-- The first tree goes out in round 1. -/
theorem fixed_zero : 1 ≤ ProofFile.Honest.Small.sentIn declProofFull.2.1 0 := by decide +kernel

/-- The test's four trees go out in the rounds that its own numbers name. -/
theorem fixed_seed : (List.range 4).all (fun τ =>
    ProofFile.Honest.Small.sentIn declProofFull.2.1 (3 + τ) == 8 + seedRound piUFull.nums.stages τ) = true := by
  decide +kernel

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl}

/-- **The first nine members are like the front block and the eight.** -/
theorem front_at {b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit}
    (hb : blocks (K1.qAt Zp Np) = some [b1, b2, b3, b4, b5, b6, b7, b8]) :
    List.Forall₂ Like ((P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder.take 9)
      [frontBlock Zp.p.chains, b1, b2, b3, b4, b5, b6, b7, b8] := by
  rw [shared_flat_at]
  obtain ⟨x0, x1, x2, x3, x4, x5, x6, x7, x8, tl, hxs, l0, l1, l2, l3, l4, l5, l6, l7, l8⟩ :=
    flatOf_carried (Cl := ProofFile.Cl) Zp.p.chains (K1.qAt Zp Np) b1 b2 b3 b4 b5 b6 b7 b8
      (VerifiableInference.Desc.K12.Seat.tests Np) VerifiableInference.Desc.K12.Seat.last hb
  have e := hxs
  show List.Forall₂ Like (List.take 9 _) _
  rw [e]
  exact .cons l0 (.cons l1 (.cons l2 (.cons l3 (.cons l4 (.cons l5 (.cons l6 (.cons l7
    (.cons l8 .nil))))))))

variable {W₀ Rc Tr X₀ X P₁ Wt : Type} {Bk : ProverCoinCounts}

/-- What the thread's field keeps says at member 9, at the kind's makers. -/
theorem keeps_nine (Kp₀ : Place → St → St → Prop) (Q : Desc.K14.P14) (sentU : Array OnBytes.OracleNotice)
    (s s' : St) :
    (∀ p, (VerifiableInference.Desc.Shared.sharedPlaces true)[9]? = some p → kp2 Q sentU Kp₀ p s s') ↔
      Kp₀ placeU s s' := by
  constructor
  · intro hk
    have e := hk placeU rfl
    unfold kp2 at e
    rwa [if_neg (by decide)] at e
  · intro hk p hp
    obtain rfl : p = placeU := (Option.some.inj hp).symm
    unfold kp2
    rwa [if_neg (by decide)]

/-- **The letters at the kind's makers are `LaidU`.** -/
theorem laidU_head (h : P5J.AtMg OnBytes.secondHashFunction Z D r Zp Np cF)
    (H : Prover W₀ Rc ProofFile.Inst TableKey Tr X₀ X) (N : NumbersS) (ℓ : WitLens Wt)
    (Mg₀ : Common W₀ Rc TableKey → MeaningS St P₁ Wt) (other : ℕ → St → Bool)
    (nothingLeft : St → Bool) (wts : W₀ → Weights) (rnd : Rc → TableRand)
    (rest : Coins Bk → Common W₀ Rc TableKey → List Fmt.Drawn → Wt)
    (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hb : blocks (K1.qAt Zp Np) = some [b1, b2, b3, b4, b5, b6, b7, b8])
    (JO : TestJob (Common W₀ Rc TableKey) X₀) (own₀ : X₀)
    (table : Fmt.TreeSource → Coins Bk → Common W₀ Rc TableKey → List Fmt.Drawn → Place × Table)
    (htb : table = tableShared (K1.qAt Zp Np) wts rnd
      (jobDoorU (X₀ := X₀) Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] H.storedWords wts rnd).toRun.toTest
      JO own₀)
    (fixed : Fmt.TreeSource → ℕ) (hfx : ∀ i, fixed (.own i) = ProofFile.Honest.Small.sentIn declProofFull.2.1 i) (n₁ n₂ : ℕ)
    (Vd : Common W₀ Rc TableKey → Prop) (Rd : ℕ → Common W₀ Rc TableKey → St → Prop)
    (Kp₀ : Place → St → St → Prop)
    (w : Common W₀ Rc TableKey) (nO : H2U.PlaceNums) (hO : Np.O = some nO)
    (hf : (H.shared.find? fun g => g.place == (fourOf Np).U.place) =
      some (proverSideOfProximityTest (jobDoorU (X₀ := X₀) Zp Np [b1, b2, b3, b4, b5, b6, b7, b8]
                         H.storedWords wts rnd).toRun.toTest)) :
    ∃ blk, LaidU Zp Np
      (lettersShared Zp Np cF H N (fun v => mgWords ℓ (K1.qAt Zp Np) N (Mg₀ v))
        (form2 (K1.qAt Zp Np) other) nothingLeft (fun s => OnBytes.Means.InOrder s.st)
        (witL ℓ (K1.qAt Zp Np) (sentOf (K1.qAt Zp Np).S) (holds2 (K1.qAt Zp Np) wts rnd) rest)
        table fixed n₁ n₂ Vd Rd (kp2 (K1.qAt Zp Np) (sentOf (K1.qAt Zp Np).S) Kp₀) w)
      ℓ Mg₀ other wts rnd (fun k v hd => ℓ.get (rest k v hd)) H.storedWords Zp.p.chains
      b1 b2 b3 b4 b5 b6 b7 b8 JO own₀ blk := by
  obtain ⟨x, hx, hl⟩ := (tailLike_shared Zp Np cF H N
    (fun v => mgWords ℓ (K1.qAt Zp Np) N (Mg₀ v)) (form2 (K1.qAt Zp Np) other) nothingLeft
    (fun s => OnBytes.Means.InOrder s.st)
    (witL ℓ (K1.qAt Zp Np) (sentOf (K1.qAt Zp Np).S) (holds2 (K1.qAt Zp Np) wts rnd) rest)
    table fixed n₁ n₂ Vd Rd (kp2 (K1.qAt Zp Np) (sentOf (K1.qAt Zp Np).S) Kp₀) w
    b1 b2 b3 b4 b5 b6 b7 b8 nO hO hb).nine
  refine ⟨x,
    { alike := ProofFile.Honest.K14.alike_shared_at_laid h.scope h.laid
      split := rfl
      meaning := rfl
      shape := rfl
      order := fun _ => Iff.rfl
      wit := fun k v hd => ProofFile.Honest.K14.get_witL ℓ _ _ _ rest k v hd
      first := fun _ => rfl
      stored := fun _ => rfl
      eight := hb
      front := front_at hb
      member := hx
      seat := seat_of_like hl
      half := hf
      table := htb
      fixed₀ := by
        show 1 ≤ fixed (.own 0)
        rw [hfx]
        exact fixed_zero
      fixedAt := fun τ hτ => ?_ }⟩
  have e := List.all_eq_true.1 fixed_seed τ (List.mem_range.2 (by omega))
  show fixed (.own (3 + τ)) = _
  rw [hfx]
  exact beq_iff_eq.1 e

end ProofFile.Honest.K12.AtFile

end

#print axioms ProofFile.Honest.K12.AtFile.fixed_zero
#print axioms ProofFile.Honest.K12.AtFile.fixed_seed
#print axioms ProofFile.Honest.K12.AtFile.front_at
#print axioms ProofFile.Honest.K12.AtFile.keeps_nine
#print axioms ProofFile.Honest.K12.AtFile.laidU_head
