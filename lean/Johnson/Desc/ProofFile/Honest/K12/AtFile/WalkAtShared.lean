-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/WalkAtShared.lean: `WalkFacts` (K12/AtFile/SharedWalk.lean) at a shared
thread whose list is alike to the written one, whose table is `tableShared` and whose count is `sentIn` at the
written rounds: what a walk over the chain takes once for all members.

  `shared_length`   the written list has twelve members
  `depths_all`   `DepthsAt` at every border and run: `table_depths` (OSaid.lean), `declared_of_each`
  `walk_shared`  the statement

The premises. hplan: the description's test on its blocks. hstops: the prover's halves stop at no list. hLU, hLO:
the book lays the two tests' jobs. c2, c5: `covers_head`.

Limits. Public lists and tables' depths alone. Nothing on completeness, on soundness or on what is hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.OSaid
import Johnson.Desc.ProofFile.Honest.K12.AtFile.FitsShared
import Johnson.Desc.ProofFile.Honest.K12.AtFile.SharedWalk

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace ProofFile.Honest.K12.AtFile
open OnBytes (TableKey)
open VerifiableInference.Desc (Block Alike₂)
open VerifiableInference.Desc (K1.qAt)
open VerifiableInference.Desc.K12 (P12)
open Desc.K14 (St)
open ProofFile.Honest
open ProofFile.Honest.K14 (jobU jobOmega sendPlace treesU)
open ProofFile.Honest.K12
open ProofFile.Honest.K12.AtProof (fourOf)
open P2Law.ProofPlan (WP declProofFull)

/-- The written list has twelve members. -/
theorem shared_length : sharedR.length = 12 := by decide +kernel

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl}
  {pO : P12} {Bk : ProverCoinCounts} {Cl W₀ Rc X₀ P₁ Wt V Pb : Type}

/-- **`DepthsAt` at every border and every state of a run.** -/
theorem depths_all (h : P5J.AtMg o Z D r Zp Np cF) (hO : (fourOf Np).O = some pO)
    (T : Thread Bk St Cl V (Common W₀ Rc TableKey) X₀ Pb)
    (hl : List.Forall₂ Alike₂ WP.shared.blocksInOrder T.bs) (ht : T.taken = [])
    (wts : W₀ → Weights) (rnd : Rc → TableRand) (JU JO : TestJob (Common W₀ Rc TableKey) X₀) (own₀ : X₀)
    (htb : T.table = tableShared (K1.qAt Zp Np) wts rnd JU JO own₀)
    (hJU : JU.p = (fourOf Np).U) (hJO : JO.p = pO) (hfr : JO.fresh = none)
    (hLU : laysB Bk 1 JU = true) (hLO : laysB Bk 1 JO = true)
    (hu : treesU (K1.qAt Zp Np) = 1)
    (c2 : takesCover Bk ⟨sendPlace 2, 0⟩ (jobU ⟨K1.qAt Zp Np, 0⟩) = true)
    (c5 : takesCover Bk ⟨sendPlace 5, 0⟩ (jobOmega ⟨K1.qAt Zp Np, 0⟩) = true)
    (b : ℕ) (k : Coins Bk) (m : Mid (Common W₀ Rc TableKey) X₀) : DepthsAt T b k m := by
  refine depthsAt_of_declared
    (declared_of_each T hl depthShared depths_shared (by rw [ht]; exact opens_shared) b ?_) k m
  intro σ hσ k' w hd
  have hσ' : σ ∈ T.taken ++ (List.range (treesTo T.bs b)).map Fmt.TreeSource.own := hσ
  have hle : treesTo T.bs b ≤ 11 := by
    have e : sharedR = T.bs.map roundsTrees := rounds_alike hl
    rw [trees_rounds, ← e]
    have h1 := sum_take_le (·.2) sharedR b (b + 12) (by omega)
    have e2 : sharedR.take (b + 12) = sharedR :=
      List.take_of_length_le (by rw [shared_length]; omega)
    rw [e2, trees_shared] at h1
    exact h1
  rw [ht, List.nil_append] at hσ'
  obtain ⟨n, hn, rfl⟩ := List.mem_map.1 hσ'
  rw [htb]
  exact table_depths h hO wts rnd JU JO own₀ hJU hJO hfr hLU hLO hu c2 c5 n
    (lt_of_lt_of_le (List.mem_range.1 hn) hle) k' w hd

/-- **`WalkFacts` at a shared thread of the proof file.** -/
theorem walk_shared (h : P5J.AtMg o Z D r Zp Np cF) (hO : (fourOf Np).O = some pO)
    (L : ProofFile.Honest.SharedThread.Letters Bk St Cl W₀ Rc TableKey X₀ P₁ Wt) (hsp : L.split = true)
    (hl : List.Forall₂ Alike₂ WP.shared.blocksInOrder L.thread.bs)
    (hplan : ∀ x ∈ L.thread.bs, x.planOk = true ∧ x.shaped = true)
    (hstops : AtPublicFiles.Stops.NoStop L.thread.hs)
    (hfx : ∀ i, L.thread.fixed (.own i) = ProofFile.Honest.Small.sentIn declProofFull.2.1 i)
    (wts : W₀ → Weights) (rnd : Rc → TableRand) (JU JO : TestJob (Common W₀ Rc TableKey) X₀) (own₀ : X₀)
    (htb : L.thread.table = tableShared (K1.qAt Zp Np) wts rnd JU JO own₀)
    (hJU : JU.p = (fourOf Np).U) (hJO : JO.p = pO) (hfr : JO.fresh = none)
    (hLU : laysB Bk 1 JU = true) (hLO : laysB Bk 1 JO = true)
    (hu : treesU (K1.qAt Zp Np) = 1)
    (c2 : takesCover Bk ⟨sendPlace 2, 0⟩ (jobU ⟨K1.qAt Zp Np, 0⟩) = true)
    (c5 : takesCover Bk ⟨sendPlace 5, 0⟩ (jobOmega ⟨K1.qAt Zp Np, 0⟩) = true) :
    WalkFacts L.thread 12 where
  fits := fits_shared L hsp hl (fun b hb => (hplan b hb).2) hfx
  shaped := hplan
  stops := hstops
  opens := fun b _ => opensAvailable_shared _ hl rfl b
  depths := fun b _ => depths_all h hO L.thread hl rfl wts rnd JU JO own₀ htb hJU hJO hfr hLU hLO hu c2 c5 b

end ProofFile.Honest.K12.AtFile

end

#print axioms ProofFile.Honest.K12.AtFile.shared_length
#print axioms ProofFile.Honest.K12.AtFile.depths_all
#print axioms ProofFile.Honest.K12.AtFile.walk_shared
