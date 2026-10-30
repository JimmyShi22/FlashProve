-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
  Compile/Batch/MeanSeed.lean: three parts of two honest provers query no Fiat-Shamir oracle, if the
  seed's oracle (`σ.o` of a `SeedOracle`, Rom/SpecDerive.lean: an auxiliary oracle, used as a source
  of coins) is `OracleName.other` (Compile/Batch/Oracles.lean). The provers are those of `argP` (proving key
  (i, seed): Compile/Batch/StarS.lean) and of `argPL` (the lazy prover:
  Compile/Batch/SeedLazyDefs.lean); the three parts, all outside the chains of a batch (`chainTU`,
  Compile/Batch/ProverU.lean), are told under "The parts:" below (words of this library:
  lean/GLOSSARY.md).
    `notFb_seed`, `onlyQ_derived`, `onlyQ_levelsV`, `onlyQ_opL`
        no query goes to `fb t` (`OnlyQ`, `NotFb`: Compile/Batch/CompleteUnif.lean), if the seed's
        oracle is `other` (`onlyQ_derived`: for any program c with `NoFbS c`; the node's program has
        it by `nf_nodeP'`, Compile/Batch/NoFb.lean)
    `onlyQ_opensExtL`, `onlyQ_finishSlotL`, `onlyQ_slotL`, `onlyQ_finishAllL`
        the same for the proof strings, if the algorithm opL that makes an opening makes no such
        query (the lazy prover's: `onlyQ_opL`)
  The parts: the node of the sampled copy, derived again from the seed (here only the general lemma
  `onlyQ_derived`); the levels above the cached one; the openings, each made when it is needed (by
  `NoFbS`, Compile/Batch/NoFb.lean).
  Limits: nothing on a mean: this file does not prove a bound on the mean weight of the Fiat-Shamir
  queries of these provers. Nothing on the committers of these schemes.
-/
import Compile.Batch.NoFb
import Compile.Batch.SeedLazyDefs
import Compile.Batch.CompleteURef
import Compile.Batch.CompleteURefNoGhost
import Compile.Batch.CompleteUUnif
import Compile.Batch.NeedCostP

noncomputable section

open scoped ENNReal

namespace Compile.Batch
open Iop Rom Prob ZKCP


namespace MeanSeed
open Compile.Batch.Ref Compile.Batch.RefU Compile.Batch.Cmpl
  Compile.Batch.CmplU Compile.Batch.CompleteUnif
open Seed

variable {I X : Type} {lam : ℕ} {L : BatchProtocol I X}

/-! ## 1. What has no Fiat-Shamir query -/

section Fixed
variable (W : QueryLayout lam L) (WP : WireBP L) (p : Params) (bk : CoinPlan)
  (σ : SeedOracle (spec lam W.K L)) (hσ : σ.o = OracleName.other) (t : Tag)
include hσ

theorem notFb_seed (s : Fin (σ.sd + 1)) (j : ℕ) : NotFb t σ.o (σ.pt s j) := by
  show σ.o ≠ OracleName.fb t
  rw [hσ]
  exact fun e => OracleName.noConfusion e

/-- a program without a Fiat-Shamir query, erased, its coins derived from the seed -/
theorem onlyQ_derived {α : Type} {c : St lam W.K L α} (h : NoFbS c) (vs : List Bits)
    (s : Fin (σ.sd + 1)) (j : ℕ) :
    OnlyQ (S := spec lam W.K L) (NotFb t) (((erase c vs).blocks bk).derive σ s j) :=
  OnlyQ.derive σ s (notFb_seed W σ hσ t s) (OnlyQ.blocks bk (h.erase t vs)) j

omit hσ in
theorem onlyQ_levelsV (d : ℕ) (l : List (Dig lam)) :
    OnlyQ (S := spec lam W.K L) (NotFb t) (levelsM (hashTreeNode (K := W.K) (L := L)) d l) :=
  onlyQ_levelsM t (fun _ _ => onlyQ_askV t OracleName.node (fun e => OracleName.noConfusion e) _) d l

theorem onlyQ_opL (ℓ : ℕ) (k : I × Fin (σ.sd + 1)) (j : ℕ) (r : L.EncodingRandomness) (lvl : List (Dig lam))
    (hi : List (List (Dig lam))) (q : ℕ) :
    OnlyQ (S := spec lam W.K L) (NotFb t) (opL W WP p bk σ ℓ k j r lvl hi q) :=
  OnlyQ.bind (onlyQ_derived W bk σ hσ t (nf_leavesE p.sMT _) [] k.2 _) fun _ =>
    OnlyQ.bind (onlyQ_levelsV W t ℓ _) fun _ => trivial

end Fixed

section Strings
variable {K : ℕ} (t : Tag) {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E) {Wt : Type}
  (H : BatchHonestProver Q Wt) (wq : ProtocolQueryLayout lam K Q) (wp : WirePB Q H) (w : Wt)
  (opL : ℕ → TypedOracleComputation lam K L (Option (Bits × List (Dig lam))))
  (hO : ∀ q, OnlyQ (S := spec lam K L) (NotFb t) (opL q))

theorem nf_finishSlotG (ext : (E.Pos → Bool) → ExtF lam E) (c0 : H.Coin0) (a0 : Acc0) (j : ℕ)
    (x : Y) (cj : H.Coin) (acc : SlotAcc lam K (Y × H.Coin)) :
    NoFbS (finishSlotG (L := L) Q H wq wp w ext c0 a0 j x cj acc) := by
  unfold finishSlotG
  dsimp only
  split_ifs
  · trivial
  · exact fun vs => (nf_opensB _ _ _ _ _ _ _).bind fun f => trivial

include hO

theorem onlyQ_opensExtL (we : WireE E) (y : E.Str) (isRead : E.Pos → Bool) :
    ∀ ps, OnlyQ (S := spec lam K L) (NotFb t) (opensExtL we y opL isRead ps)
  | [] => trivial
  | q :: ps => OnlyQ.bind (onlyQ_opensExtL we y isRead ps) fun of => by
      cases of with
      | none => trivial
      | some f =>
        show OnlyQ (S := spec lam K L) (NotFb t) (if isRead q then _ else _)
        cases isRead q
        · trivial
        · exact OnlyQ.bind (hO _) fun _ => trivial

theorem onlyQ_finishSlotL (c0 : H.Coin0) (a0 : Acc0) (j : ℕ) (x : Y) (cj : H.Coin)
    (acc : SlotAcc lam K (Y × H.Coin)) (vs : List Bits) :
    OnlyQ (S := spec lam K L) (NotFb t) (finishSlotL Q H wq wp w opL c0 a0 j x cj acc vs) := by
  unfold finishSlotL
  dsimp only
  split_ifs
  · trivial
  · refine OnlyQ.bind (onlyQ_opensExtL t opL hO _ _ _ _) fun og => ?_
    cases og with
    | none => trivial
    | some gx =>
      exact OnlyQ.bind ((nf_finishSlotG Q H wq wp w _ c0 a0 j x cj acc).erase t vs) fun _ => trivial

theorem onlyQ_slotL (fl : ℕ → Bool) (c0 : H.Coin0) (a0 : Acc0) (j : ℕ)
    (acc : SlotAcc lam K (Y × H.Coin)) (vs : List Bits) :
    OnlyQ (S := spec lam K L) (NotFb t) (slotL Q H wq wp w opL fl c0 a0 j acc vs) := by
  unfold slotL
  cases acc.x with
  | none => trivial
  | some xc =>
    obtain ⟨x, cj⟩ := xc
    show OnlyQ (S := spec lam K L) (NotFb t) (if fl j then _ else _)
    cases fl j
    · trivial
    · exact onlyQ_finishSlotL t Q H wq wp w opL hO c0 a0 j x cj acc vs

theorem onlyQ_finishAllL (fl : ℕ → Bool) (c0 : H.Coin0) (a0 : Acc0) :
    ∀ (j : ℕ) (zs : List (SlotAcc lam K (Y × H.Coin))) (vs : List Bits),
      OnlyQ (S := spec lam K L) (NotFb t) (Seed.finishAllL Q H wq wp w opL fl c0 a0 j zs vs)
  | _, [], _ => trivial
  | j, acc :: zs, vs => OnlyQ.bind (onlyQ_slotL t Q H wq wp w opL hO fl c0 a0 j acc vs) fun o1 => by
      cases o1 with
      | none => trivial
      | some o => exact OnlyQ.bind (onlyQ_finishAllL fl c0 a0 (j + 1) zs o.2) fun _ => trivial

end Strings

end MeanSeed

open MeanSeed CompleteUnif Seed


end Compile.Batch
