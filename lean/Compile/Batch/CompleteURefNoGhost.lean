-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/CompleteURefNoGhost.lean: the algorithms without tokens for the prover with free empty
slots (Compile/Batch/CompleteURefDefs.lean) never query the ghost names `fbw` (words of this
library: lean/GLOSSARY.md). A token is a position in a store (Compile/Batch/CompleteRefDefs.lean); a
ghost name `fbw t k` is an oracle of the analysis, which no algorithm of the scheme ever queries
(`OracleName`, Compile/Batch/Oracles.lean). Towards completeness of the compiled scheme.

So under `realF f` they run as under f (`runEager_realF_of_noGhost`,
Compile/Batch/CompleteRefNoGhost.lean), which is how a distribution proved for the programs with
tokens under `realF f` comes back to the scheme's f.

    ng_optO, ng_rleavesOU, ng_reqRootOU, ng_chainOU, ng_proveOU, ng_batOU, noGhost_RBU
-/
import Compile.Batch.CompleteRefNoGhost
import Compile.Batch.CompleteURefDefs

noncomputable section

namespace Compile.Batch
open Iop Rom Ref RefU

variable {I X : Type} {lam K : ℕ} {L : BatchProtocol I X}

theorem ng_optO {σ τ : Type} {g : σ → TypedOracleComputation lam K L τ} (hg : ∀ a, NoGhost (g a)) :
    ∀ o : Option σ, NoGhost (optO g o)
  | none => trivial
  | some a => (hg a).bind fun _ => trivial

theorem ng_rleavesOU :
    ∀ cs : List (Option Bits), NoGhost (rleavesOU (lam := lam) (K := K) (L := L) cs)
  | [] => trivial
  | some _ :: cs => (ng_rleaf _).bind fun _ => (ng_rleavesOU cs).bind fun _ => trivial
  | none :: cs => (ng_freshO _).bind fun _ => (ng_rleavesOU cs).bind fun _ => trivial

theorem ng_reqRootOU (dR : ℕ) (cs : List (Option Bits)) :
    NoGhost (reqRootOU (lam := lam) (K := K) (L := L) dR cs) :=
  (ng_rleavesOU cs).bind fun _ => (ng_levelsM (fun _ _ => ng_rnode _) _ _).bind fun _ => trivial

section Rounds
variable (sMT : ℕ) (t : Tag) (cms : List (Dig lam)) (dR : ℕ)

theorem ng_chainOU :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A) (embS : (p : OPos s) → OSym s p → Body L)
        (embP : PlainPart s A → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ) (ph : PhO) (σ0 : SStrat s A)
        (vs : List (Option (VSlot lam K X s))),
      NoGhost (chainOU sMT t cms dR s A W embS embP i ph σ0 vs)
  | [], _, _, _, _, _, _, _, _ => trivial
  | r :: s, (a, A), (w, W), embS, embP, i, ph, (m0, k0), vs => by
      simp only [chainOU]
      split
      · exact (ng_eachO (ng_optO (ng_slotLoO sMT t cms a w _ _ i _)) vs).bind fun _ =>
          ng_chainOU s A W _ _ _ _ _ _
      · exact (ng_eachO (ng_optO (ng_slotJoinO sMT t a w _ _ i)) vs).bind fun _ =>
          (ng_reqRootOU _ _).bind fun _ =>
            (ng_root0O sMT a w _ _).bind fun _ =>
              (ng_askG _ _ _ _ _).bind fun _ => ng_chainOU s A W _ _ _ _ _ _
      · exact (ng_root0O sMT a w _ _).bind fun _ =>
          (ng_askG _ _ _ _ _).bind fun _ => ng_chainOU s A W _ _ _ _ _ _
      · exact ng_chainOU s A W _ _ _ _ _ _

end Rounds

section Prove
variable (sMT sFS : ℕ) (t : Tag) {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E) {Wt : Type}
  (H : BatchHonestProver Q Wt) (wq : ProtocolQueryLayout lam K Q) (wp : WirePB Q H)
  (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L)
  (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X) (depthReq : ℕ)
  (cms : List (Dig lam)) (w : Wt)

theorem ng_proveOU (xs : List (Option Y)) :
    NoGhost (proveOU sMT sFS t Q H wq wp embS embP xin depthReq cms w xs) :=
  (ng_drawO _).bind fun c0 =>
    (ng_eachO (ng_optO fun x => ng_initO sFS Q H wp xin w c0 (some x)) xs).bind fun _ =>
      ng_chainOU sMT t cms depthReq _ _ _ _ _ _ _ _ _

end Prove

section Scheme
variable {lam : ℕ} {L : BatchProtocol I X} (W : QueryLayout lam L) (WP : WireBP L) (p : Params) (i : I)

theorem ng_batOU (xs : List X) (a : Fin L.maxBatchSize) (x : X) (nd : L.EncodingRandomness × Dig lam) :
    NoGhost (batOU W WP p i xs a x nd) :=
  (ng_drawO _).bind fun _ => (ng_proveOU _ _ _ _ _ _ _ _ _ _ _ _ _ _).bind fun _ => trivial

/-- The small experiment of the prover with free empty slots never queries a ghost name. -/
theorem noGhost_RBU (xs : List X) (a : Fin L.maxBatchSize) (x : X) : NoGhost (RBU W WP p i xs a x) :=
  (ng_nodeO W WP p i).bind (ng_batOU W WP p i xs a x)

end Scheme

end Compile.Batch
