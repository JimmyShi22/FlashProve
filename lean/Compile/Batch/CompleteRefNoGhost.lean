-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/CompleteRefNoGhost.lean: the small experiments never query the ghost names `fbw`
(Compile/Batch/Oracles.lean). A ghost name `fbw t k` is an oracle of the analysis, which no
algorithm of the scheme ever queries. In a round with proof-of-work bits (Iop/BatchWire.lean: GrW)
the honest prover queries fb t once for each nonce that it uses; its program in the language of
Rom/Defer.lean writes attempt number k + 1 as a query to fbw t k, at the same input; the scheme is
that program with fb t written back for fbw t k (`realQ`). Towards completeness of the compiled
scheme whose rounds may have proof-of-work bits.

The algorithms without tokens of Compile/Batch/CompleteRefDefs.lean make no query to the ghost
names: for every wire record, with proof-of-work bits or without, well-formed or not (words of this
library: lean/GLOSSARY.md).

  `ng_freshO` .. `ng_linkO`  The same for each of their parts (`ng_eachO`, `ng_pairUp`,
                             `ng_levelsM`: if the algorithm that is passed in makes none).
  `noGhost_RT`, `noGhost_RL`  `NoGhost` (Compile/Batch/GhostGuards.lean) of the two small
                              experiments `RT` and `RL`
  `runEager_realF_of_noGhost`  so, for fixed oracle functions, it is the same to run them under f or
                               under `realF f` ("f with fb t in the place of fbw t k":
                               Compile/Batch/SpecLoop.lean)
-/
import Compile.Batch.GhostGuards
import Compile.Batch.CompleteRefDefs
import Compile.Batch.LoopEager

noncomputable section

namespace Compile.Batch
open Iop Rom Ref

variable {I X : Type} {lam K : ℕ} {L : BatchProtocol I X}

theorem ng_opure {α : Type} (a : α) : NoGhost (OComp.pure a : TypedOracleComputation lam K L α) := trivial
theorem ng_leaf (q : LeafIn L) : NoGhost (askTypedOracle (lam := lam) (L := L) (K := K) OracleName.leaf q) := fun _ =>
  trivial
theorem ng_node (q : Bits × Bits) : NoGhost (askTypedOracle (lam := lam) (L := L) (K := K) OracleName.node q) :=
  fun _ => trivial
theorem ng_rleaf (q : Bits) : NoGhost (askTypedOracle (lam := lam) (L := L) (K := K) OracleName.rleaf q) := fun _ =>
  trivial
theorem ng_rnode (q : Bits × Bits) : NoGhost (askTypedOracle (lam := lam) (L := L) (K := K) OracleName.rnode q) :=
  fun _ => trivial

theorem ng_freshO (l : ℕ) : NoGhost (freshO (lam := lam) (K := K) (L := L) l) := fun _ => trivial
theorem ng_drawO {β : Type} (e : Enum β) : NoGhost (drawO (lam := lam) (K := K) (L := L) e) :=
  fun _ => trivial

theorem ng_eachO {σ τ : Type} {g : σ → TypedOracleComputation lam K L τ} (hg : ∀ a, NoGhost (g a)) :
    ∀ l : List σ, NoGhost (eachO g l)
  | [] => trivial
  | a :: l => (hg a).bind fun _ => (ng_eachO hg l).bind fun _ => trivial

theorem ng_pairUp {hN : Dig lam → Dig lam → TypedOracleComputation lam K L (Dig lam)} (h : ∀ a b, NoGhost (hN a b)) :
    ∀ l : List (Dig lam), NoGhost (pairUp hN l)
  | [] => trivial
  | [_] => trivial
  | a :: b :: l => (h a b).bind fun _ => (ng_pairUp h l).bind fun _ => trivial

theorem ng_levelsM {hN : Dig lam → Dig lam → TypedOracleComputation lam K L (Dig lam)} (h : ∀ a b, NoGhost (hN a b)) :
    ∀ (d : ℕ) (l : List (Dig lam)), NoGhost (levelsM hN d l)
  | 0, _ => trivial
  | d + 1, l => (ng_pairUp h l).bind fun u => (ng_levelsM h d u).bind fun _ => trivial

theorem ng_leafO (sMT : ℕ) (b : Body L) : NoGhost (leafO (lam := lam) (K := K) sMT b) :=
  (ng_freshO _).bind fun _ => ng_leaf _

theorem ng_rootO (sMT d : ℕ) (leaf : ℕ → Body L) :
    NoGhost (rootO (lam := lam) (K := K) sMT d leaf) :=
  (ng_eachO (ng_leafO sMT) _).bind fun _ =>
    (ng_levelsM (fun _ _ => ng_node _) _ _).bind fun _ => trivial

theorem ng_rootOO (sMT : ℕ) (has : Bool) (d : ℕ) (leaf : ℕ → Body L) :
    NoGhost (rootOO (lam := lam) (K := K) sMT has d leaf) := by
  cases has
  · trivial
  · exact (ng_rootO sMT d leaf).bind fun _ => trivial

theorem ng_rootsOO (sMT : ℕ) :
    ∀ (ds : List ℕ) (leaf : ℕ → ℕ → Body L),
      NoGhost (rootsOO (lam := lam) (K := K) sMT ds leaf)
  | [], _ => trivial
  | d :: ds, leaf =>
    (ng_rootO sMT d (leaf 0)).bind fun _ =>
      (ng_rootsOO sMT ds fun n => leaf (n + 1)).bind fun _ => trivial

theorem ng_leafEO (sMT : ℕ) (x : Body L × Bool) : NoGhost (leafEO (lam := lam) (K := K) sMT x) := by
  unfold leafEO
  split
  · exact ng_leafO _ _
  · exact ng_leaf _

theorem ng_rootEO (sMT d : ℕ) (leaf : ℕ → Body L × Bool) :
    NoGhost (rootEO (lam := lam) (K := K) sMT d leaf) :=
  (ng_eachO (ng_leafEO sMT) _).bind fun _ =>
    (ng_levelsM (fun _ _ => ng_node _) _ _).bind fun _ => trivial

theorem ng_reqRootO (dR : ℕ) (cs : List Bits) :
    NoGhost (reqRootO (lam := lam) (K := K) (L := L) dR cs) :=
  (ng_eachO (fun _ => ng_rleaf _) _).bind fun _ =>
    (ng_levelsM (fun _ _ => ng_rnode _) _ _).bind fun _ => trivial

/-! ## The search: on strings it queries fb t at every attempt -/

theorem ng_askW {C P : Type} (g : GrW C P) (chal : Blk lam K → C) (t : Tag) (q : ℕ → FbIn lam L t) :
    ∀ n j : ℕ, NoGhost (askW g chal t q n j)
  | 0, j => ng_fb t _
  | n + 1, j => (ng_fb t (q j)).bind fun ans => by
      by_cases ho : g.ok (chal ans.1) = true
      · rw [if_pos ho]; trivial
      · rw [if_neg ho]; exact ng_askW g chal t q n (j + 1)

theorem ng_askG {C P : Type} (gr : Option (GrW C P)) (chal : Blk lam K → C) (t : Tag)
    (q : P → FbIn lam L t) (α : P) :
    NoGhost (askG gr chal t q α) := by
  cases gr with
  | none => exact ng_fb t _
  | some g => exact ng_askW g chal t _ _ _

/-! ## Rounds, chains, one execution -/

section Rounds
variable (sMT : ℕ) (t : Tag) (cms : List (Dig lam)) (dR : ℕ)

theorem ng_slotLoO {r : Round} {s : Shape} (a : RAnn r) (w : WireRB lam K r a)
    (emb : (p : r.Pos) → r.Sym p → Body L) (plJ : a.Pj → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ)
    (ph : PhO) (v : VSlot lam K X (r :: s)) :
    NoGhost (slotLoO sMT t cms a w emb plJ i ph v) :=
  (ng_rootOO _ _ _ _).bind fun _ => (ng_askG _ _ _ _ _).bind fun _ => trivial

theorem ng_slotJoinO {r : Round} {s : Shape} (a : RAnn r) (w : WireRB lam K r a)
    (emb : (p : r.Pos) → r.Sym p → Body L) (plJ : a.Pj → PlainPart (shapeOf L t) (annOf L t))
    (i : ℕ) (v : VSlot lam K X (r :: s)) :
    NoGhost (slotJoinO sMT t a w emb plJ i v) :=
  (ng_rootOO _ _ _ _).bind fun _ => (ng_g t _).bind fun _ => trivial

theorem ng_root0O {r : Round} (a : RAnn r) (w : WireRB lam K r a)
    (emb : (p : r.Pos) → r.Sym p → Body L) (m0 : a.M0) :
    NoGhost (root0O (lam := lam) (K := K) (L := L) sMT a w emb m0) :=
  ng_rootOO _ _ _ _

theorem ng_chainO :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A) (embS : (p : OPos s) → OSym s p → Body L)
        (embP : PlainPart s A → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ) (ph : PhO) (σ0 : SStrat s A)
        (vs : List (VSlot lam K X s)),
      NoGhost (chainO sMT t cms dR s A W embS embP i ph σ0 vs)
  | [], _, _, _, _, _, _, _, _ => trivial
  | r :: s, (a, A), (w, W), embS, embP, i, ph, (m0, k0), vs => by
      simp only [chainO]
      split
      · exact (ng_eachO (ng_slotLoO sMT t cms a w _ _ i _) vs).bind fun _ =>
          ng_chainO s A W _ _ _ _ _ _
      · exact (ng_eachO (ng_slotJoinO sMT t a w _ _ i) vs).bind fun _ =>
          (ng_reqRootO _ _).bind fun _ =>
            (ng_root0O sMT a w _ _).bind fun _ =>
              (ng_askG _ _ _ _ _).bind fun _ => ng_chainO s A W _ _ _ _ _ _
      · exact (ng_root0O sMT a w _ _).bind fun _ =>
          (ng_askG _ _ _ _ _).bind fun _ => ng_chainO s A W _ _ _ _ _ _
      · exact ng_chainO s A W _ _ _ _ _ _

end Rounds

section Prove
variable (sMT sFS : ℕ) (t : Tag) {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E) {Wt : Type}
  (H : BatchHonestProver Q Wt) (wq : ProtocolQueryLayout lam K Q) (wp : WirePB Q H)
  (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L)
  (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X) (depthReq : ℕ)
  (cms : List (Dig lam)) (w : Wt)

theorem ng_initO (c0 : H.Coin0) (x : Option Y) :
    NoGhost (initO (lam := lam) (K := K) (L := L) sFS Q H wp xin w c0 x) :=
  (ng_drawO _).bind fun _ => (ng_freshO _).bind fun _ => trivial

theorem ng_proveO (xs : List (Option Y)) :
    NoGhost (proveO sMT sFS t Q H wq wp embS embP xin depthReq cms w xs) :=
  (ng_drawO _).bind fun c0 =>
    (ng_eachO (ng_initO sFS Q H wp xin w c0) xs).bind fun _ =>
      ng_chainO sMT t cms depthReq _ _ _ _ _ _ _ _ _

end Prove

/-! ## The two small experiments -/

section Scheme
variable {lam : ℕ} {L : BatchProtocol I X} (W : QueryLayout lam L) (WP : WireBP L) (p : Params) (i : I)

theorem ng_nodeO : NoGhost (nodeO W WP p i) :=
  (ng_drawO _).bind fun _ => (ng_rootEO _ _ _).bind fun _ => trivial
theorem ng_testO (nd : L.EncodingRandomness × Dig lam) : NoGhost (testO W WP p i nd) :=
  (ng_proveO _ _ _ _ _ _ _ _ _ _ _ _ _ _).bind fun _ => trivial
theorem ng_linkO (nd0 nd : L.EncodingRandomness × Dig lam) : NoGhost (linkO W WP p i nd0 nd) :=
  (ng_proveO _ _ _ _ _ _ _ _ _ _ _ _ _ _).bind fun _ => trivial

/-- The small experiment `RT` never queries a ghost name. -/
theorem noGhost_RT : NoGhost (Ref.RT W WP p i) := (ng_nodeO W WP p i).bind (ng_testO W WP p i)
theorem noGhost_RL : NoGhost (Ref.RL W WP p i) :=
  (ng_nodeO W WP p i).bind fun nd0 => (ng_nodeO W WP p i).bind (ng_linkO W WP p i nd0)

end Scheme

/-- An algorithm that never queries a ghost name runs alike under f and under realF f. -/
theorem runEager_realF_of_noGhost
    {α : Type} {c : TypedOracleComputation lam K L α} (h : NoGhost c) (f : Fam (spec lam K L)) :
    c.runEager (realF f) = c.runEager f := by
  have e := realQ_eager I X lam K L α c f
  rw [realQ_of_noGhost c h] at e
  exact e.symm

end Compile.Batch
