-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/VCost.lean: a bound on the number of hash queries of the compiled verifier.

When the typed oracles are implemented by one hash function (a random oracle on bit strings,
`rom lam`, Rom/OSpec.lean; the implementation: `OracleCoding`, Rom/Family.lean), a typed query costs as many
hash queries as its answer has hash blocks (`blk`, Compile/Batch/ImplOf.lean): K + 1 for a
Fiat-Shamir query, and one for every other query of the verifier (to g, and to the leaf and node
oracles of all trees).

  `costBound_V`  On every execution path the costs of the queries of `V W p v x π` add up to at most
                 `cVB W`.

The bound on the number of typed queries is `tVB W` (Compile/Batch/SpecBinding.lean; `detBound_V`,
Compile/Batch/GlueBinding.lean).

Notation: `lam`, `K`: natural numbers: digests have `lam` bits; an answer of `fb t` is K hash blocks
and a chaining value (the head of Compile/Batch/Oracles.lean); `g`: `OracleName.g t`, a constructor of `OracleName`:
in the joining round (the first shared round after the local ones), the slot value (the same head);
`W.T`, `W.Lk`, `W.B`: the fields of `QueryLayout` for Test, Link and Batch (`ProtocolQueryLayout`; Iop/BatchWire.lean);
`W.depthReq`: a natural number: depth of a request tree (the field's comment).
"The implementation" in this file's comments is not the released programs: what is said of it need
not hold of them (lean/LIMITS.md, L1).
-/
import Compile.Batch.GlueBinding
import Compile.Batch.ImplOf
import Rom.Cost

set_option autoImplicit false

namespace Compile.Batch
open Iop Rom

variable {I X : Type} {lam K : ℕ} {L : BatchProtocol I X}

/-- the bound on the hash queries of the compiled verifier of one slot: K + 1 for each round of the
chain, one to g, for each opened position a leaf and a path, and a leaf and a path in the request
tree -/
def cVQB {Y : Type} {E : ExtSpec} {Q : BatchInteractiveOracleProof Y E} (wq : ProtocolQueryLayout lam K Q) (depthReq : ℕ) : ℕ :=
  (Q.loc.shape.length * (K + 1) + 1) + (wq.nOpen * (wq.maxDepth + 1) + (depthReq + 1))

/-- the bound on the hash queries of V -/
def cVB (W : QueryLayout lam L) : ℕ := cVQB W.T W.depthReq + cVQB W.Lk W.depthReq + cVQB W.B W.depthReq

theorem cVB_le_of (W : QueryLayout lam L) {a b c N : ℕ} (hT : cVQB W.T W.depthReq ≤ a)
    (hL : cVQB W.Lk W.depthReq ≤ b) (hB : cVQB W.B W.depthReq ≤ c) (hN : a + b + c ≤ N) :
    cVB W ≤ N :=
  le_trans (Nat.add_le_add (Nat.add_le_add hT hL) hB) hN

namespace VCost

abbrev CB {α : Type} (c : TypedOracleComputation lam K L α) (t : ℕ) : Prop :=
  OComp.CostBound (S := spec lam K L) (blk K) c t

theorem cb_askV (o : OracleName) (q : domOf lam L o) : CB (askTypedOracle (L := L) (K := K) o q) (blk K o) :=
  OComp.CostBound.ask (S := spec lam K L) o q

theorem cb_chainB (t : Tag) (cms : List (Dig lam)) (x : Option X) (salt : Bits) (rtreq : Dig lam) :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A) (embP : PlainPart s A → PlainPart (shapeOf L t) (annOf L t))
        (i : ℕ) (ph : Phase lam) (rts : List (Dig lam)) (pls : Plains s),
      CB (recomputeChain (L := L) t cms x salt rtreq s A W embP i ph rts pls)
        (s.length * (K + 1) + ph.joins)
  | [], _, _, _, _, _, _, _ => OComp.CostBound.pure _ _
  | _ :: s, (a, A), (w, W), embP, i, ph, rts, (pl, pls) => by
      simp only [recomputeChain]
      split
      · rename_i h next e
        split
        · rename_i rt rts' _
          simp only [bind_eq]
          refine (OComp.CostBound.bind (t := s.length * (K + 1) + ph.joins + 0)
            (fun ans =>
              OComp.CostBound.bind (t := 0) (fun r => OComp.CostBound.pure _ _)
                ((cb_chainB t cms x salt rtreq s A W _ _ _ rts' pls).mono
                  (Nat.add_le_add_left (joins_of_one e _) _)))
            (cb_askV _ _)).mono ?_
          simp only [List.length_cons, blk, Nat.succ_mul]
          omega
        · exact OComp.CostBound.pure _ _
      · rename_i h next e
        split
        · rename_i rt rts' _
          simp only [bind_eq]
          refine (OComp.CostBound.bind (t := s.length * (K + 1) + ph.joins + 0)
            (fun ans =>
              OComp.CostBound.bind (t := 0) (fun r => OComp.CostBound.pure _ _)
                ((cb_chainB t cms x salt rtreq s A W _ _ _ rts' pls).mono
                  (Nat.add_le_add_left (joins_of_one e _) _)))
            (cb_askV _ _)).mono ?_
          simp only [List.length_cons, blk, Nat.succ_mul]
          omega
        · exact OComp.CostBound.pure _ _
      · rename_i ρ e
        split
        · rename_i rtj rts1 _
          split
          · rename_i rt0 rts' _
            simp only [bind_eq]
            refine (OComp.CostBound.bind (t := (K + 1) + (s.length * (K + 1) + 0 + 0)) (fun c =>
              OComp.CostBound.bind (t := s.length * (K + 1) + 0 + 0) (fun ans =>
                OComp.CostBound.bind (t := 0) (fun r => OComp.CostBound.pure _ _)
                  (cb_chainB t cms x salt rtreq s A W _ _ (.shr _ (show Dig lam from c)) rts' pls))
                (cb_askV (L := L) (K := K) (OracleName.fb t) _)) (cb_askV (L := L) (K := K) (OracleName.g t) _)).mono ?_
            simp only [List.length_cons, joins_of_join e, blk, Nat.succ_mul]
            omega
          · exact OComp.CostBound.pure _ _
        · exact OComp.CostBound.pure _ _
      · exact OComp.CostBound.pure _ _

theorem cb_climbM (node : Dig lam → Dig lam → TypedOracleComputation lam K L (Dig lam)) (hn : ∀ a b, CB (node a b) 1) :
    ∀ (path : List (Dig lam)) (j : ℕ) (c : Dig lam), CB (climbM node path j c) path.length
  | [], _, _ => OComp.CostBound.pure _ _
  | s :: ss, j, c => by
      simp only [climbM, bind_eq]
      have hlen : 1 + ss.length ≤ (s :: ss).length := by simp only [List.length_cons]; omega
      split_ifs
      · exact (OComp.CostBound.bind (fun u => cb_climbM node hn ss (j / 2) u) (hn c s)).mono hlen
      · exact (OComp.CostBound.bind (fun u => cb_climbM node hn ss (j / 2) u) (hn s c)).mono hlen

theorem cb_runCheck (c : Check lam L) : CB (runCheck (K := K) c) (c.path.length + 1) := by
  simp only [runCheck, bind_eq]
  refine (OComp.CostBound.bind (t := c.path.length + 0) (fun d =>
    OComp.CostBound.bind (t := 0)
      (fun r => OComp.CostBound.pure _ _) (cb_climbM hashTreeNode (fun a b => cb_askV _ _) c.path c.j d))
    (cb_askV (L := L) (K := K) OracleName.leaf c.inp)).mono ?_
  simp only [blk]
  omega

theorem cb_runChecks (m : ℕ) :
    ∀ l : List (Check lam L),
      (∀ c ∈ l, c.path.length ≤ m) → CB (runChecks (K := K) l) (l.length * (m + 1))
  | [], _ => OComp.CostBound.pure _ _
  | c :: cs, h => by
      simp only [runChecks, bind_eq]
      refine (OComp.CostBound.bind (t := cs.length * (m + 1) + 0) (fun a =>
        OComp.CostBound.bind (t := 0) (fun b => OComp.CostBound.pure _ _)
          (cb_runChecks m cs fun c' hc' => h c' (List.mem_cons_of_mem _ hc')))
        ((cb_runCheck c).mono (t := m + 1) (by have := h c List.mem_cons_self; omega))).mono ?_
      simp only [List.length_cons, Nat.succ_mul]
      omega

theorem cb_reqCheck (depthReq : ℕ) (rtreq : Dig lam) (slot : ℕ)
    (path : List (Dig lam)) (c : Dig lam) :
    CB (reqCheck (L := L) (K := K) depthReq rtreq slot path c) (depthReq + 1) := by
  unfold reqCheck
  split_ifs with h
  · simp only [bind_eq]
    refine (OComp.CostBound.bind (t := path.length + 0) (fun d =>
      OComp.CostBound.bind (t := 0)
        (fun r => OComp.CostBound.pure _ _) (cb_climbM rnodeV (fun a b => cb_askV _ _) path slot d))
      (cb_askV (L := L) (K := K) OracleName.rleaf _)).mono ?_
    simp only [blk]
    omega
  · exact OComp.CostBound.pure _ _

theorem cb_afterB {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E) (wq : ProtocolQueryLayout lam K Q)
    (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L) (embE : E.Sym → Body L)
    (depthReq : ℕ) (cms : List (Dig lam)) (x : Y) (π : OneProtocolProof lam Q) (ρ : Rho Q.loc.shape)
    (rts : RootsOfChain lam Q.loc.shape) (ph : Phase lam) :
    CB (afterB Q wq embS embE depthReq cms x π ρ rts ph)
      (wq.nOpen * (wq.maxDepth + 1) + (depthReq + 1)) := by
  unfold afterB
  split
  · rename_i a b _ _
    split_ifs with hc
    · simp only [bind_eq]
      refine OComp.CostBound.bind (fun ok => ?_)
        ((cb_runChecks wq.maxDepth (a ++ b) ?_).mono (Nat.mul_le_mul_right (wq.maxDepth + 1) hc.1))
      · split
        · exact (OComp.CostBound.bind (s := 0) (t := 0)
              (fun _ => OComp.CostBound.pure _ _) (OComp.CostBound.pure _ _)).mono (Nat.zero_le _)
        · exact (OComp.CostBound.bind (t := 0)
              (fun _ => OComp.CostBound.pure _ _) (cb_reqCheck _ _ _ _ _)).mono
            (Nat.le_of_eq (Nat.add_zero _))
      · intro c hmem
        have := List.all_eq_true.1 hc.2 c hmem
        simp only [Check.wellFormed, Bool.and_eq_true, decide_eq_true_eq] at this
        omega
    · exact OComp.CostBound.pure _ _
  · exact OComp.CostBound.pure _ _

theorem counts_cb :
    Counts (spec lam K L) (fun {_} c t => OComp.CostBound (S := spec lam K L) (blk K) c t) where
  pure := fun a t => OComp.CostBound.pure a t
  bind := fun h hg => OComp.CostBound.bind hg h
  mono := fun h hst => h.mono hst

/-- The cost of `checkPrunedOpenings`, the end of `verifyOneProtocol` with pruned Merkle paths, is at most what the
openings cost and what the request tree costs if the chain has passed the joining round (`reqCost`,
Compile/Batch/ForestFacts.lean). -/
theorem cb_afterBO' {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E) (wq : ProtocolQueryLayout lam K Q)
    (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L) (embE : E.Sym → Body L)
    (depthReq : ℕ) (cms : List (Dig lam)) (x : Y) (π : OneProtocolProof lam Q) (ρ : Rho Q.loc.shape)
    (rts : RootsOfChain lam Q.loc.shape) (ph : Phase lam) :
    CB (checkPrunedOpenings Q wq embS embE depthReq cms x π ρ rts ph)
      (wq.nOpen * (wq.maxDepth + 1) + reqCost depthReq ph) :=
  Counts.afterBO counts_cb (cb_askV OracleName.leaf) (cb_askV OracleName.node) (cb_askV OracleName.rleaf) (cb_askV OracleName.rnode)
    Q wq embS embE depthReq cms x π ρ rts ph

theorem cb_afterBO {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E) (wq : ProtocolQueryLayout lam K Q)
    (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L) (embE : E.Sym → Body L)
    (depthReq : ℕ) (cms : List (Dig lam)) (x : Y) (π : OneProtocolProof lam Q) (ρ : Rho Q.loc.shape)
    (rts : RootsOfChain lam Q.loc.shape) (ph : Phase lam) :
    CB (checkPrunedOpenings Q wq embS embE depthReq cms x π ρ rts ph)
      (wq.nOpen * (wq.maxDepth + 1) + (depthReq + 1)) :=
  (cb_afterBO' Q wq embS embE depthReq cms x π ρ rts ph).mono
    (Nat.add_le_add_left (reqCost_le _ _) _)

theorem cb_verifyBS (sMT sFS : ℕ) (t : Tag) {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E)
    (wq : ProtocolQueryLayout lam K Q) (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L)
    (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X)
    (embE : E.Sym → Body L) (depthReq : ℕ) (cms : List (Dig lam)) (x : Y) (π : OneProtocolProof lam Q) :
    CB (verifyOneProtocol sMT sFS t Q wq embS embP xin embE depthReq cms x π) (cVQB wq depthReq) := by
  unfold verifyOneProtocol recomputeChainOfProof cVQB
  refine OComp.CostBound.bind (fun r => ?_)
    (cb_chainB t cms (xin x) π.salt π.rtreq Q.loc.shape Q.ann wq.sh embP 0 .first π.roots π.plains)
  rcases r with _ | ⟨ρ, rts, ph⟩
  · exact OComp.CostBound.pure _ _
  · dsimp only
    split_ifs
    · exact cb_afterBO Q wq embS embE depthReq cms x π ρ rts ph
    · exact OComp.CostBound.pure _ _

end VCost

open VCost in
/-- On every execution path the queries of `V` cost at most `cVB W` hash queries. -/
theorem costBound_V (W : QueryLayout lam L) (p : Params) (v : IVK lam L) (x : X) (π : Prf lam L) :
    OComp.CostBound (S := spec lam W.K L) (blk W.K) (V W p v x π) (cVB W) := by
  unfold V cVB
  split
  · split_ifs
    · simp only [bind_eq]
      refine (OComp.CostBound.bind (t := cVQB W.Lk W.depthReq + (cVQB W.B W.depthReq + 0)) (fun a =>
        OComp.CostBound.bind (t := cVQB W.B W.depthReq + 0) (fun b =>
          OComp.CostBound.bind (t := 0) (fun c => OComp.CostBound.pure _ _)
            (cb_verifyBS _ _ _ _ W.B _ _ _ _ _ _ _ _))
          (cb_verifyBS _ _ _ _ W.Lk _ _ _ _ _ _ _ _)) (cb_verifyBS _ _ _ _ W.T _ _ _ _ _ _ _ _)).mono ?_
      omega
    · exact OComp.CostBound.pure _ _
  · exact OComp.CostBound.pure _ _

end Compile.Batch
