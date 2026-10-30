-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/RunIsVNoCoin.lean: the function that the compiler's verifier runs on each proof string tosses no
coin.

That function is `verifyOneProtocol` (Compile/Batch/Verifier.lean), a tree of queries to typed oracles
(`Rom.OComp`). "Tosses no coin" (`NoCoin`) says that no node of the tree draws randomness: the
verifier is deterministic given the oracles' answers.

Two statements and proofs; by name, in the namespace `Run.NC`, a lemma F_nc for a function F under
`verifyOneProtocol`. In `Spec.run_verifyBS` the digests have 256 bits (`lam` is 256).

Main names:
  `Spec.noCoin_verifyBS`: the title's statement, for all arguments.
  `Spec.run_verifyBS`: so Run/RunIsV.lean's `run_bare_lax` holds at Vt := `verifyOneProtocol ..` with no
    hypothesis but that N bounds the parser's count (`hN`), beside whatever the arguments hold as
    proofs.

Why: Run/RunIsV.lean says that an evaluation on a file is the definition's run of "the parser's
tree, then the typed verifier over the one oracle", for a typed verifier that tosses no coin. Here
that hypothesis is shown for Compile/Batch/Verifier.lean's `verifyOneProtocol`. The climb of a path and the
walk of a pruned set are treated for any way of hashing two digests that tosses no coin
(Compile/MerkleM.lean: `climbM`; Hash/Octopus.lean: `lone`, `stepC`, `octC`).

Notation:
  `sMT`, `sFS`: the length of the salt of a leaf, and of the salt of a chain
    (Compile/Batch/Verifier.lean);
  `t`: which compiled protocol: `test`, `link` or `onl` (`Tag`, Compile/Oracles.lean);
  `wq`: the wiring (`ProtocolQueryLayout`, Iop/BatchWire.lean);
  `embS`, `embP`, `embE`: how symbols and plain parts are written into queries (`verifyB`,
    Compile/Batch/Verifier.lean);
  `xin`: a map; `xin x` is `recomputeChain`'s `x`, the whole instance (Compile/Batch/Verifier.lean);
  `depthReq`: depth of the request tree (`QueryLayout.depthReq`, Iop/BatchWire.lean);
  `cms`: the external roots (`verifyB`, Compile/Batch/Verifier.lean).

Limits: this file says nothing on the whole verifier of a scheme (the key's test, the link, the
slots). What the head of Run/RunIsV.lean lists as not said is not said here either. One exception,
on coins: that `verifyOneProtocol` tosses no coin is what this file states.

Terms: lean/GLOSSARY.md.
-/
/- Limits: that a proof file is accepted or refused is no theorem of this library. It is the outcome
   of a `#guard` line, or of an evaluation outside the library, such as a test by Lean's evaluator,
   which leaves no declaration. So nothing that is checked of declarations is checked of such an
   evaluation. No clause of a soundness theorem of Fmt/ and Run/ speaks of a run. -/
import Run.RunIsVProofs
import Compile.Batch.Verifier

set_option autoImplicit false

namespace Run
open Rom Iop Compile Compile.Batch

namespace Spec

/-- States: `verifyOneProtocol` tosses no coin. -/
def noCoin_verifyBS : Prop :=
  ∀ (I X : Type) (lam K : ℕ) (L : BatchProtocol I X) (sMT sFS : ℕ) (t : Tag) (Y : Type) (E : ExtSpec)
      (Q : BatchInteractiveOracleProof Y E) (wq : ProtocolQueryLayout lam K Q)
      (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L)
      (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X)
      (embE : E.Sym → Body L) (depthReq : ℕ) (cms : List (Dig lam)) (x : Y) (π : OneProtocolProof lam Q),
    (verifyOneProtocol (L := L) sMT sFS t Q wq embS embP xin embE depthReq cms x π).NoCoin

/-- States: the definition's run (`ZKCP.OComp.run`, ZKCP/Defs.lean) of "the lenient parser's tree,
then `verifyOneProtocol` over the one oracle" is the point mass at the evaluation at `verifyOneProtocol` (`verdictV`,
Run/RunIsV.lean). The statement has no hypothesis but that N bounds the parser's count (`hN`),
beside whatever the arguments hold as proofs. -/
def run_verifyBS : Prop :=
  ∀ (I X : Type) (K : ℕ) (L : BatchProtocol I X) (sMT sFS : ℕ) (t : Tag) (Y : Type) (E : ExtSpec)
      (Q : BatchInteractiveOracleProof Y E) (wq : ProtocolQueryLayout 256 K Q)
      (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L)
      (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X)
      (embE : E.Sym → Body L) (depthReq : ℕ) (m : OracleCoding (spec 256 K L) 256)
      (sp : Y → _root_.Fmt.Spec) (T : Typing Q) (N : ℕ) (hN : ∀ x, laxN (sp x) ≤ N)
      (f : ZKCP.Oracle 256) (ivk : List (Dig 256)) (x : Y) (b : ByteArray),
    ((paOfLax sp T N hN).thenV
        (exitV m (verifyOneProtocol (L := L) sMT sFS t Q wq embS embP xin embE depthReq)) ivk x b).run f =
      PMF.pure (verdictV m (verifyOneProtocol (L := L) sMT sFS t Q wq embS embP xin embE depthReq) f ivk x
          (keep ivk (parseLaxW (m := Id) (hI f) (sp x) T b)))

end Spec

namespace NC
variable {I X : Type} {lam K : ℕ} {L : BatchProtocol I X}

theorem pureN {S : OSpec} {α : Type} (a : α) : (Pure.pure a : Rom.OComp S α).NoCoin := trivial

theorem bindN {S : OSpec} {α β : Type} {c : Rom.OComp S α} {g : α → Rom.OComp S β}
    (hc : c.NoCoin) (hg : ∀ a, (g a).NoCoin) : (c >>= g).NoCoin :=
  OComp.NoCoin.bind hc hg

theorem askV_nc (o : Batch.OracleName) (q : Batch.domOf lam L o) :
    (Compile.Batch.askTypedOracle (K := K) (L := L) o q).NoCoin := fun _ => trivial

section Walks
variable {S : OSpec} {D : Type} (hN : D → D → Rom.OComp S D) (h : ∀ a b, (hN a b).NoCoin)
include h

theorem climbM_nc : ∀ (p : List D) (j : ℕ) (c : D), (Compile.climbM hN p j c).NoCoin
  | [], _, _ => trivial
  | s :: ss, j, c => by
      simp only [Compile.climbM]
      split
      · exact bindN (h _ _) fun u => climbM_nc ss (j / 2) u
      · exact bindN (h _ _) fun u => climbM_nc ss (j / 2) u

theorem lone_nc (i : ℕ) (a s : D) : (Octopus.lone hN i a s).NoCoin := by
  unfold Octopus.lone
  split
  · exact h _ _
  · exact h _ _

variable [Inhabited D]

theorem stepC_nc : ∀ (js : List ℕ) (v s : List D), (Octopus.stepC hN js v s).NoCoin
  | [], _, _ => trivial
  | [i], v, s => by
      simp only [Octopus.stepC]
      exact bindN (lone_nc hN h _ _ _) fun _ => trivial
  | i :: j :: l, v, s => by
      simp only [Octopus.stepC]
      split
      · exact bindN (h _ _) fun _ => bindN (stepC_nc l _ _) fun _ => trivial
      · exact bindN (lone_nc hN h _ _ _) fun _ => bindN (stepC_nc (j :: l) _ _) fun _ => trivial

theorem octC_nc : ∀ (d : ℕ) (js : List ℕ) (v s : List D), (Octopus.octC hN d js v s).NoCoin
  | 0, _, _, _ => trivial
  | d + 1, js, v, s => by
      simp only [Octopus.octC]
      exact bindN (stepC_nc hN h _ _ _) fun _ => octC_nc d _ _ _

end Walks

theorem nodeV_nc (a b : Dig lam) : (Compile.Batch.hashTreeNode (K := K) (L := L) a b).NoCoin := askV_nc _ _

theorem rnodeV_nc (a b : Dig lam) : (Compile.Batch.rnodeV (K := K) (L := L) a b).NoCoin :=
  askV_nc _ _

theorem chainB_nc (t : Tag) (cms : List (Dig lam)) (x : Option X) (salt : Bits) (rtreq : Dig lam) :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A) (embP : PlainPart s A → PlainPart (shapeOf L t) (annOf L t))
        (i : ℕ) (ph : Phase lam) (rts : List (Dig lam)) (pls : Plains s),
      (Compile.Batch.recomputeChain (L := L) t cms x salt rtreq s A W embP i ph rts pls).NoCoin
  | [], _, _, _, _, _, _, _ => trivial
  | _ :: s, (a, A), (w, W), embP, i, ph, rts, (pl, pls) => by
      simp only [Compile.Batch.recomputeChain]
      split
      · split
        · exact bindN (askV_nc _ _) fun _ =>
            bindN (chainB_nc t cms x salt rtreq s A W _ _ _ _ _) fun _ => trivial
        · exact trivial
      · split
        · exact bindN (askV_nc _ _) fun _ =>
            bindN (chainB_nc t cms x salt rtreq s A W _ _ _ _ _) fun _ => trivial
        · exact trivial
      · split
        · split
          · exact bindN (askV_nc _ _) fun _ =>
              bindN (askV_nc _ _) fun _ =>
                bindN (chainB_nc t cms x salt rtreq s A W _ _ _ _ _) fun _ => trivial
          · exact trivial
        · exact trivial
      · exact trivial

theorem leavesV_nc : ∀ es : List (ℕ × Check lam L), (Compile.Batch.leavesV (K := K) es).NoCoin
  | [] => trivial
  | e :: es => by
      simp only [Compile.Batch.leavesV]
      exact bindN (askV_nc _ _) fun _ => bindN (leavesV_nc es) fun _ => trivial

theorem runForest_nc (F : Forest lam L) (s : List (Dig lam)) :
    (Compile.Batch.runForest (K := K) F s).NoCoin := by
  simp only [Compile.Batch.runForest]
  exact bindN (leavesV_nc _) fun _ => bindN (octC_nc _ nodeV_nc _ _ _ _) fun _ => trivial

theorem runForests_nc :
    ∀ (Fs : List (Forest lam L)) (s : List (Dig lam)),
      (Compile.Batch.runForests (K := K) Fs s).NoCoin
  | [], _ => trivial
  | F :: Fs, s => by
      simp only [Compile.Batch.runForests]
      exact bindN (runForest_nc _ _) fun _ => bindN (runForests_nc Fs _) fun _ => trivial

theorem reqCheck_nc (depthReq : ℕ) (rtreq : Dig lam) (slot : ℕ)
    (path : List (Dig lam)) (c : Dig lam) :
    (Compile.Batch.reqCheck (K := K) (L := L) depthReq rtreq slot path c).NoCoin := by
  unfold Compile.Batch.reqCheck
  split
  · exact bindN (askV_nc _ _) fun _ => bindN (climbM_nc _ rnodeV_nc _ _ _) fun _ => trivial
  · exact trivial

variable {Y : Type} {E : ExtSpec} {Q : BatchInteractiveOracleProof Y E}

theorem reqPart_nc (depthReq : ℕ) (π : OneProtocolProof lam Q) (ph : Phase lam) :
    (Compile.Batch.reqPart (K := K) (L := L) depthReq π ph).NoCoin := by
  unfold Compile.Batch.reqPart
  split
  · exact trivial
  · exact reqCheck_nc _ _ _ _ _

theorem afterF_nc (wq : ProtocolQueryLayout lam K Q) (depthReq : ℕ) (x : Y) (π : OneProtocolProof lam Q)
    (ρ : Rho Q.loc.shape) (rts : RootsOfChain lam Q.loc.shape) (ph : Phase lam)
    (Fs : List (Forest lam L)) (s : List (Dig lam)) :
    (Compile.Batch.afterF Q wq depthReq x π ρ rts ph Fs s).NoCoin :=
  OComp.NoCoin.bind (runForests_nc _ _) fun _ =>
    OComp.NoCoin.bind (reqPart_nc _ _ _) fun _ => trivial

theorem afterBO_nc (wq : ProtocolQueryLayout lam K Q)
    (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L) (embE : E.Sym → Body L)
    (depthReq : ℕ) (cms : List (Dig lam)) (x : Y) (π : OneProtocolProof lam Q) (ρ : Rho Q.loc.shape)
    (rts : RootsOfChain lam Q.loc.shape) (ph : Phase lam) :
    (Compile.Batch.checkPrunedOpenings Q wq embS embE depthReq cms x π ρ rts ph).NoCoin := by
  unfold Compile.Batch.checkPrunedOpenings
  split
  · split
    · exact afterF_nc _ _ _ _ _ _ _ _ _
    · exact trivial
  · exact trivial

end NC

theorem noCoin_verifyBS : Spec.noCoin_verifyBS := by
  intro I X lam K L sMT sFS t Y E Q wq embS embP xin embE depthReq cms x π
  refine OComp.NoCoin.bind (NC.chainB_nc _ _ _ _ _ _ _ _ _ _ _ _ _) fun r => ?_
  cases r with
  | none => exact trivial
  | some z =>
    obtain ⟨ρ, rts, ph⟩ := z
    show (if proofHasStrictFormat sMT sFS Q wq depthReq x π ρ rts ph then
        checkPrunedOpenings Q wq embS embE depthReq cms x π ρ rts ph
      else pure false : TypedOracleComputation lam K L Bool).NoCoin
    split
    · exact NC.afterBO_nc _ _ _ _ _ _ _ _ _ _
    · exact trivial

theorem run_verifyBS :
    Spec.run_verifyBS := fun I X K L sMT sFS t Y E Q wq embS embP xin embE depthReq m sp T N hN f ivk x b =>
  run_bare_lax (spec 256 K L) Y Y E Q m
    (verifyOneProtocol (L := L) sMT sFS t Q wq embS embP xin embE depthReq) sp T N hN f ivk x b
    (fun cms x π =>
      noCoin_verifyBS I X 256 K L sMT sFS t Y E Q wq embS embP xin embE depthReq cms x π)

end Run
