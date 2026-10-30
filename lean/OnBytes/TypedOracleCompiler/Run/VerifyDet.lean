-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Run/VerifyDet.lean.
Run/VerifyDet.lean: THE COMPILED VERIFIER OF ONE SLOT (Compile.Batch.verifyOneProtocol), RUN UNDER FIXED
ORACLE FUNCTIONS, IS A PLAIN FUNCTION OF THESE FUNCTIONS: FOR EVERY PROTOCOL AND EVERY WIRING.
Definitions and statements (Run.Spec.vd_*); the proofs are in Run/VerifyDetProofs.lean. Generic: no
format, no hash, no toy.
WHY. verifyOneProtocol is a tree of queries (Compile/Batch/Verifier.lean). To RUN it one fixes a family g of
oracle functions and takes the run in which every coin toss yields 0 (Rom/Cache.lean: OComp.det; the
verifier tosses none). Here the monad goes: a function verifyF g, written beside verifyOneProtocol clause by
clause, with "ask the oracle o at q" replaced by "g o q", and the theorem that it IS that run. A
first step towards a twin that an evaluator can run at protocols with large sets of verifier
messages: what is left to be replaced after this step are pure functions alone.
   nodeF g, rnodeF g          the two node oracles as functions of two digests
   chainF g ..                the chain: a recursion on the shape, with the same five acts, the same
                              taking of roots, the same queries as recomputeChain
   runForestF g, runForestsF g     the walks: the leaves' digests by g; the library's pure pruned
                                   walk (Hash/OctopusFacts.lean: octF) at nodeF g; every node left
                                   is compared with its tree's root
   reqCheckF g, reqPartF g    the check in the request tree: the pure climb
                              (Compile/MerkleList.lean: climbF) at rnodeF g
   afterBOF g ..              what follows the chain: THE SAME forestsOf, the same tests without a
                              query, the walks, the request tree, THE SAME decision on THE SAME
                              transcript mkTr
   verifyF g ..           chainF;  THE SAME proofHasStrictFormat;  afterBOF
   Spec.vd_chain, vd_forests, vd_req, vd_after       each part is the run of its part
   Spec.vd_verify         (verifyOneProtocol sMT sFS t Q wq embS embP xin embE depthReq cms x π).det g =
                          verifyF g sMT sFS t Q wq embS embP xin embE depthReq cms x π
WHAT IS NOT SAID. Nothing on soundness: an equation between two ways of computing one truth value.
THE VALUES AGREE; THE NUMBER OF CALLS NEED NOT: the tree asks all its queries before it joins the
three truth values (the walks, the request tree, the decision); in compiled code "and" on truth
values is lazy, so a run of verifyF can call g less often than the tree asks. proofHasStrictFormat, forestsOf,
mkTr and the protocol's decision are used AS THEY STAND: whatever an evaluator has to build for them
(the rounds' records with their finite types, sets of read positions) it still has to build. Nothing
on a run with coins (the verifier has none; not shown here).

Terms: lean/GLOSSARY.md.

-/
import Run.VerifyDet
import OnBytes.TypedOracleCompiler.Compile.Batch.Verifier
import Compile.Batch.SeedCache
import Compile.OctopusRom
import Rom.Cache

set_option autoImplicit false

namespace TypedOracleCompiler.Run
open TypedOracleCompiler.Iop Rom _root_.Compile TypedOracleCompiler.Compile.Batch
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run

section
variable {I X : Type} {lam K : ℕ} {L : BatchProtocolWithLeafBody I X} (g : Fam (TypedOracleCompiler.Compile.Batch.typedOracleFamily lam K L))

/-- the node oracle, the request tree's node oracle, as functions -/
def nodeF (a b : Dig lam) : Dig lam := g TypedOracleCompiler.Compile.Batch.OracleName.node
    ((List.ofFn a, List.ofFn b) : Bits × Bits)
def rnodeF (a b : Dig lam) : Dig lam := g TypedOracleCompiler.Compile.Batch.OracleName.rnode
    ((List.ofFn a, List.ofFn b) : Bits × Bits)

/-- The chain, as a function of the oracle functions. -/
def chainF (t : Tag) (cms : List (Dig lam)) (x : Option X) (salt : Bits) (rtreq : Dig lam) :
    (s : Shape) → (A : RoundSplits s) → RoundsQueryLayout lam K s A → (PlainPart s A → PlainPart (shapeOf L t) (annOf L t)) →
    ℕ → Phase lam → List (Dig lam) → Plains s → Option (Rho s × RootsOfChain lam s × Phase lam)
  | [], _, _, _, _, ph, _, _ => some ((), (), ph)
  | _ :: s, (a, A), (w, W), embP, i, ph, rts, (pl, pls) =>
      match actOf cms (x.map L.early) salt a.kind ph with
      | some (.one h true next) =>
          match takeRt w.depthJ.length rts with
          | some (rt, rts') =>
              let ans : (Fin K → Dig lam) × Dig lam :=
                g (TypedOracleCompiler.Compile.Batch.OracleName.fb t)
                  (⟨i, h.withLate (lateInstancePart L i x), rt,
                    embP (.inl (.inr (a.plain pl).2))⟩ : FbIn lam L t)
              (chainF t cms x salt rtreq s A W (fun z => embP (.inr z)) (i + 1)
                  (next (List.ofFn ans.2)) rts' pls).map
                fun z => ((w.chal ans.1, z.1), ((none, some rt), z.2.1), z.2.2)
          | none => none
      | some (.one h false next) =>
          match takeRt w.depth0.length rts with
          | some (rt, rts') =>
              let ans : (Fin K → Dig lam) × Dig lam :=
                g (TypedOracleCompiler.Compile.Batch.OracleName.fb t)
                    (⟨i, h, rt, embP (.inl (.inl (a.plain pl).1))⟩ : FbIn lam L t)
              (chainF t cms x salt rtreq s A W (fun z => embP (.inr z)) (i + 1)
                  (next (List.ofFn ans.2)) rts' pls).map
                fun z => ((w.chal ans.1, z.1), ((some rt, none), z.2.1), z.2.2)
          | none => none
      | some (.join ρ) =>
          match takeRt w.depthJ.length rts with
          | some (rtj, rts1) =>
              match takeRt w.depth0.length rts1 with
              | some (rt0, rts') =>
                  let c : Dig lam :=
                    g (TypedOracleCompiler.Compile.Batch.OracleName.g t)
                        (⟨i, ρ, rtj, embP (.inl (.inr (a.plain pl).2))⟩ : JoiningRoundQuery lam L t)
                  let ans : (Fin K → Dig lam) × Dig lam :=
                    g (TypedOracleCompiler.Compile.Batch.OracleName.fb t)
                      (⟨i, .f4 cms (List.ofFn rtreq), rt0,
                        embP (.inl (.inl (a.plain pl).1))⟩ : FbIn lam L t)
                  (chainF t cms x salt rtreq s A W (fun z => embP (.inr z)) (i + 1)
                      (.shr (List.ofFn ans.2) c) rts' pls).map
                    fun z => ((w.chal ans.1, z.1), ((some rt0, some rtj), z.2.1), z.2.2)
              | none => none
          | none => none
      | none => none

/-! ### The walks -/

/-- all checks of a forest at once -/
def runForestF (F : Forest lam L) (s : List (Dig lam)) : Bool :=
  ((Octopus.upN F.depth F.idx).zip
      (Octopus.octF (nodeF g) F.depth F.idx
        (F.cs.map fun e => (g TypedOracleCompiler.Compile.Batch.OracleName.leaf e.2.inp : Dig lam)) s)).all
    fun m => decide (m.2 = F.treeRoot m.1)

def runForestsF : List (Forest lam L) → List (Dig lam) → Bool
  | [], _ => true
  | F :: Fs, s => runForestF g F (s.take F.need) && runForestsF Fs (s.drop F.need)

/-! ### The request tree -/

def reqCheckF (depthReq : ℕ) (rtreq : Dig lam) (slot : ℕ) (path : List (Dig lam)) (c : Dig lam)
    (rs : Bits) : Bool :=
  if path.length = depthReq ∧ slot < 2 ^ depthReq then
    decide (climbF (rnodeF g) path slot (g TypedOracleCompiler.Compile.Batch.OracleName.rleaf
        (List.ofFn c ++ rs : Bits) : Dig lam) = rtreq)
  else false

variable {Y : Type} {E : ExtSpec}

def reqPartF {Q : BatchInteractiveOracleProof Y E} (depthReq : ℕ) (π : OneProtocolProof lam Q) (ph : Phase lam) : Bool :=
  match ph.slotVal with
  | none => true
  | some c => reqCheckF g depthReq π.rtreq π.slot π.path c π.rsalt

/-! ### The verifier -/

/-- what follows the chain -/
def afterBOF (Q : BatchInteractiveOracleProof Y E) (wq : ProtocolQueryLayout lam K Q)
    (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L) (embE : E.Sym → Body L)
    (depthReq : ℕ) (cms : List (Dig lam)) (x : Y) (π : OneProtocolProof lam Q) (ρ : Rho Q.loc.shape)
    (rts : RootsOfChain lam Q.loc.shape) (ph : Phase lam) : Bool :=
  match forestsOf Q wq embS embE cms x π ρ rts with
  | some Fs =>
      if (flatF Fs).length ≤ wq.nOpen ∧
          (flatF Fs).all (fun c => c.wellFormed && decide (c.depth ≤ wq.maxDepth)) then
        runForestsF g Fs (readsF Fs) && reqPartF g depthReq π ph &&
          Q.loc.accept x (wq.ext.build fun p => (π.ext p).map Opening.sym)
            (mkTr Q.loc.shape Q.ann wq.sh rts π.plains ρ π.opens)
      else false
  | none => false

/-- THE COMPILED VERIFIER OF ONE SLOT AS A FUNCTION OF THE ORACLE FUNCTIONS. -/
def verifyF (sMT sFS : ℕ) (t : Tag) (Q : BatchInteractiveOracleProof Y E) (wq : ProtocolQueryLayout lam K Q)
    (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L)
    (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X)
    (embE : E.Sym → Body L) (depthReq : ℕ) (cms : List (Dig lam)) (x : Y) (π : OneProtocolProof lam Q) : Bool :=
  match chainF g t cms (xin x) π.salt π.rtreq Q.loc.shape Q.ann wq.sh embP 0
      .first π.roots π.plains with
  | none => false
  | some (ρ, rts, ph) =>
    if proofHasStrictFormat sMT sFS Q wq depthReq x π ρ rts ph then
      afterBOF g Q wq embS embE depthReq cms x π ρ rts ph
    else false

end

namespace Spec

def vd_chain : Prop :=
  ∀ (I X : Type) (lam K : ℕ) (L : BatchProtocolWithLeafBody I X) (g : Fam (TypedOracleCompiler.Compile.Batch.typedOracleFamily lam K L))
      (t : Tag)
      (cms : List (Dig lam)) (x : Option X) (salt : Bits) (rtreq : Dig lam) (s : Shape) (A : RoundSplits s)
      (W : RoundsQueryLayout lam K s A) (embP : PlainPart s A → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ) (ph : Phase lam)
      (rts : List (Dig lam)) (pls : Plains s),
    (recomputeChain t cms x salt rtreq s A W embP i ph rts pls).det g =
      chainF g t cms x salt rtreq s A W embP i ph rts pls

def vd_forests : Prop :=
  ∀ (I X : Type) (lam K : ℕ) (L : BatchProtocolWithLeafBody I X) (g : Fam (TypedOracleCompiler.Compile.Batch.typedOracleFamily lam K L)),
    (∀ (F : Forest lam L) (s : List (Dig lam)), (runForest (K := K) F s).det g = runForestF g F s) ∧
    ∀ (Fs : List (Forest lam L)) (s : List (Dig lam)),
      (runForests (K := K) Fs s).det g = runForestsF g Fs s

def vd_req : Prop :=
  ∀ (I X : Type) (lam K : ℕ) (L : BatchProtocolWithLeafBody I X) (g : Fam (TypedOracleCompiler.Compile.Batch.typedOracleFamily lam K L))
      (depthReq : ℕ)
      (rtreq : Dig lam) (slot : ℕ) (path : List (Dig lam)) (c : Dig lam) (rs : Bits),
    (reqCheck (L := L) (K := K) depthReq rtreq slot path c rs).det g =
      reqCheckF g depthReq rtreq slot path c rs

def vd_after : Prop :=
  ∀ (I X : Type) (lam K : ℕ) (L : BatchProtocolWithLeafBody I X) (g : Fam (TypedOracleCompiler.Compile.Batch.typedOracleFamily lam K L))
      (Y : Type) (E : ExtSpec)
      (Q : BatchInteractiveOracleProof Y E) (wq : ProtocolQueryLayout lam K Q)
      (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L) (embE : E.Sym → Body L)
      (depthReq : ℕ) (cms : List (Dig lam)) (x : Y) (π : OneProtocolProof lam Q) (ρ : Rho Q.loc.shape)
      (rts : RootsOfChain lam Q.loc.shape) (ph : Phase lam),
    (checkPrunedOpenings Q wq embS embE depthReq cms x π ρ rts ph).det g =
      afterBOF g Q wq embS embE depthReq cms x π ρ rts ph

/-- THE RUN OF THE COMPILED VERIFIER IS verifyF. -/
def vd_verify : Prop :=
  ∀ (I X : Type) (lam K : ℕ) (L : BatchProtocolWithLeafBody I X) (g : Fam (TypedOracleCompiler.Compile.Batch.typedOracleFamily lam K L))
      (Y : Type) (E : ExtSpec)
      (sMT sFS : ℕ) (t : Tag) (Q : BatchInteractiveOracleProof Y E) (wq : ProtocolQueryLayout lam K Q)
      (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L)
      (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X)
      (embE : E.Sym → Body L) (depthReq : ℕ) (cms : List (Dig lam)) (x : Y) (π : OneProtocolProof lam Q),
    (verifyOneProtocol sMT sFS t Q wq embS embP xin embE depthReq cms x π).det g =
      verifyF g sMT sFS t Q wq embS embP xin embE depthReq cms x π

end Spec
end TypedOracleCompiler.Run
