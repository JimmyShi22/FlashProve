-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Run/TwinDefs.lean.
Run/TwinDefs.lean: A TWIN OF THE COMPILED VERIFIER OF ONE SLOT (Compile.Batch.verifyOneProtocol) ON A
SKELETON OF THE PROTOCOL: A FIRST STEP TOWARDS A FORM THAT THE EVALUATOR CAN RUN AT ROUNDS WITH VERY
MANY VERIFIER MESSAGES. Definitions only. That the twin IS verifyOneProtocol, as a tree of queries:
Run/TwinTie.lean.
WHY. A round (Iop.Round) carries the instance Fintype Chal AS DATA: at run time the list of all
verifier messages. verifyOneProtocol recurses on the list of rounds, so compiled Lean, which is strict,
builds every round, and with it that list, at every run: linear in the number of verifier messages;
hopeless for one drawn field element. (The kernel is lazy and does not build it.) THE SKELETON. RS:
the fields of a round, THE INSTANCE BEHIND A FUNCTION OF Unit (finT), which is made and never
called. RS.up r : the round; up S : the shape. BOTH STAND IN TYPES ONLY in what follows. For a round
written in the usual way, up of its skeleton is that round by definition.
    PS Y E          the skeleton of a batch protocol: S, blinded, extReads, reads, accept, ann; P.up
                    : BatchInteractiveOracleProof Y E
WHAT IS WRITTEN AGAIN: what matches on the shape or reads a data field of a round or of the ambient
interface: the library's texts, with "(S : List RS)" for "(s : Shape)" and types at up S:
    effPlainT, effPlainsT, mkTrT, countT, strictST, forestsT, chainT (early, late: the interface's
    two fields, handed over as arguments), chainQT, forestsOfT, afterFT, afterBOT, strictBT, verifyT
ALL OTHER HELPERS ARE THE LIBRARY'S OWN. THAT WAS NOT ENOUGH FOR A RUN: OBSERVED SINCE, with a trace
in a round's instance: at several of these helpers (Forest.split, flatF, readsF, runForests,
forestExt, reqCheck, reqPart; also RAnn.allLocal) the evaluator builds the interface, the protocol
or the round though it stands in their types alone: SO verifyT STILL BUILDS THE LISTS. THE FORM THAT
RUNS IS Run/ThinDefs.lean: verifyP. This file stays for its tie in the monad (Run/TwinTie.lean), on
which that form's tie rests.
WHAT IS NOT SAID. That verifyT can be run at a round with very many verifier messages: it cannot
(above).

Terms: lean/GLOSSARY.md.

-/
import Run.TwinDefs
import OnBytes.TypedOracleCompiler.Compile.Batch.Verifier

set_option autoImplicit false

namespace TypedOracleCompiler.Run.Twin
open TypedOracleCompiler.Iop Rom _root_.Compile TypedOracleCompiler.Compile.Batch
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run _root_.Run.Twin
export _root_.Run.Twin (RS up PS lateT)

variable {I X : Type} {lam K : ℕ} {L : BatchProtocolWithLeafBody I X}

def effPlainT (r : RS) (a : RAnn r.up) (rt : RtC lam × RtC lam) (pl : r.Plain) : r.Plain :=
  a.plain.symm (if rt.1.isSome then (a.plain pl).1 else (a.plain r.dPlain).1,
    if rt.2.isSome then (a.plain pl).2 else (a.plain r.dPlain).2)

def effPlainsT : (S : List RS) → RoundSplits (up S) → RootsOfChain lam (up S) → Plains (up S) → Plains (up S)
  | [], _, _, _ => ()
  | r :: S, (a, A), (rt, rts), (pl, pls) => (effPlainT r a rt pl, effPlainsT S A rts pls)

def mkTrT :
    (S : List RS) → (A : RoundSplits (up S)) → RoundsQueryLayout lam K (up S) A → RootsOfChain lam (up S) → Plains (up S) →
    Rho (up S) → ((p : OPos (up S)) → Option (Opening lam (OSym (up S) p))) → Tr (up S)
  | [], _, _, _, _, _, _ => ()
  | r :: S, (a, A), (w, W), (rt, rts), (pl, pls), (c, ρ), f =>
      ((w.pt.ofSyms fun p => match rootAt w rt p, f (.inl p) with
          | true, some op => op.sym
          | _, _ => w.pt.zero p, effPlainT r a rt pl), c, mkTrT S A W rts pls ρ fun p => f (.inr p))

def countT : (S : List RS) → RootsOfChain lam (up S) → ℕ
  | [], _ => 0
  | _ :: S, (rt, rts) => (rt.1.getD []).length + (rt.2.getD []).length + countT S rts

def strictST (sMT : ℕ) :
    (S : List RS) → (A : RoundSplits (up S)) → RoundsQueryLayout lam K (up S) A → RootsOfChain lam (up S) →
    (OPos (up S) → Bool) → ((p : OPos (up S)) → Option (Opening lam (OSym (up S) p))) → Bool
  | [], _, _, _, _, _ => true
  | _ :: S, (_, A), (w, W), (rt, rts), isRead, f =>
      strictTrees sMT w.posAt0 w.depth0 (rt.1.getD [])
        (fun p => isRead (.inl p)) (fun p => f (.inl p)) &&
      strictTrees sMT w.posAtJ w.depthJ (rt.2.getD [])
        (fun p => isRead (.inl p)) (fun p => f (.inl p)) &&
      strictST sMT S A W rts (fun p => isRead (.inr p)) (fun p => f (.inr p))

def forestsT :
    (S : List RS) → (A : RoundSplits (up S)) → RoundsQueryLayout lam K (up S) A →
    ((p : OPos (up S)) → OSym (up S) p → Body L) → RootsOfChain lam (up S) → (OPos (up S) → Bool) →
    ((p : OPos (up S)) → Option (Opening lam (OSym (up S) p))) → Option (List (Forest lam L))
  | [], _, _, _, _, _, _ => some []
  | _ :: S, (_, A), (w, W), emb, (rt, rts), isRead, f =>
      match checksTrees w.posAt0 (fun p => emb (.inl p))
          (fun p => isRead (.inl p)) (fun p => f (.inl p)) 0 w.depth0 (rt.1.getD []),
        checksTrees w.posAtJ (fun p => emb (.inl p))
          (fun p => isRead (.inl p)) (fun p => f (.inl p)) 0 w.depthJ (rt.2.getD []),
        forestsT S A W (fun p => emb (.inr p)) rts
          (fun p => isRead (.inr p)) (fun p => f (.inr p)) with
      | some a, some b, some c =>
          some (Compile.Batch.forestsT w.pr0 a ++ (Compile.Batch.forestsT w.prJ b ++ c))
      | _, _, _ => none

def chainT (early : X → X) (late : Option ℕ) (t : Tag) (cms : List (Dig lam)) (x : Option X)
    (salt : Bits) (rtreq : Dig lam) :
    (S : List RS) → (A : RoundSplits (up S)) → RoundsQueryLayout lam K (up S) A →
    (PlainPart (up S) A → PlainPart (shapeOf L t) (annOf L t)) → ℕ → Phase lam → List (Dig lam) → Plains (up S) →
    TypedOracleComputation lam K L (Option (Rho (up S) × RootsOfChain lam (up S) × Phase lam))
  | [], _, _, _, _, ph, _, _ => pure (some ((), (), ph))
  | _ :: S, (a, A), (w, W), embP, i, ph, rts, (pl, pls) =>
      match actOf cms (x.map early) salt a.kind ph with
      | some (.one h true next) =>
          match takeRt w.depthJ.length rts with
          | some (rt, rts') => do
              let ans ← askTypedOracle (L := L) (K := K) (OracleName.fb t)
                (⟨i, h.withLate (lateT late i x), rt,
                  embP (.inl (.inr (a.plain pl).2))⟩ : FbIn lam L t)
              let r ← chainT early late t cms x salt rtreq S A W (fun z => embP (.inr z)) (i + 1)
                (next (List.ofFn ans.2)) rts' pls
              pure (r.map fun z => ((w.chal ans.1, z.1), ((none, some rt), z.2.1), z.2.2))
          | none => pure none
      | some (.one h false next) =>
          match takeRt w.depth0.length rts with
          | some (rt, rts') => do
              let ans ← askTypedOracle (L := L) (K := K) (OracleName.fb t)
                (⟨i, h, rt, embP (.inl (.inl (a.plain pl).1))⟩ : FbIn lam L t)
              let r ← chainT early late t cms x salt rtreq S A W (fun z => embP (.inr z)) (i + 1)
                (next (List.ofFn ans.2)) rts' pls
              pure (r.map fun z => ((w.chal ans.1, z.1), ((some rt, none), z.2.1), z.2.2))
          | none => pure none
      | some (.join ρ) =>
          match takeRt w.depthJ.length rts with
          | some (rtj, rts1) =>
              match takeRt w.depth0.length rts1 with
              | some (rt0, rts') => do
                  let c ← askTypedOracle (L := L) (K := K) (OracleName.g t)
                    (⟨i, ρ, rtj, embP (.inl (.inr (a.plain pl).2))⟩ : JoiningRoundQuery lam L t)
                  let ans ← askTypedOracle (L := L) (K := K) (OracleName.fb t)
                    (⟨i, .f4 cms (List.ofFn rtreq), rt0,
                      embP (.inl (.inl (a.plain pl).1))⟩ : FbIn lam L t)
                  let r ← chainT early late t cms x salt rtreq S A W (fun z => embP (.inr z))
                    (i + 1) (.shr (List.ofFn ans.2) c) rts' pls
                  pure (r.map fun z => ((w.chal ans.1, z.1), ((some rt0, some rtj), z.2.1), z.2.2))
              | none => pure none
          | none => pure none
      | none => pure none

variable {Y : Type} {E : ExtSpec}

def chainQT (early : X → X) (late : Option ℕ) (t : Tag) (P : PS Y E) (wq : ProtocolQueryLayout lam K P.up)
    (embP : PlainPart (up P.S) P.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X)
    (cms : List (Dig lam)) (x : Y) (π : OneProtocolProof lam P.up) :
    TypedOracleComputation lam K L (Option (Rho (up P.S) × RootsOfChain lam (up P.S) × Phase lam)) :=
  chainT early late t cms (xin x) π.salt π.rtreq P.S P.ann wq.sh embP 0 .first π.roots π.plains

def forestsOfT (P : PS Y E) (wq : ProtocolQueryLayout lam K P.up)
    (embS : (p : OPos (up P.S)) → OSym (up P.S) p → Body L) (embE : E.Sym → Body L)
    (cms : List (Dig lam)) (x : Y) (π : OneProtocolProof lam P.up) (ρ : Rho (up P.S)) (rts : RootsOfChain lam (up P.S)) :
    Option (List (Forest lam L)) :=
  haveI := wq.decO
  haveI := wq.ext.dec
  match forestsT P.S P.ann wq.sh embS rts
          (fun p => decide (p ∈ P.reads x ρ (effPlainsT P.S P.ann rts π.plains))) π.opens,
        forestExt wq.ext embE cms (fun p => decide (p ∈ P.extReads x ρ)) π.ext with
  | some a, some b => some (a ++ b)
  | _, _ => none

def afterFT (P : PS Y E) (wq : ProtocolQueryLayout lam K P.up) (depthReq : ℕ) (x : Y)
    (π : OneProtocolProof lam P.up) (ρ : Rho (up P.S)) (rts : RootsOfChain lam (up P.S)) (ph : Phase lam)
    (Fs : List (Forest lam L)) (s : List (Dig lam)) : TypedOracleComputation lam K L Bool :=
  (runForests Fs s).bind fun ok =>
  (reqPart depthReq π ph).bind fun okr =>
  pure (ok && okr && P.accept x (wq.ext.build fun p => (π.ext p).map Opening.sym)
    (mkTrT P.S P.ann wq.sh rts π.plains ρ π.opens))

def afterBOT (P : PS Y E) (wq : ProtocolQueryLayout lam K P.up)
    (embS : (p : OPos (up P.S)) → OSym (up P.S) p → Body L) (embE : E.Sym → Body L)
    (depthReq : ℕ) (cms : List (Dig lam)) (x : Y) (π : OneProtocolProof lam P.up) (ρ : Rho (up P.S))
    (rts : RootsOfChain lam (up P.S)) (ph : Phase lam) : TypedOracleComputation lam K L Bool :=
  match forestsOfT P wq embS embE cms x π ρ rts with
  | some Fs =>
      if (flatF Fs).length ≤ wq.nOpen ∧
          (flatF Fs).all (fun c => c.wellFormed && decide (c.depth ≤ wq.maxDepth)) then
        afterFT P wq depthReq x π ρ rts ph Fs (readsF Fs)
      else pure false
  | none => pure false

def strictBT (sMT sFS : ℕ) (P : PS Y E) (wq : ProtocolQueryLayout lam K P.up) (depthReq : ℕ) (x : Y)
    (π : OneProtocolProof lam P.up) (ρ : Rho (up P.S)) (rts : RootsOfChain lam (up P.S)) (ph : Phase lam) : Bool :=
  haveI := wq.decO
  haveI := wq.ext.dec
  decide (π.salt.length = sFS) && decide (π.roots.length ≤ countT P.S rts) &&
    strictST sMT P.S P.ann wq.sh rts
      (fun p => decide (p ∈ P.reads x ρ (effPlainsT P.S P.ann rts π.plains))) π.opens &&
    strictExt sMT wq.ext (fun p => decide (p ∈ P.extReads x ρ)) π.ext &&
    decide (π.slot < 2 ^ depthReq) && (ph.slotVal.isSome || π.path.isEmpty) &&
    (ph.slotVal.isSome || π.rsalt.isEmpty)

/-- THE TWIN. -/
def verifyT (early : X → X) (late : Option ℕ) (sMT sFS : ℕ) (t : Tag) (P : PS Y E)
    (wq : ProtocolQueryLayout lam K P.up) (embS : (p : OPos (up P.S)) → OSym (up P.S) p → Body L)
    (embP : PlainPart (up P.S) P.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X)
    (embE : E.Sym → Body L) (depthReq : ℕ) (cms : List (Dig lam)) (x : Y) (π : OneProtocolProof lam P.up) :
    TypedOracleComputation lam K L Bool :=
  (chainQT early late t P wq embP xin cms x π).bind fun r =>
    match r with
    | none => pure false
    | some (ρ, rts, ph) =>
      if strictBT sMT sFS P wq depthReq x π ρ rts ph then
        afterBOT P wq embS embE depthReq cms x π ρ rts ph
      else pure false

end TypedOracleCompiler.Run.Twin
