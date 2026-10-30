-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Run/TwinDet.lean.
Run/TwinDet.lean: THE TWIN OF THE COMPILED VERIFIER OF ONE SLOT ON A SKELETON OF ROUNDS
(Run/TwinDefs.lean: verifyT), RUN UNDER FIXED ORACLE FUNCTIONS, IS A PLAIN FUNCTION OF THESE
FUNCTIONS; AND SO IS THE LIBRARY'S VERIFIER AT THE SKELETON'S PROTOCOL. Definitions and statements
(Run.Twin.Spec.twd_*); the proofs are in Run/TwinDetProofs.lean. Generic: no format, no hash, no
toy.
WHY. Two things stand between Compile.Batch.verifyOneProtocol and a run by an evaluator at rounds with very
many verifier messages: it recurses on the list of rounds, whose records hold the list of all
verifier messages (cured by the skeleton: Run/TwinDefs.lean, Run/TwinTie.lean), and it is a tree of
queries (cured for the library's own text in Run/VerifyDet.lean). Here both cures together: a
function WITHOUT A MONAD that recurses on the SKELETON.
   chainTF g early late ..    the chain: Run/VerifyDet.lean's chainF, with "(S : List RS)" for "(s :
                              Shape)", types at up S, and the ambient interface's two fields early,
                              late as arguments
   afterBOTF g ..             what follows the chain: the twin's forestsOfT and mkTrT; the walks and
                              the request tree by Run/VerifyDet.lean's runForestsF g, reqPartF g (a
                              shape stands in their types alone); the skeleton's decision
   verifyTF g ..          chainTF;  the twin's strictBT;  afterBOTF
   Spec.twd_chain, twd_after    each part is the run of its part of the twin
   Spec.twd_twin           (verifyT early late sMT sFS t P wq embS embP xin embE depthReq cms x
                           π).det g = verifyTF g early late sMT sFS t P wq embS embP xin embE
                           depthReq cms x π
   Spec.twd_verify         (verifyOneProtocol sMT sFS t P.up wq embS embP xin embE depthReq cms x π).det g =
                           verifyTF g L.early L.late sMT sFS t P wq embS embP xin embE depthReq cms
                           x π (with Run/TwinTie.lean: verifyT_eq)
WHAT IS NOT SAID. Nothing on soundness: equations between ways of computing one truth value. The
values agree; the number of calls of g need not ("and" on truth values is lazy in compiled code).
THAT AN EVALUATOR RUNS verifyTF FAST, OR AT ALL, AT A GIVEN PROTOCOL: it still evaluates whatever it
is handed (reads, accept, wires, g); where these are functions that hash anew at every call, so does
the run. Nothing here is made faster.

Terms: lean/GLOSSARY.md.

-/
import Run.TwinDet
import OnBytes.TypedOracleCompiler.Run.TwinDefs
import OnBytes.TypedOracleCompiler.Run.VerifyDet

set_option autoImplicit false

namespace TypedOracleCompiler.Run.Twin
open TypedOracleCompiler.Iop Rom _root_.Compile TypedOracleCompiler.Compile.Batch
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run _root_.Run.Twin

section
variable {I X : Type} {lam K : ℕ} {L : BatchProtocolWithLeafBody I X} (g : Fam (TypedOracleCompiler.Compile.Batch.typedOracleFamily lam K L))

/-- The chain on the skeleton, as a function of the oracle functions. -/
def chainTF (early : X → X) (late : Option ℕ) (t : Tag) (cms : List (Dig lam)) (x : Option X)
    (salt : Bits) (rtreq : Dig lam) :
    (S : List RS) → (A : RoundSplits (up S)) → RoundsQueryLayout lam K (up S) A →
    (PlainPart (up S) A → PlainPart (shapeOf L t) (annOf L t)) → ℕ → Phase lam → List (Dig lam) → Plains (up S) →
    Option (Rho (up S) × RootsOfChain lam (up S) × Phase lam)
  | [], _, _, _, _, ph, _, _ => some ((), (), ph)
  | _ :: S, (a, A), (w, W), embP, i, ph, rts, (pl, pls) =>
      match actOf cms (x.map early) salt a.kind ph with
      | some (.one h true next) =>
          match takeRt w.depthJ.length rts with
          | some (rt, rts') =>
              let ans : (Fin K → Dig lam) × Dig lam :=
                g (TypedOracleCompiler.Compile.Batch.OracleName.fb t)
                  (⟨i, h.withLate (lateT late i x), rt,
                    embP (.inl (.inr (a.plain pl).2))⟩ : FbIn lam L t)
              (chainTF early late t cms x salt rtreq S A W (fun z => embP (.inr z)) (i + 1)
                  (next (List.ofFn ans.2)) rts' pls).map
                fun z => ((w.chal ans.1, z.1), ((none, some rt), z.2.1), z.2.2)
          | none => none
      | some (.one h false next) =>
          match takeRt w.depth0.length rts with
          | some (rt, rts') =>
              let ans : (Fin K → Dig lam) × Dig lam :=
                g (TypedOracleCompiler.Compile.Batch.OracleName.fb t)
                    (⟨i, h, rt, embP (.inl (.inl (a.plain pl).1))⟩ : FbIn lam L t)
              (chainTF early late t cms x salt rtreq S A W (fun z => embP (.inr z)) (i + 1)
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
                  (chainTF early late t cms x salt rtreq S A W (fun z => embP (.inr z)) (i + 1)
                      (.shr (List.ofFn ans.2) c) rts' pls).map
                    fun z => ((w.chal ans.1, z.1), ((some rt0, some rtj), z.2.1), z.2.2)
              | none => none
          | none => none
      | none => none

variable {Y : Type} {E : ExtSpec}

/-- what follows the chain -/
def afterBOTF (P : PS Y E) (wq : ProtocolQueryLayout lam K P.up)
    (embS : (p : OPos (up P.S)) → OSym (up P.S) p → Body L) (embE : E.Sym → Body L)
    (depthReq : ℕ) (cms : List (Dig lam)) (x : Y) (π : OneProtocolProof lam P.up) (ρ : Rho (up P.S))
    (rts : RootsOfChain lam (up P.S)) (ph : Phase lam) : Bool :=
  match forestsOfT P wq embS embE cms x π ρ rts with
  | some Fs =>
      if (flatF Fs).length ≤ wq.nOpen ∧
          (flatF Fs).all (fun c => c.wellFormed && decide (c.depth ≤ wq.maxDepth)) then
        runForestsF g Fs (readsF Fs) && reqPartF g depthReq π ph &&
          P.accept x (wq.ext.build fun p => (π.ext p).map Opening.sym)
            (mkTrT P.S P.ann wq.sh rts π.plains ρ π.opens)
      else false
  | none => false

/-- THE TWIN AS A FUNCTION OF THE ORACLE FUNCTIONS. -/
def verifyTF (early : X → X) (late : Option ℕ) (sMT sFS : ℕ) (t : Tag) (P : PS Y E)
    (wq : ProtocolQueryLayout lam K P.up) (embS : (p : OPos (up P.S)) → OSym (up P.S) p → Body L)
    (embP : PlainPart (up P.S) P.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X)
    (embE : E.Sym → Body L) (depthReq : ℕ) (cms : List (Dig lam)) (x : Y) (π : OneProtocolProof lam P.up) :
    Bool :=
  match chainTF g early late t cms (xin x) π.salt π.rtreq P.S P.ann wq.sh embP 0
      .first π.roots π.plains with
  | none => false
  | some (ρ, rts, ph) =>
    if strictBT sMT sFS P wq depthReq x π ρ rts ph then
      afterBOTF g P wq embS embE depthReq cms x π ρ rts ph
    else false

end

namespace Spec

def twd_chain : Prop :=
  ∀ (I X : Type) (lam K : ℕ) (L : BatchProtocolWithLeafBody I X) (g : Fam (TypedOracleCompiler.Compile.Batch.typedOracleFamily lam K L))
      (early : X → X)
      (late : Option ℕ) (t : Tag) (cms : List (Dig lam)) (x : Option X) (salt : Bits)
      (rtreq : Dig lam) (S : List RS) (A : RoundSplits (up S)) (W : RoundsQueryLayout lam K (up S) A)
      (embP : PlainPart (up S) A → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ) (ph : Phase lam)
      (rts : List (Dig lam)) (pls : Plains (up S)),
    (chainT early late t cms x salt rtreq S A W embP i ph rts pls).det g =
      chainTF g early late t cms x salt rtreq S A W embP i ph rts pls

def twd_after : Prop :=
  ∀ (I X : Type) (lam K : ℕ) (L : BatchProtocolWithLeafBody I X) (g : Fam (TypedOracleCompiler.Compile.Batch.typedOracleFamily lam K L))
      (Y : Type) (E : ExtSpec)
      (P : PS Y E) (wq : ProtocolQueryLayout lam K P.up) (embS : (p : OPos (up P.S)) → OSym (up P.S) p → Body L)
      (embE : E.Sym → Body L) (depthReq : ℕ) (cms : List (Dig lam)) (x : Y) (π : OneProtocolProof lam P.up)
      (ρ : Rho (up P.S)) (rts : RootsOfChain lam (up P.S)) (ph : Phase lam),
    (afterBOT P wq embS embE depthReq cms x π ρ rts ph).det g =
      afterBOTF g P wq embS embE depthReq cms x π ρ rts ph

/-- The run of the twin is verifyTF. -/
def twd_twin : Prop :=
  ∀ (I X : Type) (lam K : ℕ) (L : BatchProtocolWithLeafBody I X) (g : Fam (TypedOracleCompiler.Compile.Batch.typedOracleFamily lam K L))
      (Y : Type) (E : ExtSpec)
      (early : X → X) (late : Option ℕ) (sMT sFS : ℕ) (t : Tag) (P : PS Y E)
      (wq : ProtocolQueryLayout lam K P.up) (embS : (p : OPos (up P.S)) → OSym (up P.S) p → Body L)
      (embP : PlainPart (up P.S) P.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X)
      (embE : E.Sym → Body L) (depthReq : ℕ) (cms : List (Dig lam)) (x : Y) (π : OneProtocolProof lam P.up),
    (verifyT early late sMT sFS t P wq embS embP xin embE depthReq cms x π).det g =
      verifyTF g early late sMT sFS t P wq embS embP xin embE depthReq cms x π

/-- THE RUN OF THE LIBRARY'S VERIFIER AT THE SKELETON'S PROTOCOL IS verifyTF. -/
def twd_verify : Prop :=
  ∀ (I X : Type) (lam K : ℕ) (L : BatchProtocolWithLeafBody I X) (g : Fam (TypedOracleCompiler.Compile.Batch.typedOracleFamily lam K L))
      (Y : Type) (E : ExtSpec)
      (sMT sFS : ℕ) (t : Tag) (P : PS Y E) (wq : ProtocolQueryLayout lam K P.up)
      (embS : (p : OPos (up P.S)) → OSym (up P.S) p → Body L)
      (embP : PlainPart (up P.S) P.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X)
      (embE : E.Sym → Body L) (depthReq : ℕ) (cms : List (Dig lam)) (x : Y) (π : OneProtocolProof lam P.up),
    (verifyOneProtocol sMT sFS t P.up wq embS embP xin embE depthReq cms x π).det g =
      verifyTF g L.early L.late sMT sFS t P wq embS embP xin embE depthReq cms x π

end Spec
end TypedOracleCompiler.Run.Twin
