-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/TwinDet.lean: the compiled verifier of one slot at the protocol of a skeleton of rounds, run
under fixed oracle functions, is a plain function of these functions that recurses on the skeleton
(`verifyTF`).

Definitions and statements (each a `Prop` in `Run.Twin.Spec`); the proofs are in
Run/TwinDetProofs.lean. Generic: no format, no hash, no toy.
`Compile.Batch.verifyOneProtocol` (Compile/Batch/Verifier.lean) is the compiled verifier of one slot of a
batch protocol: on one argument string it recomputes the Fiat-Shamir hash chain, tests the string's
format, checks the Merkle openings and, if the chain has joined, the path in the request tree, and
runs the protocol's `accept`. It is written as a tree of oracle queries (`OComp`); `OComp.det g`
(Rom/Cache.lean) is the result of the run under the oracle functions g in which every coin toss
yields 0.
A skeleton (`RS`, `PS`, Run/TwinDefs.lean) has the fields of a round, or of a batch protocol, with
the instance `Fintype Chal` behind a function of `Unit`; `P.up` is the skeleton's protocol.
`verifyT` (Run/TwinDefs.lean) is the analogue of `verifyOneProtocol` that recurses on the skeleton. (`Twin`
in these files' names: `verifyOneProtocol` written again so that it recurses on a skeleton.)
Many statements of this library are written twice: a definition in the namespace `Spec` states a
proposition, and a theorem of the same name outside that namespace proves it (lean/GLOSSARY.md).

Why: two things stand between `verifyOneProtocol` and a run by an evaluator at rounds with very many verifier
messages. It recurses on the list of rounds, whose records hold the list of all verifier messages;
for this Run/TwinDefs.lean and Run/TwinTie.lean have the skeleton. And it is a tree of queries; for
this Run/VerifyDet.lean has a plain function, for `verifyOneProtocol` itself. Here both together: a function
without a monad that recurses on the skeleton.

Main names:
  `chainTF g early late`: the chain: `chainF` of Run/VerifyDet.lean, with `(S : List RS)` for
    `(s : Shape)`, types at `up S`, and the two fields `early`, `late` of the interface L as
    arguments.
  `verifyTF g`, `Spec.twd_twin`, `Spec.twd_verify`: their doc comments tell them.
  `afterBOTF g`: what follows the chain. It uses `forestsOfT` and `mkTrT` of Run/TwinDefs.lean. The
    walks up the Merkle trees and the request tree are made by `runForestsF g`, `reqPartF g` of
    Run/VerifyDet.lean, which are not written again here (a shape stands in their types alone). The
    last test is the skeleton's `accept`.
  `Spec.twd_chain`, `Spec.twd_after`: `chainTF g`, `afterBOTF g` are the runs under g of `chainT`,
    `afterBOT`, the parts of `verifyT`, at all arguments.

Notation:
  `sMT`, `sFS`: the length of the salt of a leaf, and of the salt of a chain
    (Compile/Batch/Verifier.lean);
  `early`: what of an instance is written into a chain's first query (`BatchProtocol.early`, Iop/Batch.lean);
  `late`: the round into whose query the whole instance is written (`BatchProtocol.late`, Iop/Batch.lean);
  `embS`, `embP`, `embE`: how symbols and plain parts are written into queries (`verifyB`,
    Compile/Batch/Verifier.lean);
  `xin`: a map; `xin x` is `recomputeChain`'s `x`, the whole instance (Compile/Batch/Verifier.lean);
  `depthReq`: depth of the request tree (`QueryLayout.depthReq`, Iop/BatchWire.lean);
  `cms`: the external roots (`verifyB`, Compile/Batch/Verifier.lean).

Limits: this file says nothing on soundness: equations between ways of computing one truth value.
The values agree; the number of calls of g need not ("and" on truth values is lazy in compiled
code). This file does not say that an evaluator runs `verifyTF` fast, or at all, at a given
protocol: it still evaluates whatever it is handed (reads, accept, wires, g); where these are
functions that hash anew at every call, so does the run. Nothing here is made faster. On what the
evaluator builds at `flatF` and `readsF`, which `afterBOTF` calls, see Limits in the head of
Run/TwinDefs.lean.

Terms: lean/GLOSSARY.md.
-/
import Run.TwinDefs
import Run.VerifyDet

set_option autoImplicit false

namespace Run.Twin
open Iop Rom Compile Compile.Batch

section
variable {I X : Type} {lam K : ℕ} {L : BatchProtocol I X} (g : Fam (Batch.spec lam K L))

/-- The chain on the skeleton, as a function of the oracle functions: `chainT` (Run/TwinDefs.lean)
with each query replaced by the value of g at it. -/
def chainTF (early : X → X) (late : Option ℕ) (t : Tag) (cms : List (Dig lam)) (x : Option X)
    (salt : Bits) (rtreq : Dig lam) :
    (S : List RS) → (A : RoundSplits (up S)) → RoundsQueryLayout lam K (up S) A →
    (PlainPart (up S) A → PlainPart (shapeOf L t) (annOf L t)) → ℕ → Phase lam → List (Dig lam) → Plains (up S) →
    Option (Rho (up S) × RootsOfChain lam (up S) × Phase lam)
  | [], _, _, _, _, ph, _, _ => some ((), (), ph)
  | _ :: S, (a, A), (w, W), embP, i, ph, rts, (pl, pls) =>
      match actOf cms (x.map early) salt a.kind ph with
      | some (.one h true next) =>
          match takeRt w.hasJ rts with
          | some (rt, rts') =>
              let ans : (Fin K → Dig lam) × Dig lam :=
                g (Batch.OracleName.fb t)
                  (⟨i, h.withLate (lateT late i x), rt,
                    embP (.inl (.inr (a.plain pl).2))⟩ : FbIn lam L t)
              (chainTF early late t cms x salt rtreq S A W (fun z => embP (.inr z)) (i + 1)
                  (next (List.ofFn ans.2)) rts' pls).map
                fun z => ((w.chal ans.1, z.1), ((none, some rt), z.2.1), z.2.2)
          | none => none
      | some (.one h false next) =>
          match takeRt w.has0 rts with
          | some (rt, rts') =>
              let ans : (Fin K → Dig lam) × Dig lam :=
                g (Batch.OracleName.fb t) (⟨i, h, rt, embP (.inl (.inl (a.plain pl).1))⟩ : FbIn lam L t)
              (chainTF early late t cms x salt rtreq S A W (fun z => embP (.inr z)) (i + 1)
                  (next (List.ofFn ans.2)) rts' pls).map
                fun z => ((w.chal ans.1, z.1), ((some rt, none), z.2.1), z.2.2)
          | none => none
      | some (.join ρ) =>
          match takeRt w.hasJ rts with
          | some (rtj, rts1) =>
              match takeRt w.has0 rts1 with
              | some (rt0, rts') =>
                  let c : Dig lam :=
                    g (Batch.OracleName.g t) (⟨i, ρ, rtj, embP (.inl (.inr (a.plain pl).2))⟩ : JoiningRoundQuery lam L t)
                  let ans : (Fin K → Dig lam) × Dig lam :=
                    g (Batch.OracleName.fb t)
                      (⟨i, .f4 cms (List.ofFn rtreq), rt0,
                        embP (.inl (.inl (a.plain pl).1))⟩ : FbIn lam L t)
                  (chainTF early late t cms x salt rtreq S A W (fun z => embP (.inr z)) (i + 1)
                      (.shr (List.ofFn ans.2) c) rts' pls).map
                    fun z => ((w.chal ans.1, z.1), ((some rt0, some rtj), z.2.1), z.2.2)
              | none => none
          | none => none
      | none => none

variable {Y : Type} {E : ExtSpec}

/-- What follows the chain. -/
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

/-- `verifyT` (Run/TwinDefs.lean) as a function of the oracle functions. -/
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
  ∀ (I X : Type) (lam K : ℕ) (L : BatchProtocol I X) (g : Fam (Batch.spec lam K L)) (early : X → X)
      (late : Option ℕ) (t : Tag) (cms : List (Dig lam)) (x : Option X) (salt : Bits)
      (rtreq : Dig lam) (S : List RS) (A : RoundSplits (up S)) (W : RoundsQueryLayout lam K (up S) A)
      (embP : PlainPart (up S) A → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ) (ph : Phase lam)
      (rts : List (Dig lam)) (pls : Plains (up S)),
    (chainT early late t cms x salt rtreq S A W embP i ph rts pls).det g =
      chainTF g early late t cms x salt rtreq S A W embP i ph rts pls

def twd_after : Prop :=
  ∀ (I X : Type) (lam K : ℕ) (L : BatchProtocol I X) (g : Fam (Batch.spec lam K L)) (Y : Type) (E : ExtSpec)
      (P : PS Y E) (wq : ProtocolQueryLayout lam K P.up) (embS : (p : OPos (up P.S)) → OSym (up P.S) p → Body L)
      (embE : E.Sym → Body L) (depthReq : ℕ) (cms : List (Dig lam)) (x : Y) (π : OneProtocolProof lam P.up)
      (ρ : Rho (up P.S)) (rts : RootsOfChain lam (up P.S)) (ph : Phase lam),
    (afterBOT P wq embS embE depthReq cms x π ρ rts ph).det g =
      afterBOTF g P wq embS embE depthReq cms x π ρ rts ph

/-- States: the run of `verifyT` under g is `verifyTF g`, at all arguments. -/
def twd_twin : Prop :=
  ∀ (I X : Type) (lam K : ℕ) (L : BatchProtocol I X) (g : Fam (Batch.spec lam K L)) (Y : Type) (E : ExtSpec)
      (early : X → X) (late : Option ℕ) (sMT sFS : ℕ) (t : Tag) (P : PS Y E)
      (wq : ProtocolQueryLayout lam K P.up) (embS : (p : OPos (up P.S)) → OSym (up P.S) p → Body L)
      (embP : PlainPart (up P.S) P.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X)
      (embE : E.Sym → Body L) (depthReq : ℕ) (cms : List (Dig lam)) (x : Y) (π : OneProtocolProof lam P.up),
    (verifyT early late sMT sFS t P wq embS embP xin embE depthReq cms x π).det g =
      verifyTF g early late sMT sFS t P wq embS embP xin embE depthReq cms x π

/-- States: the run under g of `verifyOneProtocol` at the skeleton's protocol `P.up` is `verifyTF g` at
`L.early`, `L.late` and P, at all arguments. -/
def twd_verify : Prop :=
  ∀ (I X : Type) (lam K : ℕ) (L : BatchProtocol I X) (g : Fam (Batch.spec lam K L)) (Y : Type) (E : ExtSpec)
      (sMT sFS : ℕ) (t : Tag) (P : PS Y E) (wq : ProtocolQueryLayout lam K P.up)
      (embS : (p : OPos (up P.S)) → OSym (up P.S) p → Body L)
      (embP : PlainPart (up P.S) P.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X)
      (embE : E.Sym → Body L) (depthReq : ℕ) (cms : List (Dig lam)) (x : Y) (π : OneProtocolProof lam P.up),
    (verifyOneProtocol sMT sFS t P.up wq embS embP xin embE depthReq cms x π).det g =
      verifyTF g L.early L.late sMT sFS t P wq embS embP xin embE depthReq cms x π

end Spec
end Run.Twin
