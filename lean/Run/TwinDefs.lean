-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/TwinDefs.lean: the compiled verifier of one slot (`Compile.Batch.verifyOneProtocol`) written again so
that it recurses on a skeleton of the protocol (`verifyT`); that this is not enough for a run at
rounds with very many verifier messages: see Limits.

Definitions only. That `verifyT`, at the interface's `early` and `late`, is `verifyOneProtocol`, as a tree of
queries: Run/TwinTie.lean.
`Compile.Batch.verifyOneProtocol` (Compile/Batch/Verifier.lean): on one argument string it recomputes the
Fiat-Shamir hash chain, tests the string's format, checks the Merkle openings and, if the chain has
joined, the path in the request tree, and runs the protocol's `accept`. It is written as a tree of
oracle queries (`OComp`).

Why: a round (`Iop.Round`) carries the instance `Fintype Chal` as data: at run time the list of all
verifier messages. `verifyOneProtocol` recurses on the list of rounds, so compiled Lean, which is strict,
builds every round, and with it that list, at every run: linear in the number of verifier messages;
hopeless for one drawn field element. (The kernel is lazy and does not build it.)

Main names:
  `RS`: the skeleton of a round: the fields of a round, the instance behind a function of `Unit`
    (`finT`), which the functions below are meant never to call (`RS.up` calls it; see Limits).
    `RS.up r`, `up S` and `P.up` stand in types only in the functions that follow. For a round
    written in the usual way, `up` of its skeleton is that round by definition.
  `PS Y E`: the skeleton of a batch protocol: `S`, `blinded`, `extReads`, `reads`, `accept`, `ann`;
    `P.up : BatchInteractiveOracleProof Y E`.
  `effPlainT`, `effPlainsT`, `mkTrT`, `countT`, `strictST`, `forestsT`, `lateT`, `chainT`,
    `chainQT`, `forestsOfT`, `afterFT`, `afterBOT`, `strictBT`, `verifyT`: what is written again:
    what matches on the shape, reads a data field of a round, of the protocol or of the interface L,
    or calls a function that does. These are the library's definitions, with `(S : List RS)` for
    `(s : Shape)` and types at `up S`; in `chainT` the interface's two fields `early`, `late` are
    handed over as arguments. All other helpers are the library's own.

Limits: to write these functions again is not enough for a run. Observed, with a trace in a round's
instance: at several of the library's own helpers (`Forest.split`, `flatF`, `readsF`, `runForests`,
`forestExt`, `reqCheck`, `reqPart`; also `RAnn.allLocal`) the evaluator builds the interface, the
protocol or the round though it stands in their types alone: so `verifyT` builds the lists.
The form that runs is `verifyP` (Run/ThinDefs.lean; its limits: part 4 of that head). This file is
here for the equation between trees of queries in Run/TwinTie.lean, on which the proof of
`thin_verify` (Run/ThinTieProofs.lean) rests: `verifyP` at `fun _ => L`, `L.early`, `L.late` is the
run of `verifyOneProtocol` at `P.up` under the same oracle functions. This file does not say that `verifyT`
can be run at a round with very many verifier messages: it cannot (above).

Terms: lean/GLOSSARY.md.
-/
import Compile.Batch.Verifier

set_option autoImplicit false

namespace Run.Twin
open Iop Rom Compile Compile.Batch

/-- A round, its instance `Fintype Chal` behind a function of `Unit`. -/
structure RS where
  Orc    : Type
  Pos    : Type
  Sym    : Pos → Type
  rd     : Orc → (p : Pos) → Sym p
  Plain  : Type
  Chal   : Type
  dOrc   : Orc
  dPlain : Plain
  finT   : Unit → Fintype Chal
  ne     : Nonempty Chal

/-- The round of the skeleton r. -/
@[reducible] def RS.up (r : RS) : Round :=
  { Orc := r.Orc, Pos := r.Pos, Sym := r.Sym, rd := r.rd, Plain := r.Plain, Chal := r.Chal,
    dOrc := r.dOrc, dPlain := r.dPlain, finChalT := r.finT, neChal := r.ne }

/-- The shape of a list of skeletons of rounds. -/
@[reducible] def up : List RS → Shape
  | [] => []
  | r :: S => r.up :: up S

/-- The skeleton of a batch protocol. -/
structure PS (Y : Type) (E : ExtSpec) where
  S        : List RS
  blinded  : OPos (up S) → Bool
  extReads : Y → Rho (up S) → Finset E.Pos
  reads    : Y → Rho (up S) → Plains (up S) → Finset (OPos (up S))
  accept   : Y → E.Str → Tr (up S) → Bool
  ann      : RoundSplits (up S)

/-- The batch protocol of the skeleton P. -/
@[reducible] def PS.up {Y : Type} {E : ExtSpec} (P : PS Y E) : BatchInteractiveOracleProof Y E :=
  ⟨⟨Twin.up P.S, P.blinded, P.extReads, P.reads, P.accept⟩, P.ann⟩

variable {I X : Type} {lam K : ℕ} {L : BatchProtocol I X}

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
      ((w.pt.ofSyms fun p => match rootAt a rt p, f (.inl p) with
          | true, some op => op.sym
          | _, _ => w.pt.zero p, effPlainT r a rt pl), c, mkTrT S A W rts pls ρ fun p => f (.inr p))

def countT : (S : List RS) → RootsOfChain lam (up S) → ℕ
  | [], _ => 0
  | _ :: S, (rt, rts) => rt.1.join.toList.length + rt.2.join.toList.length + countT S rts

def strictST (sMT : ℕ) :
    (S : List RS) → (A : RoundSplits (up S)) → RoundsQueryLayout lam K (up S) A → RootsOfChain lam (up S) →
    (OPos (up S) → Bool) → ((p : OPos (up S)) → Option (Opening lam (OSym (up S) p))) → Bool
  | [], _, _, _, _, _ => true
  | _ :: S, (_, A), (w, W), (rt, rts), isRead, f =>
      strictComp sMT w.posAt0 w.depth0 rt.1.join.isSome
        (fun p => isRead (.inl p)) (fun p => f (.inl p)) &&
      strictComp sMT w.posAtJ w.depthJ rt.2.join.isSome
        (fun p => isRead (.inl p)) (fun p => f (.inl p)) &&
      strictST sMT S A W rts (fun p => isRead (.inr p)) (fun p => f (.inr p))

def forestsT :
    (S : List RS) → (A : RoundSplits (up S)) → RoundsQueryLayout lam K (up S) A →
    ((p : OPos (up S)) → OSym (up S) p → Body L) → RootsOfChain lam (up S) → (OPos (up S) → Bool) →
    ((p : OPos (up S)) → Option (Opening lam (OSym (up S) p))) → Option (List (Forest lam L))
  | [], _, _, _, _, _, _ => some []
  | _ :: S, (_, A), (w, W), emb, (rt, rts), isRead, f =>
      match checksOpt w.posAt0 w.depth0 (fun p => emb (.inl p)) rt.1.join
          (fun p => isRead (.inl p)) (fun p => f (.inl p)),
        checksOpt w.posAtJ w.depthJ (fun p => emb (.inl p)) rt.2.join
          (fun p => isRead (.inl p)) (fun p => f (.inl p)),
        forestsT S A W (fun p => emb (.inr p)) rts
          (fun p => isRead (.inr p)) (fun p => f (.inr p)) with
      | some a, some b, some c =>
          some (Forest.split w.pr0
              ⟨w.depth0, fun _ => rt.1.join.getD default, a.map fun c => (0, c)⟩ ++
            (Forest.split w.prJ
                ⟨w.depthJ, fun _ => rt.2.join.getD default, b.map fun c => (0, c)⟩ ++ c))
      | _, _, _ => none

/-- What the query of round i holds of the protocol's instance x, beside what stands in the first
query. (`Head.withLate` writes it into a head of format `f2` alone.) -/
def lateT (late : Option ℕ) (i : ℕ) (x : Option X) : Option X := if late = some i then x else none

def chainT (early : X → X) (late : Option ℕ) (t : Tag) (cms : List (Dig lam)) (x : Option X)
    (salt : Bits) (rtreq : Dig lam) :
    (S : List RS) → (A : RoundSplits (up S)) → RoundsQueryLayout lam K (up S) A →
    (PlainPart (up S) A → PlainPart (shapeOf L t) (annOf L t)) → ℕ → Phase lam → List (Dig lam) → Plains (up S) →
    TypedOracleComputation lam K L (Option (Rho (up S) × RootsOfChain lam (up S) × Phase lam))
  | [], _, _, _, _, ph, _, _ => pure (some ((), (), ph))
  | _ :: S, (a, A), (w, W), embP, i, ph, rts, (pl, pls) =>
      match actOf cms (x.map early) salt a.kind ph with
      | some (.one h true next) =>
          match takeRt w.hasJ rts with
          | some (rt, rts') => do
              let ans ← askTypedOracle (L := L) (K := K) (OracleName.fb t)
                (⟨i, h.withLate (lateT late i x), rt,
                  embP (.inl (.inr (a.plain pl).2))⟩ : FbIn lam L t)
              let r ← chainT early late t cms x salt rtreq S A W (fun z => embP (.inr z)) (i + 1)
                (next (List.ofFn ans.2)) rts' pls
              pure (r.map fun z => ((w.chal ans.1, z.1), ((none, some rt), z.2.1), z.2.2))
          | none => pure none
      | some (.one h false next) =>
          match takeRt w.has0 rts with
          | some (rt, rts') => do
              let ans ← askTypedOracle (L := L) (K := K) (OracleName.fb t)
                (⟨i, h, rt, embP (.inl (.inl (a.plain pl).1))⟩ : FbIn lam L t)
              let r ← chainT early late t cms x salt rtreq S A W (fun z => embP (.inr z)) (i + 1)
                (next (List.ofFn ans.2)) rts' pls
              pure (r.map fun z => ((w.chal ans.1, z.1), ((some rt, none), z.2.1), z.2.2))
          | none => pure none
      | some (.join ρ) =>
          match takeRt w.hasJ rts with
          | some (rtj, rts1) =>
              match takeRt w.has0 rts1 with
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
    decide (π.slot < 2 ^ depthReq) && (ph.slotVal.isSome || π.path.isEmpty)

/-- `verifyOneProtocol` written again on the skeleton. -/
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

end Run.Twin
