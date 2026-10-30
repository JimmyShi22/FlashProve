-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
CompileK/KnowExt.lean: the named witness extractor of the compiled argument. Definitions only.

This file is about witness extraction from a non-interactive argument in the random-oracle model: an
extractor without rewinding, which reads the proof and the lists of queries of the committer and the
prover.
A named extractor is one that a statement gives as a term (`HasIndexBindingWith`, ZKCP/Gen.lean).
E_w(ivk, trC, x, π, trP), as the cited definition (lean/CREDITS.md) types it: no oracle access, and
NOT the verifier's queries.
   1  take the roots that are in the slot's argument string π, dealt out to the rounds (`rtsPure`,
      the verifier's chain without its queries; which root belongs to which round depends on the
      kinds of the rounds and the wire's flags alone);
   2  run the Merkle extractor of Compile/Batch on the committer's trace followed by the prover's,
      under these roots; this gives the symbols of all oracles of the slot's local transcript
      (`readStar`, the oracles of the transcript τ∗ of Compile/Batch/Runs.lean, without its verifier
      messages);
   3  apply wit, the witness map of the IOP (Ior/Batch.lean: by type it reads the instance and
      oracle symbols only).
E_i is the index extractor of Compile/Batch (`extractorB`, Compile/Batch/SpecBinding.lean),
unchanged.

Main names: `extractorBW` (the links in the proofs), `extractorBKW` (the links in the key).

Terms: lean/GLOSSARY.md: chain, link (the tie between two encodings of the index), named extractor,
slot, trace, wire, witness map.
-/
import Compile.Batch.Sound
import Compile.Batch.SpecBinding
import Compile.Batch.StarK
import Iop.Pull
import Ior.Batch
import Ior.OrcsPush
import CompileK.GenWit
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Compile.Batch
open Iop Rom ZKCP Compile.GenMap Compile.GenPub

variable {I X Wn : Type} {lam K : ℕ} {L : BatchProtocol I X}

/-- The phases of a slot's chain, without their values. -/
inductive PhK
  | first
  | loc
  | shr
  | aft

/-- The verifier's chain without its queries: the roots of the list, dealt out to the components of
the rounds. none: the format of a round is not defined or a root is missing (then V rejects). -/
def rtsPure :
    (s : Shape) → (A : RoundSplits s) → RoundsQueryLayout lam K s A → PhK → List (Dig lam) → Option (RootsOfChain lam s)
  | [], _, _, _, _ => some ()
  | _ :: s, (a, A), (w, ws), ph, rts =>
      match a.kind, ph with
      | .lo, .first | .lo, .loc =>
          (takeRt w.hasJ rts).bind fun z =>
            (rtsPure s A ws .loc z.2).map fun r => ((none, some z.1), r)
      | .lo, .shr | .lo, .aft =>
          (takeRt w.hasJ rts).bind fun z => (rtsPure s A ws .aft z.2).map fun r => ((none, some z.1), r)
      | .sh, .loc =>
          (takeRt w.hasJ rts).bind fun zj => (takeRt w.has0 zj.2).bind fun z0 =>
            (rtsPure s A ws .shr z0.2).map fun r => ((some z0.1, some zj.1), r)
      | .sh, .shr =>
          (takeRt w.has0 rts).bind fun z => (rtsPure s A ws .shr z.2).map fun r => ((some z.1, none), r)
      | .sh, .first | .sh, .aft => none

/-- No component is sent. -/
def RootsOfChain.none : (s : Shape) → RootsOfChain lam s
  | [] => ()
  | _ :: s => ((Option.none, Option.none), RootsOfChain.none s)

/-- The oracles of τ∗: under the given roots, what the trace determines. -/
def readStar (tr : Trace (spec lam K L)) :
    (s : Shape) → (A : RoundSplits s) → RoundsQueryLayout lam K s A → ((p : OPos s) → Body L → Option (OSym s p)) →
    RootsOfChain lam s → Plains s → Orcs s
  | [], _, _, _, _, _, p => nomatch p
  | _ :: _, (_, _), (w, _), prjS, (rt, _), (pl, _), .inl p =>
    Round.rd _ (msgStar tr w (fun p => prjS (.inl p)) rt pl).1 p
  | _ :: s, (_, A), (_, ws), prjS, (_, rts), (_, pls), .inr p =>
    readStar tr s A ws (fun p => prjS (.inr p)) rts pls p

variable (W : QueryLayout lam L)

/-- The roots of the slot's argument string, round by round. -/
def rtsB (π : OneProtocolProof lam L.onlineBatch) : RootsOfChain lam L.onlineBatch.loc.shape :=
  (rtsPure L.onlineBatch.loc.shape L.onlineBatch.ann W.B.sh .first π.roots).getD (RootsOfChain.none _)

/-- The oracles of the slot's local transcript that the trace determines under the roots of π. -/
def readB (tr : Tc W) (π : OneProtocolProof lam L.onlineBatch) : Orcs L.onlineBatch.loc.shape :=
  readStar tr L.onlineBatch.loc.shape L.onlineBatch.ann W.B.sh (prjSym Tag.onl) (rtsB W π) π.plains

/-- E_i as in Compile/Batch. E_w: roots of π; Merkle extraction from the committer's trace followed
by the prover's; wit. w0: the value for a proof without a slot's string (V rejects it). -/
def extractorBW (wit : X → Orcs L.onlineBatch.loc.shape → Wn) (w0 : Wn) :
    ZKCP.Gen.Extractor (spec lam W.K L) I X Wn (IVK lam L) (Prf lam L) where
  Ei := fun v tr => L.decodeIndex (extEnc W tr v.cm)
  Ew := fun _ trC x π trP => match π.piB with
    | some πB => wit x (readB W (trC ++ trP) πB)
    | none => w0

/-- The same for the scheme with the links in the verification key. -/
def extractorBKW (wit : X → Orcs L.onlineBatch.loc.shape → Wn) (w0 : Wn) :
    Gen.Extractor (spec lam W.K L) I X Wn (IVKK lam L) (PrfK lam L) :=
  pullE liftK (pubE pubK (extractorBW W wit w0))

end Compile.Batch
