-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/PlanQRun.lean: defines the function that the scheme's verifier applies to a key's Test string,
and its evaluation on a file. The function is made from a description of a proof's rounds and a
decision on an untyped view. The key is the scheme's verifier's key: a root and the Test string
(`IVK`, Compile/Batch/Star.lean). A Test string is the proof of the compiled Test, as typed data:
field `piT` of `IVK`, Compile/Batch/Star.lean.

The scheme is what the library's compiler makes of an interface. Its verifier
(Compile/Batch/Star.lean) runs three functions, each of them `Compile.Batch.verifyOneProtocol` at one of the
interface's protocols (the three protocols of an interface: fields `offline`, `link`, `onlineBatch` of `BatchProtocol`,
Iop/Batch.lean): `vTS` on the Test string of the key, `vLS` and `vBS` on the two strings of a proof
(Compile/Batch/Verifier.lean). Test: the interface's offline test (`BatchProtocol.offline`, Iop/Batch.lean); its
language: the external string decodes.
This file uses the library's own terms, unchanged. It joins
   Run/PlanQTypes.lean (rounds, shape, view, protocol),
   Run/PlanDraws.lean and Run/PlanDrawsQ.lean (a round's verifier messages as the values of its
     draws; the block sampler; the choice of challenge types, that is, of what a round's verifier
     message is),
   Run/PlanQWire.lean (wiring),
   Run/PlanQPage.lean (interface, spelling of queries, typing),
   Run/ParseChain.lean and Run/ParseLax.lean (the two readers, strict and lenient).
Run/PlanQS.lean writes the construction again, there at an interface whose Batch is made from its
own protocol `PSof` (under the tag "onl"), in a form that can also be evaluated at rounds that draw
field elements.

1. What the file contains. Definitions that can be evaluated.
   `ck f` (Run/PlanDrawsQ.lean): Challenges as sampled values, over the field f: a round's verifier
     message is the values of its draws. The view: what the format's own record of a round's draws
     holds.
   `kOf S`, `chalOf f K`: The number of blocks of a verifier message: the greatest over the rounds
     (the wiring has one number for all). Each round's sampler, read on the first blocks.
   `WQ S dec`: The interface's wiring: Test's from S; Link and Batch have no rounds.
   `VQ S dec`: `Compile.Batch.vTS (WQ S dec)` at the data below. By its definition this is
     `Compile.Batch.verifyOneProtocol` under the tag "test" at the interface's own Test and wiring. Its term
     is untouched. The data are those that S gives: salts of 256 + 8 · (the plan's bytes of a leaf's
     salt) bits in the trees (the run's value, then the file's salt), 256 bits in the first query.
   `Who`: The outcome: limits (`PQ.ok S` fails); the reader refused; the verifier refused; accepted.
   `runStrict`, `runLax S dec file`: The reader at the format's hash; then `VQ` by `OComp.det` at
     the typed oracle functions that a single oracle on the format's strings induces
     (Run/CodingFast.lean: `famFast`, which that file proves equal to Run/CodingFn.lean's `famOf`;
     each answer's hash is computed once).

2. What is checked when the file compiles. Only the types.

3. Theorems. None.

Notation: `0, 0` at the end of `Lk` and `B` in `WQ`: the fields `nOpen`, `maxDepth` (`ProtocolQueryLayout`,
Iop/BatchWire.lean); `depth`: depth of the tree over an encoded index (`QueryLayout.depth`,
Iop/BatchWire.lean); `depthReq`: depth of the request tree (`QueryLayout.depthReq`, Iop/BatchWire.lean).

4. What a further protocol needs, what may be said, and what is not claimed.
   A further protocol needs S (a description) and dec (a decision on the view). A statement is not a
     typed argument: its bytes stand in `S.statement` (they enter the chain's first value), and dec
     is the decision at that statement. That the two speak of one statement is the caller's duty.
   Of a file that is accepted one may say: "accepted by the function that the scheme's verifier runs
     on a key's Test string, at an interface whose Test is this protocol". One may not say "by the
     scheme's verifier" (that runs three such functions, under a key).
   No statement on soundness follows. No law of the interface or of the wiring is shown, and with an
     encoded index of length 0 what a theorem says of an accepted Test string is empty.
   The oracles are typed, not a single oracle reached through an encoding of the queries. What runs
     is `VQ` itself, at the typed oracle functions named above. Run/CodingFn.lean's map from a typed
     query to a string gives these functions, and that file defines no inverse of the map. What runs
     is not `VQ` put over a single oracle (`OComp.overOne`, Rom/Family.lean) by an encoding with its
     inverse. Run/PageQ.lean and the files on it have that, for the construction as Run/PlanQS.lean
     writes it and not for `VQ`.
   The evaluator builds the list of all values of a round's verifier messages when it runs these
     terms. So a round that draws field elements cannot be run by a test (#guard) here; the kernel
     can. Run/PlanQS.lean removes this limit.
   Limits: see "To be declared with every use" in the head of Run/ParseBS.lean (`leafSalt`).

Terms: lean/GLOSSARY.md.
-/
import Run.PlanQWire
import Run.PlanQPage
import Run.PlanDrawsQ
import Run.ParseLax
import Rom.Cache
import Run.CodingFast

set_option autoImplicit false

namespace Run.PQ
open Iop Rom Compile Compile.Batch

/-- the blocks of a verifier's message: the greatest number over the rounds -/
def kOf (S : _root_.Fmt.Spec) : Nat := kMax (fun e k => (bsRound S.plan.field e k).b) (rds S)

/-- each round's sampler on K blocks -/
def chalOf (f : _root_.Fmt.Fld) (K : Nat) : ∀ e k, (Fin K → Dig 256) → (ck f).Ch e k := fun e k =>
  cutK (bsRound f e k) K

/-- the wire of Link's empty external oracles -/
def weL : WireE (twoExternalStrings 0 Unit) :=
  ⟨[], fun p => p.elim (·.elim0) (·.elim0), fun p => p.elim (·.elim0) (·.elim0), 0,
    fun _ => (fun p => p.elim0, fun p => p.elim0),
    inferInstanceAs (DecidableEq (Fin 0 ⊕ Fin 0)), false⟩

/-- The wiring of the ambient interface: Test's is the description's; Link and Batch have no
round. -/
def WQ (S : _root_.Fmt.Spec) (dec : View → Bool) :
    QueryLayout 256 (Lt (ck S.plan.field) (rds S) dec) where
  K := kOf S + 1
  T := wqT (ck S.plan.field) (kOf S) (chalOf S.plan.field (kOf S)) (rds S) fun _ => dec
  Lk := ⟨(), weL, inferInstanceAs (DecidableEq Empty), 0, 0⟩
  B := ⟨(), we0, inferInstanceAs (DecidableEq Empty), 0, 0⟩
  depth := 0
  depthReq := 0

/-- The verifier: the function that the scheme's verifier runs on a key's Test string, at the
interface whose Test is the description's protocol. -/
def VQ (S : _root_.Fmt.Spec) (dec : View → Bool) (cm : Dig 256)
    (π : OneProtocolProof 256 (BatchInteractiveOracleProof.ofProto (QU (ck S.plan.field) (rds S) dec))) :
    TypedOracleComputation 256 (kOf S + 1) (Lt (ck S.plan.field) (rds S) dec) Bool :=
  vTS (WQ S dec) (256 + 8 * S.plan.salt) 256 cm π

/-- The outcome of a run: accepted, or what refused: the limits, the reader or the verifier. -/
inductive Who where
  | limits
  | reader
  | verifier
  | accepted
  deriving DecidableEq, Repr

/-- the verifier's run on what a reader hands out; if `ok S`, the outcome is `.reader` at `none`,
and also where the list of digests has not exactly one member (`parseW` and `parseLaxW` end in
`toBPrf`, Run/ParseChain.lean, whose list has exactly one) -/
def runOn (S : _root_.Fmt.Spec) (dec : View → Bool)
    (x : Option
      (List (Dig 256) × OneProtocolProof 256 (BatchInteractiveOracleProof.ofProto (QU (ck S.plan.field) (rds S) dec)))) : Who :=
  if ok S then
    match x with
    | some ([cm], π) =>
      if (VQ S dec cm π).det
          (famFast _root_.Fmt.oracle (PD S (ck S.plan.field) dec) (kOf S + 1)) then .accepted
      else .verifier
    | _ => .reader
  else .limits

/-- The run, through the page's own reader. -/
def runStrict (S : _root_.Fmt.Spec) (dec : View → Bool) (file : ByteArray) : Who :=
  runOn S dec (parseW (m := Id) _root_.Fmt.formatHash S (TY S (ck S.plan.field) dec) file)

/-- The run, through the lenient reader. -/
def runLax (S : _root_.Fmt.Spec) (dec : View → Bool) (file : ByteArray) : Who :=
  runOn S dec (parseLaxW (m := Id) _root_.Fmt.formatHash S (TY S (ck S.plan.field) dec) file)

end Run.PQ
