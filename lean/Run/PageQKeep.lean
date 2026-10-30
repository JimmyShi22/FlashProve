-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/PageQKeep.lean: the generic construction (any plan), over a single oracle (Run/PageQRun.lean),
with the hash's state kept after the whole blocks of what all blocks of one chain answer share, and
the fast lenient reader: for long messages. What it runs is what Run/PageQRun.lean runs: theorems.

The compiled verifier (`Compile.Batch.verifyOneProtocol`) asks typed oracles. An encoding of the typed
queries as bit strings (`Rom.OracleCoding`, Rom/Family.lean; here `theImpl` of Run/PageQ.lean's `pageQ`)
puts it over a single oracle on bit strings. The run function here, `run1K`, takes a proof file's
bytes to a value of `Who` (Run/PlanQRun.lean): `accepted`, or who refuses: `limits`, `reader`,
`verifier`.
The generic construction (Run/PlanQS.lean) makes from a description (`S : Fmt.Spec`,
Fmt/Rules8.lean) a protocol, its wiring and run functions. Definitions that compute; statements
(each a `Prop` in `Run.PQ.Spec`) and proofs; tests (#guard).
The family `gQ` (Run/PageQ.lean), at which Run/PageQRun.lean runs, writes, for every block of every
chain answer, the string of the encoding of the queries as bits, and hashes it whole.
Run/CodingThinKeep.lean's `famCK` answers a chain query that fits the format from the call's data,
the state kept, and writes no string. Its tie has two hypotheses. At a description both are
theorems: Run/PageQFit.lean (`pageQ_fit`, under its hypotheses: what the encoding's partial codes
write are the strings of the format's calls), Run/PageQFits.lean (`fitsQ`, a test that looks at no
element of the message; `fitsQ_put`: where it holds the encoding writes at every block).

Main names:
  `gQK S C dec K h`: `famCK` at `pageQ`, `PDS`, `fitsQ`; `Spec.gQK_eq`: 0 < K →
    `gQK S C dec K h = gQ S C dec K h`.
  `V1K S dec h cm π`: Run/PageQRun.lean's `V1` with `gQK` for `gQ`, and with Run/ThinReads.lean's
    `verifyPR` (the set of positions read split round by round) for `verifyPB`; `Spec.v1K_eq`:
    `V1K` = `V1`: so by Run/PageQRun.lean's `v1_eq` it is the run of `Compile.Batch.verifyOneProtocol` put
    over the single oracle, all blocks asked.
  `run1KOn`, `run1K S dec file`: the fast lenient reader, then `V1K`; `Spec.run1K_eq`:
    `run1K S dec file = run1 S dec file`.

Tests. At 21 files of a small toy of this library's own (`Fmt.Toy1.files`): `run1K`'s outcome
(accepted, or which part refuses), evaluated, is `run1`'s. At the format page's known answer of
section 8 (a round that draws elements of the extension field): both fields: accepted; at the
second field alone: with one byte altered, at every eighth byte: the outcome is `run1`'s.

Limits (what it is not): as in Run/PageQRun.lean: the files are this library's own or the page's;
no soundness is claimed; tests leave no theorem. Nothing on time (measured outside this file).
Limits: see "To be declared with every use" in the head of Run/ParseBS.lean (`leafSalt`).

Terms: lean/GLOSSARY.md.
-/
import Run.PageQRun
import Run.PageQFit
import Run.PageQFits
import Run.CodingThinKeep
import Run.ThinReads

set_option autoImplicit false

namespace Run.PQ
open Iop Rom Compile Compile.Batch

theorem fitsQ_round (S : _root_.Fmt.Spec) (C : CK) (dec : View → Bool) (K : ℕ)
    (q : FbIn 256 (LfQ S C dec ()) .onl) (h : fitsQ S C dec K q = true) : q.round ≠ 0 := by
  obtain ⟨round, head, rt, plain⟩ := q
  cases round with
  | zero => cases h
  | succ i => exact Nat.succ_ne_zero i

/-- The typed oracle functions read out of the single oracle, the state kept. -/
def gQK (S : _root_.Fmt.Spec) (C : CK) (dec : View → Bool) (K : ℕ) (h : OKQ S = true) :
    Fam (spec 256 K (LfQ S C dec ())) :=
  famCK (LfQ S C dec) (pageQ S C dec K h) (PDS S C dec) (fitsQ S C dec K)

def Spec.gQK_eq : Prop :=
  ∀ (S : _root_.Fmt.Spec) (C : CK) (dec : View → Bool) (K : ℕ) (_ : 0 < K) (h : OKQ S = true),
    gQK S C dec K h = gQ S C dec K h

theorem gQK_eq : Spec.gQK_eq := fun S C dec K hK h =>
  famCK_eq (L := LbS C (rds S) dec) (pageQ S C dec K h) (PDS S C dec) (fitsQ S C dec K)
    (pageQ_fit S C dec K hK h) fun q hq => ⟨fitsQ_round S C dec K q hq, fitsQ_put S C dec K q hq⟩

/-- The verifier over the single oracle, the state kept. -/
def V1K (S : _root_.Fmt.Spec) (dec : View → Bool) (h : OKQ S = true) (cm : Dig 256)
    (π : OneProtocolProof 256 (PSof (ck S.plan.field) (rds S) dec).up) : Bool :=
  Thin.verifyPR (lam := 256) (K := kOf S + 1) (fun _ => LbS (ck S.plan.field) (rds S) dec)
    (gQK S (ck S.plan.field) dec (kOf S + 1) h) id none (256 + 8 * S.plan.salt) 256 .onl
    (PSof (ck S.plan.field) (rds S) dec)
    (wqS (ck S.plan.field) (kOf S) (chalOf S.plan.field (kOf S)) (rds S) dec)
    (fun p a => some (.inr ⟨Tag.onl, ⟨p, a⟩⟩)) (embPS (ck S.plan.field) (rds S) dec) some
    (fun s => some (.inl s)) 0 [cm] () π

def Spec.v1K_eq : Prop :=
  ∀ (S : _root_.Fmt.Spec) (dec : View → Bool) (h : OKQ S = true) (cm : Dig 256)
      (π : OneProtocolProof 256 (PSof (ck S.plan.field) (rds S) dec).up),
    V1K S dec h cm π = V1 S dec h cm π

theorem v1K_eq : Spec.v1K_eq := fun S dec h cm π => by
  unfold V1K V1
  rw [Thin.verifyPR_eq, gQK_eq S (ck S.plan.field) dec (kOf S + 1) (Nat.succ_pos _) h]

def run1KOn (S : _root_.Fmt.Spec) (dec : View → Bool)
    (x : Option (List (Dig 256) × OneProtocolProof 256 (PSof (ck S.plan.field) (rds S) dec).up)) : Who :=
  if ok S then
    if h : OKQ S = true then
      match x with
      | some ([cm], π) => if V1K S dec h cm π then .accepted else .verifier
      | _ => .reader
    else .limits
  else .limits

/-- The run over the single oracle, through the fast lenient reader. -/
def run1K (S : _root_.Fmt.Spec) (dec : View → Bool) (file : ByteArray) : Who :=
  run1KOn S dec
    (parseLaxFP (PSof (ck S.plan.field) (rds S) dec) S (TYS S (ck S.plan.field) dec) file)

def Spec.run1K_eq : Prop :=
  ∀ (S : _root_.Fmt.Spec) (dec : View → Bool) (file : ByteArray), run1K S dec file = run1 S dec file

theorem run1K_eq : Spec.run1K_eq := fun S dec file => by
  unfold run1K run1
  rw [(laxFast_parse _ S _ file).1]
  unfold run1KOn run1On
  simp only [v1K_eq S dec]
  rfl

end Run.PQ

-- the 21 files of `Fmt.Toy1`
open Run Run.PQ Run.PQ.TS in
#guard (_root_.Fmt.Toy1.files.map fun f => run1K (T1.S (1, 2, 3)) (T1.dec (1, 2, 3)) f.2.1) == (_root_.Fmt.Toy1.files.map fun f => run1 (T1.S (1, 2, 3)) (T1.dec (1, 2, 3)) f.2.1)
open Run Run.PQ Run.PQ.TS in
#guard run1K (T1.S (1, 2, 3)) (T1.dec (1, 2, 3)) _root_.Fmt.Toy1.honest == .accepted
-- the page's known answer of section 8: a round that draws elements of the extension field
open Run Run.PQ Run.PQ.TS in
#guard run1K (K8 .two) yes _root_.Fmt.Known8.file2 == .accepted && run1K (K8 .one) yes _root_.Fmt.Known8.file1 == .accepted
open Run Run.PQ Run.PQ.TS in
#guard (places _root_.Fmt.Known8.file2).all fun i => run1K (K8 .two) yes (_root_.Fmt.flipAt _root_.Fmt.Known8.file2 i) == run1 (K8 .two) yes (_root_.Fmt.flipAt _root_.Fmt.Known8.file2 i)
