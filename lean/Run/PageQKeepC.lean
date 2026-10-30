-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/PageQKeepC.lean: the run over the single oracle at any choice of challenge types (a record of
type `CK`, called a kit in the code) (Run/PageQRunC.lean), in the fast form, meant for the
programs' full parameters; proved equal.

The compiled verifier (`Compile.Batch.verifyOneProtocol`) asks typed oracles. An encoding of the typed
queries as bit strings (`Rom.OracleCoding`, Rom/Family.lean; here `theImpl` of Run/PageQ.lean's `pageQ`)
puts it over a single oracle on bit strings. The run functions here take a proof file's bytes to a
value of `Who` (Run/PlanQRun.lean): `accepted`, or who refuses: `limits`, `reader`, `verifier`.
A wiring (`ProtocolQueryLayout`, Iop/BatchWire.lean) says, round by round, how oracle messages are laid into
hash trees and how blocks of hash output become verifier messages. Definitions that compute;
theorems.
Run/PageQKeep.lean makes Run/PageQRun.lean's run fast with challenges as sampled values (`ck`): the
hash's state kept after the whole blocks of what all blocks of a chain answer share (no string of
bits is written at a fitting chain query), the set of positions read split round by round
(`verifyPR`), the fast lenient reader. All three are generic in that choice. Here the same step
with the choice of challenge types as a parameter, so that the run with challenges as hash blocks
(`ckP`; the library's "pull") (Run/PlanPull.lean), where the conditions on a wiring (`OKG`) hold
(`Spec.planPull_okg`, under its hypotheses), has it too.

Main names:
  `V1CF S C K chal dec h cm π`: `V1C` with `gQK` for `gQ` and Run/ThinReads.lean's `verifyPR` for
    `verifyPB`; `v1cf_eq`: `V1CF` = `V1C`.
  `run1CF S C K chal dec file`: the fast lenient reader, then `V1CF`; `run1cf_eq`: `run1CF` =
    `run1C`, for all arguments.
  `run1PF S dec file`: with challenges as hash blocks (`ckP`); `run1pf_eq`: `run1PF` = `run1P`.
So what is stated of `V1C`, `run1C`, `run1P` (Run/PageQRunC.lean: `v1c_eq`: the run of
`Compile.Batch.verifyOneProtocol` over the single oracle, all blocks asked) holds of what runs here.

Limits: all that the heads of Run/PageQRun.lean and Run/PageQRunC.lean leave out is not said here
either. That it runs fast, or at all, is no theorem.
Limits: see "To be declared with every use" in the head of Run/ParseBS.lean (`leafSalt`).

Terms: lean/GLOSSARY.md.
-/
import Run.PageQRunC
import Run.PageQKeep

set_option autoImplicit false

namespace Run.PQ
open Iop Rom Compile Compile.Batch

/-- The verifier over the single oracle at any choice of challenge types, the state kept. -/
def V1CF (S : _root_.Fmt.Spec) (C : CK) (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k)
    (dec : View → Bool) (h : OKQ S = true) (cm : Dig 256) (π : OneProtocolProof 256 (PSof C (rds S) dec).up) :
    Bool :=
  Thin.verifyPR (lam := 256) (K := K + 1) (fun _ => LbS C (rds S) dec) (gQK S C dec (K + 1) h)
    id none (256 + 8 * S.plan.salt) 256 .onl (PSof C (rds S) dec) (wqS C K chal (rds S) dec)
    (fun p a => some (.inr ⟨Tag.onl, ⟨p, a⟩⟩)) (embPS C (rds S) dec) some
    (fun s => some (.inl s)) 0 [cm] () π

def Spec.v1cf_eq : Prop :=
  ∀ (S : _root_.Fmt.Spec) (C : CK) (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k)
      (dec : View → Bool) (h : OKQ S = true) (cm : Dig 256) (π : OneProtocolProof 256 (PSof C (rds S) dec).up),
    V1CF S C K chal dec h cm π = V1C S C K chal dec h cm π

theorem v1cf_eq : Spec.v1cf_eq := fun S C K chal dec h cm π => by
  unfold V1CF V1C
  rw [Thin.verifyPR_eq, gQK_eq S C dec (K + 1) (Nat.succ_pos _) h]

def run1CFOn (S : _root_.Fmt.Spec) (C : CK) (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k)
    (dec : View → Bool) (x : Option (List (Dig 256) × OneProtocolProof 256 (PSof C (rds S) dec).up)) : Who :=
  if ok S then
    if h : OKQ S = true then
      match x with
      | some ([cm], π) => if V1CF S C K chal dec h cm π then .accepted else .verifier
      | _ => .reader
    else .limits
  else .limits

/-- The run over the single oracle at any choice of challenge types, through the fast lenient
reader. -/
def run1CF (S : _root_.Fmt.Spec) (C : CK) (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k)
    (dec : View → Bool) (file : ByteArray) : Who :=
  run1CFOn S C K chal dec (parseLaxFP (PSof C (rds S) dec) S (TYS S C dec) file)

def Spec.run1cf_eq : Prop :=
  ∀ (S : _root_.Fmt.Spec) (C : CK) (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k)
      (dec : View → Bool) (file : ByteArray),
    run1CF S C K chal dec file = run1C S C K chal dec file

theorem run1cf_eq : Spec.run1cf_eq := fun S C K chal dec file => by
  unfold run1CF run1C
  rw [(laxFast_parse _ S _ file).1]
  unfold run1CFOn run1COn
  simp only [v1cf_eq S C K chal dec]
  rfl

/-- The run with challenges as hash blocks (`ckP`), fast. -/
def run1PF (S : _root_.Fmt.Spec) (dec : View → Bool) (file : ByteArray) : Who :=
  run1CF S (ckP S.plan.field) (kOf S) (chalP S.plan.field (kOf S)) dec file

theorem run1pf_eq (S : _root_.Fmt.Spec) (dec : View → Bool) (file : ByteArray) :
    run1PF S dec file = run1P S dec file :=
  run1cf_eq S _ _ _ dec file

end Run.PQ
