-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/PageQFull.lean: the run over the single oracle at the wiring with whole paths, after the parser
that fills whole paths, at any choice of challenge types (a record of type `CK`, called a kit in
the code); its instance with challenges as hash blocks (`ckP`; the library's "pull").

The compiled verifier (`Compile.Batch.verifyOneProtocol`) asks typed oracles. An encoding of the typed
queries as bit strings (`Rom.OracleCoding`, Rom/Family.lean; here `theImpl` of Run/PageQ.lean's `pageQ`)
puts it over a single oracle on bit strings. The run functions here take a proof file's bytes to a
value of `Who` (Run/PlanQRun.lean): `accepted`, or who refuses: `limits`, `reader`, `verifier`.
A wiring (`ProtocolQueryLayout`, Iop/BatchWire.lean) says, round by round, how oracle messages are laid into
hash trees and how blocks of hash output become verifier messages. Each round's wire (`WireRB`) has
a flag (`prJ`) for how the opened leaves of the hash tree over a slot's component (a round here has
no other tree) are checked: together, over a pruned set of paths, or, without the flag, each along
a whole path of its own. Definitions that compute; theorems.

Why: the wirings of the top theorems are pulled and have whole paths, not pruned openings (every
opened leaf climbs a whole path of its own). Run/PageQRunC.lean's run stands at any choice of
challenge types, but at the wiring with pruned openings. Run/PlanQSF.lean has the wiring with whole
paths (`wqSF`) and the parser that fills whole paths, at typed oracle functions written directly
from the format. Here the two meet over a single oracle.

Main names:
  `V1W S C K chal dec h cm π`: the evaluable form of the compiled verifier (Run/ThinBits.lean:
    `verifyPB`) at `wqSF`, with g := `gQ S C dec (K + 1) h`: the form to state with.
  `Spec.v1w_eq`: `V1W` .. = ((`Compile.Batch.verifyOneProtocol` .. (`PSof` C ..).up (`wqSF` C K chal ..) ..
    [cm] () π).overOne (`theImpl (pageQ S C dec (K + 1) h)`)).det `oBits`: for every S, C, K, chal,
    dec, cm, π with the test `OKQ S`.
  `run1W S C K chal dec file : Who`: the whole-path parser at the format's hash (`parseFullWP` in
    the identity monad), then `V1W`.
  `V1WF`, `run1WF`: the form that runs: the hash's state kept (`gQK`), the set of positions read
    split round by round (`verifyPR`), the fast whole-path parser (`parseFullFP`); `v1wf_eq`:
    `V1WF` = `V1W`; `run1wf_eq`: `run1WF` = `run1W`, for all arguments.
  `run1WP`, `run1WPF S dec file`: with challenges as hash blocks (`ckP`) (Run/PlanPull.lean: `ckP`,
    `chalP`; the description's own number of blocks); `run1wpf_eq`.

Limits: all that the heads of Run/PageQRun.lean and Run/PageQRunC.lean leave out is not said here
either.
This file does not say that this wiring is the compiler's generic wiring. The generic wiring has
depths by a cardinality and places by a numbering: these are not compared with this wiring's in
this file. There is a theorem for challenges as hash blocks, on the compiler's generic wiring of a
Test followed by the library's step for the work tests: `Spec.planPull_wq` (stated in
Run/PlanPullWq.lean; proved in Run/PlanPullWqProofs.lean); no equation with the library's forms for
Batch is stated.
This file says nothing on a tie of `run1W`'s verdict to the definition's run of a tree of queries:
the whole-path parser as such a tree is another file's (`Spec.run1W_is`, stated in
Run/Run1Full.lean [not in this library; so here read: not proved in this library], under its
hypotheses).
Tests are not here: Run/PageQFullM1F.lean, Run/PageQFullM1R.lean, Run/PageQFullM1T.lean.
Limits: see "To be declared with every use" in the head of Run/ParseBS.lean (`leafSalt`).

Terms: lean/GLOSSARY.md.
-/
/- Limits: that a proof file is accepted or refused is no theorem of this library. It is the outcome
   of a `#guard` line, or of an evaluation outside the library, such as a test by Lean's evaluator,
   which leaves no declaration. So nothing that is checked of declarations is checked of such an
   evaluation. No clause of a soundness theorem of Fmt/ and Run/ speaks of a run. -/
import Run.PageQKeepC
import Run.PlanQSF

set_option autoImplicit false

namespace Run.PQ
open Iop Rom Compile Compile.Batch

/-- The verifier over the single oracle at the wiring without the flag (whole paths: `wqSF`). -/
def V1W (S : _root_.Fmt.Spec) (C : CK) (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k)
    (dec : View → Bool) (h : OKQ S = true) (cm : Dig 256) (π : OneProtocolProof 256 (PSof C (rds S) dec).up) :
    Bool :=
  Thin.verifyPB (lam := 256) (K := K + 1) (fun _ => LbS C (rds S) dec) (gQ S C dec (K + 1) h)
    id none (256 + 8 * S.plan.salt) 256 .onl (PSof C (rds S) dec) (wqSF C K chal (rds S) dec)
    (fun p a => some (.inr ⟨Tag.onl, ⟨p, a⟩⟩)) (embPS C (rds S) dec) some
    (fun s => some (.inl s)) 0 [cm] () π

def Spec.v1w_eq : Prop :=
  ∀ (S : _root_.Fmt.Spec) (C : CK) (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k)
      (dec : View → Bool) (h : OKQ S = true) (cm : Dig 256) (π : OneProtocolProof 256 (PSof C (rds S) dec).up),
    V1W S C K chal dec h cm π =
      ((verifyOneProtocol (lam := 256) (K := K + 1) (L := LbS C (rds S) dec) (256 + 8 * S.plan.salt) 256 .onl
          (PSof C (rds S) dec).up (wqSF C K chal (rds S) dec)
          (fun p a => some (.inr ⟨Tag.onl, ⟨p, a⟩⟩)) (embPS C (rds S) dec) some
          (fun s => some (.inl s)) 0 [cm] () π).overOne
        (theImpl (pageQ S C dec (K + 1) h))).det oBits

theorem v1w_eq : Spec.v1w_eq := fun S C K chal dec h cm π => by
  rw [det_overOne, ← gQ_eq]
  exact Thin.thin_bits Unit Unit 256 (K + 1) (LbS C (rds S) dec) _ Unit E0
    (256 + 8 * S.plan.salt) 256 .onl (PSof C (rds S) dec) (wqSF C K chal (rds S) dec) _ _ some
    (fun s => some (.inl s)) 0 [cm] () π

def run1WOn (S : _root_.Fmt.Spec) (C : CK) (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k)
    (dec : View → Bool) (x : Option (List (Dig 256) × OneProtocolProof 256 (PSof C (rds S) dec).up)) : Who :=
  if ok S then
    if h : OKQ S = true then
      match x with
      | some ([cm], π) => if V1W S C K chal dec h cm π then .accepted else .verifier
      | _ => .reader
    else .limits
  else .limits

/-- The run over the single oracle, through the parser that fills whole paths. -/
def run1W (S : _root_.Fmt.Spec) (C : CK) (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k)
    (dec : View → Bool) (file : ByteArray) : Who :=
  run1WOn S C K chal dec
    (parseFullWP (m := Id) _root_.Fmt.formatHash (PSof C (rds S) dec) S (TYS S C dec) file)

/-! ### The form that runs -/

def V1WF (S : _root_.Fmt.Spec) (C : CK) (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k)
    (dec : View → Bool) (h : OKQ S = true) (cm : Dig 256) (π : OneProtocolProof 256 (PSof C (rds S) dec).up) :
    Bool :=
  Thin.verifyPR (lam := 256) (K := K + 1) (fun _ => LbS C (rds S) dec) (gQK S C dec (K + 1) h)
    id none (256 + 8 * S.plan.salt) 256 .onl (PSof C (rds S) dec) (wqSF C K chal (rds S) dec)
    (fun p a => some (.inr ⟨Tag.onl, ⟨p, a⟩⟩)) (embPS C (rds S) dec) some
    (fun s => some (.inl s)) 0 [cm] () π

def Spec.v1wf_eq : Prop :=
  ∀ (S : _root_.Fmt.Spec) (C : CK) (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k)
      (dec : View → Bool) (h : OKQ S = true) (cm : Dig 256) (π : OneProtocolProof 256 (PSof C (rds S) dec).up),
    V1WF S C K chal dec h cm π = V1W S C K chal dec h cm π

theorem v1wf_eq : Spec.v1wf_eq := fun S C K chal dec h cm π => by
  unfold V1WF V1W
  rw [Thin.verifyPR_eq, gQK_eq S C dec (K + 1) (Nat.succ_pos _) h]

def run1WFOn (S : _root_.Fmt.Spec) (C : CK) (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k)
    (dec : View → Bool) (x : Option (List (Dig 256) × OneProtocolProof 256 (PSof C (rds S) dec).up)) : Who :=
  if ok S then
    if h : OKQ S = true then
      match x with
      | some ([cm], π) => if V1WF S C K chal dec h cm π then .accepted else .verifier
      | _ => .reader
    else .limits
  else .limits

def run1WF (S : _root_.Fmt.Spec) (C : CK) (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k)
    (dec : View → Bool) (file : ByteArray) : Who :=
  run1WFOn S C K chal dec (parseFullFP (PSof C (rds S) dec) S (TYS S C dec) file)

def Spec.run1wf_eq : Prop :=
  ∀ (S : _root_.Fmt.Spec) (C : CK) (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k)
      (dec : View → Bool) (file : ByteArray),
    run1WF S C K chal dec file = run1W S C K chal dec file

theorem run1wf_eq : Spec.run1wf_eq := fun S C K chal dec file => by
  unfold run1WF run1W
  rw [(laxFast_parse _ S _ file).2]
  unfold run1WFOn run1WOn
  simp only [v1wf_eq S C K chal dec]

/-! ### With challenges as hash blocks (`ckP`) -/

def run1WP (S : _root_.Fmt.Spec) (dec : View → Bool) (file : ByteArray) : Who :=
  run1W S (ckP S.plan.field) (kOf S) (chalP S.plan.field (kOf S)) dec file

/-- Challenges as hash blocks, whole paths, a single oracle: the form that runs. -/
def run1WPF (S : _root_.Fmt.Spec) (dec : View → Bool) (file : ByteArray) : Who :=
  run1WF S (ckP S.plan.field) (kOf S) (chalP S.plan.field (kOf S)) dec file

theorem run1wpf_eq (S : _root_.Fmt.Spec) (dec : View → Bool) (file : ByteArray) :
    run1WPF S dec file = run1WP S dec file :=
  run1wf_eq S _ _ _ dec file

end Run.PQ
