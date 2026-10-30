-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/PlanQSF.lean: the generic construction, from the description of a proof file to the compiled
verifier, with whole paths in the place of pruned openings.

The compiled verifier (`Compile.Batch.verifyOneProtocol`) is the verifier of the non-interactive argument
that the library's compiler makes of an interactive oracle protocol. A wiring is the data that say
how deep the trees are, where a position stands among a tree's leaves, and how hash output becomes
challenges. A wiring has a flag that selects how Merkle openings are checked. With the flag (pruned
openings), the opened leaves of a tree share one set of sibling digests and the tree is checked by
one walk, as the verifier of the format page does (docs/format/FORMAT.md, which comes with the
programs, the C++
implementation that comes with this Lean code). Without the flag (whole paths), each opened leaf has
an authentication path of its own. Run/PlanQS.lean makes, from a description, a typed protocol and a
wiring with the flag. The wirings in the compiler's top theorems do not have it. This file repeats
the construction of Run/PlanQS.lean at wirings without the flag. Run/PlanQS.lean itself is not
changed.

1. What the file contains.
   `wireSF`, `wiresSLF`, `wqSF`
                              The wirings of Run/PlanQS.lean with the flag set to false. Nothing
                              else differs.
   `VPF S dec cm π : Bool`    The evaluable form of the compiled verifier (Run/ThinReads.lean,
                              `verifyPR`: the walks in the trees are made on digests as data, and
                              the set of positions read is split round by round), at these wirings.
   `runFullS S dec file : Who`
                              The run function. First a parser that fills whole paths
                              (Run/ParseLaxFast.lean, `parseFullFP`): a proof file holds pruned
                              openings, so the parser hashes the opened leaves and walks up, to give
                              every opened leaf a whole path with real values. It compares no root
                              and tests no proof of work. Then `VPF`.
   `VPFC`, `runOnFC`, `runFullC S C K chal dec file`
                              The general forms. Their parameters are C, the choice of challenge
                              types (for each round the type of the verifier's message, and the map
                              from such a message to the format's record of what was drawn); K, the
                              number of hash blocks; and chal, the samplers. `VPF`, `runOnSF` and
                              `runFullS` are these, by definition, with challenges as sampled values
                              (`ck`). With challenges as hash blocks (`ckP`): Run/PlanQSFP.lean.
   Who checks what is as in Run/ParseFull.lean: the verifier climbs every path itself, from its own
   leaf query, to the root that was sent.

2. What is checked when the file compiles. Nothing beyond the proofs.

3. Theorems (statements `Run.PQ.Spec.*`, with their proofs).
   `vpf_eq`                   `VPF S dec cm π` = (`Compile.Batch.verifyOneProtocol` .. (PSof ..).up (wqSF ..)
                              .. [cm] () π).det (famP ..), for every S, dec, cm, π.
   `runF_reader`              `runFullS` is the run on `parseFullWP` at the identity monad and the
                              format's hash function: the fast form (`parseFullFP`) changes no
                              value.
   `vpfc_eq`, `runFC_reader`  The same two statements for the general forms.

4. What is not claimed. Everything that the head of Run/PlanQS.lean lists as not claimed. Among it:
   no statement on soundness; and, with challenges as sampled values (`VPF`, `runFullS`), at a round
   that draws a field element the wiring does not obey the library's laws (`ProtocolQueryLayout.OKG`,
   Iop/BatchWire.lean), and no hypothesis of a compilation theorem is met at it: `wireSF` differs
   from `wireS` in the flag alone. (Of which hypothesis the words "no hypothesis … is met at it"
   speak, and what is had of the others, the soundness among them at the relation "everything", and
   empty: Run/PlanQS.lean, the head, 4.) No condition on a wiring is stated here (see
   Run/PlanQSFLaws.lean). Nothing is said on running time.
   Limits: see "To be declared with every use" in the head of Run/ParseBS.lean (`leafSalt`).

Terms: lean/GLOSSARY.md.
-/
/- Limits: that a proof file is accepted or refused is no theorem of this library. It is the outcome
   of a `#guard` line, or of an evaluation outside the library, such as a test by Lean's evaluator,
   which leaves no declaration. So nothing that is checked of declarations is checked of such an
   evaluation. No clause of a soundness theorem of Fmt/ and Run/ speaks of a run. -/
import Run.PlanQS
import Run.ThinReads

set_option autoImplicit false

namespace Run.PQ
open Iop Rom Compile Compile.Batch
open Run.Twin (RS PS)

/-- a round's wiring, without the flag for pruned openings -/
def wireSF (C : CK) (K : Nat) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k) (d : RD) :
    WireRB 256 (K + 1) (roundS C d).up (roundS C d).lo :=
  { wireS C K chal d with prJ := false }

def wiresSLF (C : CK) (K : Nat) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k) :
    (ds : List RD) → RoundsQueryLayout 256 (K + 1) (uL C ds) (Twin.allLo (SL C ds))
  | [] => ()
  | d :: ds => (wireSF C K chal d, wiresSLF C K chal ds)

/-- The wiring without the flag. -/
def wqSF (C : CK) (K : Nat) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k)
    (ds : List RD) (dec : View → Bool) :
    ProtocolQueryLayout 256 (K + 1) (PSof C ds dec).up :=
  ⟨(wire0S C K chal, wiresSLF C K chal ds), we0, decOS C ds, nOpen ds, maxDepth ds⟩

/-- The evaluable form of the compiled verifier at that wiring, for every choice of challenge types
and samplers. -/
def VPFC (S : _root_.Fmt.Spec) (C : CK) (K : Nat) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k)
    (dec : View → Bool) (cm : Dig 256) (π : OneProtocolProof 256 (PSof C (rds S) dec).up) : Bool :=
  Thin.verifyPR (lam := 256) (K := K + 1) (fun _ => LbS C (rds S) dec)
    (famK (fun _ => LbS C (rds S) dec) (PDS S C dec) (K + 1)) id none (256 + 8 * S.plan.salt) 256
    .onl (PSof C (rds S) dec) (wqSF C K chal (rds S) dec) (fun p a => some (.inr ⟨Tag.onl, ⟨p, a⟩⟩))
    (embPS C (rds S) dec) some (fun s => some (.inl s)) 0 [cm] () π

/-- States: what is evaluated (`VPFC`) is the run of the compiled verifier at the wiring without the
flag, for every choice of challenge types and samplers. -/
def Spec.vpfc_eq : Prop :=
  ∀ (S : _root_.Fmt.Spec) (C : CK) (K : Nat) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k)
      (dec : View → Bool) (cm : Dig 256) (π : OneProtocolProof 256 (PSof C (rds S) dec).up),
    VPFC S C K chal dec cm π =
      (verifyOneProtocol (lam := 256) (K := K + 1) (L := LbS C (rds S) dec) (256 + 8 * S.plan.salt) 256 .onl
          (PSof C (rds S) dec).up (wqSF C K chal (rds S) dec)
          (fun p a => some (.inr ⟨Tag.onl, ⟨p, a⟩⟩)) (embPS C (rds S) dec) some
          (fun s => some (.inl s)) 0 [cm] () π).det
        (famP (fun _ => LbS C (rds S) dec) _root_.Fmt.oracle (PDS S C dec) (K + 1))

theorem vpfc_eq : Spec.vpfc_eq := fun S C K chal dec cm π => by
  unfold VPFC
  rw [famK_eq]
  exact Thin.thin_reads Unit Unit 256 (K + 1) (LbS C (rds S) dec) _ Unit E0
    (256 + 8 * S.plan.salt) 256 .onl (PSof C (rds S) dec) (wqSF C K chal (rds S) dec) _ _ some
    (fun s => some (.inl s)) 0 [cm] () π

def runOnFC (S : _root_.Fmt.Spec) (C : CK) (K : Nat) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k)
    (dec : View → Bool) (x : Option (List (Dig 256) × OneProtocolProof 256 (PSof C (rds S) dec).up)) : Who :=
  if ok S then
    match x with
    | some ([cm], π) => if VPFC S C K chal dec cm π then .accepted else .verifier
    | _ => .reader
  else .limits

/-- The run function through the parser that fills whole paths, for every choice of challenge types
and samplers. -/
def runFullC (S : _root_.Fmt.Spec) (C : CK) (K : Nat) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k)
    (dec : View → Bool) (file : ByteArray) : Who :=
  runOnFC S C K chal dec (parseFullFP (PSof C (rds S) dec) S (TYS S C dec) file)

def Spec.runFC_reader : Prop :=
  ∀ (S : _root_.Fmt.Spec) (C : CK) (K : Nat) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k)
      (dec : View → Bool) (file : ByteArray),
    runFullC S C K chal dec file =
      runOnFC S C K chal dec
        (parseFullWP (m := Id) _root_.Fmt.formatHash (PSof C (rds S) dec) S (TYS S C dec) file)

theorem runFC_reader : Spec.runFC_reader := by
  intro S C K chal dec file
  unfold runFullC
  rw [(laxFast_parse _ S _ file).2]

/-! ## With challenges as sampled values -/

/-- The evaluable form of the compiled verifier at that wiring, with challenges as sampled values.
-/
def VPF (S : _root_.Fmt.Spec) (dec : View → Bool) (cm : Dig 256)
    (π : OneProtocolProof 256 (PSof (ck S.plan.field) (rds S) dec).up) : Bool :=
  VPFC S (ck S.plan.field) (kOf S) (chalOf S.plan.field (kOf S)) dec cm π

/-- States: what is evaluated (`VPF`) is the run of the compiled verifier at the wiring without the
flag. -/
def Spec.vpf_eq : Prop :=
  ∀ (S : _root_.Fmt.Spec) (dec : View → Bool) (cm : Dig 256)
      (π : OneProtocolProof 256 (PSof (ck S.plan.field) (rds S) dec).up),
    VPF S dec cm π =
      (verifyOneProtocol (lam := 256) (K := kOf S + 1) (L := LbS (ck S.plan.field) (rds S) dec)
          (256 + 8 * S.plan.salt) 256 .onl (PSof (ck S.plan.field) (rds S) dec).up
          (wqSF (ck S.plan.field) (kOf S) (chalOf S.plan.field (kOf S)) (rds S) dec)
          (fun p a => some (.inr ⟨Tag.onl, ⟨p, a⟩⟩)) (embPS (ck S.plan.field) (rds S) dec) some
          (fun s => some (.inl s)) 0 [cm] () π).det
        (famP (fun _ => LbS (ck S.plan.field) (rds S) dec) _root_.Fmt.oracle
          (PDS S (ck S.plan.field) dec) (kOf S + 1))

theorem vpf_eq : Spec.vpf_eq := fun S dec cm π =>
  vpfc_eq S (ck S.plan.field) (kOf S) (chalOf S.plan.field (kOf S)) dec cm π

def runOnSF (S : _root_.Fmt.Spec) (dec : View → Bool)
    (x : Option (List (Dig 256) × OneProtocolProof 256 (PSof (ck S.plan.field) (rds S) dec).up)) : Who :=
  runOnFC S (ck S.plan.field) (kOf S) (chalOf S.plan.field (kOf S)) dec x

/-- The run function through the parser that fills whole paths. -/
def runFullS (S : _root_.Fmt.Spec) (dec : View → Bool) (file : ByteArray) : Who :=
  runFullC S (ck S.plan.field) (kOf S) (chalOf S.plan.field (kOf S)) dec file

def Spec.runF_reader : Prop :=
  ∀ (S : _root_.Fmt.Spec) (dec : View → Bool) (file : ByteArray), runFullS S dec file =
    runOnSF S dec
      (parseFullWP (m := Id) _root_.Fmt.formatHash (PSof (ck S.plan.field) (rds S) dec) S
        (TYS S (ck S.plan.field) dec) file)

theorem runF_reader : Spec.runF_reader := fun S dec file =>
  runFC_reader S (ck S.plan.field) (kOf S) (chalOf S.plan.field (kOf S)) dec file

end Run.PQ
