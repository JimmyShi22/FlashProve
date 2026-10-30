-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/PlanQXRun.lean: a run function for entry files (it maps a file to an outcome) with the compiled
verifier, for any description.

The stages:
   (1) a file;
   (2) the reader in front (head, the copy's root);
   (3) the reader of a proof with stored tables (Fmt/Rules8X.lean);
   (4) a typed Link string (Run/PlanQX.lean: `toBPrfX`);
   (5) the compiled verifier under two roots, the key's and the file's, with BLAKE2b behind typed
       oracle functions;
   (6) and any decision on a view.
What Run/ToyLk.lean writes out directly for one made-up example is given here as functions of a
description.

The compiled verifier is the library's `Compile.Batch.verifyOneProtocol` (Compile/Batch/Verifier.lean), a
computation that puts typed queries to oracles. Here (`famX` at `Fmt.oracle`) a leaf query, a node
query, or a block of the answer to a chain query under the tag "link", that has a spelling as a call
of the format's hash is answered by `Fmt.oracle` at that call's string; all else is constant.
Interface, wiring and view: the head of Run/PlanQX.lean.

Sources. Written against the format page (docs/format/FORMAT.md, which comes with the programs) at
an edition that is not the one that ships: R13.1, R13.3, R13.5 for the file's head and the
first query; R4.6, R7.4, R7.19, R8.7 for the stored tables. R13.1, R13.3, R4.6 and R8.7
are the same in a second edition, also not the one that ships. R13.5, R7.4 and R7.19
differ between the two; according to a restatement, in wording, in pointers and in a
clause on the
record of vertices met, and in no byte. The programs are the C++ implementation that comes with this
Lean code.

1. What the file contains.
   `XD`: the description: that of the proof's rounds (Fmt/Rules8.lean: `Spec`; its field "statement"
     is not read, but for its size, which `D.ok` tests through that file's `Spec.small`); the
     statement as a function of the two roots; the openings of stored tables, round by round
     (Fmt/Rules8X.lean: `Stored`).
   `D.ds`, `D.xs`, `D.a`: the rounds, the openings of stored tables (which string: the statement's
     item 0 or 1), the stored trees' depth. None depends on a root, so the protocol's types do not
     either.
   `D.ok`: the limits, as a test: Run/PlanQTypes.lean's `ok` on the chain's own part; `okX`; all
     stored trees of one depth; items 0 and 1 alone. One limit is this library's own: a leaf of a
     stored table must have a salt of as many bytes as a leaf of the proof's own trees. The reason:
     the compiled verifier's strict format has one length for the salts of own and of external
     leaves. Another length is not rendered.
   `D.L dec`: the interface. Link is the protocol. Index, encoding and decoder are placeholders.
   `PDX`, `firstX`, `leafX`, `famX`: how typed oracle queries are spelled as the format's hash
     calls. The rounds after the first query are spelled as in Run/PlanQS.lean, at the tag "link".
     The two digests in the first query are the roots; they go into the statement, and the
     parameters' digest is a constant of the description. A leaf that holds a symbol of a stored
     table is hashed under the stored leaves' number 174, tree 0, index 2^a + the symbol's position,
     starting from the configuration's digest.
   `headEntry`, `readHead`: FORMAT.md, R13.1 and R13.3, at a table whose answers are empty: eight
     bytes CPEN H821; the copy's root, 32 bytes; the rest is the proof. (H821 is the version at the
     second field, R4.3. R13.1 names it alone; a description at the first field would want another
     head, and none exists.)
   `runEntry D dec r0 file`: the outcome: limits; reader (the head, or the proof's reader, which
     checks all openings itself, or the typing refuses); verifier; accepted.

2. What is checked when the file compiles. Only the types and the proof.

3. Theorems.
   `vx_eq`: VX D dec r0 r1 π is the run of `Compile.Batch.verifyOneProtocol` at the tag "link" under [r0, r1]
     at `famX`.

4. What is not claimed, or stands elsewhere.
   The key is not verified: r0 is the caller's. No statement on soundness follows. No soundness
   statement is made in Run/ or Fmt/ for a protocol made here from a description, beyond the two
   conditions sound and low of the record `MetX` (Run/PlanQXDoor.lean), which but for one clause are
   empty: "What is not claimed" in the head of Run/PlanQXDoor.lean. The library has a link protocol
   with such statements (Cb/Ld/LdLink.lean); nothing in Run/ or Fmt/ connects the two protocols.
   Run/ has the two conditions, at the language "everything", in `lu_sound` and, under its
   hypotheses, `metX` (Run/PlanQXDoorProofs.lean).
   A record's answers (tables with s > 0) are not rendered.
   The reader checks everything itself, so on files the verifier speaks only where the decision
   refuses (not proved in Run/ or Fmt/; not said of every description that `D.ok` admits: `extOf`
   (Run/PlanQX.lean) types a string's first opening alone, and `D.ok` asks nothing of `D.stm`, from
   which the reader takes the stored tables' roots). A lenient reader, which leaves work, leaves,
   paths and roots to the verifier: Run/ParseLaxX.lean; what the lenient reader refuses: part 1 of the head of Run/ParseLaxX.lean.
   Forms made for fast evaluation: Run/PlanQXFast.lean, Run/PlanQXFastR.lean.
   The oracle is a family of typed functions, not a single oracle reached through an encoding of the
   queries with proved laws.
   Limits: see "To be declared with every use" in the head of Run/ParseBS.lean (`leafSalt`).

Terms: lean/GLOSSARY.md.
-/
/- Limits: that a proof file is accepted or refused is no theorem of this library. It is the outcome
   of a `#guard` line, or of an evaluation outside the library, such as a test by Lean's evaluator,
   which leaves no declaration. So nothing that is checked of declarations is checked of such an
   evaluation. No clause of a soundness theorem of Fmt/ and Run/ speaks of a run. -/
import Run.PlanQX
import Run.PlanPull

set_option autoImplicit false

namespace Run.PQ
open Iop Rom Compile Compile.Batch

/-- The description. -/
structure XD where
  base   : _root_.Fmt.Spec
  stm    : ByteArray → ByteArray → ByteArray
  stored : List (List _root_.Fmt.Stored)

namespace XD

def atR (D : XD) (r0 r1 : ByteArray) : _root_.Fmt.SpecX :=
  ⟨{ D.base with statement := D.stm r0 r1 }, D.stored⟩
abbrev ds (D : XD) : List RD := rds D.base
def xs (D : XD) : List XO :=
  D.stored.zipIdx.flatMap fun t => t.1.map fun s => ⟨t.2, s.item == 1, s.lo, s.count⟩
def a (D : XD) : Nat := (D.stored.flatten.head?.map (·.sh.a)).getD 0
abbrev C (D : XD) : CK := ckP D.base.plan.field
abbrev K (D : XD) : Nat := kOf D.base

/-- The limits. -/
def ok (D : XD) : Bool :=
  PQ.ok D.base && okX D.ds D.a D.xs &&
    D.stored.flatten.all fun s => s.sh.a == D.a && s.salt == D.base.plan.salt && decide (s.item ≤ 1)

/-- the interface -/
abbrev L (D : XD) (dec : View → Bool) : BatchProtocol Unit Unit :=
  LkX (I := Unit) (RI := Unit) D.C D.ds D.a D.xs dec (fun _ _ p => (p.val, [])) (fun _ => some ())

end XD

/-- The spellings of the rounds after the first query. -/
def PDX (D : XD) (dec : View → Bool) : PageD (D.L dec) .link where
  label := D.base.label
  kind := fun i => if i = 0 then 7 else ((D.base.rounds[i - 1]?).map (·.kind.num)).getD 7
  work := fun i => if i = 0 then 0 else ((D.base.rounds[i - 1]?).map (·.entry.work)).getD 0
  stm := fun _ => ByteArray.empty
  msg := fun _ rt pl => match pl with
    | .inl _ => ByteArray.empty
    | .inr q => msgSL D.C (rt.getD ByteArray.empty) D.ds q
  nonce := fun _ pl => match pl with
    | .inl _ => 0
    | .inr q => nonceSL D.C D.ds q
  leaf := fun s => match s with
    | ⟨.inl p, _⟩ => p.elim
    | ⟨.inr q, col⟩ => leafSL D.C D.base.plan.salt D.ds ⟨q, col⟩
  cfg := D.base.cfg

/-- The first query: the two digests in its head are the roots. -/
def firstX (D : XD) (dec : View → Bool) (K : Nat) (q : FbIn 256 (D.L dec) .link) (j : Fin (K + 1)) :
    Option _root_.Fmt.OQ :=
  match q.round, q.head with
  | 0, .f1 [cm, cm'] none salt =>
      if j.val = K then
        some ⟨0, 160, 0, D.base.label, _root_.Fmt.zero32,
            firstBytes (_root_.Fmt.paramsDigest D.base.params)
              (D.stm (digToBytes cm) (digToBytes cm')) salt⟩
      else none
  | 0, _ => none
  | _, _ => fbCall (PDX D dec) K q j

/-- A leaf: of a stored tree, or of the chain's own. -/
def leafX (D : XD) (dec : View → Bool) (q : LeafIn (D.L dec)) : Option _root_.Fmt.OQ :=
  match q.body with
  | some (.inl s) =>
      if bitsToBytes (q.salt.take 256) == D.base.cfg then
        some ⟨0, 174, _root_.Fmt.leafPlace 0 s.2.length ((q.salt.length - 256) / 64), 2 ^ D.a + s.1,
          D.base.cfg, _root_.Fmt.leafBytes s.2 (bitsToBytes (q.salt.drop 256))⟩
      else none
  | _ => leafCall (PDX D dec) q

/-- The typed oracle functions that a function on the format's strings induces. -/
def famX (D : XD) (dec : View → Bool) (O : ByteArray → ByteArray) (K : Nat) :
    Fam (spec 256 K (D.L dec))
  | .leaf, q => ansOf O (leafX D dec q)
  | .node, q => ansOf O (nodeCallC D.base.cfg q)
  | .fb .link, q => (fun k => ansOf O (firstX D dec K q k.castSucc), ansOf O (firstX D dec K q (Fin.last K)))
  | .fb .test, _ => (fun _ _ => false, fun _ => false)
  | .fb .onl, _ => (fun _ _ => false, fun _ => false)
  | .fbw _ _, _ => (fun _ _ => false, fun _ => false)
  | .rleaf, _ => fun _ => false
  | .rnode, _ => fun _ => false
  | .g _, _ => fun _ => false
  | .ann, _ => ()
  | .other, _ => fun _ => false

/-- The verifier. -/
def VX (D : XD) (dec : View → Bool) (r0 r1 : ByteArray)
    (π : OneProtocolProof 256 (skeletonOverBothExternalStrings D.C D.ds D.a D.xs dec).up) : Bool :=
  VPX (I := Unit) (RI := Unit) D.C D.K (chalP D.base.plan.field D.K) D.ds D.a D.xs dec
    (fun _ _ p => (p.val, [])) (fun _ => some ()) (famX D dec _root_.Fmt.oracle (D.K + 1))
    (256 + 8 * D.base.plan.salt) (bytesToDig r0) (bytesToDig r1) π

/-- States that, for all arguments, what runs (`VX`) is the run of the compiled verifier of one
slot, at the tag "link", under the two roots. -/
def Spec.vx_eq : Prop :=
  ∀ (D : XD) (dec : View → Bool) (r0 r1 : ByteArray)
      (π : OneProtocolProof 256 (skeletonOverBothExternalStrings D.C D.ds D.a D.xs dec).up),
    VX D dec r0 r1 π =
      (verifyOneProtocol (lam := 256) (K := D.K + 1) (L := D.L dec) (256 + 8 * D.base.plan.salt) 256 .link
          (skeletonOverBothExternalStrings D.C D.ds D.a D.xs dec).up
          (wqX D.C D.K (chalP D.base.plan.field D.K) D.ds D.a D.xs dec)
          (fun p s => some (.inr ⟨Tag.link, ⟨p, s⟩⟩))
          (embPX D.C D.ds D.a D.xs dec (fun _ _ p => (p.val, [])) (fun _ => some ()))
          (fun _ => none) (fun s => some (.inl s)) 0 [bytesToDig r0, bytesToDig r1] () π).det
        (famX D dec _root_.Fmt.oracle (D.K + 1))

theorem vx_eq : Spec.vx_eq := fun D dec r0 r1 π =>
  vpx_eq Unit Unit D.C D.K (chalP D.base.plan.field D.K) D.ds D.a D.xs dec
    (fun _ _ p => (p.val, [])) (fun _ => some ()) (famX D dec _root_.Fmt.oracle (D.K + 1))
    (256 + 8 * D.base.plan.salt) (bytesToDig r0) (bytesToDig r1) π

/-- the head of an entry file: its eight bytes -/
def headEntry : ByteArray := _root_.Fmt.ascii "CPENH821"

/-- The reader in front: the copy's root; the chain's bytes. -/
def readHead (file : ByteArray) : Option (ByteArray × ByteArray) :=
  if file.size ≥ 40 && file.extract 0 8 == headEntry then
    some (file.extract 8 40, file.extract 40 file.size)
  else none

/-- The run function: from an entry file to an outcome. -/
def runEntry (D : XD) (dec : View → Bool) (r0 file : ByteArray) : Who :=
  if D.ok then
    match readHead file with
    | none => .reader
    | some (r1, rest) =>
      match (_root_.Fmt.wholeChainX (m := Id) _root_.Fmt.formatHash (D.atR r0 r1) rest).bind
          (toBPrfX D.base.plan.salt D.base.cfg D.C D.ds D.a D.xs dec) with
      | none => .reader
      | some π => if VX D dec r0 r1 π then .accepted else .verifier
  else .limits

end Run.PQ
