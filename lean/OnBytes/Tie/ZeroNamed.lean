-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/ZeroNamed.lean: the exit code 0 of the program, with one digest, and one shape where a
shape is held, in the chains that were read back from their parameter bytes, and with the commitment
ID as it stands among the call's options.

OnBytes/Tie/SameChains.lean proves that where the three checks of a call said yes, the chains in p
hold one digest, and those that hold a shape one shape (`SameChains`; `tableShape_oneTime` stands
there too). Here "a chain in p" is what the program has read back from that chain's parameter bytes,
not the chain in a file. OnBytes/Shell/AtOptions.lean proves that the ID which the options as read
hold stands among the call's options, behind the five names, right behind `-id`.
OnBytes/Tie/ZeroFacts.lean joins these with the other clauses on the exit code 0, and the two
theorems of this file are short corollaries of `main_zero_facts`, each with a part of the clauses in
one statement.

Main theorems. `main_zero_same`: all that `main_zero_id` (OnBytes/Shell/AtWholeId.lean) says of the
exit code 0, and of the same run `SameChains`. `main_zero_named`: all that `main_zero_same` says,
and of the same run: the arguments are `verify`, the five names, and options that hold `-id` and,
right behind it, the ID.

What is not claimed. Nothing on soundness. `SameChains` speaks of the chains that `Verify.planned`
returns and the checks are given, not of bytes in the key file, the entry file or the proof file:
whether each check binds its file to the digest that its chains hold can only be read off the code
and is no theorem. `SameChains p d` is a property of the three configuration files alone: of the
checks' yes the proofs use only that the parameter bytes are few. Of the limits in the head of
OnBytes/Shell/AtWholeId.lean, with those of OnBytes/Shell/AtWhole.lean that it keeps, three are
lifted here. Two by `main_zero_same`: that the chains under which the three checks ran hold the same
shape of the stored tables and the same digest, and that the digest in p, which enters the
commitment ID, is the digest that these chains hold. One by `main_zero_named`: that the ID in the
options stands right behind `-id` among the options of the command line. That last clause follows
from two clauses of `main_zero_same`: it says openly what they hold and adds no further fact on the
run. All other limits in the heads of OnBytes/Tie/SameChains.lean and OnBytes/Shell/AtOptions.lean
hold here too. The program is the Lean text `verify-on-bytes`; nothing here is said of the C++
program `cp_verify` or of how its results compare. For proofs only; the program does not import this
file.
-/
import OnBytes.Tie.ZeroFacts

set_option autoImplicit false

namespace OnBytes.Tie

open OnBytes.Shell (Steps opsIO World Event fileLimit wholeReads kindOf Asked)
open OnBytes.Proof

/-- The exit code 0 of the entry function, which covers both `YES` and `WITHIN LIMITS`. All clauses
but the last are those of `main_zero_id`, whose docstring and `main_zero`'s say them in words; the
number 128 is that of the options' field for the requested bits, which is also its value if the call
names no bits, and no bound on an error. The last clause: the digest in p and in each of the seven
chains in p is the digest of the three configuration files' bytes, the chains that hold a shape of
the stored tables hold one shape, and the entry's chain in p is what `Entry.check` reads from the
bytes that it is given. The shape that enters the commitment ID, `p.chains.tableShape`, is the one
in the key's one-time chain (`tableShape_oneTime`), so it is that one shape. -/
theorem main_zero_same {args : List String} {s s' : World}
    (h : Shell.Run (_root_.main args) s 0 s') :
    ∃ (config ivk request y proof : String) (a : Asked) (r : Model.Verify.Read)
      (lay ent : ByteArray)
      (t : List Event) (p : Model.Verify.Planned) (C : Model.Verify.Common)
      (table further : Params.TableName) (id : String),
      kindOf args = .whole config ivk request y proof a ∧
      Steps opsIO (wholeReads config ivk request y proof r.entry (.bytes r.pol) (.bytes r.KL)
        (.bytes lay) (.bytes r.key) (.bytes r.request) (.bytes r.y) (.bytes r.proof)
        (.bytes ent) ++ t) s s' ∧
      r.layout = some lay ∧ r.key.size ≤ fileLimit ∧ ent.size ≤ fileLimit ∧
      Model.Verify.planned r.pol r.KL (some lay) = .ok p ∧
      Model.Verify.commonOfCall r = .ok C ∧ C.chains = p.chains ∧
      Key.check p.chains.key r.key = .ok table ∧
      Entry.check (p.chains.bytes .link) table ent = .ok further ∧
      (∃ so cov item links,
        Model.Head.stFromCall (Model.Verify.words32 r.request) (Model.Verify.words32 r.y) C.X.T =
          .ok so ∧
        Model.Head.coveredOf so C.X.T C.X.P.h.V = .ok cov ∧
        Proof.requestItem r.pol r.KL r.request = some item ∧
        Model.Verify.linksOf C.X cov = .ok links ∧
        Proof.check p.chains.proof further r.entry item r.request (Model.ofNat so.y)
          (Model.Stages.runLinksH (C.built.links.zipWith (fun b l => { b with run := l.run }) links)
            p.chains.proof.first C.X.layers.wsLay) r.proof = .accepted) ∧
      a.options.id = some id ∧
      Model.Verify.idAsked id =
        some (Fmt.hex (Key.commitmentId p.chains.tableShape p.cfg table)) ∧
      a.options.bits = 128 ∧
      SameChains p (Params.configurationDigest [r.pol, lay, r.KL]) := by
  obtain ⟨w, f⟩ := main_zero_facts h
  exact ⟨w.config, w.ivk, w.request, w.y, w.proof, w.a, w.r, w.lay, w.ent, _, w.p, w.C, w.table,
    w.further, w.id, f.kind, f.steps, f.layout, f.keySize, f.entSize, f.planned, f.common,
    f.chains, f.keyYes, f.entryYes, f.proofYes, f.idRead, f.idFormed, f.bits, f.same⟩

/-- The exit code 0 of the entry function, which covers both `YES` and `WITHIN LIMITS`. The first
clause: the arguments are `verify`, the five names, and options that hold `-id` and, right behind
it, the ID `id`; that the pair stands in the options once is not stated. All other clauses are those
of `main_zero_same`, whose docstring says them in words or names where they are said; `id` is the ID
of which they speak. -/
theorem main_zero_named {args : List String} {s s' : World}
    (h : Shell.Run (_root_.main args) s 0 s') :
    ∃ (config ivk request y proof : String) (a : Asked) (r : Model.Verify.Read)
      (lay ent : ByteArray)
      (t : List Event) (p : Model.Verify.Planned) (C : Model.Verify.Common)
      (table further : Params.TableName) (id : String) (pre post : List String),
      args = "verify" :: config :: ivk :: request :: y :: proof ::
        (pre ++ "-id" :: id :: post) ∧
      kindOf args = .whole config ivk request y proof a ∧
      Steps opsIO (wholeReads config ivk request y proof r.entry (.bytes r.pol) (.bytes r.KL)
        (.bytes lay) (.bytes r.key) (.bytes r.request) (.bytes r.y) (.bytes r.proof)
        (.bytes ent) ++ t) s s' ∧
      r.layout = some lay ∧ r.key.size ≤ fileLimit ∧ ent.size ≤ fileLimit ∧
      Model.Verify.planned r.pol r.KL (some lay) = .ok p ∧
      Model.Verify.commonOfCall r = .ok C ∧ C.chains = p.chains ∧
      Key.check p.chains.key r.key = .ok table ∧
      Entry.check (p.chains.bytes .link) table ent = .ok further ∧
      (∃ so cov item links,
        Model.Head.stFromCall (Model.Verify.words32 r.request) (Model.Verify.words32 r.y) C.X.T =
          .ok so ∧
        Model.Head.coveredOf so C.X.T C.X.P.h.V = .ok cov ∧
        Proof.requestItem r.pol r.KL r.request = some item ∧
        Model.Verify.linksOf C.X cov = .ok links ∧
        Proof.check p.chains.proof further r.entry item r.request (Model.ofNat so.y)
          (Model.Stages.runLinksH (C.built.links.zipWith (fun b l => { b with run := l.run }) links)
            p.chains.proof.first C.X.layers.wsLay) r.proof = .accepted) ∧
      a.options.id = some id ∧
      Model.Verify.idAsked id =
        some (Fmt.hex (Key.commitmentId p.chains.tableShape p.cfg table)) ∧
      a.options.bits = 128 ∧
      SameChains p (Params.configurationDigest [r.pol, lay, r.KL]) := by
  obtain ⟨w, f⟩ := main_zero_facts h
  obtain ⟨pre, post, e⟩ := f.named
  exact ⟨w.config, w.ivk, w.request, w.y, w.proof, w.a, w.r, w.lay, w.ent, _, w.p, w.C, w.table,
    w.further, w.id, pre, post, e, f.kind, f.steps, f.layout, f.keySize, f.entSize, f.planned,
    f.common, f.chains, f.keyYes, f.entryYes, f.proofYes, f.idRead, f.idFormed, f.bits, f.same⟩

end OnBytes.Tie

#print axioms OnBytes.Tie.main_zero_same
#print axioms OnBytes.Tie.main_zero_named
