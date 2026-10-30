-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Shell/AtWhole.lean: from the exit code 0 of the program to the yes of the three functions
that check the key file, the entry file and the proof file.

The exit code 0 is that of a whole call, the command `verify` on a request, that ended with `YES` or
with `WITHIN LIMITS` (`program_yes`, OnBytes/Shell/AtTie.lean). OnBytes/Model/VerifyLawsWhole.lean
unfolds the function behind that call. OnBytes/Shell/AtWholeKind.lean and OnBytes/Tie/ZeroFacts.lean
join the two and gather the clauses that the theorems named there state of the exit code 0, once, by
name. The two theorems of this file are short corollaries, each with a part of these clauses in one
statement: `program_zero_run` of `program_zero_kind`, `main_zero` of `Tie.main_zero_facts`.

Main theorems. The eight reads, `wholeReads`, are defined in OnBytes/Shell/AtWholeKind.lean.
- `program_zero_run`: if `program args` returns 0, the call was a whole call; the run of
  `call modelChecks args` whose answers the program's three operations gave was eight reads, the
  lines of a passing result e before its last, and one more line; `Verify.wholeCall` on the call's
  options and the eight answers is e; and every answer with bytes has fewer bytes than were asked
  for.
- `main_zero`, on the entry function `main`: if `main args` returns 0, then moreover all eight reads
  were answered with bytes; the answers for the key file and the entry file are within the files'
  limit; `Verify.planned` on the bytes of the three configuration files returned a value p;
  `Key.check` said yes on the bytes of the key file, under the key's three chains in p;
  `Entry.check` said yes on the bytes of the entry file, under the parameter bytes of the entry's
  chain in p and against the table that `Key.check` returned; and `Proof.check` said `accepted` on
  the bytes of the proof file, under the proof's three chains in p and against the table that
  `Entry.check` returned.

What is not claimed. Nothing on soundness: the theorems say which function said yes on which bytes,
not what such a yes is worth. So they do not say that the reply is the model's. The exit code 0
covers both last lines of a whole call that passed, `YES` and `WITHIN LIMITS`; `main_zero` does not
say which it was (`program_zero_run` gives the result e; `Tie.ZeroFacts.kinds` says which). The
tables that the checks share are values of `Params.TableName`: a root and the answers of a record.
Each check reads them under the shape and the digest in the chains that it is given for its file;
that the chains under which the three checks run hold the same shape and digest is not stated here:
see OnBytes/Tie/SameChains.lean. Much of what a whole call tests is in no conclusion here: what the
tests before the stages test (`Verify.readCall`); what `Verify.planned` tests; that the statement's
item fits what the sub-proofs use (`Verify.statementHeld`); the stages' accounting, so whether the
plans in p meet a target, and the bits of the call; the commitment ID and its comparison with the
option `-id`; the acceptance policy; what the result is about, that is which positions of the
request; and the conditions of the standard parameter form. How request and reply enter is stated
only as far as the arguments of `Proof.check` show it: what that function binds is not. Of the links
that `Proof.check` is given, only their form is stated. An exit code here is the number that `main`
returns; a shell sees it modulo 256. No step to the compiled verifier (a term of the library's Lean
theory, not machine code) is made here. The converse is not stated,
and nothing says that some files make a call pass. The bytes are the answers of the program's reads
in Lean's model of IO (OnBytes/Shell/AtOps.lean): Lean's logic knows nothing of files, so nothing
says that they are a file's content. Nothing about compiled code, Lean's run-time or the operating
system. The program is the Lean text `verify-on-bytes`; nothing here is said of the C++ program
`cp_verify` or of how its results compare. For proofs only; the program does not import this file.
-/
import OnBytes.Tie.ZeroFacts

set_option autoImplicit false

namespace OnBytes.Shell

open OnBytes.Model
open OnBytes.Model.Stages (CallEnd StageName Closing)

/-- The exit code 0. If the program returns 0, the call was a whole call. The run of
`call modelChecks args` whose answers the three operations gave was eight reads, the lines of a
passing result e before its last, and one more line l, written with success; that l is e's last line
is stated in `program_yes` (OnBytes/Shell/AtTie.lean), not here. The tests before the entry is read
returned the number k of the entry, and `Verify.wholeCall` on the call's options and the eight
answers is e. Every read that was answered with bytes got fewer bytes than it asked for. -/
theorem program_zero_run {args : List String} {s s' : World} (h : Run (program args) s 0 s') :
    ∃ (config ivk request y proof : String) (a : Asked)
      (pol kl lay key req yy prf ent : FileRead) (k : Nat) (e : CallEnd) (l : String),
      kindOf args = .whole config ivk request y proof a ∧
      (call modelChecks args).Ends
        (wholeReads config ivk request y proof k pol kl lay key req yy prf ent ++
          (saidAll modelChecks.lists (before { bits := a.options.bits, leaf := k } e) ++
            [.say l true])) (.ended e) ∧
      Steps opsIO (wholeReads config ivk request y proof k pol kl lay key req yy prf ent ++
        (saidAll modelChecks.lists (before { bits := a.options.bits, leaf := k } e) ++
          [.say l true])) s s' ∧
      e.passing = true ∧
      Verify.entryNumber a.options (filesOf pol kl lay key req yy prf) = .ok k ∧
      Verify.wholeCall a.options { filesOf pol kl lay key req yy prf with entry := fileIn ent } =
        e ∧
      ∀ q n (b : ByteArray),
        Event.read q n (.bytes b) ∈
          wholeReads config ivk request y proof k pol kl lay key req yy prf ent → b.size < n := by
  obtain ⟨config, ivk, request, y, proof, a, pol, kl, lay, key, req, yy, prf, ent, k, e, l, k1, h1,
    h2, hk, k2, k3, sz⟩ := program_zero_kind h
  refine ⟨config, ivk, request, y, proof, a, pol, kl, lay, key, req, yy, prf, ent, k, e, l, k1, h1,
    h2, ?_, k2, k3, sz⟩
  obtain ⟨ab, cl, ⟨e1, _⟩ | ⟨e1, _⟩⟩ := hk <;> rw [e1] <;> rfl

/-- The exit code 0 of the entry function, which covers both `YES` and `WITHIN LIMITS`. If
`main args` returns 0, the call was a whole call, and the program's operations gave eight reads that
were answered with bytes, and then the steps t. r holds the bytes of seven of them and a number,
`r.entry`: the eighth read is of the entry file with that number, and `Proof.check` is given it;
that it is the number in the proof file's head is not stated here. lay is the layout file's bytes,
which r holds too, and ent the entry file's. The key file's and the entry file's bytes are within
the files' limit. `Verify.planned` on the three configuration files' bytes returned p, and the
common beginning of the stages returned C, which holds p's chains. `Key.check` said yes on the key
file's bytes, under the key's three chains in p, and returned `table`. `Entry.check` said yes on the
entry file's bytes, under the parameter bytes of the entry's chain in p and against `table`, and
returned `further`. `Proof.check` said `accepted` on the proof file's bytes, under the proof's three
chains in p and against `further`, with the entry's number, the item that `Proof.requestItem` forms,
the request file's own bytes, the reply of the call, and the links as built, each with the check
that knows the request. -/
theorem main_zero {args : List String} {s s' : World} (h : Run (_root_.main args) s 0 s') :
    ∃ (config ivk request y proof : String) (a : Asked) (r : Verify.Read) (lay ent : ByteArray)
      (t : List Event) (p : Verify.Planned) (C : Verify.Common)
      (table further : Params.TableName),
      kindOf args = .whole config ivk request y proof a ∧
      Steps opsIO (wholeReads config ivk request y proof r.entry (.bytes r.pol) (.bytes r.KL)
        (.bytes lay) (.bytes r.key) (.bytes r.request) (.bytes r.y) (.bytes r.proof)
        (.bytes ent) ++ t) s s' ∧
      r.layout = some lay ∧ r.key.size ≤ fileLimit ∧ ent.size ≤ fileLimit ∧
      Verify.planned r.pol r.KL (some lay) = .ok p ∧
      Verify.commonOfCall r = .ok C ∧ C.chains = p.chains ∧
      Key.check p.chains.key r.key = .ok table ∧
      Entry.check (p.chains.bytes .link) table ent = .ok further ∧
      ∃ so cov item links,
        Head.stFromCall (Verify.words32 r.request) (Verify.words32 r.y) C.X.T = .ok so ∧
        Head.coveredOf so C.X.T C.X.P.h.V = .ok cov ∧
        Proof.requestItem r.pol r.KL r.request = some item ∧
        Verify.linksOf C.X cov = .ok links ∧
        Proof.check p.chains.proof further r.entry item r.request (ofNat so.y)
          (Stages.runLinksH (C.built.links.zipWith (fun b l => { b with run := l.run }) links)
            p.chains.proof.first C.X.layers.wsLay) r.proof = .accepted := by
  obtain ⟨w, f⟩ := Tie.main_zero_facts h
  exact ⟨w.config, w.ivk, w.request, w.y, w.proof, w.a, w.r, w.lay, w.ent, _, w.p, w.C, w.table,
    w.further, f.kind, f.steps, f.layout, f.keySize, f.entSize, f.planned, f.common, f.chains,
    f.keyYes, f.entryYes, f.proofYes⟩

end OnBytes.Shell

#print axioms OnBytes.Shell.program_zero_run
#print axioms OnBytes.Shell.main_zero
