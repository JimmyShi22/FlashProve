-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Shell/AtWholeId.lean: the exit code 0 of the program, with the commitment ID and the bits.

`main_zero` (OnBytes/Shell/AtWhole.lean) leads from the exit code 0 to the yes of the three
functions that check the key file, the entry file and the proof file.
OnBytes/Model/VerifyLawsId.lean adds what a whole call that passed has tested of the commitment ID
and of the requested bits. OnBytes/Tie/ZeroFacts.lean joins the two, and the theorem of this file is
a short corollary of `Tie.main_zero_facts`, with these clauses in one statement.

Main theorem. `main_zero_id`: all that `main_zero` says, and of the same run: the options as read
hold an ID; in lower-case digits it is the hexadecimal form of `Key.commitmentId` on the tables'
shape and the digest in p, the value that `Verify.planned` returned on the three configuration
files' bytes, and on the table that `Key.check` returned; and the requested bits are 128.

What is not claimed. Nothing on soundness. What the commitment ID fixes is not stated here:
`Key.commitmentId` is a function of the shape, of the digest of the three configuration files, and
of the table's root and answers (the record's seeds, which the hashed string also holds, are drawn
by the hash from shape, digest and root), and nothing is proved here of the hash in it, nor of
`Fmt.hex`: that equal digits mean equal bytes is not stated here; OnBytes/Tie/IdKey.lean proves it
(`hex_inj`). That what enters the hashed string is coded one to one is proved in
OnBytes/Tie/IdKeySeed.lean, of a string that is `Fmt.publishedBytes` by
OnBytes/Tie/IdKeySeedFmt.lean; OnBytes/Tie/IdKey.lean proves the like of the string without the
seeds, which is not what the ID hashes. Neither this file nor OnBytes/Tie/ZeroId.lean says what two
whole calls that returned 0 under one ID share. It is not proved here, of two runs of the term
`main`, that if the two IDs are the same in lower-case
digits, what enters the two IDs is equal (shape, digest, root, answers and the seeds that the
program draws), or the bytes of the two differ and the format's hash, under the number 179, has one
value at both; no probability. The key's proofs,
the entry, the request, the reply and the proof file do not enter the ID. That the digest in p,
which enters the ID, is the digest that the chains in p hold, under which the three checks read, is
not stated here: see OnBytes/Tie/SameChains.lean. That the ID in the options stands right behind
`-id` among the call's options is the matter of the function that reads the options (`readOptions`,
OnBytes/Shell/Whole.lean) and is not stated here: see OnBytes/Shell/AtOptions.lean and
OnBytes/Tie/ZeroNamed.lean. That the caller took it from where the commitment is published is the
caller's matter. The number 128 is what the options' field for the requested bits holds, which is
also its value if the call names no bits: that any round's error is below 2^-128 is not stated. Of
the limits in the head of OnBytes/Shell/AtWhole.lean two are lifted here: the bits of the call, and
the commitment ID and its comparison with the ID in the options. All others hold here too, and those
in the head of OnBytes/Model/VerifyLawsId.lean. The program is the Lean text `verify-on-bytes`;
nothing here is said of the C++ program `cp_verify` or of how its results compare. For proofs only;
the program does not import this file.
-/
import OnBytes.Tie.ZeroFacts

set_option autoImplicit false

namespace OnBytes.Shell

open OnBytes.Model
open OnBytes.Model.Stages (CallEnd StageName Closing)

/-- The exit code 0 of the entry function, which covers both `YES` and `WITHIN LIMITS`. All clauses
but the last three are those of `main_zero`, whose docstring says them in words. The last three: the
options as read hold an ID; in lower-case digits it is the hexadecimal form of `Key.commitmentId` on
the tables' shape and the digest in p and on `table`, the table that `Key.check` returned; and the
requested bits are 128, which is the field of the options, also its value if the call names no bits,
and no bound on an error. -/
theorem main_zero_id {args : List String} {s s' : World} (h : Run (_root_.main args) s 0 s') :
    ∃ (config ivk request y proof : String) (a : Asked) (r : Verify.Read) (lay ent : ByteArray)
      (t : List Event) (p : Verify.Planned) (C : Verify.Common)
      (table further : Params.TableName) (id : String),
      kindOf args = .whole config ivk request y proof a ∧
      Steps opsIO (wholeReads config ivk request y proof r.entry (.bytes r.pol) (.bytes r.KL)
        (.bytes lay) (.bytes r.key) (.bytes r.request) (.bytes r.y) (.bytes r.proof)
        (.bytes ent) ++ t) s s' ∧
      r.layout = some lay ∧ r.key.size ≤ fileLimit ∧ ent.size ≤ fileLimit ∧
      Verify.planned r.pol r.KL (some lay) = .ok p ∧
      Verify.commonOfCall r = .ok C ∧ C.chains = p.chains ∧
      Key.check p.chains.key r.key = .ok table ∧
      Entry.check (p.chains.bytes .link) table ent = .ok further ∧
      (∃ so cov item links,
        Head.stFromCall (Verify.words32 r.request) (Verify.words32 r.y) C.X.T = .ok so ∧
        Head.coveredOf so C.X.T C.X.P.h.V = .ok cov ∧
        Proof.requestItem r.pol r.KL r.request = some item ∧
        Verify.linksOf C.X cov = .ok links ∧
        Proof.check p.chains.proof further r.entry item r.request (ofNat so.y)
          (Stages.runLinksH (C.built.links.zipWith (fun b l => { b with run := l.run }) links)
            p.chains.proof.first C.X.layers.wsLay) r.proof = .accepted) ∧
      a.options.id = some id ∧
      Verify.idAsked id =
        some (Fmt.hex (Key.commitmentId p.chains.tableShape p.cfg table)) ∧
      a.options.bits = 128 := by
  obtain ⟨w, f⟩ := Tie.main_zero_facts h
  exact ⟨w.config, w.ivk, w.request, w.y, w.proof, w.a, w.r, w.lay, w.ent, _, w.p, w.C, w.table,
    w.further, w.id, f.kind, f.steps, f.layout, f.keySize, f.entSize, f.planned, f.common,
    f.chains, f.keyYes, f.entryYes, f.proofYes, f.idRead, f.idFormed, f.bits⟩

end OnBytes.Shell

#print axioms OnBytes.Shell.main_zero_id
