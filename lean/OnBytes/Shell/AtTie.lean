-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Shell/AtTie.lean: from the exit code that the program's entry function returns to a verdict
on the bytes that were read.

`main_iff` (OnBytes/Shell/AtMain.lean) ties a run of the entry function, `program args`, to a run of
the value `call C args`. OnBytes/Shell/AtCall.lean and AtWord.lean say what such a run is. Here the
two are joined. Main theorems:
- `program_passed`, and from it `program_product`, `program_links`, `program_key`, `program_entry`,
  `program_toyProof`: if a call on the files of a test protocol returns the exit code 3, it has read
  the files that the call names, in their order, and the call's function of OnBytes/Shell/Toys.lean
  gives `accepted` on the bytes read. For `product`, `links` and `entry` only, OnBytes/Tie/Program.lean
  goes on from that verdict, under two hypotheses stated there, to a yes of what it
  calls the compiled verifier: a term of the library's theory, not machine code. No soundness claim.
- `program_yes`: if the exit code is 0, the call was a whole call, and `wholeCall`
  (OnBytes/Model/Verify.lean) on the call's options and the answers of its eight reads is a yes or a
  result within limits. OnBytes/Shell/AtWhole.lean goes on from there to the three functions that
  check the files.
- `program_said`, `program_within`: the same for a run that hands over `YES`, or a line that begins
  with W, whatever the exit code.

What is not claimed. Nothing on soundness. An exit code here is the number that `program` returns; a
shell sees it modulo 256, and it is below 256 (`main_small`, OnBytes/Shell/AtMain.lean). The exit
code 3 is also that of a call on one file alone that found no fault: from that 3 no theorem on
`program` starts here; those of OnBytes/Shell/AtPart.lean do. For lines that begin with P or T and
for the line for programs, which check passed is proved for `call C args` alone (`said_part`,
`said_test`, `said_result`, OnBytes/Shell/AtWord.lean), which `main_iff` joins to the program. On
`program` itself there is, from these lines, only `program_sizes` (OnBytes/Shell/AtSize.lean), on
the lengths of the answers. Nothing about compiled code, Lean's run-time or the operating system:
the theorems are about the term `program args` in Lean's model of IO (OnBytes/Shell/AtOps.lean).
Theorems only; the program does not import this file.
-/
import OnBytes.Shell.AtMain
import OnBytes.Shell.AtWord

namespace OnBytes.Shell

open OnBytes.Model.Stages (CallEnd)

/-- If the program, called on the files of a test protocol, returns 3, then it has read the call's
paths in their order, the verdict on the bytes read is `accepted`, and it has printed the line on
proof of work directly before its last line. -/
theorem program_passed {args paths : List String} {notes : List Note}
    {v : List ByteArray → Option Verdict} {w : List ByteArray → Work} {s s' : World}
    (hk : kindOf args = .toy paths notes v w) (h : Run (program args) s 3 s') :
    ∃ (bs : List ByteArray) (o : Option Model.Stages.WorkCount) (least : Nat),
      bs.length = paths.length ∧ v bs = some .accepted ∧ w bs = .ok (o, least) ∧
      Steps opsIO (readEvents paths bs ++
        (saidAll modelChecks.lists (notes.map Line.note ++ [.work o least]) ++
          [.say "TEST FILES PASSED" true])) s s' := by
  obtain ⟨evs, r, h1, h2, h3⟩ := (main_iff modelChecks args s s' 3).1 h
  have n1 : r ≠ .fault := by
    intro e
    rw [e] at h3
    cases h3
  have n2 : r ≠ .unwritten := by
    intro e
    rw [e] at h3
    cases h3
  obtain ⟨pre, l, he, hl⟩ := call_last h1 n1 n2
  have hm : Event.say l true ∈ evs := by
    rw [he]
    exact List.mem_append_right _ List.mem_cons_self
  cases r with
  | fault => exact absurd rfl n1
  | unwritten => exact absurd rfl n2
  | planned => cases h3
  | testPassed =>
    have hl2 : l = Line.testPassed.text modelChecks.lists := hl
    obtain ⟨paths', notes', v', w', bs, o, least, k1, k2, k3, k4, _, k6, _⟩ :=
      said_test (by rw [hl2]; exact hd_text _ _) h1 hm
    rw [hk] at k1
    cases k1
    rw [k6, hl2] at h2
    exact ⟨bs, o, least, k2, k3, k4, h2⟩
  | ended e =>
    exfalso
    obtain ⟨p, hl2⟩ := hl
    cases e with
    | partPassed st cl =>
      have hP : hd l = some 'P' := by
        rw [hl2]
        exact hd_text _ _
      have hne : l ≠ Line.planOnly.text modelChecks.lists := by
        rw [hl2]
        exact partPassed_ne_planOnly _ st
      obtain ⟨_, _, _, _, k⟩ := said_part hP hne h1 hm
      rcases k with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, k1, _⟩ |
        ⟨_, _, _, _, _, _, _, k1, _⟩ | ⟨_, _, _, _, _, _, _, _, _, k1, _⟩ <;>
        · rw [hk] at k1
          cases k1
    | yes a cl => cases h3
    | withinLimits a cl => cases h3
    | notVer cs o cl => cases h3
    | refusedBy st w0 n => cases h3
    | wrongId => cases h3
    | policy w0 => cases h3
    | no n => cases h3
    | notChecked n => cases h3
    | unreadable role => cases h3
    | usage w0 => cases h3

/-- The call `product`, with the paths p of the public file and f of the proof file. If the program
returns 3, it has read p and f, in this order, and `product` on the bytes read is `accepted`. -/
theorem program_product {args : List String} {bits : Nat} {p f : String} {s s' : World}
    (hk : kindOf args = toyKind bits ["product", p, f]) (h : Run (program args) s 3 s') :
    ∃ (pb fb : ByteArray) (t : List Event),
      Steps opsIO (readEvents [p, f] [pb, fb] ++ t) s s' ∧ product bits pb fb = .accepted := by
  obtain ⟨bs, _, _, hl, hv, _, h2⟩ := program_passed hk h
  match bs, hl, hv, h2 with
  | [pb, fb], _, hv, h2 => exact ⟨pb, fb, _, h2, Option.some.inj hv⟩

/-- The call `links`, with the paths p of the public file and f of the proof file. If the program
returns 3, it has read p and f, in this order, and `links` on the bytes read is `accepted`. -/
theorem program_links {args : List String} {bits : Nat} {p f : String} {s s' : World}
    (hk : kindOf args = toyKind bits ["links", p, f]) (h : Run (program args) s 3 s') :
    ∃ (pb fb : ByteArray) (t : List Event),
      Steps opsIO (readEvents [p, f] [pb, fb] ++ t) s s' ∧ links bits pb fb = .accepted := by
  obtain ⟨bs, _, _, hl, hv, _, h2⟩ := program_passed hk h
  match bs, hl, hv, h2 with
  | [pb, fb], _, hv, h2 => exact ⟨pb, fb, _, h2, Option.some.inj hv⟩

/-- The call `key`, with the paths p1 and p2 of the two public files and f of the key file. If the
program returns 3, it has read the three, in this order, and `key` on the bytes read is
`accepted`. -/
theorem program_key {args : List String} {bits : Nat} {p1 p2 f : String} {s s' : World}
    (hk : kindOf args = toyKind bits ["key", p1, p2, f]) (h : Run (program args) s 3 s') :
    ∃ (p1b p2b fb : ByteArray) (t : List Event),
      Steps opsIO (readEvents [p1, p2, f] [p1b, p2b, fb] ++ t) s s' ∧
      key bits p1b p2b fb = .accepted := by
  obtain ⟨bs, _, _, hl, hv, _, h2⟩ := program_passed hk h
  match bs, hl, hv, h2 with
  | [p1b, p2b, fb], _, hv, h2 => exact ⟨p1b, p2b, fb, _, h2, Option.some.inj hv⟩

/-- The call `entry`, with the paths p1 and p2 of the two public files, k of the key file and f of
the entry file. If the program returns 3, it has read the four, in this order, and `entry` on
the bytes read is `accepted`. -/
theorem program_entry {args : List String} {bits : Nat} {p1 p2 k f : String} {s s' : World}
    (hk : kindOf args = toyKind bits ["entry", p1, p2, k, f]) (h : Run (program args) s 3 s') :
    ∃ (p1b p2b kb fb : ByteArray) (t : List Event),
      Steps opsIO (readEvents [p1, p2, k, f] [p1b, p2b, kb, fb] ++ t) s s' ∧
      entry bits p1b p2b kb fb = .accepted := by
  obtain ⟨bs, _, _, hl, hv, _, h2⟩ := program_passed hk h
  match bs, hl, hv, h2 with
  | [p1b, p2b, kb, fb], _, hv, h2 => exact ⟨p1b, p2b, kb, fb, _, h2, Option.some.inj hv⟩

/-- The call `toy-proof`, with the number of the stored copy and seven paths: two public files, the
file that names the table, request, reply, claims, proof file. If the program returns 3, it has read
the seven, in this order, and `toyProof` on the number and the bytes read is `accepted`. -/
theorem program_toyProof {args : List String} {bits : Nat}
    {p1 p2 tf number rq rp cl f : String} {s s' : World}
    (hk : kindOf args = toyKind bits ["toy-proof", p1, p2, tf, number, rq, rp, cl, f])
    (h : Run (program args) s 3 s') :
    ∃ (p1b p2b tb rqb rpb clb fb : ByteArray) (t : List Event),
      Steps opsIO (readEvents [p1, p2, tf, rq, rp, cl, f] [p1b, p2b, tb, rqb, rpb, clb, fb] ++ t)
        s s' ∧
      toyProof bits p1b p2b tb number rqb rpb clb fb = .accepted := by
  obtain ⟨bs, _, _, hl, hv, _, h2⟩ := program_passed hk h
  match bs, hl, hv, h2 with
  | [p1b, p2b, tb, rqb, rpb, clb, fb], _, hv, h2 =>
    exact ⟨p1b, p2b, tb, rqb, rpb, clb, fb, _, h2, Option.some.inj hv⟩

/-- The exit code 0. If the program returns 0, the call was a whole call; the result e of
`wholeCall` (OnBytes/Model/Verify.lean) on the call's options and the answers of its eight reads is
a yes or a result within limits; and from s to s' the three operations gave the answers of these
eight reads and took the lines of e, the last of which is `YES` or begins with `WITHIN LIMITS`. -/
theorem program_yes {args : List String} {s s' : World} (h : Run (program args) s 0 s') :
    ∃ (config ivk request y proof : String) (a : Asked)
      (pol kl lay key req yy prf ent : FileRead) (k : Nat) (e : CallEnd),
      kindOf args = .whole config ivk request y proof a ∧
      Model.Verify.entryNumber a.options (filesOf pol kl lay key req yy prf) = .ok k ∧
      Model.Verify.wholeCall a.options
        { filesOf pol kl lay key req yy prf with entry := fileIn ent } = e ∧
      (∃ about cl, e = .yes about cl ∨ e = .withinLimits about cl) ∧
      Steps opsIO ([.read (config ++ "/policy.txt") (textLimit + 1) pol,
        .read (config ++ "/KL.bin") (fileLimit + 1) kl,
        .read (config ++ "/layout.txt") (textLimit + 1) lay,
        .read (ivk ++ "/key.bin") (fileLimit + 1) key, .read request (fileLimit + 1) req,
        .read y (fileLimit + 1) yy, .read proof (fileLimit + 1) prf,
        .read (ivk ++ "/leaf/" ++ toString k ++ ".bin") (fileLimit + 1) ent] ++
        (saidAll modelChecks.lists (before { bits := a.options.bits, leaf := k } e) ++
          [.say ((verdict {} e).text modelChecks.lists) true])) s s' := by
  obtain ⟨evs, r, h1, h2, h3⟩ := (main_iff modelChecks args s s' 0).1 h
  obtain ⟨about, cl, hr⟩ := status_zero h3
  have n1 : r ≠ .fault := by
    rcases hr with rfl | rfl <;> exact fun e => by cases e
  have n2 : r ≠ .unwritten := by
    rcases hr with rfl | rfl <;> exact fun e => by cases e
  obtain ⟨pre, l, he, hl⟩ := call_last h1 n1 n2
  have hm : Event.say l true ∈ evs := by
    rw [he]
    exact List.mem_append_right _ List.mem_cons_self
  rcases hr with rfl | rfl
  · obtain ⟨p, hl2⟩ := hl
    have hl3 : l = "YES" := hl2
    rw [hl3] at hm
    obtain ⟨config, ivk, request, y, proof, a, pol, kl, lay, key, req, yy, prf, ent, k, ab, c2, k1,
      k2, k3, k4, _⟩ := said_yes h1 hm
    rw [k4] at h2
    exact ⟨config, ivk, request, y, proof, a, pol, kl, lay, key, req, yy, prf, ent, k, _, k1, k2,
      k3, ⟨ab, c2, Or.inl rfl⟩, h2⟩
  · obtain ⟨p, hl2⟩ := hl
    obtain ⟨config, ivk, request, y, proof, a, pol, kl, lay, key, req, yy, prf, ent, k, ab, c2, k1,
      k2, k3, k4, k5, _⟩ := said_within (by rw [hl2]; exact hd_text _ _) h1 hm
    rw [k5, k4] at h2
    exact ⟨config, ivk, request, y, proof, a, pol, kl, lay, key, req, yy, prf, ent, k, _, k1, k2,
      k3, ⟨ab, c2, Or.inr rfl⟩, h2⟩

/-- The word `YES`, for the program itself. Whatever code the program returns, it has a run with the
answers that the three operations gave; and if that run hands the line `YES` to standard output,
whether or not that succeeds, the call was a whole call, and `wholeCall` (OnBytes/Model/Verify.lean)
on the call's options and the answers of the run's eight reads is a yes.
By `steps_one` (OnBytes/Shell/AtOps.lean) there is no other run from the same state. -/
theorem program_said {args : List String} {s s' : World} {c : UInt32}
    (h : Run (program args) s c s') :
    ∃ evs r, (call modelChecks args).Ends evs r ∧ Steps opsIO evs s s' ∧ r.status = c ∧
      ∀ ok, Event.say "YES" ok ∈ evs →
        ∃ (config ivk request y proof : String) (a : Asked)
          (pol kl lay key req yy prf ent : FileRead) (k : Nat) (about : Model.Stages.Covered)
          (cl : Model.Stages.Closing),
          kindOf args = .whole config ivk request y proof a ∧
          Model.Verify.entryNumber a.options (filesOf pol kl lay key req yy prf) = .ok k ∧
          Model.Verify.wholeCall a.options
            { filesOf pol kl lay key req yy prf with entry := fileIn ent } = .yes about cl ∧
          evs = [.read (config ++ "/policy.txt") (textLimit + 1) pol,
            .read (config ++ "/KL.bin") (fileLimit + 1) kl,
            .read (config ++ "/layout.txt") (textLimit + 1) lay,
            .read (ivk ++ "/key.bin") (fileLimit + 1) key, .read request (fileLimit + 1) req,
            .read y (fileLimit + 1) yy, .read proof (fileLimit + 1) prf,
            .read (ivk ++ "/leaf/" ++ toString k ++ ".bin") (fileLimit + 1) ent] ++
            (saidAll modelChecks.lists
              (before { bits := a.options.bits, leaf := k } (.yes about cl)) ++
              saidLast "YES" ok) := by
  obtain ⟨evs, r, h1, h2, h3⟩ := (main_iff modelChecks args s s' c).1 h
  refine ⟨evs, r, h1, h2, h3, fun ok hm => ?_⟩
  obtain ⟨config, ivk, request, y, proof, a, pol, kl, lay, key, req, yy, prf, ent, k, ab, cl, e0,
    e1, e2, e3, _⟩ := said_yes h1 hm
  exact ⟨config, ivk, request, y, proof, a, pol, kl, lay, key, req, yy, prf, ent, k, ab, cl, e0, e1,
    e2, e3⟩

/-- The words `WITHIN LIMITS`, for the program itself. As `program_said`, for a line that begins
with W: `wholeCall` on the call's options and the answers of the run's eight reads is a result
within limits, and the line is that result's last line. -/
theorem program_within {args : List String} {s s' : World} {c : UInt32}
    (h : Run (program args) s c s') :
    ∃ evs r, (call modelChecks args).Ends evs r ∧ Steps opsIO evs s s' ∧ r.status = c ∧
      ∀ l ok, hd l = some 'W' → Event.say l ok ∈ evs →
        ∃ (config ivk request y proof : String) (a : Asked)
          (pol kl lay key req yy prf ent : FileRead) (k : Nat) (about : Model.Stages.Covered)
          (cl : Model.Stages.Closing),
          kindOf args = .whole config ivk request y proof a ∧
          Model.Verify.entryNumber a.options (filesOf pol kl lay key req yy prf) = .ok k ∧
          Model.Verify.wholeCall a.options
            { filesOf pol kl lay key req yy prf with entry := fileIn ent } =
              .withinLimits about cl ∧
          l = (Line.withinLimits about).text modelChecks.lists ∧
          evs = [.read (config ++ "/policy.txt") (textLimit + 1) pol,
            .read (config ++ "/KL.bin") (fileLimit + 1) kl,
            .read (config ++ "/layout.txt") (textLimit + 1) lay,
            .read (ivk ++ "/key.bin") (fileLimit + 1) key, .read request (fileLimit + 1) req,
            .read y (fileLimit + 1) yy, .read proof (fileLimit + 1) prf,
            .read (ivk ++ "/leaf/" ++ toString k ++ ".bin") (fileLimit + 1) ent] ++
            (saidAll modelChecks.lists
              (before { bits := a.options.bits, leaf := k } (.withinLimits about cl)) ++
              saidLast l ok) := by
  obtain ⟨evs, r, h1, h2, h3⟩ := (main_iff modelChecks args s s' c).1 h
  refine ⟨evs, r, h1, h2, h3, fun l ok hc hm => ?_⟩
  obtain ⟨config, ivk, request, y, proof, a, pol, kl, lay, key, req, yy, prf, ent, k, ab, cl, e0,
    e1, e2, e3, e4, _⟩ := said_within hc h1 hm
  exact ⟨config, ivk, request, y, proof, a, pol, kl, lay, key, req, yy, prf, ent, k, ab, cl, e0, e1,
    e2, e3, e4⟩

end OnBytes.Shell

#print axioms OnBytes.Shell.program_within
#print axioms OnBytes.Shell.program_said
#print axioms OnBytes.Shell.program_yes
#print axioms OnBytes.Shell.program_product
#print axioms OnBytes.Shell.program_toyProof
