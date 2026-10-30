-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Shell/AtWholeKind.lean: the exit code 0 of the program: the run, and the result with its
kind and its last line, so that `YES` and `WITHIN LIMITS` stay apart.

If `program args` returns 0, the call was a whole call, and its run was eight reads, the lines of a
result e before its last, and one more line l. This file says so, and which result it was: e is a
yes and l is `YES`, or e is a result within limits and l is that result's last line. `program_yes`
(OnBytes/Shell/AtTie.lean) keeps the two apart already, with the last line as a function of e; it
lacks the run of `call` and the sizes of the answers. The theorem here has all of these of one run.
`program_zero_run` (OnBytes/Shell/AtWhole.lean) is a corollary that says of e only that it is a
passing result.

Main definition: `wholeReads`. Main theorem: `program_zero_kind`.

What is not claimed. Nothing on soundness. All limits in the head of OnBytes/Shell/AtWhole.lean hold
here too. What a yes is about, and what a result within limits is about, is not stated: the values
`about` and `cl` are named and nothing is said of them. The program is the Lean port built from
OnBytes/; nothing here is said of the C++ program `cp_verify` or of how its results compare. For
proofs only; the program does not import this file.

-/
import OnBytes.Shell.AtPart
import OnBytes.Model.VerifyLawsWhole

set_option autoImplicit false

namespace OnBytes.Shell

open OnBytes.Model
open OnBytes.Model.Stages (CallEnd StageName Closing Covered)

/-- The eight reads of a whole call with their answers. k: the number of the entry. -/
def wholeReads (config ivk request y proof : String) (k : Nat)
    (pol kl lay key req yy prf ent : FileRead) : List Event :=
  [.read (config ++ "/policy.txt") (textLimit + 1) pol,
   .read (config ++ "/KL.bin") (fileLimit + 1) kl,
   .read (config ++ "/layout.txt") (textLimit + 1) lay,
   .read (ivk ++ "/key.bin") (fileLimit + 1) key, .read request (fileLimit + 1) req,
   .read y (fileLimit + 1) yy, .read proof (fileLimit + 1) prf,
   .read (ivk ++ "/leaf/" ++ toString k ++ ".bin") (fileLimit + 1) ent]

/-- The exit code 0, with the kind of the result. All clauses but the fourth are those of
`program_zero_run`, whose docstring says them in words. The fourth stands in the place of the clause
that e is a passing result: either e is a yes and the last line l is `YES`, or e is a result within
limits and l is the text of that result's last line. Nothing is said of `about` and `cl`. -/
theorem program_zero_kind {args : List String} {s s' : World} (h : Run (program args) s 0 s') :
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
      (∃ (about : Covered) (cl : Closing),
        (e = .yes about cl ∧ l = "YES") ∨
          (e = .withinLimits about cl ∧ l = (Line.withinLimits about).text modelChecks.lists)) ∧
      Verify.entryNumber a.options (filesOf pol kl lay key req yy prf) = .ok k ∧
      Verify.wholeCall a.options { filesOf pol kl lay key req yy prf with entry := fileIn ent } =
        e ∧
      ∀ q n (b : ByteArray),
        Event.read q n (.bytes b) ∈
          wholeReads config ivk request y proof k pol kl lay key req yy prf ent → b.size < n := by
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
    subst hl3
    have sz : ∀ q n (b : ByteArray), Event.read q n (.bytes b) ∈ evs → b.size < n :=
      fun q n b hq => pass_sizes h1 hm (c := 'Y') (by decide) (by decide) hq
    obtain ⟨config, ivk, request, y, proof, a, pol, kl, lay, key, req, yy, prf, ent, k, ab, c2, k1,
      k2, k3, k4, k5⟩ := said_yes h1 hm
    cases k5
    subst k4
    exact ⟨config, ivk, request, y, proof, a, pol, kl, lay, key, req, yy, prf, ent, k, _, _, k1,
      h1, h2, ⟨_, _, Or.inl ⟨rfl, rfl⟩⟩, k2, k3,
      fun q n b hq => sz q n b (List.mem_append_left _ hq)⟩
  · obtain ⟨p, hl2⟩ := hl
    have hW : hd l = some 'W' := by
      rw [hl2]
      exact hd_text _ _
    have sz : ∀ q n (b : ByteArray), Event.read q n (.bytes b) ∈ evs → b.size < n :=
      fun q n b hq => pass_sizes h1 hm hW (by decide) hq
    obtain ⟨config, ivk, request, y, proof, a, pol, kl, lay, key, req, yy, prf, ent, k, ab, c2, k1,
      k2, k3, kl2, k4, k5⟩ := said_within hW h1 hm
    cases k5
    subst k4
    exact ⟨config, ivk, request, y, proof, a, pol, kl, lay, key, req, yy, prf, ent, k, _, _, k1,
      h1, h2, ⟨_, _, Or.inr ⟨rfl, kl2⟩⟩, k2, k3,
      fun q n b hq => sz q n b (List.mem_append_left _ hq)⟩

end OnBytes.Shell
