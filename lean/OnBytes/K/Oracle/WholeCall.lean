-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/K/Oracle/WholeCall.lean: `PortYesAt` (OnBytes/K/Top.lean) from a pass of the program's own
pure function on the bytes of a whole call, `Model.Verify.wholeCall`. A pass is `.passing = true`:
of a whole call that is the result YES or the result WITHIN LIMITS (`status_of_passing`,
OnBytes/K/Oracle/ExitOf.lean, states the status 0; these two results alone have it: `status_zero`,
OnBytes/Shell/AtCall.lean).

Why. `PortYesAt F id table further` says what the exit code 0 of the entry function hands on about
the eight files' bytes. The theorems on the entry file's checker have it as a hypothesis. Whether
any files meet it cannot be asked at the entry function: `main` reads its files by operations of
Lean's core, constants without a body that the kernel can unfold, so no run of `main` can be
exhibited in Lean. Behind its reads the program is a pure function of options and bytes,
`wholeCall`. `main_zero_port` (OnBytes/K/Top.lean) has `PortYesAt`, at some two tables, from the
exit code 0. This file has it, at some two tables and for all files, from a pass of `wholeCall`, the
entry's number and the bounds on the files' sizes: no run of the shell stands in its statement.

So "some files meet `PortYesAt`" is had from ONE closed equation on eight byte strings and the
options: `(wholeCall o (callOf F)).passing = true`, beside `entryNumber o (callOf F) = .ok F.entry`
and eight comparisons of sizes. One way alone is proved.

The options o are free. A pass forces an ID in them and the bits 128, and the theorem says both.
`nextToken`, `policy` and `noProofOfWork` stay free in the statement's form (that a pass can be had
at each of their values is not said): under a named policy the pass can be WITHIN LIMITS, which can
say less than YES (OnBytes/Model/VerifyInputs.lean). The last clause of `main_zero_served`
(OnBytes/K/ExitServed.lean), that with the served options the statement is served at the call's own
three public files (`servedAt`, by `wholeCall_served`, OnBytes/K/ServedLaws.lean), comes from the
same pass and is in the conclusion too.

Main definitions: `callOf` (the eight files as `wholeCall` takes them), `Within` (the program's
limits on their sizes).
Main theorem: `portYes_of_wholeCall`.

What is not claimed. THAT THE EQUATION HOLDS OF ANY FILES: it is proved of none here. THAT A CALL OF
THE PROGRAM ENDS WITH THE EXIT CODE 0 WHERE `wholeCall` PASSES: `main_zero_served` goes from the
exit code to the pure function, and nothing in this file goes back; the way back, in Lean's model of
the program, is OnBytes/K/Oracle/ExitOf.lean. At the small example the three larger files have about
1.1, 0.5 and 4.2 million bytes; no attempt was made to have the kernel evaluate `wholeCall` on them.
That the compiled program ends in 0 on some files is a fact of a run of compiled code, on the build
that ran, and no theorem; it speaks of this file's term only if that build was made from the same
sources. Nothing on the shell: that `main` hands `wholeCall` the bytes that lie on a disk is not
said here. `PortYesAt` is weaker than the exit code 0 (the head of OnBytes/K/Top.lean). Nothing on
soundness; no probability.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.K.Top

set_option autoImplicit false

namespace OnBytes.K.Oracle

open OnBytes.Shell (fileLimit textLimit)
open OnBytes.Model.Verify (Options wholeCall entryNumber)

/-- The eight files of a whole call as the program's pure function takes them: each was read. -/
def callOf (F : Files) : Model.Verify.Files where
  policy := some F.pol
  KL := some F.KL
  layout := some (some F.lay)
  key := some F.key
  request := some F.request
  y := some F.y
  proof := some F.proof
  entry := some F.ent

/-- The program's limits on the sizes of the eight files. -/
def Within (F : Files) : Prop :=
  F.key.size ≤ fileLimit ∧ F.ent.size ≤ fileLimit ∧ F.pol.size ≤ textLimit ∧
    F.lay.size ≤ textLimit ∧ F.KL.size ≤ fileLimit ∧ F.request.size ≤ fileLimit ∧
    F.y.size ≤ fileLimit ∧ F.proof.size ≤ fileLimit

/-- Where the program's pure function passes a whole call on the eight files' bytes (YES or WITHIN
LIMITS), and the files are within the program's limits, `PortYesAt` holds of them, at the ID in the
options and at two tables; the options hold the bits 128; and, if the options are the served ones,
`servedAt` is true at F's own three public files and the user's statement made of the files and the
options (the last clause of `main_zero_served`, by `wholeCall_served`). The entry's number in F is
the one that the proof file names (hk). The other options are free. For all options and files; of no
files is the hypothesis shown. -/
theorem portYes_of_wholeCall {o : Options} {F : Files}
    (hk : entryNumber o (callOf F) = .ok F.entry)
    (hp : (wholeCall o (callOf F)).passing = true) (hw : Within F) :
    ∃ (id : String) (table further : Params.TableName),
      o.id = some id ∧ o.bits = 128 ∧ PortYesAt F id table further ∧
      (optionsServed o = true →
        servedAt ⟨F.pol, F.lay, F.KL⟩ ⟨F.pol, F.lay, F.KL, F.request, F.y, o⟩ = true) := by
  have hp' : (wholeCall o { callOf F with entry := some F.ent }).passing = true := hp
  obtain ⟨r, entb, p, C, table, further, g1, g2, g3, g4, g5, g6, g7, g8, g9, _⟩ :=
    Model.Verify.wholeCall_passed hk hp'
  obtain ⟨⟨id, i1, i2⟩, i3⟩ := Model.Verify.wholeCall_id hk hp' g1 g4 g7
  obtain ⟨_, _, q3, q4⟩ := wholeCall_stages hp' g1 g3 g5
  obtain ⟨x1, _, x3⟩ := common_fields g5 g4
  obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := Model.Verify.readCall_ok g1
  obtain ⟨layb, hl⟩ := Model.Verify.planned_layout g4
  rw [hl] at f3 g4
  have q5 : optionsServed o = true →
      servedAt ⟨r.pol, layb, r.KL⟩ ⟨r.pol, layb, r.KL, r.request, r.y, o⟩ = true :=
    fun ho => wholeCall_served hk hp' g1 g3 g5 hl g4 ho
  have e1 : r.pol = F.pol := (Option.some.inj f1).symm
  have e2 : r.KL = F.KL := (Option.some.inj f2).symm
  have e3 : layb = F.lay := (Option.some.inj (Option.some.inj f3)).symm
  have e4 : r.key = F.key := (Option.some.inj f4).symm
  have e5 : r.request = F.request := (Option.some.inj f5).symm
  have e6 : r.y = F.y := (Option.some.inj f6).symm
  have e7 : r.proof = F.proof := (Option.some.inj f7).symm
  have e8 : entb = F.ent := (Option.some.inj g3).symm
  obtain ⟨so, cov, item, links, c1, c2, c3, c4, c5⟩ := g9
  obtain ⟨ac, w, q3⟩ := q3
  rw [i3] at q4
  rw [e3] at hl
  rw [e1, e2, e3] at g4
  rw [e4] at g7
  rw [e8] at g8 q3
  rw [e5, e6] at c1
  rw [e1, e2, e5] at c3
  rw [e5, e7] at c5
  rw [e1, e2, e3, e5, e6] at q5
  obtain ⟨w1, w2, w3, w4, w5, w6, w7, w8⟩ := hw
  refine ⟨id, table, further, i1, i3, ?_, q5⟩
  exact ⟨r, p, C, e1, e2, hl, e4, e5, e6, e7, g2, w1, w2, g4, g5, g6,
    g7, g8, ⟨so, cov, item, links, c1, c2, c3, c4, c5⟩, i2, Tie.checks_same g4 g7 g8 c5, q4,
    ⟨o, ac, w, i1, i3, q3⟩, ⟨x1, x3⟩, w3, w4, w5, w6, w7, w8⟩

end OnBytes.K.Oracle
