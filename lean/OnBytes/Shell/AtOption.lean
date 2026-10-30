-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Shell/AtOption.lean: the option `-no-proof-of-work`, from the arguments of the entry
function to the results of the stages of a call that passed.

OnBytes/Model/VerifyLawsOption.lean says what holds of the stages' results if a call passes and its
options as read hold `-no-proof-of-work`. This file leads there from the arguments of the entry
function `main`: from the string `-no-proof-of-work` among the call's options to the field in the
options as read, and from the exit codes 0 and 3 to the calls.

Main theorems.
- `readOptions_noWork`: if `readOptions` (OnBytes/Shell/Whole.lean) returns options as read, and the
  string `-no-proof-of-work` is among the strings that it was given, then the field for the option
  is set; or `Model.policyNamedRead` takes that very string for a policy, and the options as read
  hold a policy.
- `partOptions_noWork`: under the same two conditions, in a call on one file alone the field is set:
  the options of such a call hold no policy.
- `main_key_option`, `main_leaf_option`: if `main`, called with `verify -key` or `verify -leaf`, the
  names and options among which the string stands, returns 3, then the result of the call's one
  stage is not a pass with a note on work, and its record does not say that some round meets the
  target only with its work.
- `main_zero_option`: the same of the three stages of a whole call, if `main` returns 0 and the
  string stands among the options behind the five names; under one hypothesis, see below.
- `Tie.zero_option_named`: the same conclusion of the record that meets `Tie.ZeroFacts`
  (OnBytes/Tie/ZeroFacts.lean), under the same hypothesis. `main_zero_option` is a short corollary
  of `Tie.main_zero_facts` and `Tie.zero_option`.

What is not claimed. Nothing on soundness. `main_zero_option` has a hypothesis that speaks of no
file: that `Model.policyNamedRead` refuses the string `-no-proof-of-work`. It is not proved here:
`decide` does not get through `String.splitOn`. A `#guard` behind the theorem evaluates it when this
file is built; that is a test and no theorem. Without the hypothesis the string could be the value
of `-policy` and no option. All limits in the head of OnBytes/Model/VerifyLawsOption.lean hold here
too: above all, whether the stages' notes on work and their records are right is not stated, and
nothing is said of a call that does not pass or of a call without the option. The converse is not
stated: that the field is set only if the string stands among the options. A name may itself be
`-no-proof-of-work`: the names are not read as options. Nothing leads from the arguments to a named
policy: `wholeCall_within` stays on the options as read. The exit code 3 is also that of a call on a
test protocol's files that passed: the theorems start from the command and the code together. An
exit code here is the number that `main` returns; a shell sees it modulo 256. The arguments are
those that the entry function is given; nothing on how a shell forms them. The answers of the reads
are those in Lean's model of IO (OnBytes/Shell/AtOps.lean): Lean's logic knows nothing of files, so
nothing says that they are a file's content. Nothing about compiled code, Lean's run-time or the
operating system. The program is the Lean text `verify-on-bytes`; nothing here is said of the C++
program `cp_verify` or of how its results compare. For proofs only; the program does not import this
file.
-/
import OnBytes.Tie.ZeroFacts
import OnBytes.Shell.AtOptions
import OnBytes.Model.VerifyLawsOption

set_option autoImplicit false

namespace OnBytes.Shell

open OnBytes.Model
open OnBytes.Model.Stages (CallEnd StageName Closing passedWithWork recordNeedsWork)

/-- The reader of a number refuses the string `-no-proof-of-work`, whatever the bound. -/
theorem decimal_noWork (most : Nat) : decimal most "-no-proof-of-work" = none := by
  rfl

/-- The string `-no-proof-of-work` is no ID. -/
theorem isId_noWork : isId "-no-proof-of-work" = false := by
  decide

/-- The reader of the options never takes the field for `-no-proof-of-work` back: if it is set at
the beginning, it is set in what the reader returns. -/
theorem readOptions_keeps (opts : List String) (a0 a : Asked) :
    readOptions opts a0 = .ok a → a0.options.noProofOfWork = true →
      a.options.noProofOfWork = true := by
  fun_induction readOptions opts a0 <;> intro h h0 <;>
  first
    | (cases h; done)
    | (cases h; exact h0)
    | (rename_i ih; exact ih h h0)
    | (rename_i ih; exact ih h rfl)

/-- If the options hold a policy at the beginning, so do those that the reader returns. -/
theorem readOptions_policy (opts : List String) (a0 a : Asked) :
    readOptions opts a0 = .ok a → a0.options.policy.isSome = true →
      a.options.policy.isSome = true := by
  fun_induction readOptions opts a0 <;> intro h h0 <;>
  first
    | (cases h; done)
    | (cases h; exact h0)
    | (rename_i ih; exact ih h h0)
    | simp_all

/-- If the reader of the options returns options, and the string `-no-proof-of-work` is among the
strings that it was given: the field for the option is set; or `Model.policyNamedRead` takes that
very string for a policy and the options as read hold a policy. The second case is that of the
string as the value of `-policy`; that it does not arise is not proved. The readers of the values of
`-bits`, `-j` and `-id` refuse the string (`decimal_noWork`, `isId_noWork`). -/
theorem readOptions_noWork (opts : List String) (a0 a : Asked) :
    readOptions opts a0 = .ok a → "-no-proof-of-work" ∈ opts →
      a.options.noProofOfWork = true ∨
        ((Model.policyNamedRead "-no-proof-of-work").isSome = true ∧
          a.options.policy.isSome = true) := by
  fun_induction readOptions opts a0 <;> intro h hm <;>
  first
    | (cases h; done)
    | (cases hm; done)
    | (exact Or.inl (readOptions_keeps _ _ _ h rfl))
    | (rename_i ih
       rcases List.mem_cons.mp hm with e | e
       · exact absurd e (by decide)
       · exact ih h e)
    | (rename_i ih
       rcases List.mem_cons.mp hm with e | e
       · exact absurd e (by decide)
       · rcases List.mem_cons.mp e with e | e
         · subst e
           first
             | (simp_all [decimal_noWork, isId_noWork]; done)
             | (rename_i hp
                exact Or.inr ⟨by rw [hp]; rfl, readOptions_policy _ _ _ h rfl⟩)
         · exact ih h e)

/-- The options of a call on one file alone: if they are read without a refusal and the string
`-no-proof-of-work` is among them, the field for the option is set. Such options hold no policy, so
the second case of `readOptions_noWork` does not arise. -/
theorem partOptions_noWork {options : List String} {a : Asked} (h : partOptions options = .ok a)
    (hm : "-no-proof-of-work" ∈ options) : a.options.noProofOfWork = true := by
  unfold partOptions at h
  split at h
  · cases h
  · rename_i b hb
    split at h
    · cases h
    · rename_i hn
      cases h
      rcases readOptions_noWork _ _ _ hb hm with e | ⟨_, e⟩
      · exact e
      · simp_all

/-- The exit code 0 with `-no-proof-of-work`. The hypothesis `hno` speaks of no file:
`Model.policyNamedRead` refuses the string `-no-proof-of-work`; it is not proved, and the `#guard`
behind this theorem evaluates it. If the entry function returns 0, the arguments are `verify`, five
names and options, the call was a whole call with the options a as read, and the program's
operations gave the eight reads and then the steps t. If the string `-no-proof-of-work` is among the
options, then for the files r that `Verify.readCall` returned on the answers of the first seven
reads and the bytes of the entry: of the three stages' results (`Verify.stagesOf`) none is that of a
stage that passed with a note on work, and the record of the last stage does not say that some round
meets the target only with its work. Whether the notes and the record are right is not stated.
Remarks on the code, no part of the statement: the exit code 0 covers both `YES` and
`WITHIN LIMITS`; from the results that `Verify.stagesOf` gives, `Verify.wholeCall` forms the result
of the call. -/
theorem main_zero_option {args : List String} {s s' : World}
    (hno : Model.policyNamedRead "-no-proof-of-work" = none)
    (h : Run (_root_.main args) s 0 s') :
    ∃ (config ivk request y proof : String) (options : List String) (a : Asked)
      (pol kl lay key req yy prf ent : FileRead) (k : Nat) (t : List Event),
      args = "verify" :: config :: ivk :: request :: y :: proof :: options ∧
      kindOf args = .whole config ivk request y proof a ∧
      Steps opsIO (wholeReads config ivk request y proof k pol kl lay key req yy prf ent ++ t)
        s s' ∧
      ("-no-proof-of-work" ∈ options →
        ∃ r entb, Verify.readCall a.options (filesOf pol kl lay key req yy prf) = .ok r ∧
          fileIn ent = some entb ∧
          passedWithWork (Verify.stagesOf a.options r entb).1 = false ∧
          recordNeedsWork (Verify.stagesOf a.options r entb).1 = false) := by
  obtain ⟨w, f⟩ := Tie.main_zero_facts h
  obtain ⟨options, e1, e2⟩ := kindOf_whole f.kind
  refine ⟨w.config, w.ivk, w.request, w.y, w.proof, options, w.a, .bytes w.r.pol, .bytes w.r.KL,
    .bytes w.lay, .bytes w.r.key, .bytes w.r.request, .bytes w.r.y, .bytes w.r.proof, .bytes w.ent,
    w.r.entry, _, e1, f.kind, f.steps, fun hm => ?_⟩
  rcases readOptions_noWork _ _ _ e2 hm with e | ⟨e, _⟩
  · obtain ⟨q1, q2⟩ := Tie.zero_option f e
    exact ⟨w.r, w.ent, f.read, rfl, q1, q2⟩
  · rw [hno] at e
    cases e

#guard (Model.policyNamedRead "-no-proof-of-work").isNone

/-- The command `verify -key` with the string `-no-proof-of-work` among its options. If the entry
function returns 3, the options were read as some a, and the program's operations gave the four
reads, answered with bytes, and then the steps t. For the files r that `Verify.readFirst` returned
on these bytes and the common beginning C: the result of the stage key is not a pass with a note on
work, and its record does not say that some round meets the target only with its work. Whether the
note and the record are right is not stated. -/
theorem main_key_option {config key : String} {options : List String} {s s' : World}
    (h : Run (_root_.main ("verify" :: "-key" :: config :: key :: options)) s 3 s')
    (hm : "-no-proof-of-work" ∈ options) :
    ∃ (a : Asked) (pol kl lay kb : ByteArray) (t : List Event) (r : Verify.Read)
      (C : Verify.Common),
      partOptions options = .ok a ∧
      Steps opsIO (keyReads config key pol kl lay kb ++ t) s s' ∧
      Verify.readFirst a.options
        (keyFiles (.bytes pol) (.bytes kl) (.bytes lay) (.bytes kb)) false = .ok r ∧
      Verify.commonOfCall r = .ok C ∧
      passedWithWork
        [Verify.stageOut .key C.idHex (Verify.keyStage C a.options.bits r.key)] = false ∧
      recordNeedsWork
        [Verify.stageOut .key C.idHex (Verify.keyStage C a.options.bits r.key)] = false := by
  obtain ⟨a, pol, kl, lay, kb, cl, p, table, g1, _, g3, _, _, _, _, g8, _⟩ := main_key h
  obtain ⟨r, C, q1, q2, q3, q4⟩ :=
    Verify.keyCall_option g8 (partOptions_noWork g1 hm)
  exact ⟨a, pol, kl, lay, kb, _, r, C, g1, g3, q1, q2, q3, q4⟩

/-- The command `verify -leaf` with the string `-no-proof-of-work` among its options. If the entry
function returns 3, the options were read as some a, and the program's operations gave the five
reads, answered with bytes, and then the steps t. For the files r that `Verify.readFirst` returned
on these bytes and the common beginning C: the result of the stage leaf is not a pass with a note on
work, and its record does not say that some round meets the target only with its work. Whether the
note and the record are right is not stated. -/
theorem main_leaf_option {config key entry : String} {options : List String} {s s' : World}
    (h : Run (_root_.main ("verify" :: "-leaf" :: config :: key :: entry :: options)) s 3 s')
    (hm : "-no-proof-of-work" ∈ options) :
    ∃ (a : Asked) (pol kl lay kb ent : ByteArray) (t : List Event) (r : Verify.Read)
      (C : Verify.Common),
      partOptions options = .ok a ∧
      Steps opsIO (leafReads config key entry pol kl lay kb ent ++ t) s s' ∧
      Verify.readFirst a.options
        (leafFiles (.bytes pol) (.bytes kl) (.bytes lay) (.bytes kb) (.bytes ent)) false = .ok r ∧
      Verify.commonOfCall r = .ok C ∧
      passedWithWork
        [Verify.stageOut .leaf C.idHex (Verify.leafStage C a.options.bits ent)] = false ∧
      recordNeedsWork
        [Verify.stageOut .leaf C.idHex (Verify.leafStage C a.options.bits ent)] = false := by
  obtain ⟨a, pol, kl, lay, kb, ent, cl, p, first, further, j, g1, _, g3, _, _, _, _, _, g9, _⟩ :=
    main_leaf h
  obtain ⟨r, C, q1, q2, q3, q4⟩ :=
    Verify.leafCall_option g9 (partOptions_noWork g1 hm)
  exact ⟨a, pol, kl, lay, kb, ent, _, r, C, g1, g3, q1, q2, q3, q4⟩

end OnBytes.Shell

namespace OnBytes.Tie

open OnBytes.Shell (World)
open OnBytes.Model
open OnBytes.Model.Stages (passedWithWork recordNeedsWork)

/-- `zero_option` (OnBytes/Tie/ZeroFacts.lean) from the arguments. The hypothesis `hno` speaks of no
file: `Model.policyNamedRead` refuses the string `-no-proof-of-work`; it is not proved, and the
`#guard` behind `main_zero_option` evaluates it. Under `ZeroFacts`, if the arguments are `verify`,
five names and options among which the string `-no-proof-of-work` stands, what `zero_option`
concludes holds. It is `main_zero_option`'s conclusion, of the record w. -/
theorem zero_option_named {args : List String} {s s' : World} {w : WholeSeen}
    (hno : Model.policyNamedRead "-no-proof-of-work" = none) (h : ZeroFacts args s s' w)
    {config ivk request y proof : String} {options : List String}
    (ha : args = "verify" :: config :: ivk :: request :: y :: proof :: options)
    (hm : "-no-proof-of-work" ∈ options) :
    passedWithWork (Verify.stagesOf w.a.options w.r w.ent).1 = false ∧
      recordNeedsWork (Verify.stagesOf w.a.options w.r w.ent).1 = false := by
  obtain ⟨options', e1, e2⟩ := Shell.kindOf_whole h.kind
  have eo : options' = options := by
    rw [ha] at e1
    simp only [List.cons.injEq] at e1
    exact e1.2.2.2.2.2.2.symm
  subst eo
  rcases Shell.readOptions_noWork _ _ _ e2 hm with e | ⟨e, _⟩
  · exact zero_option h e
  · rw [hno] at e
    cases e

end OnBytes.Tie

#print axioms OnBytes.Shell.main_zero_option
#print axioms OnBytes.Tie.zero_option_named
#print axioms OnBytes.Shell.main_key_option
#print axioms OnBytes.Shell.main_leaf_option
