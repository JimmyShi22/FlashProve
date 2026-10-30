-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/ZeroFacts.lean: the clauses that four theorems state of the exit code 0 of the entry
function, and some more, said once: a record of values, and the facts on it by name.

The values of a whole call that returned 0 are the fields of one record, `WholeSeen`, and clauses
that are proved of them are the fields of one structure, `ZeroFacts`, each with its own comment. A
theorem that goes on from the exit code 0 can take `ZeroFacts` as its hypothesis, for every record
that meets it, and name the clause that it uses. The clauses: those of `program_zero_kind`
(OnBytes/Shell/AtWholeKind.lean): the run of `call`, the eight reads and the steps behind them, the
sizes of all answers, the entry's number, the result of the call with its kind and its last line;
what `Verify.wholeCall_passed`, `wholeCall_id` and `wholeCall_within`
(OnBytes/Model/VerifyLawsWhole.lean, VerifyLawsId.lean, VerifyLawsOption.lean) give of a call that
passed: that all eight answers are bytes, what `Verify.readCall`, `Verify.planned` and the common
beginning of the stages returned, the layout file's bytes (`Verify.planned_layout`,
OnBytes/Model/VerifyLaws.lean), the yes of the three checks, the commitment ID, the bits, a named
policy at a result within limits; `SameChains` (OnBytes/Tie/SameChains.lean); and where the ID
stands among the arguments (OnBytes/Shell/AtOptions.lean). Four theorems state parts of these
clauses, each in one statement, and are short corollaries: `main_zero`, `main_zero_id`
(OnBytes/Shell/AtWhole.lean, AtWholeId.lean), `main_zero_same`, `main_zero_named`
(OnBytes/Tie/ZeroNamed.lean). Their docstrings say most of the clauses in words; `ends`, `sizes`,
`number`, `call` and `kinds` are in none of them. A fifth, `main_zero_option`
(OnBytes/Shell/AtOption.lean), follows from the clauses with `zero_option`.

Main definitions: `WholeSeen`, `WholeSeen.seven`, `WholeSeen.files`, `WholeSeen.events`,
`ZeroFacts`.
Main theorems.
- `main_zero_facts`: if `main args` returns 0, some record meets `ZeroFacts`.
- `zeroFacts_unique`: for one list of arguments and one state at the start, at most one record does.
- `zero_yes_iff`: under `ZeroFacts` the last line is `YES` exactly if the result is a yes.
- `zero_option`: what holds of the three stages' results under `ZeroFacts` if the options as read
  hold `-no-proof-of-work`. It uses `zero_passing`. From the string among the arguments:
  `zero_option_named` (OnBytes/Shell/AtOption.lean).

What is not claimed. Nothing on soundness. `ZeroFacts` is a predicate on a record; it says what the
Lean program computed in a run that returned 0, in Lean's model of IO, and nothing on whether a file
is honest. That `ZeroFacts` gives the exit code 0 back is not stated. Other theorems start from the
exit code 0 with values of their own and are not restated here, `whole_call_ties`
(OnBytes/Tie/WholeCall.lean [not in this library]) on the key file's one-time chain among them. All
limits in the heads of the files named above hold here too, but for those that a field lifts. Of the
values `about` and `cl` in the result nothing is said: not which positions a yes covers, not that
the policy is the file's, not what the closing lines hold. That `w.r.entry` is the number in the
proof file's head is not stated: it is the number that `Verify.entryNumber` and `Verify.readCall`
returned. Nothing says that some files make a call return 0. The program is the Lean port built from
OnBytes/; nothing here is said of the C++ program `cp_verify` or of how its results compare. For
proofs only; the program does not import this file.

-/
import OnBytes.Tie.SameChains
import OnBytes.Shell.AtWholeKind
import OnBytes.Shell.AtOptions
import OnBytes.Model.VerifyLawsId
import OnBytes.Model.VerifyLawsOption

set_option autoImplicit false

namespace OnBytes.Tie

open OnBytes.Shell (Steps opsIO World Event Asked FileRead fileLimit wholeReads kindOf filesOf
  fileIn saidAll before modelChecks Line)
open OnBytes.Model
open OnBytes.Model.Stages (CallEnd Closing Covered passedWithWork recordNeedsWork)
open OnBytes.Proof

/-- Values of a whole call. What ties them to a run, and to each other, is said in `ZeroFacts` and
nowhere else. -/
structure WholeSeen where
  /-- the first of the five names: the folder from which policy.txt, KL.bin and layout.txt are
  read -/
  config : String
  /-- the second name: the folder from which key.bin and the entry leaf/<k>.bin are read -/
  ivk : String
  /-- the third name: the request file -/
  request : String
  /-- the fourth name: the y file -/
  y : String
  /-- the fifth name: the proof file -/
  proof : String
  /-- the options as read -/
  a : Asked
  /-- what `Verify.readCall` returned (`ZeroFacts.read`): the bytes of seven files, a number, and
  the call's record of its ID and options -/
  r : Verify.Read
  /-- the layout file's bytes -/
  lay : ByteArray
  /-- the entry file's bytes -/
  ent : ByteArray
  /-- what `Verify.planned` returned -/
  p : Verify.Planned
  /-- what the common beginning of the stages returned -/
  C : Verify.Common
  /-- the table that `Key.check` returned -/
  table : Params.TableName
  /-- the table that `Entry.check` returned -/
  further : Params.TableName
  /-- the ID that the options as read hold -/
  id : String
  /-- the result of the call -/
  result : CallEnd
  /-- the last line that the run wrote -/
  last : String

/-- The files of the call before the entry is read: the first seven reads' answers. -/
def WholeSeen.seven (w : WholeSeen) : Verify.Files :=
  filesOf (.bytes w.r.pol) (.bytes w.r.KL) (.bytes w.lay) (.bytes w.r.key) (.bytes w.r.request)
    (.bytes w.r.y) (.bytes w.r.proof)

/-- The files of the call as `Verify.wholeCall` is given them: the eight reads' answers. -/
def WholeSeen.files (w : WholeSeen) : Verify.Files :=
  { w.seven with entry := fileIn (.bytes w.ent) }

/-- The events of the run: the eight reads, answered with bytes, the lines of the result before its
last, and the last line, written with success. -/
def WholeSeen.events (w : WholeSeen) : List Event :=
  wholeReads w.config w.ivk w.request w.y w.proof w.r.entry (.bytes w.r.pol) (.bytes w.r.KL)
    (.bytes w.lay) (.bytes w.r.key) (.bytes w.r.request) (.bytes w.r.y) (.bytes w.r.proof)
    (.bytes w.ent) ++
      (saidAll modelChecks.lists (before { bits := w.a.options.bits, leaf := w.r.entry } w.result)
        ++ [.say w.last true])

/-- A predicate on a record w, for arguments and two states. `main_zero_facts` says that some record
meets it if `main args` returned 0 from s to s'. The docstrings of `main_zero`, `main_zero_id`,
`main_zero_same` and `main_zero_named`, which are corollaries, say most of the clauses in words.
Nothing on soundness. -/
structure ZeroFacts (args : List String) (s s' : World) (w : WholeSeen) : Prop where
  /-- the arguments: `verify`, the five names, and options that hold `-id` and, right behind it,
  the ID; that the pair stands in the options once is not stated -/
  named : ∃ pre post, args = "verify" :: w.config :: w.ivk :: w.request :: w.y :: w.proof ::
    (pre ++ "-id" :: w.id :: post)
  /-- the call was a whole call, with the options as read -/
  kind : kindOf args = .whole w.config w.ivk w.request w.y w.proof w.a
  /-- `call modelChecks args` has a run with these events, which ends with the result -/
  ends : (Shell.call modelChecks args).Ends w.events (.ended w.result)
  /-- the program's operations gave these events from s to s' -/
  steps : Steps opsIO w.events s s'
  /-- every one of the eight reads got fewer bytes than it asked for -/
  sizes : ∀ q n (b : ByteArray),
    Event.read q n (.bytes b) ∈ wholeReads w.config w.ivk w.request w.y w.proof w.r.entry
      (.bytes w.r.pol) (.bytes w.r.KL) (.bytes w.lay) (.bytes w.r.key) (.bytes w.r.request)
      (.bytes w.r.y) (.bytes w.r.proof) (.bytes w.ent) → b.size < n
  /-- the layout file's bytes are those in r -/
  layout : w.r.layout = some w.lay
  /-- the key file is within the files' limit; it follows from `sizes` -/
  keySize : w.r.key.size ≤ fileLimit
  /-- the entry file is within the files' limit; it follows from `sizes` -/
  entSize : w.ent.size ≤ fileLimit
  /-- the tests before the entry is read returned the number in r; it follows from `read` -/
  number : Verify.entryNumber w.a.options w.seven = .ok w.r.entry
  /-- `Verify.readCall` on the options as read and the first seven answers returned r -/
  read : Verify.readCall w.a.options w.seven = .ok w.r
  /-- `Verify.planned` on the three configuration files' bytes returned p -/
  planned : Verify.planned w.r.pol w.r.KL (some w.lay) = .ok w.p
  /-- the common beginning of the stages returned C -/
  common : Verify.commonOfCall w.r = .ok w.C
  /-- C holds p's chains -/
  chains : w.C.chains = w.p.chains
  /-- `Key.check` said yes on the key file's bytes and returned `table` -/
  keyYes : Key.check w.p.chains.key w.r.key = .ok w.table
  /-- `Entry.check` said yes on the entry file's bytes against `table` and returned `further` -/
  entryYes : Entry.check (w.p.chains.bytes .link) w.table w.ent = .ok w.further
  /-- `Proof.check` said `accepted` on the proof file's bytes against `further`, with the number in
  r, the request's item, the request file's own bytes, the reply and the links as built -/
  proofYes : ∃ so cov item links,
    Head.stFromCall (Verify.words32 w.r.request) (Verify.words32 w.r.y) w.C.X.T = .ok so ∧
    Head.coveredOf so w.C.X.T w.C.X.P.h.V = .ok cov ∧
    Proof.requestItem w.r.pol w.r.KL w.r.request = some item ∧
    Verify.linksOf w.C.X cov = .ok links ∧
    Proof.check w.p.chains.proof w.further w.r.entry item w.r.request (ofNat so.y)
      (Stages.runLinksH (w.C.built.links.zipWith (fun b l => { b with run := l.run }) links)
        w.p.chains.proof.first w.C.X.layers.wsLay) w.r.proof = .accepted
  /-- the options as read hold the ID -/
  idRead : w.a.options.id = some w.id
  /-- in lower-case digits the ID is the hexadecimal form of `Key.commitmentId` on the tables'
  shape and the digest in p and on `table` -/
  idFormed : Verify.idAsked w.id =
    some (Fmt.hex (Key.commitmentId w.p.chains.tableShape w.p.cfg w.table))
  /-- the options' field for the requested bits holds 128, which is also its value if the call
  names no bits; no bound on an error -/
  bits : w.a.options.bits = 128
  /-- `SameChains`, whose docstring says its three parts: the digest of the three configuration
  files in p and in all seven chains; one shape of the stored tables in five of them; and that the
  parameter bytes of the entry's chain are read as the entry's chain in p -/
  same : SameChains w.p (Params.configurationDigest [w.r.pol, w.lay, w.r.KL])
  /-- `Verify.wholeCall` on the options as read and the eight answers is the result -/
  call : Verify.wholeCall w.a.options w.files = w.result
  /-- the result is a yes and the last line is `YES`; or it is a result within limits, the last
  line is that result's, and the options as read hold a policy. Nothing is said of `about` and
  `cl` -/
  kinds : ∃ (about : Covered) (cl : Closing),
    (w.result = .yes about cl ∧ w.last = "YES") ∨
      (w.result = .withinLimits about cl ∧
        w.last = (Line.withinLimits about).text modelChecks.lists ∧
        w.a.options.policy.isSome = true)

/-- The exit code 0 of the entry function: some record meets `ZeroFacts`. The fields of `ZeroFacts`
say what that is. Nothing on soundness. -/
theorem main_zero_facts {args : List String} {s s' : World}
    (h : Shell.Run (_root_.main args) s 0 s') : ∃ w, ZeroFacts args s s' w := by
  rw [Shell.main_eq] at h
  obtain ⟨config, ivk, request, y, proof, a, pol, kl, lay, key, req, yy, prf, ent, k, e, l, k1, h1,
    h2, hk, k2, k3, sz⟩ := Shell.program_zero_kind h
  have hp : (Verify.wholeCall a.options
      { filesOf pol kl lay key req yy prf with entry := fileIn ent }).passing = true := by
    rw [k3]
    obtain ⟨ab, cl, ⟨rfl, _⟩ | ⟨rfl, _⟩⟩ := hk <;> rfl
  have hpol : ∀ ab cl, e = .withinLimits ab cl → a.options.policy.isSome = true :=
    fun ab cl he => Verify.wholeCall_within k2 (k3.trans he)
  obtain ⟨r, entb, p, C, table, further, g1, g2, g3, g4, g5, g6, g7, g8, g9, _⟩ :=
    Verify.wholeCall_passed k2 hp
  obtain ⟨⟨id, i1, i2⟩, i3⟩ := Verify.wholeCall_id k2 hp g1 g4 g7
  obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := Verify.readCall_ok g1
  obtain ⟨layb, hl⟩ := Verify.planned_layout g4
  rw [hl] at f3 g4
  cases Shell.fileIn_some f1
  cases Shell.fileIn_some f2
  cases Shell.layoutIn_some f3
  cases Shell.fileIn_some f4
  cases Shell.fileIn_some f5
  cases Shell.fileIn_some f6
  cases Shell.fileIn_some f7
  cases Shell.fileIn_some g3
  subst g2
  obtain ⟨so, cov, item, links, q1, q2, q3, q4, q5⟩ := g9
  refine ⟨⟨config, ivk, request, y, proof, a, r, layb, entb, p, C, table, further, id, e, l⟩, ?_⟩
  exact
    { named := Shell.whole_id_named k1 i1
      kind := k1
      ends := h1
      steps := h2
      sizes := sz
      layout := hl
      keySize := Nat.le_of_lt_succ (sz (ivk ++ "/key.bin") _ _ (by simp [wholeReads]))
      entSize := Nat.le_of_lt_succ (sz (ivk ++ "/leaf/" ++ toString r.entry ++ ".bin") _ _
        (by simp [wholeReads]))
      number := k2
      read := g1
      planned := g4
      common := g5
      chains := g6
      keyYes := g7
      entryYes := g8
      proofYes := ⟨so, cov, item, links, q1, q2, q3, q4, q5⟩
      idRead := i1
      idFormed := i2
      bits := i3
      same := checks_same g4 g7 g8 q5
      call := k3
      kinds := by
        obtain ⟨ab, cl, ⟨e1, e2⟩ | ⟨e1, e2⟩⟩ := hk
        · exact ⟨ab, cl, Or.inl ⟨e1, e2⟩⟩
        · exact ⟨ab, cl, Or.inr ⟨e1, e2, hpol ab cl e1⟩⟩ }

/-- Under `ZeroFacts` the result is a passing one. -/
theorem zero_passing {args : List String} {s s' : World} {w : WholeSeen}
    (h : ZeroFacts args s s' w) : (Verify.wholeCall w.a.options w.files).passing = true := by
  rw [h.call]
  obtain ⟨ab, cl, ⟨e, _⟩ | ⟨e, _⟩⟩ := h.kinds <;> rw [e] <;> rfl

/-- Under `ZeroFacts` the last line that the run wrote is `YES` exactly if the result is a yes: the
last line of a result within limits begins with W. -/
theorem zero_yes_iff {args : List String} {s s' : World} {w : WholeSeen}
    (h : ZeroFacts args s s' w) : w.last = "YES" ↔ ∃ about cl, w.result = .yes about cl := by
  obtain ⟨ab, cl, ⟨e1, e2⟩ | ⟨e1, e2, _⟩⟩ := h.kinds
  · exact ⟨fun _ => ⟨ab, cl, e1⟩, fun _ => e2⟩
  · constructor
    · intro hy
      have h1 : Shell.hd w.last = some 'W' := by
        rw [e2]
        exact Shell.hd_text _ _
      rw [hy] at h1
      exact absurd h1 (by decide)
    · rintro ⟨ab', cl', e⟩
      rw [e1] at e
      cases e

/-- The option `-no-proof-of-work` under `ZeroFacts`. If the options as read hold it: of the three
stages' results (`Verify.stagesOf` on the options, r and the entry file's bytes) none is that of a
stage that passed with a note on work, and the record of the last stage does not say that some round
meets the target only with its work. Whether the notes and the record are right is not stated. How
the field follows from the arguments: OnBytes/Shell/AtOption.lean. -/
theorem zero_option {args : List String} {s s' : World} {w : WholeSeen}
    (h : ZeroFacts args s s' w) (ho : w.a.options.noProofOfWork = true) :
    passedWithWork (Verify.stagesOf w.a.options w.r w.ent).1 = false ∧
      recordNeedsWork (Verify.stagesOf w.a.options w.r w.ent).1 = false := by
  obtain ⟨r, ent, g1, g3, q1, q2⟩ := Verify.wholeCall_option h.number (zero_passing h) ho
  have e1 : r = w.r := Except.ok.inj (g1.symm.trans h.read)
  have e2 : ent = w.ent := (Option.some.inj g3).symm
  subst e1 e2
  exact ⟨q1, q2⟩

/-- For one list of arguments and one state at the start, at most one record meets `ZeroFacts`. By
`Shell.steps_one` the two runs have the same events and the same result; the events hold the eight
answers and the last line, `kind` gives the names and the options, and the other fields are values
of functions of these. So two theorems that each give a record for one run speak of the same record.
-/
theorem zeroFacts_unique {args : List String} {s s1 s2 : World} {w1 w2 : WholeSeen}
    (h1 : ZeroFacts args s s1 w1) (h2 : ZeroFacts args s s2 w2) : w1 = w2 := by
  obtain ⟨he, hr⟩ := Shell.steps_one opsIO (Shell.call modelChecks args) s s1 s2 _ _ _ _
    h1.ends h1.steps h2.ends h2.steps
  have hk := h1.kind.symm.trans h2.kind
  injection hk with c1 c2 c3 c4 c5 c6
  have hres : w1.result = w2.result := by
    injection hr
  unfold WholeSeen.events wholeReads at he
  simp only [List.cons_append, List.nil_append, List.cons.injEq, Event.read.injEq,
    FileRead.bytes.injEq] at he
  obtain ⟨⟨_, _, b1⟩, ⟨_, _, b2⟩, ⟨_, _, b3⟩, ⟨_, _, b4⟩, ⟨_, _, b5⟩, ⟨_, _, b6⟩, ⟨_, _, b7⟩,
    ⟨_, _, b8⟩, tl⟩ := he
  have hlast : w1.last = w2.last := by
    have := (List.append_inj' tl rfl).2
    simpa using this
  have hseven : w1.seven = w2.seven := by
    unfold WholeSeen.seven
    rw [b1, b2, b3, b4, b5, b6, b7]
  have hrr : w1.r = w2.r := by
    have := h1.read
    rw [c6, hseven, h2.read] at this
    exact (Except.ok.inj this).symm
  have hp : w1.p = w2.p := by
    have := h1.planned
    rw [hrr, b3, h2.planned] at this
    exact (Except.ok.inj this).symm
  have hC : w1.C = w2.C := by
    have := h1.common
    rw [hrr, h2.common] at this
    exact (Except.ok.inj this).symm
  have ht : w1.table = w2.table := by
    have := h1.keyYes
    rw [hp, hrr, h2.keyYes] at this
    exact (Except.ok.inj this).symm
  have hf : w1.further = w2.further := by
    have := h1.entryYes
    rw [hp, ht, b8, h2.entryYes] at this
    exact (Except.ok.inj this).symm
  have hid : w1.id = w2.id := by
    have := h1.idRead
    rw [c6, h2.idRead] at this
    exact (Option.some.inj this).symm
  cases w1
  cases w2
  simp only at c1 c2 c3 c4 c5 c6 b3 b8 hrr hp hC ht hf hid hres hlast
  subst c1 c2 c3 c4 c5 c6 b3 b8 hrr hp hC ht hf hid hres hlast
  rfl

end OnBytes.Tie
