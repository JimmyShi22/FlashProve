-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Shell/AtPart.lean: from the exit code 3 of the commands `verify -leaf` and `verify -key` to
the yes of the function that checks the file.

OnBytes/Shell/AtMain.lean ties a run of the program's entry function to a run of the value
`call C args`; OnBytes/Shell/AtWord.lean says what a run that prints `PART PASSED` has read and
which check has passed; OnBytes/Model/VerifyLaws.lean unfolds that check. Here the three are joined.

Main definitions: `leafReads`, `keyReads`, `partSaid`. Main theorems.
- `main_leaf`, on the entry function `main`: if `main`, called with
  `verify -leaf <config folder> <key file> <entry file>` and any options, returns 3, then the
  options were read as some a, and the run of `call modelChecks args` whose answers the program's
  three operations gave was five reads that were answered with bytes, in the order policy.txt,
  KL.bin, layout.txt, key file, entry file, and then the lines of a part that passed, of which the
  last is `PART PASSED: leaf`. Each answer is within its file's limit. `Verify.leafCall` on a's
  options and these bytes is the result whose lines were printed, and the call asked for no fewer
  bits than the threshold. `Verify.planned` on the bytes of the three configuration files returned a
  value p. `Key.readTable` read a table from the first bytes of the key file. And `Entry.check` said
  yes on the bytes of the entry file, under the parameter bytes of the entry's chain in p and
  against that table.
- `main_key`: the same for `verify -key <config folder> <key file>`, with four reads, the last line
  `PART PASSED: key`, `Verify.keyCall`, and a yes of `Key.check` on the bytes of the key file under
  the key's three chains in p, which are read back from the parameter bytes in p.
- `program_leafPart`, `program_keyPart`: the same on `program`, which is `main` (`main_eq`), for all
  arguments that `kindOf` reads as such a call.

What is not claimed. Nothing on soundness: the theorems say which function said yes on which bytes,
not what such a yes is worth. A part that passed is no verification: the two commands are meant for
the committer's own test. `verify -leaf` looks at none of the key's proofs: the table is taken from
the key file on its form alone, and a pass counts only beside a call `verify -key` that passed on
the same key file, configuration folder and bits; nothing here says that two calls have read the
same bytes. The table is read under the shape in the key's one-time chain and checked under the
shape in the entry's chain; that the two agree is not stated. Nothing is said on what
`Verify.planned` tests, or on whether the plans in p meet a target. The option `-id` is free, and no
statement names the commitment ID. The exit code 3 is also that of a call on a test protocol's files
that passed: the theorems start from the command and the code together. An exit code here is the
number that `main` returns; a shell sees it modulo 256. No step to the compiled verifier (a term of
the library's Lean theory, not machine code) is made here: see OnBytes/Tie/LeafCall.lean.
The converse is not stated, and nothing says that some files make a call
pass. The bytes are the answers of the program's reads in Lean's model of IO
(OnBytes/Shell/AtOps.lean): Lean's logic knows nothing of files, so nothing says that they are a
file's content. Nothing about compiled code, Lean's run-time or the operating system. The program is
the Lean text `verify-on-bytes`; nothing here is said of the C++ program `cp_verify` or of how its
results compare. For proofs only; the program does not import this file.
-/
import OnBytes.Shell.AtSize
import OnBytes.Model.VerifyLaws

set_option autoImplicit false

namespace OnBytes.Shell

open OnBytes.Model
open OnBytes.Model.Stages (CallEnd StageName Closing)

/-! ## Answers with bytes -/

/-- A read whose answer the checks take as bytes was answered with these bytes. -/
theorem fileIn_some {r : FileRead} {b : ByteArray} (h : fileIn r = some b) : r = .bytes b := by
  cases r with
  | bytes b0 =>
    cases h
    rfl
  | absent => cases h
  | unreadable u => cases h

/-- The same for the layout file. -/
theorem layoutIn_some {r : FileRead} {b : ByteArray} (h : layoutIn r = some (some b)) :
    r = .bytes b := by
  cases r with
  | bytes b0 =>
    cases h
    rfl
  | absent => cases h
  | unreadable u => cases h

/-! ## How the two commands are read -/

/-- The arguments of `verify -leaf` are a bad command line or a call on an entry file alone. -/
theorem kindOf_leaf (config key entry : String) (options : List String) :
    kindOf ("verify" :: "-leaf" :: config :: key :: entry :: options) =
      match partOptions options with
      | .error w => .bad w
      | .ok a => .leafPart config key entry a := by
  simp only [kindOf]
  cases partOptions options <;> rfl

/-- The arguments of `verify -key` are a bad command line or a call on a key file alone. -/
theorem kindOf_key (config key : String) (options : List String) :
    kindOf ("verify" :: "-key" :: config :: key :: options) =
      match partOptions options with
      | .error w => .bad w
      | .ok a => .keyPart config key a := by
  simp only [kindOf]
  cases partOptions options <;> rfl

/-! ## The exit code 3 -/

/-- The last line of a call on an entry file alone that passed. -/
theorem text_leaf (L : Lists) : (Line.partPassed .leaf).text L = "PART PASSED: leaf" := by
  show ("PART PASSED: " ++ "leaf" : String) = "PART PASSED: leaf"
  decide

/-- The last line of a call on a key file alone that passed. -/
theorem text_key (L : Lists) : (Line.partPassed .key).text L = "PART PASSED: key" := by
  show ("PART PASSED: " ++ "key" : String) = "PART PASSED: key"
  decide

/-- If the program returns 3 and the call is not one on the files of a test protocol, its run has
handed over, with success, a line that begins with P and is not the last line of a planning call. -/
theorem program_three {args : List String} {s s' : World} (h : Run (program args) s 3 s')
    (hk : ∀ paths notes v w, kindOf args ≠ .toy paths notes v w) :
    ∃ evs r l, (call modelChecks args).Ends evs r ∧ Steps opsIO evs s s' ∧
      Event.say l true ∈ evs ∧ hd l = some 'P' ∧ l ≠ Line.planOnly.text modelChecks.lists := by
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
    exfalso
    have hl2 : l = Line.testPassed.text modelChecks.lists := hl
    obtain ⟨paths, notes, v, w, _, _, _, k1, _⟩ :=
      said_test (by rw [hl2]; exact hd_text _ _) h1 hm
    exact hk _ _ _ _ k1
  | ended e =>
    obtain ⟨p, hl2⟩ := hl
    cases e with
    | partPassed st cl =>
      refine ⟨evs, _, l, h1, h2, hm, ?_, ?_⟩
      · rw [hl2]
        exact hd_text _ _
      · rw [hl2]
        exact partPassed_ne_planOnly _ st
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

/-! ## The steps of a run that passed -/

/-- The five reads of a call on an entry file alone, answered with bytes. -/
def leafReads (config key entry : String) (pol kl lay kb ent : ByteArray) : List Event :=
  [.read (config ++ "/policy.txt") (textLimit + 1) (.bytes pol),
   .read (config ++ "/KL.bin") (fileLimit + 1) (.bytes kl),
   .read (config ++ "/layout.txt") (textLimit + 1) (.bytes lay),
   .read key (fileLimit + 1) (.bytes kb), .read entry (fileLimit + 1) (.bytes ent)]

/-- The four reads of a call on a key file alone, answered with bytes. -/
def keyReads (config key : String) (pol kl lay kb : ByteArray) : List Event :=
  [.read (config ++ "/policy.txt") (textLimit + 1) (.bytes pol),
   .read (config ++ "/KL.bin") (fileLimit + 1) (.bytes kl),
   .read (config ++ "/layout.txt") (textLimit + 1) (.bytes lay),
   .read key (fileLimit + 1) (.bytes kb)]

/-- The lines of the result that the part st passed (by the code), and then the line `last`, all
printed with success. -/
def partSaid (st : StageName) (cl : Closing) (last : String) : List Event :=
  saidAll modelChecks.lists (before {} (.partPassed st cl)) ++ [.say last true]

/-! ## The two kinds of call -/

/-- The call on an entry file alone. If the program returns 3, the run of `call modelChecks args`
whose answers the three operations gave was five reads that were answered with bytes and the lines
of a part that passed. Each answer is within its file's limit. `Verify.leafCall` on the call's
options and these bytes is the result whose lines were printed, and the call asked for no fewer bits
than the threshold. `Verify.planned` on the three configuration files' bytes returned p;
`Key.readTable` read the table `first` from the key file's bytes, on its form alone; and
`Entry.check` said yes on the entry file's bytes, under the parameter bytes of the entry's chain in
p and against `first`. -/
theorem program_leafPart {args : List String} {config key entry : String} {a : Asked} {s s' : World}
    (hk : kindOf args = .leafPart config key entry a) (h : Run (program args) s 3 s') :
    ∃ (pol kl lay kb ent : ByteArray) (cl : Closing) (p : Verify.Planned)
      (first further : Params.TableName) (j : Nat),
      (call modelChecks args).Ends (leafReads config key entry pol kl lay kb ent ++
        partSaid .leaf cl "PART PASSED: leaf") (.ended (.partPassed .leaf cl)) ∧
      Steps opsIO (leafReads config key entry pol kl lay kb ent ++
        partSaid .leaf cl "PART PASSED: leaf") s s' ∧
      pol.size ≤ textLimit ∧ kl.size ≤ fileLimit ∧ lay.size ≤ textLimit ∧ kb.size ≤ fileLimit ∧
      ent.size ≤ fileLimit ∧
      Verify.leafCall a.options
        (leafFiles (.bytes pol) (.bytes kl) (.bytes lay) (.bytes kb) (.bytes ent)) =
          .partPassed .leaf cl ∧
      Verify.askedBelowBar a.options.bits = false ∧
      Verify.planned pol kl (some lay) = .ok p ∧
      Key.readTable p.chains.tableShape p.cfg kb = .ok (first, j) ∧
      Entry.check (p.chains.bytes .link) first ent = .ok further := by
  obtain ⟨evs, r, l, h1, h2, hm, hP, hne⟩ := program_three h (by
    intro _ _ _ _ e
    rw [hk] at e
    cases e)
  obtain ⟨st, cl, e1, e2, k⟩ := said_part hP hne h1 hm
  rcases k with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, k1, _⟩ |
    ⟨_, _, _, _, _, _, _, k1, _⟩ | ⟨_, _, _, _, pol, kl, lay, kb, ent, k1, k2, k3⟩
  · rw [hk] at k1
    cases k1
  · rw [hk] at k1
    cases k1
  · rw [hk] at k1
    cases k1
    obtain ⟨polb, klb, layb, kbb, entb, p, first, further, j, f1, f2, f3, f4, f5, g1, g2, g3, g4,
      g5⟩ := Verify.leafCall_passed (o := a.options) (f := leafFiles pol kl lay kb ent) k2
    cases fileIn_some f1
    cases fileIn_some f2
    cases layoutIn_some f3
    cases fileIn_some f4
    cases fileIn_some f5
    subst g4
    have sz : ∀ q n (b : ByteArray), Event.read q n (.bytes b) ∈ evs → b.size < n :=
      fun q n b hq => pass_sizes h1 hm hP (by decide) hq
    rw [text_leaf] at e1
    subst e1
    subst k3
    subst e2
    exact ⟨polb, klb, layb, kbb, entb, cl, p, first, further, j, h1, h2,
      Nat.le_of_lt_succ (sz (config ++ "/policy.txt") _ _ (by simp)),
      Nat.le_of_lt_succ (sz (config ++ "/KL.bin") _ _ (by simp)),
      Nat.le_of_lt_succ (sz (config ++ "/layout.txt") _ _ (by simp)),
      Nat.le_of_lt_succ (sz key _ _ (by simp)), Nat.le_of_lt_succ (sz entry _ _ (by simp)),
      k2, g5, g1, g2, g3⟩

/-- The call on a key file alone. If the program returns 3, the run of `call modelChecks args` whose
answers the three operations gave was four reads that were answered with bytes and the lines of a
part that passed. Each answer is within its file's limit. `Verify.keyCall` on the call's options and
these bytes is the result whose lines were printed, and the call asked for no fewer bits than the
threshold. `Verify.planned` on the three configuration files' bytes returned p; and `Key.check` said
yes on the key file's bytes, under the key's three chains in p, which are read back from the
parameter bytes in p. -/
theorem program_keyPart {args : List String} {config key : String} {a : Asked} {s s' : World}
    (hk : kindOf args = .keyPart config key a) (h : Run (program args) s 3 s') :
    ∃ (pol kl lay kb : ByteArray) (cl : Closing) (p : Verify.Planned) (table : Params.TableName),
      (call modelChecks args).Ends (keyReads config key pol kl lay kb ++
        partSaid .key cl "PART PASSED: key") (.ended (.partPassed .key cl)) ∧
      Steps opsIO (keyReads config key pol kl lay kb ++ partSaid .key cl "PART PASSED: key") s s' ∧
      pol.size ≤ textLimit ∧ kl.size ≤ fileLimit ∧ lay.size ≤ textLimit ∧ kb.size ≤ fileLimit ∧
      Verify.keyCall a.options (keyFiles (.bytes pol) (.bytes kl) (.bytes lay) (.bytes kb)) =
        .partPassed .key cl ∧
      Verify.askedBelowBar a.options.bits = false ∧
      Verify.planned pol kl (some lay) = .ok p ∧
      Params.KeyChains.read (p.chains.bytes .keyOneTime) (p.chains.bytes .keyShared)
        (p.chains.bytes .keySecond) = some p.chains.key ∧
      Key.check p.chains.key kb = .ok table := by
  obtain ⟨evs, r, l, h1, h2, hm, hP, hne⟩ := program_three h (by
    intro _ _ _ _ e
    rw [hk] at e
    cases e)
  obtain ⟨st, cl, e1, e2, k⟩ := said_part hP hne h1 hm
  rcases k with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, k1, _⟩ |
    ⟨_, _, _, pol, kl, lay, kb, k1, k2, k3⟩ | ⟨_, _, _, _, _, _, _, _, _, k1, _⟩
  · rw [hk] at k1
    cases k1
  · rw [hk] at k1
    cases k1
    obtain ⟨polb, klb, layb, kbb, p, table, f1, f2, f3, f4, g1, g2, g4, g5⟩ :=
      Verify.keyCall_passed (o := a.options) (f := keyFiles pol kl lay kb) k2
    cases fileIn_some f1
    cases fileIn_some f2
    cases layoutIn_some f3
    cases fileIn_some f4
    subst g4
    have sz : ∀ q n (b : ByteArray), Event.read q n (.bytes b) ∈ evs → b.size < n :=
      fun q n b hq => pass_sizes h1 hm hP (by decide) hq
    rw [text_key] at e1
    subst e1
    subst k3
    subst e2
    exact ⟨polb, klb, layb, kbb, cl, p, table, h1, h2,
      Nat.le_of_lt_succ (sz (config ++ "/policy.txt") _ _ (by simp)),
      Nat.le_of_lt_succ (sz (config ++ "/KL.bin") _ _ (by simp)),
      Nat.le_of_lt_succ (sz (config ++ "/layout.txt") _ _ (by simp)),
      Nat.le_of_lt_succ (sz key _ _ (by simp)), k2, g5, g1, (Verify.planned_read g1).1, g2⟩
  · rw [hk] at k1
    cases k1

/-! ## The two commands -/

/-- The program does not return 3 on a bad command line. -/
theorem bad_not_three {args : List String} {w : String} {s s' : World}
    (hk : kindOf args = .bad w) : ¬ Run (program args) s 3 s' := by
  intro h
  obtain ⟨evs, r, l, h1, _, hm, _, _⟩ := program_three h (by
    intro _ _ _ _ e
    rw [hk] at e
    cases e)
  unfold call at h1
  rw [hk] at h1
  exact faultWith_said h1 hm

/-- The command `verify -leaf`. If the entry function, called with these arguments, returns 3, then
the options were read as some a, and what `program_leafPart` says holds of the run. -/
theorem main_leaf {config key entry : String} {options : List String} {s s' : World}
    (h : Run (_root_.main ("verify" :: "-leaf" :: config :: key :: entry :: options)) s 3 s') :
    ∃ (a : Asked) (pol kl lay kb ent : ByteArray) (cl : Closing) (p : Verify.Planned)
      (first further : Params.TableName) (j : Nat),
      partOptions options = .ok a ∧
      (call modelChecks ("verify" :: "-leaf" :: config :: key :: entry :: options)).Ends
        (leafReads config key entry pol kl lay kb ent ++ partSaid .leaf cl "PART PASSED: leaf")
        (.ended (.partPassed .leaf cl)) ∧
      Steps opsIO (leafReads config key entry pol kl lay kb ent ++
        partSaid .leaf cl "PART PASSED: leaf") s s' ∧
      pol.size ≤ textLimit ∧ kl.size ≤ fileLimit ∧ lay.size ≤ textLimit ∧ kb.size ≤ fileLimit ∧
      ent.size ≤ fileLimit ∧
      Verify.leafCall a.options
        (leafFiles (.bytes pol) (.bytes kl) (.bytes lay) (.bytes kb) (.bytes ent)) =
          .partPassed .leaf cl ∧
      Verify.askedBelowBar a.options.bits = false ∧
      Verify.planned pol kl (some lay) = .ok p ∧
      Key.readTable p.chains.tableShape p.cfg kb = .ok (first, j) ∧
      Entry.check (p.chains.bytes .link) first ent = .ok further := by
  rw [main_eq] at h
  have hk := kindOf_leaf config key entry options
  cases ho : partOptions options with
  | error w =>
    rw [ho] at hk
    exact absurd h (bad_not_three hk)
  | ok a =>
    rw [ho] at hk
    obtain ⟨pol, kl, lay, kb, ent, cl, p, first, further, j, r⟩ := program_leafPart hk h
    exact ⟨a, pol, kl, lay, kb, ent, cl, p, first, further, j, rfl, r⟩

/-- The command `verify -key`. If the entry function, called with these arguments, returns 3, then
the options were read as some a, and what `program_keyPart` says holds of the run. -/
theorem main_key {config key : String} {options : List String} {s s' : World}
    (h : Run (_root_.main ("verify" :: "-key" :: config :: key :: options)) s 3 s') :
    ∃ (a : Asked) (pol kl lay kb : ByteArray) (cl : Closing) (p : Verify.Planned)
      (table : Params.TableName),
      partOptions options = .ok a ∧
      (call modelChecks ("verify" :: "-key" :: config :: key :: options)).Ends
        (keyReads config key pol kl lay kb ++ partSaid .key cl "PART PASSED: key")
        (.ended (.partPassed .key cl)) ∧
      Steps opsIO (keyReads config key pol kl lay kb ++ partSaid .key cl "PART PASSED: key") s s' ∧
      pol.size ≤ textLimit ∧ kl.size ≤ fileLimit ∧ lay.size ≤ textLimit ∧ kb.size ≤ fileLimit ∧
      Verify.keyCall a.options (keyFiles (.bytes pol) (.bytes kl) (.bytes lay) (.bytes kb)) =
        .partPassed .key cl ∧
      Verify.askedBelowBar a.options.bits = false ∧
      Verify.planned pol kl (some lay) = .ok p ∧
      Params.KeyChains.read (p.chains.bytes .keyOneTime) (p.chains.bytes .keyShared)
        (p.chains.bytes .keySecond) = some p.chains.key ∧
      Key.check p.chains.key kb = .ok table := by
  rw [main_eq] at h
  have hk := kindOf_key config key options
  cases ho : partOptions options with
  | error w =>
    rw [ho] at hk
    exact absurd h (bad_not_three hk)
  | ok a =>
    rw [ho] at hk
    obtain ⟨pol, kl, lay, kb, cl, p, table, r⟩ := program_keyPart hk h
    exact ⟨a, pol, kl, lay, kb, cl, p, table, rfl, r⟩

end OnBytes.Shell

#print axioms OnBytes.Shell.main_leaf
#print axioms OnBytes.Shell.main_key
