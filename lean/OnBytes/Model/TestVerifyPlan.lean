-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Model/TestVerifyPlan.lean: tests of planBytes (OnBytes/Model/Verify.lean), one of which gets
as far as the plans; of the twenty-one conditions that the stage request forms (servedOf,
OnBytes/Model/VerifyStages.lean); and of what the strict scan (polScan, OnBytes/Model/Config.lean)
says of a parameter file in which a line that the test on the policy reads (cpPolicyHeld,
OnBytes/Model/VerifyHeads.lean) is missing or has a value that it does not take, so that this test
decides nothing.

planBytes. The parameter file and the scale file are the small example's of
OnBytes/Model/TestConfig.lean, and there is no layout file. Every test that is made before the
layout file is needed then passes, among them the scan, the scales, the tables' digests, the
sub-proofs' layouts and plans, and the links' declared arrays. The call is refused where the
placement of the arrays is wanted (plan-layout, OnBytes/Model/VerifyChains.lean). In the second test
the parameter file cannot be read, and the call ends at once (cpConfRead,
OnBytes/Model/VerifyHeads.lean). The expected ends are read off these two files. The number 128 is
that of the example's line sec; both calls end before it is looked at.

The conditions. servedOf takes what all stages have in common (Common). No test builds such a value,
since that takes a whole configuration with its layout file. So these tests are statements (example)
for every such value, every request and either answer on the layout file; a statement sets only the
values that it names. Lean's kernel computes both sides when the file compiles (rfl). Five are about
servedOf's field exactMatch, four about policyNamed, one about each of the other nineteen. Each is
about its one field alone: it says nothing of the other conditions, of what the stage then does, or
of soundness. A statement that repeats servedOf's own text shows only that the inputs are passed on:
the fifth on exactMatch does, and the sections name the others. That the value false gives the
condition's name, and that lastLine (OnBytes/Model/Stages.lean) then gives not a verification, is
tested for each of the twenty-one in OnBytes/Model/TestStages.lean; that the stage hands it the list
is not tested there. Where a statement sets values, the expected ones follow the table and its notes
in verifier/docs/parameter-file.md, section "The standard parameter form".

The scan. The parameter file is the example's without its optional lines and with C 300 and theta
299 for 256 and 256: a clipped gap, the policy 300 299 0 15 8 4 of
OnBytes/Model/TestVerifyHeads.lean. The request has 64 tokens 0, since the example's line lt is 6,
and covers the positions 62 and 63, so one token of the request is checked. Twenty altered files are
tried: each of the policy's six lines taken out, with a value of eleven digits (12345678901) and
with a letter in its value (3x); the line lt taken out and with the value 21. These values were
chosen by hand. The expected names of the refusals follow from the text of polStep and polScan
(OnBytes/Model/Config.lean). A line that stands where another is due gives policy-name- and the due
line's name. The value of eleven digits is above 2^32 and 3x is no number: both give policy-line-
and the due line's place among the value lines, counted from 2 at the line prof, not the line's
number in the file. The line lt is read by name before the other lines: policy-name-lt if it is
missing, shape-words above 16. The test on the policy also decides nothing where the request does
not have the length or the range that the file asks for. The scan does not see the request, and that
case is not tried here.

No test compares with a run of the C++ verifier. All numbers and strings were typed by hand; none is
taken from a key, an entry, a proof or a model's weights.
Each test is checked when the file compiles. The file is no part of the program.
-/
import OnBytes.Model.TestConfig
import OnBytes.Model.Verify

namespace OnBytes.Model.TestVerifyPlan

open Verify Stages

/-! ## planBytes -/

/-- The end that planBytes gives, if it ends the call. -/
def planEnd (policy KL : FileIn) (layout : Option FileIn) : Option CallEnd :=
  match planBytes 128 policy KL layout with
  | .error e => some e
  | .ok _ => none

#guard planEnd (some TestConfig.kit) (some TestConfig.klFile) none == some (.no "plan-layout")
-- a file that cannot be read ends the call before that
#guard planEnd none (some TestConfig.klFile) none == some (.unreadable .policy)

/-! ## The condition exact-match of the stage request -/

/-- C with these values of the parameter file's lines C, theta, cap, sh and sT. -/
def withPolicy (C : Common) (clip theta cap sh sT : Nat) : Common :=
  { C with X := { C.X with P := { C.X.P with h :=
      { C.X.P.h with clipC := clip, theta := theta, cap := cap, digSh := sh, tabS := sT } } } }

-- Each of the five statements holds for every C, l, so and cov. Lean's kernel computes both sides.
-- Under a clipped gap, with no policy named and one position with a cost, the condition is missed.
example (C : Common) (l : Bool) (so : Head.StOwn) (cov : Head.Covered) :
    (servedOf (withPolicy C 300 299 0 8 4) {} l so { cov with hRC := 1 }).exactMatch = false := rfl
-- With the same numbers it is met if the call names a policy, whichever it names.
example (C : Common) (l : Bool) (so : Head.StOwn) (cov : Head.Covered) (p : PolicyNamed) :
    (servedOf (withPolicy C 300 299 0 8 4) { policy := some p } l so
      { cov with hRC := 1 }).exactMatch = true := rfl
-- With no policy named it is met if no position has a cost.
example (C : Common) (l : Bool) (so : Head.StOwn) (cov : Head.Covered) :
    (servedOf (withPolicy C 300 299 0 8 4) {} l so { cov with hRC := 0 }).exactMatch = true := rfl
-- With no policy named and one such position it is met if the file's policy is the exact match.
example (C : Common) (l : Bool) (so : Head.StOwn) (cov : Head.Covered) :
    (servedOf (withPolicy C 256 256 0 8 4) {} l so { cov with hRC := 1 }).exactMatch = true := rfl
-- With no policy named and at least one such position it is exactMatch (OnBytes/Model/Config.lean)
-- of the file's five numbers, whatever these are.
example (C : Common) (l : Bool) (so : Head.StOwn) (cov : Head.Covered) (a b c d e n : Nat) :
    (servedOf (withPolicy C a b c d e) {} l so { cov with hRC := n + 1 }).exactMatch =
      exactMatch a b c d e := rfl

/-! ## The condition policy-named of the stage request

The first statement names no policy. The second and the third set the file's six numbers and name
the policy clipped-gap 300 299 0 15 8. The fourth holds for every named policy and all values of the
six numbers; it repeats servedOf's own text, so it shows only that the six numbers are passed on in
their order. PolicyNamed.is has tests of its own in OnBytes/Model/TestConfigBytes.lean. -/

/-- C with this value of the parameter file's line s. -/
def withScale (C : Common) (s : Nat) : Common :=
  { C with X := { C.X with P := { C.X.P with h := { C.X.P.h with logS := s } } } }

-- Each of the four statements holds for every C, l, so and cov. Lean's kernel computes both sides.
-- With no policy named the condition is met.
example (C : Common) (l : Bool) (so : Head.StOwn) (cov : Head.Covered) :
    (servedOf C {} l so cov).policyNamed = true := rfl
-- It is met if the call names the file's own policy.
example (C : Common) (l : Bool) (so : Head.StOwn) (cov : Head.Covered) :
    (servedOf (withScale (withPolicy C 300 299 0 8 4) 15)
      { policy := some ⟨"clipped-gap", 300, 299, 0, 15, 8⟩ } l so cov).policyNamed = true := rfl
-- It is missed if the file's line C is another than the named policy's.
example (C : Common) (l : Bool) (so : Head.StOwn) (cov : Head.Covered) :
    (servedOf (withScale (withPolicy C 301 299 0 8 4) 15)
      { policy := some ⟨"clipped-gap", 300, 299, 0, 15, 8⟩ } l so cov).policyNamed = false := rfl
-- For every named policy p it is p.is (OnBytes/Model/Config.lean) of the file's six numbers.
example (C : Common) (l : Bool) (so : Head.StOwn) (cov : Head.Covered) (p : PolicyNamed)
    (a b c s d e : Nat) :
    (servedOf (withScale (withPolicy C a b c d e) s) { policy := some p } l so cov).policyNamed =
      p.is a b c s d e := rfl

/-! ## The other nineteen conditions of the stage request

One statement for each, under the condition's name in verifier/docs/parameter-file.md. Ten set
values at which the condition is met and values at which it is missed; these values alone are tried.
Eight repeat servedOf's own text (attention, placement-table, one-shift, one-placement,
softmax-table, rotary-table, norm-shifts, two-codes), and so does the second half of the statement
on next-token: they show only which value or function the field is and that its inputs are passed
on, not that the function is right. Of the functions, onePlacement has tests in
OnBytes/Model/TestStagesLinks.lean and OnBytes/Model/TestStagesLinksMore.lean, rotaryServed in
OnBytes/Model/TestConfigBytes.lean. No other
test names oneShift or normShifts, and the numbers 12 and 8 of softmax-table are tried at no value.
-/

/-- servedOf for C with P in the place of what the scan of the parameter file gave. -/
def servedWith (C : Common) (P : PolScan) (o : Options) (l : Bool) (so : Head.StOwn)
    (cov : Head.Covered) : Served :=
  servedOf { C with X := { C.X with P := P } } o l so cov

-- Each statement holds for every C, P, o, l, so and cov. Lean's kernel computes both sides.
-- attention is p4 of C's public part (profile 4).
example (C : Common) (o : Options) (l : Bool) (so : Head.StOwn) (cov : Head.Covered) :
    (servedOf C o l so cov).attention = C.X.p4 := rfl
-- routed-experts: met at NE 4, missed at NE 0.
example (C : Common) (P : PolScan) (o : Options) (l : Bool) (so : Head.StOwn)
    (cov : Head.Covered) :
    (servedWith C { P with h := { P.h with NE := 4 } } o l so cov).experts = true ∧
      (servedWith C { P with h := { P.h with NE := 0 } } o l so cov).experts = false :=
  ⟨rfl, rfl⟩
-- five-limbs: met with the line xl 5, missed without it.
example (C : Common) (P : PolScan) (o : Options) (l : Bool) (so : Head.StOwn)
    (cov : Head.Covered) :
    (servedWith C { P with xl := true } o l so cov).fiveLimbs = true ∧
      (servedWith C { P with xl := false } o l so cov).fiveLimbs = false :=
  ⟨rfl, rfl⟩
-- both-clamps: met with the lines rcl 1 and gcl 1, missed if either or both are not there.
example (C : Common) (P : PolScan) (o : Options) (l : Bool) (so : Head.StOwn)
    (cov : Head.Covered) :
    (servedWith C { P with rcl := true, gcl := true } o l so cov).clamps = true ∧
      (servedWith C { P with rcl := false, gcl := true } o l so cov).clamps = false ∧
      (servedWith C { P with rcl := true, gcl := false } o l so cov).clamps = false ∧
      (servedWith C { P with rcl := false, gcl := false } o l so cov).clamps = false :=
  ⟨rfl, rfl, rfl, rfl⟩
-- prompt-source: met at toksrc 1, missed at toksrc 0 and 2.
example (C : Common) (P : PolScan) (o : Options) (l : Bool) (so : Head.StOwn)
    (cov : Head.Covered) :
    (servedWith C { P with h := { P.h with toksrc := 1 } } o l so cov).promptSource = true ∧
      (servedWith C { P with h := { P.h with toksrc := 0 } } o l so cov).promptSource = false ∧
      (servedWith C { P with h := { P.h with toksrc := 2 } } o l so cov).promptSource = false :=
  ⟨rfl, rfl, rfl⟩
-- placement-table is the answer on the layout file.
example (C : Common) (o : Options) (l : Bool) (so : Head.StOwn) (cov : Head.Covered) :
    (servedOf C o l so cov).placementTable = l := rfl
-- table-digests: met with 32 words of digests, missed with none, with 31 and with 33.
example (C : Common) (P : PolScan) (o : Options) (l : Bool) (so : Head.StOwn)
    (cov : Head.Covered) :
    (servedWith C { P with tblPol := Array.replicate 32 0 } o l so cov).tableDigests = true ∧
      (servedWith C { P with tblPol := #[] } o l so cov).tableDigests = false ∧
      (servedWith C { P with tblPol := Array.replicate 31 0 } o l so cov).tableDigests = false ∧
      (servedWith C { P with tblPol := Array.replicate 33 0 } o l so cov).tableDigests = false :=
  ⟨rfl, rfl, rfl, rfl⟩
-- no-range-words: met without the lines eg and smax, missed with either or both.
example (C : Common) (P : PolScan) (o : Options) (l : Bool) (so : Head.StOwn)
    (cov : Head.Covered) :
    (servedWith C { P with eg := none, smax := none } o l so cov).noRangeWords = true ∧
      (servedWith C { P with eg := some 8, smax := none } o l so cov).noRangeWords = false ∧
      (servedWith C { P with eg := none, smax := some 4095 } o l so cov).noRangeWords = false ∧
      (servedWith C { P with eg := some 8, smax := some 4095 } o l so cov).noRangeWords = false :=
  ⟨rfl, rfl, rfl, rfl⟩
-- three-bytes: met at S 31, missed at S 32.
example (C : Common) (P : PolScan) (o : Options) (l : Bool) (so : Head.StOwn)
    (cov : Head.Covered) :
    (servedWith C { P with h := { P.h with Sx := 31 } } o l so cov).threeBytes = true ∧
      (servedWith C { P with h := { P.h with Sx := 32 } } o l so cov).threeBytes = false :=
  ⟨rfl, rfl⟩
-- ring-degree: met at D 2048, missed at D 1024 and 4096.
example (C : Common) (P : PolScan) (o : Options) (l : Bool) (so : Head.StOwn)
    (cov : Head.Covered) :
    (servedWith C { P with h := { P.h with D := 2048 } } o l so cov).ringDegree = true ∧
      (servedWith C { P with h := { P.h with D := 1024 } } o l so cov).ringDegree = false ∧
      (servedWith C { P with h := { P.h with D := 4096 } } o l so cov).ringDegree = false :=
  ⟨rfl, rfl, rfl⟩
-- one-shift is oneShift (OnBytes/Model/VerifyStages.lean) of C's public part.
example (C : Common) (o : Options) (l : Bool) (so : Head.StOwn) (cov : Head.Covered) :
    (servedOf C o l so cov).oneShift = oneShift C.X := rfl
-- one-placement is onePlacement (OnBytes/Model/StagesLinks.lean) of C's links and of the layout of
-- the proof's first chain.
example (C : Common) (o : Options) (l : Bool) (so : Head.StOwn) (cov : Head.Covered) :
    (servedOf C o l so cov).onePlacement =
      onePlacement C.built.links C.chains.proof.first.layout := rfl
-- softmax-table: below profile 4 it is met; at profile 4 it asks for S 12 and rx 8.
example (C : Common) (P : PolScan) (o : Options) (l : Bool) (so : Head.StOwn)
    (cov : Head.Covered) (a b : Nat) :
    (servedWith C { P with h := { P.h with Sx := a, rx := b } } o l so cov).softmaxTable =
      (!C.X.p4 || (a == 12 && b == 8)) := rfl
-- rotary-table: below profile 4 it is met; at profile 4 it is rotaryServed
-- (OnBytes/Model/Config.lean) of theta0, dh and lt.
example (C : Common) (P : PolScan) (o : Options) (l : Bool) (so : Head.StOwn)
    (cov : Head.Covered) (a b c : Nat) :
    (servedWith C { P with h := { P.h with theta0 := a, dh := b, lt := c } } o l so
      cov).rotaryTable = (!C.X.p4 || rotaryServed a b c) := rfl
-- norm-shifts is normShifts (OnBytes/Model/VerifyStages.lean) of C's public part.
example (C : Common) (o : Options) (l : Bool) (so : Head.StOwn) (cov : Head.Covered) :
    (servedOf C o l so cov).normShifts = normShifts C.X := rfl
-- reading-as-printed: met at reading 1, missed at reading 2.
example (C : Common) (P : PolScan) (o : Options) (l : Bool) (so : Head.StOwn)
    (cov : Head.Covered) :
    (servedWith C { P with frame := { P.frame with reading := 1 } } o l so
      cov).readingAsPrinted = true ∧
      (servedWith C { P with frame := { P.frame with reading := 2 } } o l so
        cov).readingAsPrinted = false :=
  ⟨rfl, rfl⟩
-- two-codes is twoCodes (OnBytes/Model/VerifyStages.lean) of C's chains.
example (C : Common) (o : Options) (l : Bool) (so : Head.StOwn) (cov : Head.Covered) :
    (servedOf C o l so cov).twoCodes = C.chains.twoCodes := rfl
-- record-one-answer: met at answers 1, missed with answers 0 or 2.
example (C : Common) (P : PolScan) (o : Options) (l : Bool) (so : Head.StOwn)
    (cov : Head.Covered) :
    (servedWith C { P with frame := { P.frame with answers := 1 } } o l so
        cov).recordOneAnswer = true ∧
      (servedWith C { P with frame := { P.frame with answers := 2 } } o l so
        cov).recordOneAnswer = false ∧
      (servedWith C { P with frame := { P.frame with answers := 0 } } o l so
        cov).recordOneAnswer = false :=
  ⟨rfl, rfl, rfl⟩
-- next-token: met without the option -next-token; with it, it asks for r + 1 = T and e = T.
example (C : Common) (o : Options) (l : Bool) (so : Head.StOwn) (cov : Head.Covered) :
    (servedOf C { o with nextToken := false } l so cov).nextToken = true ∧
      (servedOf C { o with nextToken := true } l so cov).nextToken =
        (so.r + 1 == C.X.T && so.e == C.X.T) := ⟨rfl, rfl⟩

/-! ## Twenty altered files: the test on the policy decides nothing, the scan refuses -/

/-- The names of the six lines that the test on the policy reads besides lt. -/
def six : List String := ["C", "theta", "cap", "s", "sh", "sT"]

/-- The example's value lines with a clipped gap. -/
def gapLines : List String :=
  TestConfig.valueLines.map fun l =>
    if l == "C 256" then "C 300" else if l == "theta 256" then "theta 299" else l

/-- The example's parameter file with the value lines v and without the optional lines. -/
def fileWith (v : List String) : ByteArray := TestConfig.withLines v [] TestConfig.callLines

/-- The file with a clipped gap, in which the line `name` is taken out or has another value. -/
def turned (name : String) (value : Option String) : ByteArray :=
  fileWith (gapLines.filterMap fun l =>
    if l.startsWith (name ++ " ") then value.map (name ++ " " ++ ·) else some l)

/-- The end that the test on the policy gives, if it gives one. No policy is named. The request has
64 tokens and covers the positions 62 and 63. -/
def held (pol : ByteArray) : Option CallEnd :=
  match cpPolicyHeld none pol (Array.replicate 64 0 ++ #[62, 64]) with
  | .error e => some e
  | .ok _ => none

-- the file as it is: the scan admits it, and the call is refused because it names no policy
#guard TestConfig.refusal (fileWith gapLines) == none
#guard held (fileWith gapLines) == some (.policy .notNamed)
-- one of the six lines is taken out
#guard six.all fun n => held (turned n none) == none
#guard six.map (fun n => TestConfig.refusal (turned n none)) ==
  six.map fun n => some ("policy-name-" ++ n)
-- its value has eleven digits
#guard six.all fun n => held (turned n (some "12345678901")) == none
#guard six.map (fun n => TestConfig.refusal (turned n (some "12345678901"))) ==
  (List.range 6).map fun i => some ("policy-line-" ++ toString (92 + i))
-- its value has a letter
#guard six.all fun n => held (turned n (some "3x")) == none
#guard six.map (fun n => TestConfig.refusal (turned n (some "3x"))) ==
  (List.range 6).map fun i => some ("policy-line-" ++ toString (92 + i))
-- the line lt is taken out
#guard held (turned "lt" none) == none
#guard TestConfig.refusal (turned "lt" none) == some "policy-name-lt"
-- it is above 20
#guard held (turned "lt" (some "21")) == none
#guard TestConfig.refusal (turned "lt" (some "21")) == some "shape-words"

end OnBytes.Model.TestVerifyPlan
