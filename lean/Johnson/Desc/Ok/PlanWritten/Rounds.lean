-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Ok/PlanWritten/Rounds.lean: over Johnson/Desc/Ok/PlanWritten/Test.lean and
Johnson/Desc/Ok/NumberPrices/AtDigest.lean: "the rounds that are computed from three public files,
AT EVERY DIGEST OF 32 BYTES, are given lists, and the stored table's depth is a given number": the
statement with free letters, a test with code at one anchor, a test with code on what the planner
has made (`planIsWritten`), the tools between them, and teeth.

ROW OR TOOL. EVERY DECLARATION HERE IS A TOOL AT THE PLANNER. None speaks of a description of the
protocol, so none is a row. `RoundsAre` and `RoundsWritten` are statements with free letters for the
files: THEY ARE PROVED AT NO FILES (`written_zFull`, on a description's data, is neither).

Why. The library holds the rounds of the key file's and the proof file's chains at the full size as
written values (`dryKeyFull`, `dryProofFull`, Johnson/G/DryKeyLit.lean, DryProofLit.lean), and many
theorems speak of these lists, and of the data made of them at the depth 32, alone. That these data
are what the verifier's description holds is proved in scope unless `verify` says no to all
(`written_or_no_all`), and at `OnBytes.secondHashFunction` and `VerifierAndGoals.storedPublicFiles`
(`written_zFull`, by Lean's kernel alone). Two roads lead from the files to such lists: the dry runs
of the verifier program's blocks (`dryKey`, `dryProof`, OnBytes/Maker/Files.lean), and `roundsAt`,
which calls no block of that program. THIS FILE IS ON THE SECOND ROAD ALONE.
Definitions, statements and proofs.
  `RoundsAre L a pol lay KL` (`Six`, `sameR`, `sameSix`, `planIs`, `keyOf`, `fullKey` are defined in
    Johnson/Desc/Ok/PlanWritten/Test.lean): at every c of 32 bytes `madeOfAt pol lay KL c` returns
    an m with `roundsAt m = .ok L` and `depthOf m = .ok a`. It says four things: the planner returns
    at every such c; the sendings and the declared rounds are made without a refusal; written out,
    they are L; the two files' shapes agree on the stored table's depth, and it is a.
    `RoundsWritten`: at the library's six written lists of the full size and the depth 32.
  `roundsAt_atDigest`, `depthOf_atDigest`, `declKOf_atDigest`, `declPOf_atDigest`: the rounds, the
    depth and the declared rounds do not hang on the digest. By definition: the depth is read off
    the planner's sizes, which `atDigest` keeps. `rounds_every_digest`: FROM ONE ANCHOR TO EVERY
    DIGEST: a return at one c₀ of 32 bytes with short strings (`Tie.shortB`), and the rounds L and
    the depth a there, give `RoundsAre L a`.
  `sameSix_iff`: what a yes of `sameSix` says, both ways.
  `planIs_iff`, `planIs_unique`: of `planIs L a m`, THE TEST ON WHAT WAS MADE: the rounds of m are
    made and are L, the depth is made and is a. It takes no file and no digest. What a yes says,
    both ways; a yes at one pair at most.
  `Written`, `fullSet`, `smallSet`, `written`, `planIsAmong S m`, `planIsWritten m`: THE SIX LISTS
    OF ROUNDS AND THE STORED TABLE's DEPTH ARE THOSE OF THE WRITTEN SET OF ITS KEY (what is not
    compared: the Limits). A written set is a key, six lists and a depth. The key of m is three
    sizes of the model as the strict scan of the parameter file has them (layers, width,
    vocabulary). The test looks up the first set with m's key and asks `planIs` at that set; without
    such a set it says no. The library has two written sets: the full size's, and the small
    example's. THE CHOICE GOES BY THE KEY, not by "any of the two", so that whoever knows the three
    sizes knows which set a yes speaks of.
  `written_of_yes`: what a yes says: a set of S with m's key, and the rounds and the depth are that
    set's. `full_of_yes`: at the full size's key: the six written lists of the full size and the
    depth 32. `key_of_sizes`: the three sizes 48, 5120, 202048 give that key. `yes_of_full`: the way
    back. `planIsAmong_atDigest`: the test does not hang on the digest. By definition.
  TEETH of that test. `no_of_key`: a key that is in no set is refused. `shallow`, `depthOf_val`,
    `planIsWritten_shallow`: whatever m is, with 31 for one number of the key file's shape the test
    says no. `planted`, `plant_refused`: A PLANT IS REFUSED: if the rounds of m are the full size's
    written lists with one number changed, the test says no. `planted_no`: the other way about: at
    the full size's key, where the test says yes the test at the sets with that number changed says
    no.
  `Seen`, `roundsAtZero`, `yesAt`, `roundsOk L a pol lay KL`: THE TEST AT THREE FILES, with code: at
    32 zero bytes in the digest's place (the anchor of the library's `planZero`: no step calls the
    format's hash; the second hash function stands in `publicOf`): the planner and the sendings
    return, the seven strings are short, the rounds are made and are L, the depth is made and is a.
    `steps_of_zero`, `anchor_of_ok`: what a yes says at the anchor. `roundsAre_of_ok`: a yes gives
    `RoundsAre L a`. `ok_of_roundsAre`: the converse, UNDER THE PREMISE that the strings at the
    anchor are short. `returnsOk`: with code: all is made at the anchor and the strings are short.
    `not_are_of_no`: where `returnsOk` says yes and the test says no, `RoundsAre L a` IS FALSE.
    `pinnedOk`, `pinned_of_ok`: `planIsWritten` of what is made at the anchor.
  `roundsAre_unique`: `RoundsAre` holds of one L and one a at most. `roundsOk_unique`: the test says
    yes at one pair at most.
  `roundsOf_of_are`: `RoundsAre L a` gives `roundsOf pol lay KL = .ok L`: the rounds on the road
    through `madeOf`, at the format's own digest. `planIs_of_are`, `planIs_own`: and a yes of
    `planIs L a` of what is made at every c of 32 bytes, and of what `madeOf` returns. `pinned_own`:
    from a yes of the test and of `pinnedOk`: `madeOf` returns, and `planIsWritten` says yes of what
    it returns.
  `decl_of_roundsAt`: FROM L BACK TO THE DECLARED ROUNDS: where `roundsAt m` returns L, `declKOf m`
    and `declPOf m` return, and `writtenOf` of what they return is L.1 and L.2. `decl_one_of_ok`:
    from a yes of the test: ONE pair of declared structures for all c of 32 bytes.
  `data_of_rounds`, `data_of_are`: THE COMPUTED DATA ARE THE DATA OF L AT THE DEPTH a: `dataKAt m`
    returns `WholeD.of a (dataAt a (some L.1))`, `dataPAt m` the like of L.2; at every c of 32
    bytes. `dataAt a R` is the data of R only where the makers' tests `okAt a R` say yes; where they
    say no it is the data of three EMPTY lists (OnBytes/Maker/Files.lean). At the full size's lists
    and 32 the tests' yes is proved (Johnson/G/DryKeyTests.lean, Johnson/G/DryProofTestsFull.lean),
    and Johnson/Desc/Ok/PlanWritten/AtDesc.lean (`computed_written`) has the data in the form
    `WholeD.of 32 (wholeAt …)`. This is what the clause on the depth is spent on.
  `roundsAt_congr`, `depthOf_congr`, `madeOfAt_withPol`, `roundsAre_withPol`: ANOTHER ACCEPTANCE
    POLICY WANTS NO SECOND LISTS: by the library's `plannedAt_withPol`
    (OnBytes/Tie/PlanAtPolicy.lean): if the second parameter file's strict scan is the first's with
    three other numbers, and `madeOfAt` returns there at the anchor with short strings, `RoundsAre L
    a` passes over. Its premises are shown of no files, and nothing here spends it.
  `bendLast`, `withSecond`, `bentWork`, `lessTree`, `dropped`: THREE CONTROLS ON A WRITTEN LIST: the
    written lists with the last round of the proof file's second chain bent (the library names a
    file's three chains first, shared, second: it is the third list, of 30 rounds): its work one
    more; its opened tree struck; the round dropped. `second_ne`, `second_ne_small`, `bent_ne`: each
    is another value than the written lists: BY AN EVALUATION IN LEAN's KERNEL on that chain.
    CONTROL 4: the depth 31. `control_no`: where the test says yes at the written lists and 32 it
    says no at each of the four. So beside a true first answer these four answers, and the plant's,
    are foretold by a theorem: in a run they show that the evaluator's comparison reaches that list
    and the depth, and NOTHING OF THE PLANNER.
  `oneByte`, `amongSeen`, `linesAt`, `linesBent`, `rideAt`, `threeControls`, `ride note pol bent lay
    KL`: FOR A RUN: fourteen named Bools. Seven from one call of `roundsAtZero` at pol: the test;
    `planIsWritten`; the plant; controls 1 to 4. Seven for CONTROL 5, AT A SECOND PARAMETER FILE
    bent, from one more call of `roundsAtZero`: that bent has pol's length and differs from it at
    one byte; that all is made there; the test there; `planIsWritten` there; the proof file's shared
    chain by itself; the other five lists; the depth. No theorem foretells control 5's answers. The
    last three answers are tied to no named Bool. NO LINE PRINTS THE KEY: what the first two answers
    show of it is `key_of_ok` (Johnson/Goal/Numbers/PlanWrittenScope.lean), by which the plant's
    answer is foretold beside them (`plantOk_no`). `plantOk`, `amongSeen_eq`: what the plant's line
    evaluates is `planIsAmong planted` of what was made. `ride_snd`, `ride_head`: the first eleven
    answers by name. `foretold`, `of_ride`: what a ride with the foretold answers gives: the
    statement at pol; `madeOf` returns and `planIsWritten` says yes of it; and at bent all is made
    AND THE STATEMENT IS FALSE.
  A RIDE CALLS THE PLANNER TWICE, and after each call makes the rounds twice from what was made
    (once for the test, once inside `planIsWritten`). note: a string that the first line gives back.
    It is there so that a ride at closed files is no constant: a compiled program evaluates each
    constant without arguments when its module starts up. That this argument, with the mark against
    inlining, keeps the compiler from doing so all the same is argued, not tested.

What of OnBytes/Model/ and OnBytes/Tie/ is used. Named: `Model.polScan` (OnBytes/Model/Config.lean),
`Model.Verify.configuration` (OnBytes/Model/Verify.lean), `Tie.shortB`; the fields `X.P.h.L`,
`X.P.h.d`, `X.P.h.V` of `Model.Verify.Planned` (the scan's record, `Model.Hdr`,
OnBytes/Model/Config.lean) and `chains.made.sized` of it. Called: `Tie.exc_step`,
`Tie.short_of_test`, `Tie.plannedAt_withPol`, `Params.configurationDigest_size`
(OnBytes/Model/VerifyDigest.lean). Through `madeOfAt`: `Tie.plannedAt`, the text of
`Model.Verify.planned`. All of it is a function of the public files and of c.

Limits. PROVED AT NO FILES; no test here is run in this library, and the library records no run of
one.
  IF `planIsWritten` IS LAID AMONG A DESCRIPTION's TESTS ON ITS PLAN, THAT DESCRIPTION ACCEPTS ONLY
    THESE PLANS: it says no at every plan but the two written sets. ONE SMALL SET IS WRITTEN, AND
    EVERY OTHER SMALL PARAMETER FILE OF THE LIBRARY SHARES ITS KEY (three sizes of the model) and
    has other rounds: there the test says no, at honest runs too (said here without a theorem). A
    laxer test, which pins at the full size's key alone: Johnson/Desc/Ok/PlanWritten/Pinned.lean. It
    is laid nowhere by this file. That in the
    goals' scope only the full size's set can occur is not shown HERE: `key_of_sizes` takes the
    three sizes as premises. It is shown in Johnson/Goal/Numbers/PlanWrittenScope.lean
    (`key_in_scope`), by `scan_sizes` (Johnson/Goal/PlanValues/ScopeAtPlan.lean) and
    `plannedAt_scan` (OnBytes/Tie/PlanAtPolicy.lean), which has the step to `m.p.X.P`.
  WHAT A YES IS WORTH. The written lists were printed from dry runs under the parameters that this
    library's own planner gives (the head of Johnson/G/DryProofLit.lean), and the rule of `roundsAt`
    for what a round opens was read off these same lists (the head of Johnson/G/RoundsOfPlan.lean).
    The statement is not circular: the lists are written values, and it can be false. But a yes is a
    check that the lists were copied rightly and that the fitted rule gives them back. IT IS NO
    SECOND WITNESS, and nothing here is held against the rows that the C++ planner prints.
  NOT COMPARED, of what the planner makes, by the statement or by either test. A written round is an
    entry, its kind, its items, what it opens and what it has stored. Not compared: each plan's six
    settings (field, salt, nonce, the bytes of a listed position, samples, saved: `Fmt.Plan`); the
    entry RECORD, which `Fmt.Plan.rounds` strikes (the key file's first chain has 18,852 entries and
    18,851 rounds); the planner's seven records with their numbers for the errors; the sizes and
    codes one by one, but for the one depth. NOT LOOKED AT EITHER, of what was made beside the
    plans: the planner's public part `m.p.X` but for the three sizes of the key (the target, the
    slots, the acceptance policy, the normalisations' numbers, the tables' digests, the calls); the
    links (`m.p.built`); the seven strings of parameter bytes, the labels and the digest; and that
    the plans as read back (`given.plan`), which `roundsAt` reads, are the plans as made. So "only
    these plans" pins six lists and a depth, not the run's public side. NOT COVERED beside: the
    entry file's rounds; the first road's two equations, and any tie between the two roads.
  THE FORM THAT IS COMPARED IS NOT THE FORM THAT A DESCRIPTION TAKES. Whoever reads a file takes the
    declared rounds (`declKOf`, `declPOf`); the statement compares what `writtenOf` makes of them,
    with stand-ins for a tree that is taken over. `decl_of_roundsAt` draws the declared rounds out
    as some value whose written form is L. That `writtenOf` loses nothing (two declared structures
    with one written form are one) is not shown. That a description of the protocol takes its rounds
    from `declKOf`, `declPOf` of `madeOfAt`'s value is said nowhere.
  THE SECOND HASH FUNCTION. `madeOfAt` takes no letter for it: `publicOf` calls it by name at every
    c. With another function in its place nothing is said.
  THE CONTROLS AND TEETH. No control can make `shortB` say no. Controls 1 to 3 and the plant bend
    one round of one short chain: they show that the comparison sees an entry's number, an opened
    tree and a list's length there, not that every wrong round of the long chains would be seen; the
    comparison is the derived equality of `Fmt.Round`, which takes every field. `plant_refused` has
    a premise on m that is shown of no m; `shallow m` is made by hand, by no planner. Control 5 is
    idle where the planner refuses at the second file: its second line then holds the refusal's
    words. The small example's set has no tooth of its own here, and no ride.
  Nothing at a c that has not 32 bytes. Nothing on soundness.

-/
import Johnson.Desc.Ok.NumberPrices.AtDigest
import Johnson.Desc.Ok.PlanWritten.Test
import OnBytes.Tie.PlanAtPolicy

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.PlanWritten
open Johnson.G Johnson.G.OfPlan VerifiableInference.Number
open OnBytes.Params (Rounds)
open OnBytes.Maker (WholeD dataAt)
open OnBytes.Model (polScan)
open OnBytes.Model.Verify (configuration)
open OnBytes.Tie (plannedAt_withPol exc_step shortB short_of_test)

/-- **At every digest of 32 bytes the rounds that are computed from the three public files are L,
and the stored table's depth is a.** -/
def RoundsAre (L : Six) (a : ℕ) (pol lay KL : ByteArray) : Prop :=
  ∀ c : ByteArray, c.size = 32 →
    ∃ m, madeOfAt pol lay KL c = .ok m ∧ roundsAt m = .ok L ∧ depthOf m = .ok a

/-- At the library's six written lists of the full size, and the depth 32. -/
def RoundsWritten (pol lay KL : ByteArray) : Prop :=
  RoundsAre (dryKeyFull, dryProofFull) 32 pol lay KL

/-- The rounds do not hang on the digest. By definition. -/
theorem roundsAt_atDigest (m : Made) (c : ByteArray) : roundsAt (atDigest m c) = roundsAt m := rfl

/-- The stored table's depth does not hang on the digest. By definition. -/
theorem depthOf_atDigest (m : Made) (c : ByteArray) : depthOf (atDigest m c) = depthOf m := rfl

/-- The key file's declared rounds do not hang on the digest. By definition. -/
theorem declKOf_atDigest (m : Made) (c : ByteArray) : declKOf (atDigest m c) = declKOf m := rfl

/-- The proof file's declared rounds do not hang on the digest. By definition. -/
theorem declPOf_atDigest (m : Made) (c : ByteArray) : declPOf (atDigest m c) = declPOf m := rfl

/-- **From one anchor to every digest of 32 bytes.** -/
theorem rounds_every_digest {pol lay KL c₀ : ByteArray} {m : Made} {L : Six} {a : ℕ}
    (hc : c₀.size = 32) (hm : madeOfAt pol lay KL c₀ = .ok m) (hb : shortB m.p = true)
    (hr : roundsAt m = .ok L) (hd : depthOf m = .ok a) : RoundsAre L a pol lay KL := fun c hc' =>
  ⟨atDigest m c, madeOfAt_at hc hc' (short_of_test hb) hm, (roundsAt_atDigest m c).trans hr,
    (depthOf_atDigest m c).trans hd⟩

/-- What a yes of `sameSix` says, both ways. -/
theorem sameSix_iff (x L : Six) : sameSix x L = true ↔ x = L := by
  constructor
  · intro h
    simp only [sameSix, sameR, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
    exact Prod.ext (Prod.ext h1 (Prod.ext h2 h3)) (Prod.ext h4 (Prod.ext h5 h6))
  · rintro rfl
    simp [sameSix, sameR]

/-! ## A test on what was made -/

/-- **What a yes of `planIs` says, both ways.** -/
theorem planIs_iff (L : Six) (a : ℕ) (m : Made) :
    planIs L a m = true ↔ roundsAt m = .ok L ∧ depthOf m = .ok a := by
  unfold planIs
  constructor
  · intro h
    split at h
    · rename_i x d hx hd
      have h2 := Bool.and_eq_true_iff.1 h
      rw [hx, hd, (sameSix_iff x L).1 h2.1, of_decide_eq_true h2.2]
      exact ⟨rfl, rfl⟩
    · cases h
  · rintro ⟨hr, hd⟩
    rw [hr, hd]
    exact Bool.and_eq_true_iff.2 ⟨(sameSix_iff L L).2 rfl, decide_eq_true rfl⟩

/-- `planIs` says yes at one pair at most. -/
theorem planIs_unique {L L' : Six} {a a' : ℕ} {m : Made} (h : planIs L a m = true)
    (hne : L' ≠ L ∨ a' ≠ a) : planIs L' a' m = false := by
  cases h' : planIs L' a' m with
  | false => rfl
  | true =>
    obtain ⟨r, d⟩ := (planIs_iff L a m).1 h
    obtain ⟨r', d'⟩ := (planIs_iff L' a' m).1 h'
    exact hne.elim (fun n => absurd (Except.ok.inj (r'.symm.trans r)) n)
      (fun n => absurd (Except.ok.inj (d'.symm.trans d)) n)

/-- A written set: its key, the six lists, the stored table's depth. A structure, so that further
written values can be laid beside these. -/
structure Written where
  key : ℕ × ℕ × ℕ
  six : Six
  depth : ℕ

/-- The small example's key: the lines L, d, V among the later lines of the library's copy of a
small parameter file (`policy`, OnBytes/Params/SmallFiles.lean, lines 61, 63 and 70 of
that file). That copy is the small example WITHOUT proof of work; the small example of the written
lists (`smallFiles`, Johnson/G/RoundsOfPlanGuard.lean) has other first 32 lines and shares these
later lines. Every small parameter file of the library has this key. -/
def smallKey : ℕ × ℕ × ℕ := (8, 512, 512)

/-- The full size's written set. -/
def fullSet : Written := ⟨fullKey, (dryKeyFull, dryProofFull), 32⟩

/-- The small example's written set. -/
def smallSet : Written := ⟨smallKey, (dryKeySmall, dryProofSmall), 23⟩

/-- The library's written sets. -/
def written : List Written := [fullSet, smallSet]

/-- **Of what was made: the first set of S that has its key is there, and the rounds and the depth
are that set's.** With code. -/
def planIsAmong (S : List Written) (m : Made) : Bool :=
  match S.find? fun W => decide (W.key = keyOf m) with
  | some W => planIs W.six W.depth m
  | none => false

/-- **The six lists of rounds and the stored table's depth are those of the written set of its
key.** What is not compared: the head's Limits. -/
def planIsWritten (m : Made) : Bool := planIsAmong written m

/-- **What a yes says.** -/
theorem written_of_yes {S : List Written} {m : Made} (h : planIsAmong S m = true) :
    ∃ W ∈ S, W.key = keyOf m ∧ roundsAt m = .ok W.six ∧ depthOf m = .ok W.depth := by
  unfold planIsAmong at h
  split at h
  · rename_i W hW
    have hk := List.find?_some hW
    exact ⟨W, List.mem_of_find?_eq_some hW, of_decide_eq_true hk, (planIs_iff _ _ m).1 h⟩
  · cases h

/-- **At the full size's key a yes says: the rounds are the six written lists of the full size and
the depth is 32.** -/
theorem full_of_yes {m : Made} (hk : keyOf m = fullKey) (h : planIsWritten m = true) :
    roundsAt m = .ok (dryKeyFull, dryProofFull) ∧ depthOf m = .ok 32 := by
  obtain ⟨W, hW, k, r⟩ := written_of_yes h
  unfold written at hW
  rcases List.mem_cons.1 hW with rfl | hW
  · exact r
  · rw [List.mem_singleton] at hW
    subst hW
    exact absurd (k.trans hk) (by decide)

/-- The three sizes at the full size's values give the full size's key. -/
theorem key_of_sizes {m : Made} (hL : m.p.X.P.h.L = 48) (hd : m.p.X.P.h.d = 5120)
    (hV : m.p.X.P.h.V = 202048) : keyOf m = fullKey := by
  unfold keyOf keyOfScan fullKey
  rw [hL, hd, hV]

/-- **The way back**: at the full size's key, the six written lists and the depth 32 give a yes. -/
theorem yes_of_full {m : Made} (hk : keyOf m = fullKey)
    (hr : roundsAt m = .ok (dryKeyFull, dryProofFull)) (hd : depthOf m = .ok 32) :
    planIsWritten m = true := by
  have e : (written.find? fun W => decide (W.key = keyOf m)) = some fullSet :=
    List.find?_cons_of_pos (decide_eq_true hk.symm)
  unfold planIsWritten planIsAmong
  rw [e]
  exact (planIs_iff _ _ m).2 ⟨hr, hd⟩

/-- The test does not hang on the digest. By definition. -/
theorem planIsAmong_atDigest (S : List Written) (m : Made) (c : ByteArray) :
    planIsAmong S (atDigest m c) = planIsAmong S m := rfl

/-- **A tooth: a key that is in no set is refused.** -/
theorem no_of_key {S : List Written} {m : Made} (h : ∀ W ∈ S, W.key ≠ keyOf m) :
    planIsAmong S m = false := by
  cases h' : planIsAmong S m with
  | false => rfl
  | true =>
    obtain ⟨W, hW, k, _⟩ := written_of_yes h'
    exact absurd k (h W hW)

/-- m with 31 for the logarithm of the length of the stored table's code in the key file's shape. -/
def shallow (m : Made) : Made :=
  { m with p.chains.made.sized.key.once.shape.fold.index.code.logN := 31 }

/-- Where the depth is made it is the number in the key file's shape. -/
theorem depthOf_val {m : Made} {a : ℕ} (h : depthOf m = .ok a) :
    a = m.p.chains.made.sized.key.once.shape.fold.index.code.logN := by
  unfold depthOf at h
  dsimp only at h
  split at h
  · exact (Except.ok.inj h).symm
  · have h' : (Except.error _ : Except String ℕ) = .ok a := h
    cases h'

/-- **A tooth: whatever m is, at `shallow m` the test says no**: the depth there is 31, or it is
refused. -/
theorem planIsWritten_shallow (m : Made) : planIsWritten (shallow m) = false := by
  cases h : planIsWritten (shallow m) with
  | false => rfl
  | true =>
    obtain ⟨W, hW, _, _, d⟩ := written_of_yes h
    have e : W.depth = 31 := depthOf_val d
    unfold written at hW
    rcases List.mem_cons.1 hW with rfl | hW
    · exact absurd e (by decide)
    · rw [List.mem_singleton] at hW
      subst hW
      exact absurd e (by decide)

/-! ## The test at three files -/

/-- What is seen at an anchor: whether the seven strings are short; the rounds; the stored table's
depth; the key; what `planIsWritten` says of what was made. -/
structure Seen where
  short : Bool
  rounds : Six
  depth : ℕ
  key : ℕ × ℕ × ℕ
  pinned : Bool

/-- What is seen at 32 zero bytes in the digest's place. One call of the planner. The rounds are
made twice from the one m: here, and inside `planIsWritten`. -/
def roundsAtZero (pol lay KL : ByteArray) : Except String Seen :=
  madeOfAt pol lay KL Fmt.zero32 >>= fun m => roundsAt m >>= fun x => depthOf m >>= fun d =>
    .ok ⟨shortB m.p, x, d, keyOf m, planIsWritten m⟩

/-- Of what is seen: the strings are short, the rounds are L, the depth is a. -/
def yesAt (y : Seen) (L : Six) (a : ℕ) : Bool :=
  y.short && sameSix y.rounds L && decide (y.depth = a)

/-- **THE TEST**, with code. -/
def roundsOk (L : Six) (a : ℕ) (pol lay KL : ByteArray) : Bool :=
  match roundsAtZero pol lay KL with
  | .ok y => yesAt y L a
  | .error _ => false

/-- What `roundsAtZero` returns, step by step. -/
theorem steps_of_zero {pol lay KL : ByteArray} {y : Seen}
    (hy : roundsAtZero pol lay KL = .ok y) :
    ∃ m, madeOfAt pol lay KL Fmt.zero32 = .ok m ∧ roundsAt m = .ok y.rounds ∧
      depthOf m = .ok y.depth ∧ shortB m.p = y.short ∧ keyOf m = y.key ∧
      planIsWritten m = y.pinned := by
  unfold roundsAtZero at hy
  obtain ⟨m, hm, hy⟩ := bind_ok hy
  obtain ⟨x, hx, hy⟩ := bind_ok hy
  obtain ⟨d, hd, hy⟩ := bind_ok hy
  have e : y = ⟨shortB m.p, x, d, keyOf m, planIsWritten m⟩ := (Except.ok.inj hy).symm
  rw [e]
  exact ⟨m, hm, hx, hd, rfl, rfl, rfl⟩

/-- What a yes of the test says at the anchor. -/
theorem anchor_of_ok {L : Six} {a : ℕ} {pol lay KL : ByteArray}
    (h : roundsOk L a pol lay KL = true) :
    ∃ m, madeOfAt pol lay KL Fmt.zero32 = .ok m ∧ shortB m.p = true ∧ roundsAt m = .ok L ∧
      depthOf m = .ok a := by
  unfold roundsOk at h
  split at h
  · rename_i y hy
    obtain ⟨m, hm, hx, hd, hb, _, _⟩ := steps_of_zero hy
    unfold yesAt at h
    have h2 := Bool.and_eq_true_iff.1 h
    have h3 := Bool.and_eq_true_iff.1 h2.1
    rw [(sameSix_iff y.rounds L).1 h3.2] at hx
    rw [of_decide_eq_true h2.2] at hd
    exact ⟨m, hm, hb.trans h3.1, hx, hd⟩
  · cases h

/-- **A yes of the test gives the statement.** -/
theorem roundsAre_of_ok {L : Six} {a : ℕ} {pol lay KL : ByteArray}
    (h : roundsOk L a pol lay KL = true) : RoundsAre L a pol lay KL := by
  obtain ⟨m, hm, hb, hr, hd⟩ := anchor_of_ok h
  exact rounds_every_digest (Fmt.size_zeros 32) hm hb hr hd

/-- The converse, where the strings at the anchor are short. -/
theorem ok_of_roundsAre {L : Six} {a : ℕ} {pol lay KL : ByteArray} (h : RoundsAre L a pol lay KL)
    (hs : ∀ m, madeOfAt pol lay KL Fmt.zero32 = .ok m → shortB m.p = true) :
    roundsOk L a pol lay KL = true := by
  obtain ⟨m, hm, hr, hd⟩ := h Fmt.zero32 (Fmt.size_zeros 32)
  have e : roundsAtZero pol lay KL = .ok ⟨shortB m.p, L, a, keyOf m, planIsWritten m⟩ :=
    (exc_step _ hm).trans ((exc_step _ hr).trans (exc_step _ hd))
  unfold roundsOk
  rw [e]
  show yesAt ⟨shortB m.p, L, a, keyOf m, planIsWritten m⟩ L a = true
  unfold yesAt
  exact Bool.and_eq_true_iff.2
    ⟨Bool.and_eq_true_iff.2 ⟨hs m hm, (sameSix_iff L L).2 rfl⟩, decide_eq_true rfl⟩

/-- With code: at the anchor the planner and the sendings return, the rounds and the depth are made,
and the seven strings are short. -/
def returnsOk (pol lay KL : ByteArray) : Bool :=
  match roundsAtZero pol lay KL with
  | .ok y => y.short
  | .error _ => false

/-- With code: what `planIsWritten` says of what is made at the anchor; no at a refusal. -/
def pinnedOk (pol lay KL : ByteArray) : Bool :=
  match roundsAtZero pol lay KL with
  | .ok y => y.pinned
  | .error _ => false

/-- A yes of `pinnedOk`: something is made at the anchor, and `planIsWritten` says yes of it. -/
theorem pinned_of_ok {pol lay KL : ByteArray} (h : pinnedOk pol lay KL = true) :
    ∃ m, madeOfAt pol lay KL Fmt.zero32 = .ok m ∧ planIsWritten m = true := by
  unfold pinnedOk at h
  split at h
  · rename_i y hy
    obtain ⟨m, hm, _, _, _, _, hp⟩ := steps_of_zero hy
    exact ⟨m, hm, hp.trans h⟩
  · cases h

/-- **Where all is made at the anchor, the strings are short and the test says no, the statement is
false.** -/
theorem not_are_of_no {L : Six} {a : ℕ} {pol lay KL : ByteArray}
    (hr : returnsOk pol lay KL = true) (hn : roundsOk L a pol lay KL = false) :
    ¬ RoundsAre L a pol lay KL := by
  intro h
  have hs : ∀ m, madeOfAt pol lay KL Fmt.zero32 = .ok m → shortB m.p = true := by
    intro m hm
    unfold returnsOk at hr
    split at hr
    · rename_i y hy
      obtain ⟨m', hm', _, _, hb, _, _⟩ := steps_of_zero hy
      have em : m = m' := Except.ok.inj (hm.symm.trans hm')
      rw [em]
      exact hb.trans hr
    · cases hr
  rw [ok_of_roundsAre h hs] at hn
  cases hn

/-- The statement holds of one L and one a at most. -/
theorem roundsAre_unique {L L' : Six} {a a' : ℕ} {pol lay KL : ByteArray}
    (h : RoundsAre L a pol lay KL) (h' : RoundsAre L' a' pol lay KL) : L = L' ∧ a = a' := by
  obtain ⟨m, hm, hr, hd⟩ := h Fmt.zero32 (Fmt.size_zeros 32)
  obtain ⟨m', hm', hr', hd'⟩ := h' Fmt.zero32 (Fmt.size_zeros 32)
  obtain rfl : m = m' := Except.ok.inj (hm.symm.trans hm')
  exact ⟨Except.ok.inj (hr.symm.trans hr'), Except.ok.inj (hd.symm.trans hd')⟩

/-- The test says yes at one pair at most. -/
theorem roundsOk_unique {L L' : Six} {a a' : ℕ} {pol lay KL : ByteArray}
    (h : roundsOk L a pol lay KL = true) (hne : L' ≠ L ∨ a' ≠ a) :
    roundsOk L' a' pol lay KL = false := by
  cases h' : roundsOk L' a' pol lay KL with
  | false => rfl
  | true =>
    obtain ⟨e1, e2⟩ := roundsAre_unique (roundsAre_of_ok h') (roundsAre_of_ok h)
    exact hne.elim (fun n => absurd e1 n) (fun n => absurd e2 n)

/-- The rounds on the road through `madeOf`, at the format's own digest. -/
theorem roundsOf_of_are {L : Six} {a : ℕ} {pol lay KL : ByteArray} (h : RoundsAre L a pol lay KL) :
    roundsOf pol lay KL = .ok L := by
  obtain ⟨m, hm, hr, _⟩ :=
    h (configuration pol lay KL) (OnBytes.Params.configurationDigest_size _)
  exact (exc_step _ (madeOf_of_madeOfAt hm)).trans hr

/-- From the statement: at every digest of 32 bytes `planIs L a` says yes of what is made. -/
theorem planIs_of_are {L : Six} {a : ℕ} {pol lay KL : ByteArray} (h : RoundsAre L a pol lay KL)
    (c : ByteArray) (hc : c.size = 32) :
    ∃ m, madeOfAt pol lay KL c = .ok m ∧ planIs L a m = true := by
  obtain ⟨m, hm, hr, hd⟩ := h c hc
  exact ⟨m, hm, (planIs_iff L a m).2 ⟨hr, hd⟩⟩

/-- And of what `madeOf` makes, at the format's own digest. -/
theorem planIs_own {L : Six} {a : ℕ} {pol lay KL : ByteArray} (h : RoundsAre L a pol lay KL) :
    ∃ m, madeOf pol lay KL = .ok m ∧ planIs L a m = true := by
  obtain ⟨m, hm, hp⟩ :=
    planIs_of_are h (configuration pol lay KL) (OnBytes.Params.configurationDigest_size _)
  exact ⟨m, madeOf_of_madeOfAt hm, hp⟩

/-- **From a yes of the test and a yes of `pinnedOk`: `madeOf` returns, at the format's own digest,
and `planIsWritten` says yes of what it returns.** -/
theorem pinned_own {L : Six} {a : ℕ} {pol lay KL : ByteArray} (h : roundsOk L a pol lay KL = true)
    (hp : pinnedOk pol lay KL = true) :
    ∃ m, madeOf pol lay KL = .ok m ∧ planIsWritten m = true := by
  obtain ⟨m, hm, hb, _, _⟩ := anchor_of_ok h
  obtain ⟨m', hm', hp⟩ := pinned_of_ok hp
  have em : m' = m := Except.ok.inj (hm'.symm.trans hm)
  rw [em] at hp
  exact ⟨atDigest m (configuration pol lay KL),
    madeOf_of_madeOfAt (madeOfAt_at (Fmt.size_zeros 32)
      (OnBytes.Params.configurationDigest_size _) (short_of_test hb) hm),
    (planIsAmong_atDigest written m _).trans hp⟩

/-! ## From the written rounds back to the declared rounds, and on to the data -/

/-- **Where the written rounds are made, the declared rounds are made, and L is their written
form.** -/
theorem decl_of_roundsAt {m : Made} {L : Six} (h : roundsAt m = .ok L) :
    ∃ DK DP, declKOf m = .ok DK ∧ writtenOf "key file" DK = .ok L.1 ∧ declPOf m = .ok DP ∧
      writtenOf "proof file" DP = .ok L.2 := by
  unfold roundsAt at h
  obtain ⟨DK, hK, h⟩ := bind_ok h
  obtain ⟨wK, hwK, h⟩ := bind_ok h
  obtain ⟨DP, hP, h⟩ := bind_ok h
  obtain ⟨wP, hwP, h⟩ := bind_ok h
  have e : (wK, wP) = L := Except.ok.inj h
  rw [← e]
  exact ⟨DK, DP, hK, hwK, hP, hwP⟩

/-- **From a yes of the test: one pair of declared structures for all digests of 32 bytes**, with
the written forms L.1 and L.2. -/
theorem decl_one_of_ok {L : Six} {a : ℕ} {pol lay KL : ByteArray}
    (h : roundsOk L a pol lay KL = true) :
    ∃ DK DP, writtenOf "key file" DK = .ok L.1 ∧ writtenOf "proof file" DP = .ok L.2 ∧
      ∀ c : ByteArray, c.size = 32 →
        ∃ m, madeOfAt pol lay KL c = .ok m ∧ declKOf m = .ok DK ∧ declPOf m = .ok DP := by
  obtain ⟨m, hm, hb, hr, _⟩ := anchor_of_ok h
  obtain ⟨DK, DP, hK, hwK, hP, hwP⟩ := decl_of_roundsAt hr
  exact ⟨DK, DP, hwK, hwP, fun c hc =>
    ⟨atDigest m c, madeOfAt_at (Fmt.size_zeros 32) hc (short_of_test hb) hm,
      (declKOf_atDigest m c).trans hK, (declPOf_atDigest m c).trans hP⟩⟩

/-- **The computed data are `dataAt` of L at the depth a**: the data of L where the makers' tests
pass, and of three empty lists where they do not. -/
theorem data_of_rounds {m : Made} {L : Six} {a : ℕ} (h : roundsAt m = .ok L)
    (hd : depthOf m = .ok a) :
    dataKAt m = .ok (WholeD.of a (dataAt a (some L.1))) ∧
      dataPAt m = .ok (WholeD.of a (dataAt a (some L.2))) := by
  obtain ⟨DK, DP, hK, hwK, hP, hwP⟩ := decl_of_roundsAt h
  constructor
  · unfold dataKAt
    exact (exc_step _ hd).trans ((exc_step _ hK).trans (exc_step _ hwK))
  · unfold dataPAt
    exact (exc_step _ hd).trans ((exc_step _ hP).trans (exc_step _ hwP))

/-- The like from the statement, at every digest of 32 bytes. -/
theorem data_of_are {L : Six} {a : ℕ} {pol lay KL : ByteArray} (h : RoundsAre L a pol lay KL)
    (c : ByteArray) (hc : c.size = 32) :
    ∃ m, madeOfAt pol lay KL c = .ok m ∧ dataKAt m = .ok (WholeD.of a (dataAt a (some L.1))) ∧
      dataPAt m = .ok (WholeD.of a (dataAt a (some L.2))) := by
  obtain ⟨m, hm, hr, hd⟩ := h c hc
  exact ⟨m, hm, data_of_rounds hr hd⟩

/-! ## Another acceptance policy -/

/-- The rounds read the seven chains and the sendings, and nothing else of what was made. -/
theorem roundsAt_congr {m m' : Made} (hc : m'.p.chains = m.p.chains) (hk : m'.key = m.key)
    (hp : m'.proof = m.proof) : roundsAt m' = roundsAt m := by
  obtain ⟨⟨X, cfg, ch, B⟩, k, q⟩ := m
  obtain ⟨⟨X', cfg', ch', B'⟩, k', q'⟩ := m'
  dsimp only at hc hk hp
  subst hc hk hp
  rfl

/-- The depth reads the seven chains, and nothing else of what was made. -/
theorem depthOf_congr {m m' : Made} (hc : m'.p.chains = m.p.chains) : depthOf m' = depthOf m := by
  unfold depthOf
  rw [hc]

/-- At two parameter files whose strict scans differ in the policy's three numbers alone, at one
digest: the same rounds, the same depth, and the same test on the strings. -/
theorem madeOfAt_withPol {pol pol' lay KL c : ByteArray} {m m' : Made} {C theta cap : ℕ}
    (h : madeOfAt pol lay KL c = .ok m) (h' : madeOfAt pol' lay KL c = .ok m')
    (hs : polScan pol' = .ok (m.p.X.P.withPol C theta cap)) :
    roundsAt m' = roundsAt m ∧ depthOf m' = depthOf m ∧ shortB m'.p = shortB m.p := by
  have hch : m'.p.chains = m.p.chains :=
    (plannedAt_withPol (madeOfAt_planned h) (madeOfAt_planned h') hs).2.2.1
  unfold madeOfAt at h h'
  obtain ⟨p, _, h⟩ := bind_ok h
  obtain ⟨s, hs1, h⟩ := bind_ok h
  obtain ⟨p', _, h'⟩ := bind_ok h'
  obtain ⟨s', hs2, h'⟩ := bind_ok h'
  rw [← packMade_p h] at hs1
  rw [← packMade_p h', hch] at hs2
  obtain rfl : s = s' := Except.ok.inj (hs1.symm.trans hs2)
  have e : m' = { m with p := p' } := Except.ok.inj (h'.symm.trans (packMade_with h p'))
  refine ⟨roundsAt_congr hch (by rw [e]) (by rw [e]), depthOf_congr hch, ?_⟩
  unfold shortB
  rw [hch]

/-- **Another acceptance policy wants no second lists.** -/
theorem roundsAre_withPol {L : Six} {a : ℕ} {pol pol' lay KL : ByteArray} {m m' : Made}
    {C theta cap : ℕ} (hL : RoundsAre L a pol lay KL) (h : madeOfAt pol lay KL Fmt.zero32 = .ok m)
    (h' : madeOfAt pol' lay KL Fmt.zero32 = .ok m') (hb : shortB m.p = true)
    (hs : polScan pol' = .ok (m.p.X.P.withPol C theta cap)) : RoundsAre L a pol' lay KL := by
  obtain ⟨m₀, hm₀, hr, hd⟩ := hL Fmt.zero32 (Fmt.size_zeros 32)
  obtain rfl : m = m₀ := Except.ok.inj (h.symm.trans hm₀)
  obtain ⟨e1, e2, e3⟩ := madeOfAt_withPol h h' hs
  exact rounds_every_digest (Fmt.size_zeros 32) h' (e3.trans hb) (e1.trans hr) (e2.trans hd)

/-! ## Four controls on the written values -/

/-- A list with f at its last member. -/
def bendLast {α : Type} (f : α → α) (l : List α) : List α :=
  match l.getLast? with
  | some x => l.dropLast ++ [f x]
  | none => l

/-- The written lists with another value for the proof file's second chain. -/
def withSecond (R : Rounds) : Six := (dryKeyFull, (dryProofFull.1, dryProofFull.2.1, R))

/-- Control 1's second chain: the last round's work is one more. -/
def bentWorkR : Rounds :=
  bendLast (fun x => ({ x.1 with entry := { x.1.entry with work := x.1.entry.work + 1 } }, x.2))
    dryProofFull.2.2

/-- Control 2's second chain: the last round's last opened tree is struck. -/
def lessTreeR : Rounds :=
  bendLast (fun x => ({ x.1 with opens := x.1.opens.dropLast }, x.2)) dryProofFull.2.2

/-- Control 3's second chain: the last round is dropped. -/
def droppedR : Rounds := dryProofFull.2.2.dropLast

/-- Control 1. -/
def bentWork : Six := withSecond bentWorkR

/-- Control 2. -/
def lessTree : Six := withSecond lessTreeR

/-- Control 3. -/
def dropped : Six := withSecond droppedR

/-- Each control's second chain is another list than the written one. By an evaluation in Lean's
kernel, on 30 rounds. -/
theorem second_ne :
    (sameR bentWorkR dryProofFull.2.2, sameR lessTreeR dryProofFull.2.2,
      sameR droppedR dryProofFull.2.2) = (false, false, false) := by
  decide +kernel

/-- Control 1's second chain is another list than the small example's. By an evaluation in Lean's
kernel. -/
theorem second_ne_small : sameR bentWorkR dryProofSmall.2.2 = false := by
  decide +kernel

attribute [local irreducible] Johnson.G.dryProofFull Johnson.G.dryKeyFull
  Johnson.G.dryProofSmall Johnson.G.dryKeySmall bentWorkR lessTreeR droppedR

/-- Another second chain gives another value than the written lists. -/
theorem ne_of_second {R : Rounds} (h : sameR R dryProofFull.2.2 = false) :
    withSecond R ≠ (dryKeyFull, dryProofFull) := fun e =>
  of_decide_eq_false h (congrArg (fun x : Six => x.2.2.2) e)

/-- So each of the three controls is another value than the written lists. -/
theorem bent_ne :
    bentWork ≠ (dryKeyFull, dryProofFull) ∧ lessTree ≠ (dryKeyFull, dryProofFull) ∧
      dropped ≠ (dryKeyFull, dryProofFull) :=
  ⟨ne_of_second (congrArg (·.1) second_ne), ne_of_second (congrArg (·.2.1) second_ne),
    ne_of_second (congrArg (·.2.2) second_ne)⟩

/-- **Where the test says yes at the written lists and the depth 32 it says no at each of the four
controls.** -/
theorem control_no {pol lay KL : ByteArray}
    (h : roundsOk (dryKeyFull, dryProofFull) 32 pol lay KL = true) :
    roundsOk bentWork 32 pol lay KL = false ∧ roundsOk lessTree 32 pol lay KL = false ∧
      roundsOk dropped 32 pol lay KL = false ∧
      roundsOk (dryKeyFull, dryProofFull) 31 pol lay KL = false :=
  ⟨roundsOk_unique h (.inl bent_ne.1), roundsOk_unique h (.inl bent_ne.2.1),
    roundsOk_unique h (.inl bent_ne.2.2), roundsOk_unique h (.inr (by decide))⟩

/-- The written sets with one number of one list of the full size changed (control 1's value). -/
def planted : List Written := [⟨fullKey, bentWork, 32⟩, smallSet]

/-- **A tooth: A PLANT IS REFUSED.** If the rounds of m are the written lists of the full size with
one number changed, `planIsWritten` says no of m, whatever its key. -/
theorem plant_refused {m : Made} (h : roundsAt m = .ok bentWork) : planIsWritten m = false := by
  cases h' : planIsWritten m with
  | false => rfl
  | true =>
    obtain ⟨W, hW, _, r, _⟩ := written_of_yes h'
    unfold written at hW
    rcases List.mem_cons.1 hW with rfl | hW
    · exact absurd (Except.ok.inj (h.symm.trans r)) bent_ne.1
    · rw [List.mem_singleton] at hW
      subst hW
      exact absurd (congrArg (fun x : Six => x.2.2.2) (Except.ok.inj (h.symm.trans r)))
        (of_decide_eq_false second_ne_small)

/-- **The other way about**: at the full size's key, where `planIsWritten` says yes the test at the
planted sets says no. -/
theorem planted_no {m : Made} (hk : keyOf m = fullKey) (h : planIsWritten m = true) :
    planIsAmong planted m = false := by
  cases h' : planIsAmong planted m with
  | false => rfl
  | true =>
    obtain ⟨r, _⟩ := full_of_yes hk h
    obtain ⟨W, hW, k, r', _⟩ := written_of_yes h'
    unfold planted at hW
    rcases List.mem_cons.1 hW with rfl | hW
    · exact absurd (Except.ok.inj (r'.symm.trans r)) bent_ne.1
    · rw [List.mem_singleton] at hW
      subst hW
      exact absurd (k.trans hk) (by decide)

/-- `planIsAmong` of what is seen, without making the rounds anew. With code. -/
def amongSeen (S : List Written) (y : Seen) : Bool :=
  match S.find? fun W => decide (W.key = y.key) with
  | some W => sameSix y.rounds W.six && decide (y.depth = W.depth)
  | none => false

/-! ## The ride -/

/-- Two strings of bytes have one length and differ at just one place. With code. -/
def oneByte (x y : ByteArray) : Bool :=
  x.size == y.size && ((List.range x.size).filter fun i => x.get! i != y.get! i).length == 1

/-- Of what is seen at three files: the test at W and a; `planIsWritten`; the plant (the test at the
sets P); the test at each value of C; the test at the depth a - 1. A false FROM THE THIRD LINE ON
MEANS SOMETHING ONLY BESIDE A true FIRST ANSWER: at a refusal all are false, and the first line
holds the refusal's words. -/
def linesAt (note : String) (W : Six) (a : ℕ) (P : List Written) (C : List (String × Six))
    (r : Except String Seen) : List (String × Bool) :=
  match r with
  | .ok y =>
    (note ++ ": to say true: the rounds at 32 zero bytes are the written lists, the depth is " ++
        "the written one, the strings are short", yesAt y W a) ::
      ("to say true: planIsWritten of what is made at 32 zero bytes", y.pinned) ::
      ("the plant, to say false: the plan is one of the written sets with one number changed",
        amongSeen P y) ::
      (C.map fun c => (c.1, yesAt y c.2 a)) ++
      [("control 4, to say false: the depth is one less", yesAt y W (a - 1))]
  | .error e =>
    (note ++ ": refused: " ++ e, false) :: ("planIsWritten", false) :: ("the plant", false) ::
      (C.map fun c => (c.1, false)) ++ [("control 4", false)]

/-- Control 5, of what is seen at a second parameter file. Where the planner refuses there the
control is idle, and the second line holds the refusal's words. -/
def linesBent (W : Six) (a : ℕ) (pol bent : ByteArray) (r : Except String Seen) :
    List (String × Bool) :=
  ("control 5, to say true: the second parameter file has the first's length and differs at one " ++
      "byte", oneByte pol bent) ::
  match r with
  | .ok y =>
    [("control 5, to say true: at the second file all is made and the strings are short", y.short),
      ("control 5, to say false: there the rounds are the written lists and the depth the written",
        yesAt y W a),
      ("control 5, to say false: planIsWritten of what is made there", y.pinned),
      ("control 5, to say false: there the proof file's shared chain is the written list",
        sameR y.rounds.2.2.1 W.2.2.1),
      ("control 5, seen, not foretold: there the other five lists are the written lists",
        sameR y.rounds.1.1 W.1.1 && sameR y.rounds.1.2.1 W.1.2.1 &&
          sameR y.rounds.1.2.2 W.1.2.2 && sameR y.rounds.2.1 W.2.1 &&
          sameR y.rounds.2.2.2 W.2.2.2),
      ("control 5, to say true: there the depth is the written one", decide (y.depth = a))]
  | .error e =>
    [("control 5 IS IDLE: refused at the second file: " ++ e, false), ("control 5", false),
      ("control 5", false), ("control 5", false), ("control 5", false), ("control 5", false)]

/-- **FOR A RUN**, at any written set: two calls of `roundsAtZero`: at pol, and at the second
parameter file bent. -/
@[noinline] def rideAt (note : String) (W : Six) (a : ℕ) (P : List Written)
    (C : List (String × Six)) (pol bent lay KL : ByteArray) : List (String × Bool) :=
  linesAt note W a P C (roundsAtZero pol lay KL) ++
    linesBent W a pol bent (roundsAtZero bent lay KL)

/-- Controls 1 to 3, with their lines' words. -/
def threeControls : List (String × Six) :=
  [("control 1, to say false: one round's work is one more", bentWork),
    ("control 2, to say false: one opened tree is struck", lessTree),
    ("control 3, to say false: one round is dropped", dropped)]

/-- **FOR A RUN**, at the full size's written set: fourteen named Bools. -/
def ride (note : String) (pol bent lay KL : ByteArray) : List (String × Bool) :=
  rideAt note (dryKeyFull, dryProofFull) 32 planted threeControls pol bent lay KL

/-- With code: the test at the planted sets, of what is made at the anchor; no at a refusal. -/
def plantOk (pol lay KL : ByteArray) : Bool :=
  match roundsAtZero pol lay KL with
  | .ok y => amongSeen planted y
  | .error _ => false

/-- What `amongSeen` evaluates is `planIsAmong` of what is made at the anchor. -/
theorem amongSeen_eq (S : List Written) {pol lay KL : ByteArray} {y : Seen}
    (hy : roundsAtZero pol lay KL = .ok y) :
    ∃ m, madeOfAt pol lay KL Fmt.zero32 = .ok m ∧ planIsAmong S m = amongSeen S y := by
  obtain ⟨m, hm, hx, hd, _, hk, _⟩ := steps_of_zero hy
  refine ⟨m, hm, ?_⟩
  unfold planIsAmong amongSeen planIs
  rw [hx, hd, hk]

/-- The ride's first eleven answers: the test; `planIsWritten`; the plant; the test at the four
controls; that the second file differs at one byte; whether all is made there; the test and
`planIsWritten` there. -/
theorem ride_snd (note : String) (pol bent lay KL : ByteArray) :
    ((ride note pol bent lay KL).map Prod.snd).take 11 =
      [roundsOk (dryKeyFull, dryProofFull) 32 pol lay KL, pinnedOk pol lay KL, plantOk pol lay KL,
        roundsOk bentWork 32 pol lay KL, roundsOk lessTree 32 pol lay KL,
        roundsOk dropped 32 pol lay KL, roundsOk (dryKeyFull, dryProofFull) 31 pol lay KL,
        oneByte pol bent, returnsOk bent lay KL,
        roundsOk (dryKeyFull, dryProofFull) 32 bent lay KL, pinnedOk bent lay KL] := by
  unfold ride rideAt linesAt linesBent threeControls roundsOk returnsOk pinnedOk plantOk
  cases roundsAtZero pol lay KL <;> cases roundsAtZero bent lay KL <;> rfl

/-- The ride's first answer is the test's at the written lists and the depth 32. -/
theorem ride_head (note : String) (pol bent lay KL : ByteArray) :
    ((ride note pol bent lay KL).map Prod.snd).head? =
      some (roundsOk (dryKeyFull, dryProofFull) 32 pol lay KL) := by
  unfold ride rideAt linesAt roundsOk
  cases roundsAtZero pol lay KL <;> rfl

/-- What the ride's first eleven answers are to be. -/
def foretold : List Bool :=
  [true, true, false, false, false, false, false, true, true, false, false]

/-- **What a ride with the foretold answers gives**: the statement at pol; a yes of `planIsWritten`
of what `madeOf` returns; AND THE STATEMENT IS FALSE AT THE SECOND PARAMETER FILE, though all is
made there. -/
theorem of_ride {note : String} {pol bent lay KL : ByteArray}
    (h : ((ride note pol bent lay KL).map Prod.snd).take 11 = foretold) :
    RoundsWritten pol lay KL ∧
      (∃ m, madeOf pol lay KL = .ok m ∧ planIsWritten m = true) ∧
      returnsOk bent lay KL = true ∧ ¬ RoundsWritten bent lay KL := by
  rw [ride_snd] at h
  unfold foretold at h
  obtain ⟨h1, h⟩ := List.cons.inj h
  obtain ⟨h2, h⟩ := List.cons.inj h
  obtain ⟨_, h⟩ := List.cons.inj h
  obtain ⟨_, h⟩ := List.cons.inj h
  obtain ⟨_, h⟩ := List.cons.inj h
  obtain ⟨_, h⟩ := List.cons.inj h
  obtain ⟨_, h⟩ := List.cons.inj h
  obtain ⟨_, h⟩ := List.cons.inj h
  obtain ⟨h9, h⟩ := List.cons.inj h
  obtain ⟨h10, _⟩ := List.cons.inj h
  exact ⟨roundsAre_of_ok h1, pinned_own h1 h2, h9, not_are_of_no h9 h10⟩

end VerifiableInference.PlanWritten

#print axioms VerifiableInference.PlanWritten.roundsAt_atDigest
#print axioms VerifiableInference.PlanWritten.depthOf_atDigest
#print axioms VerifiableInference.PlanWritten.declKOf_atDigest
#print axioms VerifiableInference.PlanWritten.declPOf_atDigest
#print axioms VerifiableInference.PlanWritten.rounds_every_digest
#print axioms VerifiableInference.PlanWritten.sameSix_iff
#print axioms VerifiableInference.PlanWritten.planIs_iff
#print axioms VerifiableInference.PlanWritten.planIs_unique
#print axioms VerifiableInference.PlanWritten.written_of_yes
#print axioms VerifiableInference.PlanWritten.full_of_yes
#print axioms VerifiableInference.PlanWritten.key_of_sizes
#print axioms VerifiableInference.PlanWritten.yes_of_full
#print axioms VerifiableInference.PlanWritten.planIsAmong_atDigest
#print axioms VerifiableInference.PlanWritten.no_of_key
#print axioms VerifiableInference.PlanWritten.depthOf_val
#print axioms VerifiableInference.PlanWritten.planIsWritten_shallow
#print axioms VerifiableInference.PlanWritten.steps_of_zero
#print axioms VerifiableInference.PlanWritten.anchor_of_ok
#print axioms VerifiableInference.PlanWritten.roundsAre_of_ok
#print axioms VerifiableInference.PlanWritten.ok_of_roundsAre
#print axioms VerifiableInference.PlanWritten.pinned_of_ok
#print axioms VerifiableInference.PlanWritten.not_are_of_no
#print axioms VerifiableInference.PlanWritten.roundsAre_unique
#print axioms VerifiableInference.PlanWritten.roundsOk_unique
#print axioms VerifiableInference.PlanWritten.roundsOf_of_are
#print axioms VerifiableInference.PlanWritten.planIs_of_are
#print axioms VerifiableInference.PlanWritten.planIs_own
#print axioms VerifiableInference.PlanWritten.pinned_own
#print axioms VerifiableInference.PlanWritten.decl_of_roundsAt
#print axioms VerifiableInference.PlanWritten.decl_one_of_ok
#print axioms VerifiableInference.PlanWritten.data_of_rounds
#print axioms VerifiableInference.PlanWritten.data_of_are
#print axioms VerifiableInference.PlanWritten.roundsAt_congr
#print axioms VerifiableInference.PlanWritten.depthOf_congr
#print axioms VerifiableInference.PlanWritten.madeOfAt_withPol
#print axioms VerifiableInference.PlanWritten.roundsAre_withPol
#print axioms VerifiableInference.PlanWritten.second_ne
#print axioms VerifiableInference.PlanWritten.second_ne_small
#print axioms VerifiableInference.PlanWritten.ne_of_second
#print axioms VerifiableInference.PlanWritten.bent_ne
#print axioms VerifiableInference.PlanWritten.control_no
#print axioms VerifiableInference.PlanWritten.plant_refused
#print axioms VerifiableInference.PlanWritten.planted_no
#print axioms VerifiableInference.PlanWritten.amongSeen_eq
#print axioms VerifiableInference.PlanWritten.ride_snd
#print axioms VerifiableInference.PlanWritten.ride_head
#print axioms VerifiableInference.PlanWritten.of_ride
