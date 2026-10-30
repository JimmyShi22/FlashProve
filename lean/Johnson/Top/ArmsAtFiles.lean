-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/ArmsAtFiles.lean: the fields `records` and `entry` of `ArmTies` at the full size, at any
three public files Z. `ArmTies` (Johnson/Top/TieOnFilesArms.lean) is the record of named hypotheses
of the linking statement between the Lean program verify-on-bytes (OnBytes/Main.lean) and
`verifyArms r`, the verifier of which Johnson/Top/OnFilesArms.lean states soundness under its own
named hypotheses. Here the data G of the key file's and the proof file's protocols are a concrete
function of Z (defined in this library, not a parameter), and a statement is served only if one
concrete test on Z, `ownFullAtB Z`, evaluates to true. The theorems are instances of
`armTies_records_full` and `armTies_entry_full` (Johnson/Top/ArmsAtSizes.lean). Nothing new is
proved about G.
Z has three public files (`Pub`, OnBytes/K/Served.lean), the parameter file `pol`, the layout file
`lay` and the scale file `KL`. A statement is "served at Z" if `servedAt Z` (same file) evaluates to
true for it. In this file "served" requires more, as the entry on `armTies_records_full_own` below
says. The full size is that of the reference sizes (Johnson/Flat/ThreeAtFiles.lean), and the small
size is that of the small example (Johnson/Flat/SmallAtFiles.lean).

Main statements (namespace `OnBytes.K.ArmsAtFiles`):
  `bigZFull Z`: G as a total function of Z. It is `bigReq` (Johnson/Flat/ThreeAtFiles.lean) at the
    answer of the program's planner at Z (`bigZFull_of`), and the fixed record `bigStandFull` where
    the planner refuses.
  `ownFullAtB Z`: the test on Z. It evaluates to true only if the first 32 lines of Z's parameter
    file are read as the lines of the fixed public parameters (`recordGround`), the planner returns,
    the dry-run tests (`GuardsPassFull`) pass, and two tests on the numbers of blocks evaluate to
    true. This is `ownFullAt_gives`, which also gives that G is at the plan of Z. `fitsFullB` and
    `ownFullB` are its parts.
  `armTies_records_full_served`, `armTies_entry_full_served`: the two fields at any G and Z, which
    are independent parameters here, where a statement is served only if a proposition C holds. C
    implies (hypothesis hC) the three hypotheses of the two theorems of ArmsAtSizes.lean, which are
    the lines and the two tests on the numbers of blocks at G.
  `armTies_records_full_own`, `armTies_entry_full_own`: the two fields exactly as `ArmTies` states
    them, at `tieArmsFull` and `readingFull` (ArmsAtSizes.lean), with G := `bigZFull Z` and C :=
    (`ownFullAtB Z` = true). A statement x is served if it is served at Z (`servedArm`, which is
    `servedAt`), the test on Z evaluates to true, and SvK x and SvP x hold. Their parameters include
    no hypothesis: what they assume is the field's own antecedents. That is because the statement
    covers fewer cases, not because more is proved. The conditions on Z are part of "served" (limit
    1), and laws are included in the types of parameters (limit 6). An `example` after them takes
    any H of type `ArmTies` at these parameters and replaces its fields `records` and `entry` with
    these two. That is a type check, not a theorem. H's other three fields are assumed, not shown.
  `tieOwnFull`, `tieOwnFull_served`, `armTies_records_full_own_plain`,
    `armTies_entry_full_own_plain`: the two restated with SvK := (`ownFullAtB Z` = true), SvP :=
    True and Ex := False, proved directly from the two theorems of ArmsAtSizes.lean. No parameter is
    left in "served" or in the exception. "Served" is written out as two hypotheses. No files are
    excepted, so `entry` concludes its first disjunct alone. As written, these two are not fields of
    `ArmTies`.
The field `entry` concludes that the entry file is read and the protocol's check of the entry file
evaluates to true, or that the files are excepted (Ex, a parameter). The `_plain` forms conclude the
first alone. The check is run at one fixed function, the format's oracle on bit strings
(`Run.oBits`, Lean's BLAKE2b through the format's byte coding, which, on strings outside the
format's image, hashes the whole string under a reserved number). Its result is read by `det`
(Rom/Cache.lean), which sets every random sample to 0. That this check draws no random samples is
not stated in this file. That G matches Z (G is at the plan of Z, and the dry-run tests pass)
follows from the test, by `ownFullAt_gives`, not from the fields.

Limits (what is not shown):
  1. The fields hold here because the statement covers fewer cases, not because more is proved. The
     conditions on Z stand in what is served, not among the hypotheses. Where `ownFullAtB Z` is
     false, no statement is served and both fields hold vacuously. They claim nothing there. That
     the test evaluates to true at any files is not shown here. The verifier program does not run
     this test. In one sentence: the linking statement speaks only of calls whose public files pass
     a concrete test on public data that the program itself does not run. Whether the shipped public
     files pass it is for an evaluation to say. No theorem says it. This file shows it at no files.
     The condition that the planner returns does not reduce the cases covered, because a statement
     that is served at Z already implies it (`atPlan_served`, OnBytes/Flat/BigAt.lean). At a
     parameter file that begins with the 32 lines themselves, the condition on the lines is a
     theorem (`full_says_of_prefix`, OnBytes/K/Left/SaysLinesPrefix.lean). So three conjuncts of the
     test rest on an evaluation. They are the dry-run tests (two equations) and the two tests on the
     numbers of blocks. The condition that the planner returns makes `bigZFull Z` equal to
     `bigReq p` (`bigZFull_of`), at which the two tests are stated. No proof of a field uses the
     condition that the dry-run tests pass. It is in the test so that nothing is said of files at
     which the data are vacuous, the empty data of a failed dry run (limit 4).
     "Served at Z" also requires the following of the call. Its three public files are Z's, byte for
     byte. Its options name an ID of 64 hex digits and 128 bits, and name neither -policy nor
     -no-proof-of-work. The program's function for the printed digest (`Model.hPar`) returns a
     value. `tailAt`, the end of the call computed by the program's own function on the three
     stages' results without the three files' own checks (`Key.check`, `Entry.check`,
     `Proof.check`), is a yes (`isYes`). Every other ending of the call, "within limits"
     (`CallEnd.withinLimits`) among them, fails the test. That the call is accepted is not part of
     it. That the test evaluates to true at Z does not show that any call at Z is served and
     accepted. No served call that ends in a yes is shown here.
  2. The test has no argument but Z. It is constant in the statement and reads no call.
  3. G is made of the planner's answer at Z, of the reference sizes, which are constants in the Lean
     source and not read from Z, of two sample values (`recZeroFull`, `firstReq`) and of the fixed
     function `reqWithoutReply`. The header of Johnson/Flat/LinksAt.lean says that where the sizes'
     window differs from that of Z's parameter file, the program's first step refuses the request's
     words. By an informal argument from this, not proved in Lean, the dry-run tests can pass only
     where Z's window is that of the reference sizes. Nothing is assumed of `bigStandFull`. Where
     the planner refuses, the test evaluates to false.
  4. The two tests on the numbers of blocks mean something only together with the dry-run tests. On
     the empty data of a dry run that failed, they evaluate to true (see the header of
     Johnson/Top/ArmTopTests.lean).
  5. Where the planner returns p at Z, the digest in p is `Z.digest` (`planned_entry`,
     OnBytes/Model/VerifyDerives.lean, and `Pub.digest`, OnBytes/K/ArmLetters.lean). Every chain's
     parameter bytes in p are spelled under it (`planned_spelled`, OnBytes/Model/VerifyDigest.lean).
     The field `Params.Given.cfg` of the six chains that G holds is that digest where the first of
     each file's chains has fewer than 2^64 parameter bytes (`planned_key_cfg`, `planned_proof_cfg`,
     same file). The entry's coding and the seeds' data contain `Z.digest` too. These are values of
     the library's own hash function, from which the fixed function `Run.oBits` is made. In a bound
     over a random function at this input, they are constants. By the header of
     Johnson/Top/TieOnFilesArms.lean, the linking statement and the soundness statement together say
     something only of an input that contains nothing of the fixed hash function. That condition is
     not met here. G, the test and "served" are defined with the library's own hash function, not
     with a parameter for it. No theorem here carries the two fields to the record of hypotheses in
     which the typed key holds the public digest (Johnson/Top/OnFilesArmsC.lean,
     Johnson/Top/OnFilesPortC.lean).
  6. A, E, P, sX, num, M, SvK, SvP, Ex, rdK and rdP are parameters. The data are a function of Z,
     but no concrete input is defined here. SvK and SvP have no concrete definition here. Laws are
     included in the types of A and sX. E contains two types with instances (finite, nonempty), and
     each of P's three provers contains types of random coins with the same instances. X is the type
     of requests. No file that this one imports shows that these types are inhabited together at
     this X and this G. At concrete definitions of the parameters conditions can come in.
     M is intended to contain the protocol's check of the key file through a coding whose type
     contains a law. If a proof of that law takes a bound on the numbers of blocks at G as given,
     then either that bound is a hypothesis of the input, which no clause of "served" can carry, or
     G must become a term at which the bound holds at every Z. A is intended to be the claims at the
     table of scales that is read from Z (Johnson/Flat/ThreeAtFiles.lean). That the table is read is
     a further condition on Z, which the test on Z does not include. In the forms with C, C is any
     proposition.
  7. All limits in the headers of ArmsAtSizes.lean and ThreeAtFiles.lean apply here. In particular,
     the protocol's check of the entry file is the lax one (the check with the lax Link, see limit 6
     of Johnson/Top/TieArmSib.lean), run at the fixed function `Run.oBits`. It is defined, with its
     wiring, in Johnson/Top/ArmTopFull.lean (`armTopFull`), and the two fields follow it. The fields
     `key`, `proof` and `idHash` are not shown. No bound is in this file.
  This file is for proofs only. No program imports it.

-/
import Johnson.Top.ArmsAtSizes
import Johnson.Flat.ThreeAtFiles

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace OnBytes.K.ArmsAtFiles

open Rom
open OnBytes.Flat OnBytes.Slice OnBytes.Tie Hiop Cb Cb.Ood OnBytes.K OnBytes.K.Left OnBytes.K.Arm
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open VerifiableInference.OnPublicFiles
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run (bytesToDig oBits)

/-! ## The three premises of the two fields inside "served", at any data and any files -/

section Served
variable {X : Type} (G : FilesParameters X RecFull) (Z : Pub)
  (A : (frS.toDecR frZ 402653181).Claims X) (E : Coding A)
  (P : (threeProtocolsFromDryRunAtFullSize A (Flat.relationsAndEncodingOfClaims A E) G).Provers)
  (sX : Ser X)
  (num : ℕ → Plains (restFullAt A E G P).bat.loc.shape → Bool)
  (M : ArmsMore (armTopFull A E G P Z sX num))
  (SvK SvP : UserStm → Prop) (Ex : Files → Prop)
  (C : Prop)
  (rdK : (x : UserStm) → ByteArray →
    Option (Params.TableName ×
      (shapeArms
        (tieArmsFull A E G P Z sX num M (fun x => C ∧ SvK x) SvP Ex)).PiT x))
  (rdP : (x : UserStm) → ByteArray → ByteArray → ℕ →
    Option
      ((shapeArms
        (tieArmsFull A E G P Z sX num M (fun x => C ∧ SvK x) SvP Ex)).PiB x))
  (hC : C → recordGround.SaysLines Z.pol ∧ blocksFitB .two (dataKFull G) = true ∧
    blocksFitB .two (dataPFull G) = true)

include hC in
/-- The field `records` of `ArmTies` where a statement is served only if C holds, a parameter from
which the three premises of `armTies_records_full` follow. They are not proved: they stand in
"served". At a false C nothing is served. -/
theorem armTies_records_full_served :
    ∀ F o id table further, o.id = some id → o.bits = 128 →
      PortYesAt F id table further →
      (tieArmsFull A E G P Z sX num M (fun x => C ∧ SvK x) SvP Ex).Served
        (stmOf F o) →
      (∃ c,
        (tieArmsFull A E G P Z sX num M (fun x => C ∧ SvK x) SvP Ex).recOf
          (stmOf F o) table = some c) ∧
        ∃ cj,
          (tieArmsFull A E G P Z sX num M (fun x => C ∧ SvK x) SvP Ex).recOf
            (stmOf F o) further = some cj :=
  fun F o id table further h1 h2 h3 hs =>
    have hs' : servedArm Z (stmOf F o) = true ∧ (C ∧ SvK (stmOf F o)) ∧ SvP (stmOf F o) := hs
    armTies_records_full A E G P Z sX num M (fun x => C ∧ SvK x) SvP Ex (hC hs'.2.1.1).1
      (hC hs'.2.1.1).2.1 (hC hs'.2.1.1).2.2 F o id table further h1 h2 h3 hs

include hC in
/-- The field `entry` there. At a false C nothing is served. -/
theorem armTies_entry_full_served :
    ∀ F o id table further c cj, o.id = some id → o.bits = 128 →
      PortYesAt F id table further →
      (tieArmsFull A E G P Z sX num M (fun x => C ∧ SvK x) SvP Ex).Served
        (stmOf F o) →
      (tieArmsFull A E G P Z sX num M (fun x => C ∧ SvK x) SvP Ex).recOf
        (stmOf F o) table = some c →
      (tieArmsFull A E G P Z sX num M (fun x => C ∧ SvK x) SvP Ex).recOf
        (stmOf F o) further = some cj →
      (∃ πL,
        (readingFull A E G P Z sX num M
            (fun x => C ∧ SvK x) SvP Ex rdK rdP).ent
            (stmOf F o) F.key F.ent = some (further, πL) ∧
          ((inputArmsFull A E G P Z sX num M).armE
              (bytesToDig table.root) (bytesToDig further.root) c cj πL).det
            (fun _ => oBits ()) = true) ∨
        (tieArmsFull A E G P Z sX num M (fun x => C ∧ SvK x) SvP Ex).Excepted
          F :=
  fun F o id table further c cj h1 h2 h3 hs =>
    have hs' : servedArm Z (stmOf F o) = true ∧ (C ∧ SvK (stmOf F o)) ∧ SvP (stmOf F o) := hs
    armTies_entry_full A E G P Z sX num M (fun x => C ∧ SvK x) SvP Ex rdK rdP (hC hs'.2.1.1).1
      (hC hs'.2.1.1).2.1 (hC hs'.2.1.1).2.2 F o id table further c cj h1 h2 h3 hs

end Served

/-! ## The data as a total function of three public files -/

/-- A plan of no rounds. -/
def standPlanFull : Fmt.Plan := ⟨.two, 0, 0, 0, 0, 0, []⟩

/-- A chain's parameters with no bytes. -/
def standGivenFull : Params.Given := ⟨.empty, standPlanFull, .empty, []⟩

/-- The key file's three chains, with these parameters and Lean's default values. -/
def standKeyFull : Params.KeyChains :=
  ⟨⟨standGivenFull, default, default, default, default, default⟩,
    ⟨standGivenFull, default, default⟩, ⟨standGivenFull⟩⟩

/-- The proof file's three chains, likewise. -/
def standProofFull : Params.ProofChains :=
  ⟨⟨standGivenFull, default, default, default, default, [], 0, default, []⟩,
    ⟨standGivenFull, default, default⟩, ⟨standGivenFull⟩⟩

/-- A fixed record, for files at which the planner refuses. Nothing is assumed of it. -/
def bigStandFull : FilesParameters VerifiableInference.OnPublicFiles.Flat.Req RecFull :=
  ⟨standKeyFull, standProofFull, fun _ => Proof.firstEnd default, recZeroFull,
    (firstReq, recZeroFull), 0, reqWithoutReply⟩

/-- **The data of the key file's and the proof file's protocols as a total function of three public
files**: `bigReq` at the planner's answer; the fixed record where the planner refuses. -/
def bigZFull (Z : Pub) : FilesParameters VerifiableInference.OnPublicFiles.Flat.Req RecFull :=
  match planOf Z with
  | .ok p => bigReq p
  | .error _ => bigStandFull

/-- Where the planner returns p, the data are those made of p. -/
theorem bigZFull_of {Z : Pub} {p : Model.Verify.Planned} (hp : planOf Z = .ok p) :
    bigZFull Z = bigReq p := by
  unfold bigZFull
  rw [hp]

/-! ## The conditions that G and the two fields require of the files, as one test -/

/-- The two tests on the numbers of blocks at the data made of a planner's answer, as one test. -/
def fitsFullB (p : Model.Verify.Planned) : Bool :=
  blocksFitB .two (dataKFull (bigReq p)) && blocksFitB .two (dataPFull (bigReq p))

/-- If the test says yes, both tests say yes. -/
theorem fitsFull_of_test {p : Model.Verify.Planned} (h : fitsFullB p = true) :
    blocksFitB .two (dataKFull (bigReq p)) = true ∧
      blocksFitB .two (dataPFull (bigReq p)) = true := by
  unfold fitsFullB at h
  rw [Bool.and_eq_true] at h
  exact h

/-- A test on three public files. It says yes only if the planner returns, the makers' tests on the
dry runs pass, and the two tests on the numbers of blocks say yes (`ownFull_of_test`). `decide` has
code by the instance `decGuardsPassFull` (Johnson/Flat/ThreeAtFiles.lean): `GuardsPassFull` unfolds
to two equations between values of Bool. -/
def ownFullB (Z : Pub) : Bool :=
  match planOf Z with
  | .ok p => decide (GuardsPassFull (bigReq p)) && fitsFullB p
  | .error _ => false

/-- If the test says yes, the planner returns, and at its answer the makers' tests pass and the two
other tests say yes. -/
theorem ownFull_of_test {Z : Pub} (t : ownFullB Z = true) :
    ∃ p, planOf Z = .ok p ∧ GuardsPassFull (bigReq p) ∧
      blocksFitB .two (dataKFull (bigReq p)) = true ∧
      blocksFitB .two (dataPFull (bigReq p)) = true := by
  unfold ownFullB at t
  cases h : planOf Z with
  | error e =>
    rw [h] at t
    cases t
  | ok p =>
    rw [h] at t
    simp only [Bool.and_eq_true, decide_eq_true_eq] at t
    exact ⟨p, rfl, t.1, fitsFull_of_test t.2⟩

/-- **The one test on three public files**: `ownFullB`, and Z's parameter file says the lines of the
fixed public parameters (`recordGround`). -/
def ownFullAtB (Z : Pub) : Bool := TestSaysLines.linesAre recordGround Z.pol && ownFullB Z

/- Lean has code for both tests: at three empty files they run and say no. That they can say yes is
not shown here. -/
#guard !ownFullB ⟨ByteArray.empty, ByteArray.empty, ByteArray.empty⟩
#guard !ownFullAtB ⟨ByteArray.empty, ByteArray.empty, ByteArray.empty⟩

/-- **What the one test gives**: the lines of the fixed public parameters; the data are at the plan
of Z; the makers' tests on the dry runs pass; the two tests on the numbers of blocks say yes. -/
theorem ownFullAt_gives {Z : Pub} (t : ownFullAtB Z = true) :
    recordGround.SaysLines Z.pol ∧ AtPlan Z (bigZFull Z) ∧ GuardsPassFull (bigZFull Z) ∧
      blocksFitB .two (dataKFull (bigZFull Z)) = true ∧
      blocksFitB .two (dataPFull (bigZFull Z)) = true := by
  unfold ownFullAtB at t
  rw [Bool.and_eq_true] at t
  obtain ⟨p, hp, g, hK, hP⟩ := ownFull_of_test t.2
  rw [bigZFull_of hp]
  exact ⟨(TestSaysLines.linesAre_iff _ _).1 t.1, atPlan_bigReq hp, g, hK, hP⟩

/-! ## The two fields at these data, with the one test inside "served" -/

section Own
variable (Z : Pub)
  (A : (frS.toDecR frZ 402653181).Claims VerifiableInference.OnPublicFiles.Flat.Req) (E : Coding A)
  (P : (threeProtocolsFromDryRunAtFullSize A (Flat.relationsAndEncodingOfClaims A E) (bigZFull Z)).Provers)
  (sX : Ser VerifiableInference.OnPublicFiles.Flat.Req)
  (num : ℕ → Plains (restFullAt A E (bigZFull Z) P).bat.loc.shape → Bool)
  (M : ArmsMore (armTopFull A E (bigZFull Z) P Z sX num))
  (SvK SvP : UserStm → Prop) (Ex : Files → Prop)
  (rdK : (x : UserStm) → ByteArray →
    Option (Params.TableName ×
      (shapeArms
        (tieArmsFull A E (bigZFull Z) P Z sX num M
          (fun x => ownFullAtB Z = true ∧ SvK x) SvP Ex)).PiT x))
  (rdP : (x : UserStm) → ByteArray → ByteArray → ℕ →
    Option
      ((shapeArms
        (tieArmsFull A E (bigZFull Z) P Z sX num M
          (fun x => ownFullAtB Z = true ∧ SvK x) SvP Ex)).PiB x))

/-- **The field `records` of `ArmTies` at any three public files Z, at the data made of Z, where a
statement is served only if the one test on Z says yes.** No hypothesis among the parameters. This
holds because the statement covers fewer cases, not because more is proved. Where `ownFullAtB Z`
says no, nothing is served and the field holds vacuously. It claims nothing there. -/
theorem armTies_records_full_own :
    ∀ F o id table further, o.id = some id → o.bits = 128 →
      PortYesAt F id table further →
      (tieArmsFull A E (bigZFull Z) P Z sX num M
        (fun x => ownFullAtB Z = true ∧ SvK x) SvP Ex).Served
        (stmOf F o) →
      (∃ c,
        (tieArmsFull A E (bigZFull Z) P Z sX num M
          (fun x => ownFullAtB Z = true ∧ SvK x) SvP Ex).recOf
          (stmOf F o) table = some c) ∧
        ∃ cj,
          (tieArmsFull A E (bigZFull Z) P Z sX num M
            (fun x => ownFullAtB Z = true ∧ SvK x) SvP Ex).recOf
            (stmOf F o) further = some cj :=
  armTies_records_full_served (bigZFull Z) Z A E P sX num M SvK SvP Ex (ownFullAtB Z = true)
    fun t => ⟨(ownFullAt_gives t).1, (ownFullAt_gives t).2.2.2⟩

/-- **The field `entry` there**, at `readingFull` (ArmsAtSizes.lean), which reads the entry file as
`readTopFull` reads it, and the key file and the proof file by the parameters rdK and rdP. No
hypothesis among the parameters. This holds because the statement covers fewer cases, not because
more is proved, as there. -/
theorem armTies_entry_full_own :
    ∀ F o id table further c cj, o.id = some id → o.bits = 128 →
      PortYesAt F id table further →
      (tieArmsFull A E (bigZFull Z) P Z sX num M
        (fun x => ownFullAtB Z = true ∧ SvK x) SvP Ex).Served
        (stmOf F o) →
      (tieArmsFull A E (bigZFull Z) P Z sX num M
        (fun x => ownFullAtB Z = true ∧ SvK x) SvP Ex).recOf
        (stmOf F o) table = some c →
      (tieArmsFull A E (bigZFull Z) P Z sX num M
        (fun x => ownFullAtB Z = true ∧ SvK x) SvP Ex).recOf
        (stmOf F o) further = some cj →
      (∃ πL,
        (readingFull A E (bigZFull Z) P Z sX num M
            (fun x => ownFullAtB Z = true ∧ SvK x) SvP Ex rdK rdP).ent
            (stmOf F o) F.key F.ent = some (further, πL) ∧
          ((inputArmsFull A E (bigZFull Z) P Z sX num M).armE
              (bytesToDig table.root) (bytesToDig further.root) c cj πL).det
            (fun _ => oBits ()) = true) ∨
        (tieArmsFull A E (bigZFull Z) P Z sX num M
          (fun x => ownFullAtB Z = true ∧ SvK x) SvP Ex).Excepted
          F :=
  armTies_entry_full_served (bigZFull Z) Z A E P sX num M SvK SvP Ex (ownFullAtB Z = true) rdK rdP
    fun t => ⟨(ownFullAt_gives t).1, (ownFullAt_gives t).2.2.2⟩

/-- Lean's own check that the two statements are the fields `records` and `entry` of `ArmTies` at
these parameters and at `readingFull`: they are put into a term of that type. H is assumed whole;
its three other fields alone are used, and they are not shown. An example leaves no name: the build
alone checks it. -/
example
    (H : ArmTies
      (tieArmsFull A E (bigZFull Z) P Z sX num M
        (fun x => ownFullAtB Z = true ∧ SvK x) SvP Ex)
      (readingFull A E (bigZFull Z) P Z sX num M
        (fun x => ownFullAtB Z = true ∧ SvK x) SvP Ex rdK rdP)) :
    ArmTies
      (tieArmsFull A E (bigZFull Z) P Z sX num M
        (fun x => ownFullAtB Z = true ∧ SvK x) SvP Ex)
      (readingFull A E (bigZFull Z) P Z sX num M
        (fun x => ownFullAtB Z = true ∧ SvK x) SvP Ex rdK rdP) :=
  { H with
    records := armTies_records_full_own Z A E P sX num M SvK SvP Ex
    entry := armTies_entry_full_own Z A E P sX num M SvK SvP Ex rdK rdP }

end Own

/-! ## The same with no parameter left in "served" or in the exception -/

section Plain
variable (Z : Pub)
  (A : (frS.toDecR frZ 402653181).Claims VerifiableInference.OnPublicFiles.Flat.Req) (E : Coding A)
  (P : (threeProtocolsFromDryRunAtFullSize A (Flat.relationsAndEncodingOfClaims A E) (bigZFull Z)).Provers)
  (sX : Ser VerifiableInference.OnPublicFiles.Flat.Req)
  (num : ℕ → Plains (restFullAt A E (bigZFull Z) P).bat.loc.shape → Bool)
  (M : ArmsMore (armTopFull A E (bigZFull Z) P Z sX num))

/-- The linking statement's parameters with no parameter left in "served" or in the exception: a
statement is served if it is served at Z and the one test on Z says yes; no files are excepted. That
fits the entry file's field, which holds by its first limb. It is no linking statement that can be
finished: with no files excepted the fields `key` and `proof` cannot be expected to hold. -/
abbrev tieOwnFull : TieArms (inputArmsFull A E (bigZFull Z) P Z sX num M) :=
  tieArmsFull A E (bigZFull Z) P Z sX num M (fun _ => ownFullAtB Z = true) (fun _ => True)
    (fun _ => False)

/-- What "served" is at these parameters. -/
theorem tieOwnFull_served (x : UserStm) :
    (tieOwnFull Z A E P sX num M).Served x ↔ servedArm Z x = true ∧ ownFullAtB Z = true :=
  ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, trivial⟩⟩

variable
  (rdK : (x : UserStm) → ByteArray →
    Option (Params.TableName × (shapeArms (tieOwnFull Z A E P sX num M)).PiT x))
  (rdP : (x : UserStm) → ByteArray → ByteArray → ℕ →
    Option ((shapeArms (tieOwnFull Z A E P sX num M)).PiB x))

/-- **`records` restated, with "served" written out** as two hypotheses: the second is the test on
Z. In addition to these, the field's own antecedents alone. This holds because the statement covers
fewer cases, not because more is proved. Where `ownFullAtB Z` says no, it holds vacuously. It claims
nothing there. -/
theorem armTies_records_full_own_plain :
    ∀ F o id table further, o.id = some id → o.bits = 128 →
      PortYesAt F id table further →
      servedArm Z (stmOf F o) = true → ownFullAtB Z = true →
      (∃ c, (tieOwnFull Z A E P sX num M).recOf (stmOf F o) table = some c) ∧
        ∃ cj, (tieOwnFull Z A E P sX num M).recOf (stmOf F o) further = some cj :=
  fun F o id table further h1 h2 h3 hs t =>
    armTies_records_full A E (bigZFull Z) P Z sX num M (fun _ => ownFullAtB Z = true)
      (fun _ => True) (fun _ => False) (ownFullAt_gives t).1 (ownFullAt_gives t).2.2.2.1
      (ownFullAt_gives t).2.2.2.2 F o id table further h1 h2 h3 ⟨hs, t, trivial⟩

/-- **`entry` restated, with "served" written out and no files excepted**: the entry file is read,
and the protocol's check of the entry file says yes. "Served" is two hypotheses, as there; in
addition to these, the field's own antecedents alone. This holds because the statement covers fewer
cases, not because more is proved. -/
theorem armTies_entry_full_own_plain :
    ∀ F o id table further c cj, o.id = some id → o.bits = 128 →
      PortYesAt F id table further →
      servedArm Z (stmOf F o) = true → ownFullAtB Z = true →
      (tieOwnFull Z A E P sX num M).recOf (stmOf F o) table = some c →
      (tieOwnFull Z A E P sX num M).recOf (stmOf F o) further = some cj →
      ∃ πL,
        (readingFull A E (bigZFull Z) P Z sX num M (fun _ => ownFullAtB Z = true) (fun _ => True)
            (fun _ => False) rdK rdP).ent (stmOf F o) F.key F.ent = some (further, πL) ∧
          ((inputArmsFull A E (bigZFull Z) P Z sX num M).armE
              (bytesToDig table.root) (bytesToDig further.root) c cj πL).det
            (fun _ => oBits ()) = true :=
  fun F o id table further c cj h1 h2 h3 hs t hc hj =>
    (armTies_entry_full A E (bigZFull Z) P Z sX num M (fun _ => ownFullAtB Z = true)
      (fun _ => True) (fun _ => False) rdK rdP (ownFullAt_gives t).1 (ownFullAt_gives t).2.2.2.1
      (ownFullAt_gives t).2.2.2.2 F o id table further c cj h1 h2 h3 ⟨hs, t, trivial⟩ hc
      hj).resolve_right fun h => h

end Plain

end OnBytes.K.ArmsAtFiles

#print axioms OnBytes.K.ArmsAtFiles.armTies_records_full_served
#print axioms OnBytes.K.ArmsAtFiles.armTies_entry_full_served
#print axioms OnBytes.K.ArmsAtFiles.bigZFull_of
#print axioms OnBytes.K.ArmsAtFiles.fitsFull_of_test
#print axioms OnBytes.K.ArmsAtFiles.ownFull_of_test
#print axioms OnBytes.K.ArmsAtFiles.ownFullAt_gives
#print axioms OnBytes.K.ArmsAtFiles.armTies_records_full_own
#print axioms OnBytes.K.ArmsAtFiles.armTies_entry_full_own
#print axioms OnBytes.K.ArmsAtFiles.tieOwnFull_served
#print axioms OnBytes.K.ArmsAtFiles.armTies_records_full_own_plain
#print axioms OnBytes.K.ArmsAtFiles.armTies_entry_full_own_plain
