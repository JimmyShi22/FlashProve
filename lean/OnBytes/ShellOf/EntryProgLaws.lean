-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/ShellOf/EntryProgLaws.lean: the theorems on the program of EntryProg.lean. Proofs only: no
program imports this file.

States. `entryMainO_zero`, `entryMain_zero`: what exit code 0 says of a call (`ZeroSays`): the
closed check `verifyEntryFull` | `verifyEntrySmall` says yes at the three public files as read and
at the value that the parser made of the key file and the entry file, and the commitment ID that the
hash gives of these files and the value's first table is the user's. `kit_zero`: the general form.
`runAt_eq`, `runFull_eq`, `runSmall_eq`, `cRun_eq`, `idRunO_eq`, `oBO_eq`, `partAt_true`: the forms
that run are the terms of the theorems. `run_eq`: an equation for the call's truth value `runOf`.
Under. The two top theorems: nothing but the run that returns 0. `kit_zero`: such a run, and that
the verifier equals `partAt V sh g`; `run_eq`: the latter alone: proved at both sizes by
`runFull_eq`, `runSmall_eq`. `runAt_eq`: that R at O equals V at `gOf O`: proved by
`runEntryFull_eq`, `runEntrySmall_eq` (OnBytes/TypedOracleCompiler/Slice/EntryVerdictRun.lean). The others: none.
Does not show.
  1. A link to a random oracle: "for every O" is none, and at an O other than `Fmt.oracle` the code
     0 all but never comes.
  2. Any probability.
  3. Soundness: what the closed check's yes is worth is said, as far as it is, in other files.
  4. A bound joined to that yes.
  5. Support for the ID's clause from any checker, public string or bound.
  6. That 0 is ever returned: only a run can show that, and this file records none.
  7. More of the public files than `stdEntry` asks: 32 lines and a length; the rest enters by a
     digest.
  8. Anything of an executable, or of IO beyond the library's model of it: the theorems speak of the
     Lean term `entryMain`.
  9. What the heads of OnBytes/ShellOf/Laws.lean and ClaimLaws.lean list as not shown.
Notes in full, with every limit at length, stand at the end of this file.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.ShellOf.EntryProg
import OnBytes.ShellOf.ClaimLaws

set_option autoImplicit false

namespace TypedOracleCompiler.Slice
open Rom
open _root_.Iop (Dig)
open TypedOracleCompiler.Run.EntryPageSafe (gOf)
open OnBytes.Tie (EntryGround AskedE)
open OnBytes.Slice.Shapes (Cfg dgOf pubS₀)
open OnBytes.Slice.Shapes.FileSpec (own₀)

/-- The function on bytes for a run is the one that `gOf O` induces. -/
theorem oBO_eq (O : ByteArray → ByteArray) : oBO O = _root_.Run.oB (gOf O ()) := rfl

/-- The first digest for a run is the one that the check asks for, at `gOf O`. -/
theorem cRun_eq (cfg : Cfg) (O : ByteArray → ByteArray) :
    cRun cfg O = dgOf cfg (own₀ (pubS₀ cfg) (gOf O)) := by
  show cRun cfg O = _root_.Run.digToBytes (own₀ (pubS₀ cfg) (gOf O) (OnBytes.Slice.Shapes.scAt cfg))
  rw [own₀_scAt]
  rfl

/-- The ID for a run is the ID through `gOf O`. -/
theorem idRunO_eq (sh : OnBytes.Params.IndexShape) (cfg : Cfg) (t : OnBytes.Params.TableName)
    (O : ByteArray → ByteArray) : idRunO sh (cRun cfg O) t O = idOfG sh cfg t (gOf O) := by
  unfold idRunO idOfG
  rw [cRun_eq, oBO_eq]

end TypedOracleCompiler.Slice

namespace OnBytes.ShellOf.EntryProg

open OnBytes.ShellOf.Claimed
open OnBytes.Tie (AskedE EntryGround)
open TypedOracleCompiler.Slice (verifyEntryFull verifyEntrySmall runEntryFull runEntrySmall idOfG idRunO
  cRun)
open TypedOracleCompiler.Run.EntryPageSafe (gOf gOf_oracle)
open OnBytes.Slice.Shapes (Cfg)
open OnBytes.Shell (World Steps opsIO)
open Rom

/-! ## What runs is the term -/

/-- WHAT RUNS IS THE TERM: every O, every claim, every value: where the form for a run R is the
check V at `gOf O`. -/
theorem runAt_eq (R : Cfg → AskedE → (ByteArray → ByteArray) → Bool)
    (V : Cfg → AskedE → Fam (rom 256) → Bool) (sh : Params.IndexShape) (O : ByteArray → ByteArray)
    (hR : ∀ cfg a, R cfg a O = V cfg a (gOf O)) (cl : Claim) (a : AskedE) :
    runAt R sh O cl a = partAt V sh (gOf O) cl a := by
  unfold runAt partAt
  rw [hR, TypedOracleCompiler.Slice.idRunO_eq]

/-- At the full size: what runs is the closed term `verifyEntryFull` with the ID's clause. -/
theorem runFull_eq (O : ByteArray → ByteArray) (cl : Claim) (a : AskedE) :
    runAt runEntryFull Tie.recordGround.q.link.table O cl a =
      partAt verifyEntryFull Tie.recordGround.q.link.table (gOf O) cl a :=
  runAt_eq _ _ _ O (fun cfg a => TypedOracleCompiler.Slice.runEntryFull_eq cfg a O) cl a

/-- At the small example: what runs is the closed term `verifyEntrySmall` with the ID's clause. -/
theorem runSmall_eq (O : ByteArray → ByteArray) (cl : Claim) (a : AskedE) :
    runAt runEntrySmall Tie.smallRecordGround.q.link.table O cl a =
      partAt verifyEntrySmall Tie.smallRecordGround.q.link.table (gOf O) cl a :=
  runAt_eq _ _ _ O (fun cfg a => TypedOracleCompiler.Slice.runEntrySmall_eq cfg a O) cl a

/-! ## The exit code 0 -/

section
variable (V : Cfg → AskedE → Fam (rom 256) → Bool) (sh : Params.IndexShape)

/-- The verifier's yes, in its two clauses. -/
theorem partAt_true (g : Fam (rom 256)) (cl : Claim) (a : AskedE) :
    partAt V sh g cl a = true ↔
      V (cfgOf cl.cfg) a g = true ∧ idOfG sh (cfgOf cl.cfg) a.first g = cl.id := by
  unfold partAt
  rw [Bool.and_eq_true, beq_iff_eq]

/-- WHAT THE EXIT CODE 0 SAYS OF A CALL r AT A SIZE z, A CHECK V AND A SHAPE sh, for a parser p, the
words gv that a yes gives out, and a hash function g. Every letter under "there are" is pinned: the
four strings by r; id by `idAsked`; the five byte strings by the answers of the call's own five
reads; a by the parser. THE CLAIM IS NO LETTER: it is written out: the user's ID and the bytes read
in the user's folder. The bound on the public files' length and the tests on the parsed value are
not spelled: they follow by `Params.stdEntry_bytes` and by `verifyEntryFull_iff` |
`verifyEntrySmall_iff`. -/
def ZeroSays (z : Params.StdSize) (p : Parser) (gv : Claim → AskedE → List String)
    (g : Fam (rom 256)) (r : List String) (s s' : World) : Prop :=
  ∃ (id0 config key entry id : String) (pol lay kl kb eb : ByteArray) (a : AskedE),
    r = [id0, config, key, entry] ∧ Model.Verify.idAsked id0 = some id ∧
    Fits (wants config key entry) [pol, lay, kl, kb, eb] ∧
    Steps opsIO (reads (wants config key entry) [pol, lay, kl, kb, eb] ++
      said (gv ⟨id, ⟨pol, lay, kl⟩⟩ a ++ [wordE])) s s' ∧
    Params.stdEntry z ⟨pol, lay, kl⟩ = true ∧
    p ⟨id, ⟨pol, lay, kl⟩⟩ kb eb = .ok a ∧
    V ⟨pol, lay, kl⟩ a g = true ∧ idOfG sh ⟨pol, lay, kl⟩ a.first g = id

/-- For every size, parser and g, and every verifier that equals `partAt V sh g`: so a form for a
run stands in the program, and the theorem speaks of the term. -/
theorem kit_zero (z : Params.StdSize) (p : Parser) (g : Fam (rom 256))
    (verify : Claim → AskedE → Bool) (stage : Claim → AskedE → String)
    (gv : Claim → AskedE → List String)
    (hP : ∀ cl a, verify cl a = partAt V sh g cl a)
    {r : List String} {s s' : World}
    (h : Shell.Run (mainOf (bodyOf (kitAt z verify stage gv p)) r) s 0 s') :
    ZeroSays V sh z p gv g r s s' := by
  obtain ⟨id0, config, key, entry, id, pol, lay, kl, kb, eb, x, a, ha, hi, hf, hs, hst, hc, hv,
    -⟩ := main_zero h
  have hst' : stateAt z ⟨id, ⟨pol, lay, kl⟩⟩ = .ok x := hst
  unfold stateAt at hst'
  split at hst'
  · rename_i hstd
    obtain rfl := Except.ok.inj hst'
    have hv' : partAt V sh g ⟨id, ⟨pol, lay, kl⟩⟩ a = true := (hP _ _).symm.trans hv
    obtain ⟨h1, h2⟩ := (partAt_true V sh g _ a).1 hv'
    exact ⟨id0, config, key, entry, id, pol, lay, kl, kb, eb, a, ha, hi, hf, hs, hstd, hc, h1, h2⟩
  · cases hst'

/-- The call's truth value is `stdEntry`, then the verifier at the parser's value: an equation, for
all inputs. It speaks of `runOf`; what ties `runOf` to the program: `main_zero`, `main_ten`. -/
theorem run_eq (z : Params.StdSize) (p : Parser) (g : Fam (rom 256))
    (verify : Claim → AskedE → Bool) (stage : Claim → AskedE → String)
    (gv : Claim → AskedE → List String)
    (hP : ∀ cl a, verify cl a = partAt V sh g cl a) (cl : Claim) (key ent : ByteArray) :
    runOf (kitAt z verify stage gv p) cl key ent =
      (Params.stdEntry z cl.cfg &&
        match p cl key ent with
        | .ok a => partAt V sh g cl a
        | .error _ => false) := by
  by_cases h1 : Params.stdEntry z cl.cfg = true
  · have hs : (kitAt z verify stage gv p).state cl = .ok cl := by
      show stateAt z cl = _
      unfold stateAt
      rw [if_pos h1]
      rfl
    cases hp : p cl key ent with
    | error e =>
      rw [runOf_ok_error hs hp]
      simp only [h1, Bool.true_and]
    | ok a =>
      rw [runOf_ok_ok hs hp]
      simp only [h1, Bool.true_and]
      exact hP _ a
  · have hs : (kitAt z verify stage gv p).state cl = .error "std" := by
      show stateAt z cl = _
      unfold stateAt
      rw [if_neg h1]
      rfl
    rw [runOf_error hs, Bool.eq_false_iff.2 h1, Bool.false_and]

end

/-- THE PROGRAM WITH THE HASH FUNCTION AN ARGUMENT. In Lean's model of IO, for every O: if the
program at O returns the exit code 0, the first argument named a size, and at that size: `stdEntry`
holds of the three public files read in the user's folder; the closed check says yes at these three
files, at the value that the parser made of the bytes read, and at `gOf O`; and the commitment ID
that `gOf O` gives of these files and the value's first table is the user's. -/
theorem entryMainO_zero (O : ByteArray → ByteArray) {args : List String} {s s' : World}
    (h : Shell.Run (entryMainO O args) s 0 s') :
    (∃ r, args = "full" :: r ∧ ZeroSays verifyEntryFull Tie.recordGround.q.link.table Params.stdFull
      (parseE Tie.recordGround Params.stdFull) (givesO Tie.recordGround.q.link.table O) (gOf O)
      r s s') ∨
    (∃ r, args = "small" :: r ∧ ZeroSays verifyEntrySmall Tie.smallRecordGround.q.link.table
      Params.stdSmall (parseE Tie.smallRecordGround Params.stdSmall)
      (givesO Tie.smallRecordGround.q.link.table O) (gOf O) r s s') := by
  unfold entryMainO at h
  split at h
  · rename_i r
    exact Or.inl ⟨r, rfl, kit_zero _ _ _ _ _ _ _ _ (runFull_eq O) h⟩
  · rename_i r
    exact Or.inr ⟨r, rfl, kit_zero _ _ _ _ _ _ _ _ (runSmall_eq O) h⟩
  · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, ha, _⟩ := main_zero h
    cases ha

/-- THE PROGRAM AT THE FORMAT's ORACLE, MADE OF LEAN's BLAKE2b: the same, said at `Run.oBits`, the
realised oracle on bit strings. (An executable's entry may take other calls beside this term's: of
these no theorem speaks.) -/
theorem entryMain_zero {args : List String} {s s' : World}
    (h : Shell.Run (entryMain args) s 0 s') :
    (∃ r, args = "full" :: r ∧ ZeroSays verifyEntryFull Tie.recordGround.q.link.table Params.stdFull
      (parseE Tie.recordGround Params.stdFull)
      (givesO Tie.recordGround.q.link.table _root_.Fmt.oracle) _root_.Run.oBits r s s') ∨
    (∃ r, args = "small" :: r ∧ ZeroSays verifyEntrySmall Tie.smallRecordGround.q.link.table
      Params.stdSmall (parseE Tie.smallRecordGround Params.stdSmall)
      (givesO Tie.smallRecordGround.q.link.table _root_.Fmt.oracle) _root_.Run.oBits r s s') := by
  have h0 := entryMainO_zero _root_.Fmt.oracle h
  rw [gOf_oracle] at h0
  exact h0

end OnBytes.ShellOf.EntryProg

/-
Notes in full (other files' comments call these notes "the head of" this file).

OnBytes/ShellOf/EntryProgLaws.lean: the theorem on the program of OnBytes/ShellOf/EntryProg.lean.
For proofs only: no program imports it.

  `cRun_eq`, `idRunO_eq`, `runAt_eq`: WHAT RUNS IS THE TERM, at every O and on all arguments: where
    R is V at `gOf O`, `runAt R sh O` is `partAt V sh (gOf O)`. `runFull_eq`, `runSmall_eq`: so at
    `runEntryFull` | `runEntrySmall` and `verifyEntryFull` | `verifyEntrySmall`, by
    `runEntryFull_eq` | `runEntrySmall_eq` (OnBytes/TypedOracleCompiler/Slice/EntryVerdictRun.lean).
  `ZeroSays`: what the exit code 0 says of a call.
  `kit_zero`: for every size, parser and g, and every verifier that equals `partAt V sh g`.
  `run_eq`: the call's truth value `runOf` is `stdEntry`, then `partAt` at the parser's value: an
    equation.
  `entryMainO_zero`: the program with the hash an argument. `entryMain_zero`: the program at
    `Fmt.oracle`, said at `Run.oBits`.

What kind of theorem this is. A law of the shell, in Lean's model of IO: it carries the program's
exit code 0 to `verifyEntryFull … = true` | `verifyEntrySmall … = true` on the bytes read. It has
no hypothesis and no stand-in. "For every O" is no tie to a drawn oracle and buys nothing by itself:
at an O other than `Fmt.oracle` the wired parser cuts by another hash than O and the code 0 will all
but never come. No probability stands here.

What is not claimed. Nothing on soundness: what a yes of the closed check is worth is said, as far
as it is said, in OnBytes/TypedOracleCompiler/Slice/EntryVerdictRun.lean, EntryVerdictG.lean, EntryVerdictBound.lean
and the files that they name; no bound is joined to it here; the
ID's clause rests on no checker, public string or bound. That 0 is ever returned: a fact of a run:
this file records none. `stdEntry` asks the first 32 lines of the parameter file and a length, no
more; the rest of the three files enters through the hash's digest alone. Of an executable: these
theorems speak of the Lean term `entryMain`; a binary that is linked behind a shim, or whose entry
takes other calls beside, is not that term. All that the heads of OnBytes/ShellOf/Laws.lean and
ClaimLaws.lean disclaim.

-/
