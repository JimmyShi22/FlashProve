-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/ShellOf/EntryParsedLaws.lean: the theorems on the test program of EntryParsed.lean. Proofs
only: no program imports this file.

States. `entryParsedMainO_zero`, `entryParsedMain_zero`, `entryParsedCheck_returns`: what exit code
0 says (`ZeroSaysP`): the same statement as for `entryMain`, with the two parsed files' bytes in the
place of the key file's and the entry file's. `entryParsedCheck_main`: if `entryParsedCheck`
returns, `entryParsedMain` ended in 0. `kitU_zero`: the general form. `cRun_oracle`,
`seedsUnder_oracle`: at `Fmt.oracle` the reader's digest is the format's own, and its seeds are the
library's `recordSeeds`.
Under. The first three: one hypothesis, a run of the program that ends in 0 (the third: that
returns). `entryParsedCheck_main`: that it returns. `kitU_zero`: such a run, and that the verifier
equals `partAt V sh g`. `cRun_oracle`: a bound on the three public files' lengths.
`seedsUnder_oracle`: the table's root and the digest have 32 bytes each.
Does not show.
  1. Soundness: these are theorems on a test that serves the runs of lean/Ask/.
  2. What EntryProgLaws.lean lists as not shown: this is the same kind of theorem. (Its clause "the
     code 0 all but never comes" speaks of `parseE`; here the parser hashes by O too: see 3.)
  3. A link to a random oracle: "for every O" is none; no theorem and no run shows that any file
     passes at an O other than `Fmt.oracle`.
  4. That files made under the format's hash are refused at another O.
  5. Any property of `parseP`: in three statements it stands only as the function that made the
     value; that `cRun` and `seedsUnder (seedsAt (oBO O))` are its two hashed terms is read off its
     text.
  6. Anything of the original key file and leaf file.
Notes in full, with every limit at length, stand at the end of this file.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.ShellOf.EntryParsed
import OnBytes.ShellOf.EntryProgLaws
import OnBytes.Tie.LinkPlain

set_option autoImplicit false

namespace OnBytes.ShellOf.EntryParsed

open OnBytes.ShellOf.Claimed
open OnBytes.ShellOf.EntryProg
open OnBytes.Tie (AskedE seedsUnder seedsAt nameUnder seedsAt_oBits)
open TypedOracleCompiler.Slice (verifyEntryFull verifyEntrySmall cRun oBO cRun_eq oBO_eq)
open TypedOracleCompiler.Run.EntryPageSafe (gOf gOf_oracle)
open OnBytes.Slice.Shapes (Cfg)
open OnBytes.Shell (World Steps opsIO run_bind run_pure)
open Rom

/-! ## The reader's two hashed things at the format's oracle -/

/-- At `Fmt.oracle` the digest that the reader makes is the format's own digest of the three public
files. Asked: one bound on their lengths. -/
theorem cRun_oracle (cfg : Cfg)
    (hb : (_root_.Fmt.configBytes [cfg.pol, cfg.lay, cfg.KL]).size ≤ 2 ^ 32 - 144) :
    cRun cfg _root_.Fmt.oracle = Params.configurationDigest [cfg.pol, cfg.lay, cfg.KL] := by
  rw [cRun_eq, gOf_oracle]
  exact OnBytes.Slice.Shapes.dgOf_own₀ cfg hb

/-- At `Fmt.oracle` the seeds that the reader draws for a table are the port's own `recordSeeds`.
Asked: the table's root and the parameters' digest have 32 bytes. -/
theorem seedsUnder_oracle (q : Params.Link) (t : Params.TableName) (hr : t.root.size = 32)
    (hc : q.given.cfg.size = 32) :
    seedsUnder (seedsAt (oBO _root_.Fmt.oracle)) q t = seedsUnder recordSeeds q t := by
  -- by named equations, not by unfolding: see `Tie.seedsUnder_eq`
  rw [oBO_eq, gOf_oracle, seedsAt_oBits, OnBytes.Tie.seedsUnder_eq, OnBytes.Tie.seedsUnder_eq,
    nameUnder]
  exact OnBytes.Slice.recordSeedsW_oracle_table _ _ _ hr hc _ _ _ _ _ _ _ _

/-! ## The exit code 0 -/

/-- WHAT THE EXIT CODE 0 SAYS: `ZeroSays` with `wordP` for the last line written. Every letter under
"there are" is pinned as there: the four strings by r; id by `idAsked`; the five byte strings by the
answers of the call's own five reads; a by the parser. -/
def ZeroSaysP (V : Cfg → AskedE → Fam (rom 256) → Bool) (sh : Params.IndexShape)
    (z : Params.StdSize) (p : Parser) (gv : Claim → AskedE → List String)
    (g : Fam (rom 256)) (r : List String) (s s' : World) : Prop :=
  ∃ (id0 config key entry id : String) (pol lay kl kb eb : ByteArray) (a : AskedE),
    r = [id0, config, key, entry] ∧ Model.Verify.idAsked id0 = some id ∧
    Fits (wants config key entry) [pol, lay, kl, kb, eb] ∧
    Steps opsIO (reads (wants config key entry) [pol, lay, kl, kb, eb] ++
      said (gv ⟨id, ⟨pol, lay, kl⟩⟩ a ++ [wordP])) s s' ∧
    Params.stdEntry z ⟨pol, lay, kl⟩ = true ∧
    p ⟨id, ⟨pol, lay, kl⟩⟩ kb eb = .ok a ∧
    V ⟨pol, lay, kl⟩ a g = true ∧ TypedOracleCompiler.Slice.idOfG sh ⟨pol, lay, kl⟩ a.first g = id

/-- `kit_zero` for the kit with the other usage line and the other last line. -/
theorem kitU_zero (V : Cfg → AskedE → Fam (rom 256) → Bool) (sh : Params.IndexShape)
    (z : Params.StdSize) (p : Parser) (g : Fam (rom 256))
    (verify : Claim → AskedE → Bool) (stage : Claim → AskedE → String)
    (gv : Claim → AskedE → List String)
    (hP : ∀ cl a, verify cl a = partAt V sh g cl a)
    {r : List String} {s s' : World}
    (h : Shell.Run (mainOf (bodyOf (kitU z verify stage gv p)) r) s 0 s') :
    ZeroSaysP V sh z p gv g r s s' := by
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

/-- THE PROGRAM WITH THE HASH FUNCTION AN ARGUMENT: every O. -/
theorem entryParsedMainO_zero (O : ByteArray → ByteArray) {args : List String} {s s' : World}
    (h : Shell.Run (entryParsedMainO O args) s 0 s') :
    (∃ r, args = "full" :: r ∧ ZeroSaysP verifyEntryFull Tie.recordGround.q.link.table
      Params.stdFull (parseP Tie.recordGround O)
      (givesO Tie.recordGround.q.link.table O) (gOf O) r s s') ∨
    (∃ r, args = "small" :: r ∧ ZeroSaysP verifyEntrySmall Tie.smallRecordGround.q.link.table
      Params.stdSmall (parseP Tie.smallRecordGround O)
      (givesO Tie.smallRecordGround.q.link.table O) (gOf O) r s s') := by
  unfold entryParsedMainO at h
  split at h
  · rename_i r
    exact Or.inl ⟨r, rfl, kitU_zero _ _ _ _ _ _ _ _ (runFull_eq O) h⟩
  · rename_i r
    exact Or.inr ⟨r, rfl, kitU_zero _ _ _ _ _ _ _ _ (runSmall_eq O) h⟩
  · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, ha, _⟩ := main_zero h
    cases ha

/-- THE PROGRAM AT THE FORMAT's ORACLE, MADE OF LEAN's BLAKE2b: said at `Run.oBits`. -/
theorem entryParsedMain_zero {args : List String} {s s' : World}
    (h : Shell.Run (entryParsedMain args) s 0 s') :
    (∃ r, args = "full" :: r ∧ ZeroSaysP verifyEntryFull Tie.recordGround.q.link.table
      Params.stdFull (parseP Tie.recordGround _root_.Fmt.oracle)
      (givesO Tie.recordGround.q.link.table _root_.Fmt.oracle) _root_.Run.oBits r s s') ∨
    (∃ r, args = "small" :: r ∧ ZeroSaysP verifyEntrySmall Tie.smallRecordGround.q.link.table
      Params.stdSmall (parseP Tie.smallRecordGround _root_.Fmt.oracle)
      (givesO Tie.smallRecordGround.q.link.table _root_.Fmt.oracle) _root_.Run.oBits r s s') := by
  have h0 := entryParsedMainO_zero _root_.Fmt.oracle h
  rw [gOf_oracle] at h0
  exact h0

/-- If `entryParsedCheck` returns, the program returned the exit code 0, between the same states. -/
theorem entryParsedCheck_main {args : List String} {s s' : World}
    (h : Shell.Run (entryParsedCheck args) s () s') :
    Shell.Run (entryParsedMain args) s 0 s' := by
  obtain ⟨c, s1, h1, h2⟩ := run_bind.1 h
  by_cases hc : c = 0
  · subst hc
    rw [if_pos rfl] at h2
    obtain ⟨-, rfl⟩ := run_pure.1 h2
    exact h1
  · rw [if_neg hc] at h2
    have h3 : (EST.Out.error (IO.userError ("NOT A YES: the program's exit code is " ++ toString c))
        s1 : EST.Out IO.Error IO.RealWorld Unit) = EST.Out.ok () s' := h2
    cases h3

/-- IF `entryParsedCheck` RETURNS WITHOUT AN EXCEPTION: all that the exit code 0 says. -/
theorem entryParsedCheck_returns {args : List String} {s s' : World}
    (h : Shell.Run (entryParsedCheck args) s () s') :
    (∃ r, args = "full" :: r ∧ ZeroSaysP verifyEntryFull Tie.recordGround.q.link.table
      Params.stdFull (parseP Tie.recordGround _root_.Fmt.oracle)
      (givesO Tie.recordGround.q.link.table _root_.Fmt.oracle) _root_.Run.oBits r s s') ∨
    (∃ r, args = "small" :: r ∧ ZeroSaysP verifyEntrySmall Tie.smallRecordGround.q.link.table
      Params.stdSmall (parseP Tie.smallRecordGround _root_.Fmt.oracle)
      (givesO Tie.smallRecordGround.q.link.table _root_.Fmt.oracle) _root_.Run.oBits r s s') :=
  entryParsedMain_zero (entryParsedCheck_main h)

end OnBytes.ShellOf.EntryParsed

/-
Notes in full (other files' comments call these notes "the head of" this file).

OnBytes/ShellOf/EntryParsedLaws.lean: the theorem on the program of
OnBytes/ShellOf/EntryParsed.lean. For proofs only: no program imports it.

No soundness: a test. This module states laws on what the runs of lean/Ask/ call; it states nothing
on soundness.

  `cRun_oracle`, `seedsUnder_oracle`: at `Fmt.oracle` the digest and the seeds that the reader makes
    through its hash function are the format's own digest and the port's `recordSeeds`. Asked: a
    bound on the three public files' lengths; 32 bytes of the table's root and of the digest. Beside
    these two the concrete hash is named in these four files only where the program is taken at it:
    `entryParsedMain` and its two laws.
  `ZeroSaysP`: `ZeroSays` (OnBytes/ShellOf/EntryProgLaws.lean) to the letter, but for the last line
    that was written: `wordP` where that has `wordE`.
  `kitU_zero`: `kit_zero`'s proof for the kit with the other usage line and the other last line: for
    every size, parser and g, and every verifier that equals `partAt V sh g`.
  `entryParsedMainO_zero`, `entryParsedMain_zero`, `entryParsedCheck_returns`: what the exit code 0
    says: `ZeroSaysP` at the parser `parseP`: the same statement as for `entryMain`, with the two
    parsed files' bytes where that has the key file's and the entry file's.

What kind of theorem this is, and what is not claimed: as the head of EntryProgLaws.lean says. But
for one sentence there: here the wired parser is at O too. "For every O" is still no tie to a drawn
oracle: no law and no run says that any file gets the code 0 at an O other than `Fmt.oracle`; that
files made under the format's hash are refused there is no law either. NO LAW HERE SPEAKS OF
`parseP`: the two laws at the top speak of two terms that stand in its text; in the others `parseP`
stands as the function that made the value a, and no property of it is used or shown. Nothing speaks
of the original key file and leaf file.

-/
