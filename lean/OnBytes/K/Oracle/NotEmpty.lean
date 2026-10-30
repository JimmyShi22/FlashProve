-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/K/Oracle/NotEmpty.lean: a guard against emptiness for the entry file's checker that reads
through the oracle, as a conditional: if four tests on five byte strings and an ID come out as
named, the checker returns a typed value on these files, at the one oracle that is made from the
format's hash.

Why. `EntryArmO` (OnBytes/K/Oracle/ArmO.lean) has two statements on one checker. If that checker
never returned a value, its `sound` would bound the probability of an empty event. `zero` gives a
value from exit code 0 of the program, and no call is shown to end with exit code 0. This file needs
no call of the program: no request, no reply, no proof file, no exit code. It takes the three public
files, a key file, an entry file and an ID.

Main names:
  `asked_of_conv`: where the strict converter `convE` (OnBytes/TypedOracleCompiler/Slice/EntryConv.lean) returns a
    value on an entry file, the asking half's value (`askedAt`, OnBytes/Tie/EntryAsked.lean) is that
    value. It is shown at one oracle alone: the one made from the format's hash. It is `asked_conv`
    (OnBytes/K/Oracle/AskedAt.lean) without the program's yes.
  `returnsO_of_prep`: general in the ground: from the premises below, the checker returns a value o
    on these files; o's roots and answers are those of the converter's two tables, and the ID is
    o's; of o's seeds nothing is said beside the ID.
  `small_returnsO_of_prep`, `full_returnsO_of_prep`: that at the two grounds, in the letters of
    `entry_armO_small` and `entry_armO_full` (OnBytes/K/Oracle/ArmOAt.lean): the checkers of which
    these two speak.
  `lines_of_prep`, `small_saysLines_of_prep`, `full_saysLines_of_prep`: what the first premise says
    of the parameter file.

The premises of `returnsO_of_prep`. Four are tests on the bytes and the ID. (1) The bytes' side
`prepE` (OnBytes/TypedOracleCompiler/Slice/EntryRunBytes.lean), at the strict converter, returns a value v. (2) The
trusted function `verifyE` (OnBytes/TypedOracleCompiler/Slice/EntryVerdict.lean) says yes on v at the ID; the ID is
a letter, tied by that yes alone, and the conclusion's last clause is that tie said again. (3) The
root that `keyAt` reads off the key file has 32 bytes. (4) The entry file's size and 16 more are at
most 2 ^ 32 - 144, the bound in the domain of the format's hash. A fifth premise is no test: hok,
that at every digest of 32 bytes the description's base is within the limits `PQ.ok`; it runs over
all strings of 32 bytes. The ground G brings its own laws as fields. In the general statement
nothing is closed until G and zS are fixed. The two corollaries fix them: there hok is a theorem
(`small_record_ok`, `record_ok`), the ground's laws are proved in its definition, and the four tests
are closed once the bytes and the ID are given.

The setting's lines. `G.SaysLines`, under which `EntryArmO.zero` speaks, is no premise here. In its
place stands `prepE`'s first test, `Params.stdEntry zS` (OnBytes/Params/Std.lean): the reader of a
parameter file returns zS's lines on the parameter file (what its first 32 lines say), and what is
hashed for the digest of the three public files has at most 2 ^ 32 - 144 bytes. At the two grounds
zS's lines are the ground's, so the first clause is `SaysLines` there. For another ground nothing
here ties zS to G.

What is not claimed. That the checker returns a value on any files is no theorem here: every
statement is a conditional. What a conclusion says is "returns", at one fixed oracle. It says
nothing under a drawn oracle, where the event of `sound` lives: of that event these statements say
only, together with a run as below, that the checker is not one that never returns. It is less than
`EntryYesBy` (OnBytes/TypedOracleCompiler/Slice/EntryOne.lean), which also asks two keys' roots and the records'
reading.

The run. `prepE` and `verifyE` have code. One run of Lean's evaluator evaluated the four tests at
the small ground, on the small example's five files (made-up weights) and that example's own ID, at
the state of Lean's files at which this head was written: (1) a value; (2) true, in some 170
seconds; (3) 32; (4) true, the entry file having 537,440 bytes. Once; one set of files; no damaged
file. `verifyE`'s commitment ID has since taken the record's seeds into its string: this head
reports no run of the four tests behind that change. No run at the full size is on record, and no
file is named of which `full_returnsO_of_prep`'s
premises are said to hold. That is a run and no theorem: it leaves no declaration, and nothing that
is checked of declarations is checked of it. What is left to trust: that such a run evaluates the
terms as the kernel would; that the bytes fed to it are the named files'; and whatever compiled code
puts in a term's place beneath (by an attribute on a definition), which was not looked for. The
kernel itself was not brought to evaluate the tests: measured, it reduces one call of the format's
hash on 64 bytes in 0.58 seconds and on 1,024 bytes in 35 seconds, and the reader alone asks up to
26,222 strings; by another measurement the core library's `List.merge`, through which the program's
decision goes, does not reduce in the kernel.

All that the head of OnBytes/K/Oracle/ArmO.lean does not claim. Nothing on soundness; no
probability. Nothing on hiding.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.K.Oracle.ArmO

set_option autoImplicit false

namespace OnBytes.K.Oracle
open Rom Prob _root_.Compile OnBytes.Tie TypedOracleCompiler.Slice OnBytes.K.Left
open OnBytes.Slice.Shapes (Cfg dgOf pubS₀ pubS₁)
open OnBytes.Slice.Shapes.FileSpec (own₀ own₁)
open scoped ENNReal

/-- Where the strict converter returns a value on an entry file, the asking half returns that value
at the oracle made from the format's hash. Shown at that one oracle alone. c: any digest of 32
bytes. Asked: the first table's root has 32 bytes; the entry file is within the hash's bound. -/
theorem asked_of_conv (G : EntryGround) {c : ByteArray} (hc32 : c.size = 32)
    {table : Params.TableName} {ent : ByteArray} {a : AskedE} (h0 : table.root.size = 32)
    (hb : ent.size + 16 ≤ 2 ^ 32 - 144)
    (hcv : convE (linkAtCfg G.q c) table ent = some a) :
    askedAt (_root_.Run.oB (_root_.Run.oBits ())) (linkAtCfg G.q c) table ent = some a := by
  -- by named equations, not by unfolding: see `Tie.seedsUnder_eq`
  rw [convE] at hcv
  cases hr : Entry.read (linkAtCfg G.q c) table ent with
  | error e =>
    rw [hr] at hcv
    cases hcv
  | ok r =>
    rw [hr] at hcv
    obtain ⟨l0, a0, hcv⟩ := Option.bind_eq_some_iff.1 hcv
    obtain ⟨l1, a1, rfl⟩ := Option.map_eq_some_iff.1 hcv
    obtain ⟨-, -, -, -, -, h32⟩ := entry_read_spec _ table ent r hr
    have hsm : ∀ P, entryPlaceR recordSeeds (linkAtCfg G.q c) table ent = some P →
        P.spec.ok = true → smallFX P.spec ent = true := by
      intro P hP hokP
      obtain ⟨_, ⟨rs2, h2, eP⟩, _⟩ := entryPlaceR_spec_any hP
      obtain rfl : G.rs = rs2 := Option.some.inj ((G.rounds_at c).symm.trans h2)
      rw [eP] at hokP ⊢
      exact smallFX_of_withinX _ hokP (G.within_at c hc32 _ (specX_base _ hokP)) ent hb
    have key := (readWithR_reader (q := linkAtCfg G.q c) (first := table) (file := ent)
      (readInAt Fmt.oracle) (fun S i hs => readInAt_oracle S ent i Session.start hs)
      (fun S i y hx => readX_ok _ _ _ ent i _ (readInAt_read _ _ _ _ _ y.2 y.1 hx).1) hc32
      h0 hsm r).2 hr
    have H := seedsSame_oracle (linkAtCfg G.q c) hc32
    have b0 : seedsUnder (seedsAt Fmt.oracle) (linkAtCfg G.q c) table = some l0 :=
      (seedsUnder_eq _ _ _).trans
        ((H table.root h0).trans ((seedsUnder_eq _ _ _).symm.trans a0))
    have b1 : seedsUnder (seedsAt Fmt.oracle) (linkAtCfg G.q c) r.further = some l1 :=
      (seedsUnder_eq _ _ _).trans
        ((H r.further.root h32).trans ((seedsUnder_eq _ _ _).symm.trans a1))
    rw [askedAt_oBits, askedAt, key, Option.bind_some, b0, Option.bind_some, b1, Option.map_some]

section
variable (G : EntryGround)
  (hok : ∀ c : ByteArray, c.size = 32 → TypedOracleCompiler.Run.PQ.ok (entryXD G c).base = true)

/-- What the bytes' side's value says of the parameter file: its reader returns zS's lines on it. -/
theorem lines_of_prep (zS : Params.StdSize) (pol lay kl key ent : ByteArray) (v : PrepE)
    (hp : prepE G zS false pol lay kl key ent = .ok v) :
    (Params.readLines pol).toOption.map (·.1) = some zS.lines :=
  Params.stdEntry_lines (prepE_ok G zS _ _ _ _ _ v hp).1

/-- From four tests on five byte strings and an ID to a value of the checker that reads through the
oracle, general in the ground; hok, a premise of this section, is a fifth and no test. If the bytes'
side, at the strict converter, returns v on the three public files, the key file and the entry file,
and the trusted function says yes on v at the ID id, then the checker returns a typed value o on
these files, under the oracle made from the format's hash; o's roots and answers are those of v's
two tables, and id is the commitment ID of o's first root, first seeds and first answers. Asked
beside: the root that is read off the key file has 32 bytes; the entry file is within the hash's
bound. No call of the program stands in the statement. -/
theorem returnsO_of_prep (zS : Params.StdSize) (eM Bk : ℕ) (cfg : Cfg)
    (d : OnBytes.Slice.Shapes.Files) (id : String) (v : PrepE)
    (hp : prepE G zS false cfg.pol cfg.lay cfg.KL d.key d.ent = .ok v)
    (hv : verifyE G hok ⟨id, v.c, v.hc⟩ v.a = true)
    (h0 : (keyAt G.q.link.table v.c d.key).2.2.root.size = 32)
    (hb : d.ent.size + 16 ≤ 2 ^ 32 - 144) :
    ∃ o : (homeOf G hok eM).OutB cfg,
      ReturnsO (readerOf G hok eM cfg) Bk d o ∧
      o.1 = [_root_.Run.bytesToDig v.a.first.root, _root_.Run.bytesToDig v.a.further.root] ∧
      o.2.1.1 = (v.a.first.answers.map E.triple, v.a.further.answers.map E.triple) ∧
      id = stmtId G.q.link.table v.c (o.1.getD 0 default) o.2.1.2.1 o.2.1.1.1 := by
  obtain ⟨hstd, hc, hcv⟩ := prepE_ok G zS _ _ _ _ _ v hp
  obtain ⟨c, h32, q, a⟩ := v
  dsimp only at hc hcv hv h0 ⊢
  subst hc
  have hbytes := Params.stdEntry_bytes hstd
  have hpd := (homeOf G hok eM).pd_own₁ cfg hbytes
    (params_le_of_ok _ (hok _ (Params.configurationDigest_size _))) (homeOf_prm G hok eM _)
  exact returnsO_of_verifyE G hok eM Bk cfg id d a _ h32
    (OnBytes.Slice.Shapes.dgOf_own₀ cfg hbytes).symm hpd hcv (asked_of_conv G h32 h0 hb hcv) hv

end

/-- At the small example the bytes' side's value gives the ground's own clause on the parameter
file. -/
theorem small_saysLines_of_prep (pol lay kl key ent : ByteArray) (v : PrepE)
    (hp : prepE smallRecordGround Params.stdSmall false pol lay kl key ent = .ok v) :
    smallRecordGround.SaysLines pol :=
  lines_of_prep smallRecordGround Params.stdSmall pol lay kl key ent v hp

/-- The same at the full size. -/
theorem full_saysLines_of_prep (pol lay kl key ent : ByteArray) (v : PrepE)
    (hp : prepE recordGround Params.stdFull false pol lay kl key ent = .ok v) :
    recordGround.SaysLines pol :=
  lines_of_prep recordGround Params.stdFull pol lay kl key ent v hp

/-- At the small example, in the letters of `entry_armO_small` (OnBytes/K/Oracle/ArmOAt.lean): if
the four tests come out as named on five byte strings and an ID, the checker of which that theorem
speaks returns a typed value on these files. At the one oracle made from the format's hash; nothing
under a drawn oracle. A conditional: that the tests come out so on any bytes is no theorem. -/
theorem small_returnsO_of_prep (cfg : Cfg) (d : OnBytes.Slice.Shapes.Files) (id : String)
    (v : PrepE)
    (hp : prepE smallRecordGround Params.stdSmall false cfg.pol cfg.lay cfg.KL d.key d.ent = .ok v)
    (hv : verifyE smallRecordGround small_record_ok ⟨id, v.c, v.hc⟩ v.a = true)
    (h0 : (keyAt smallRecordGround.q.link.table v.c d.key).2.2.root.size = 32)
    (hb : d.ent.size + 16 ≤ 2 ^ 32 - 144) :
    ∃ o : (homeOf smallRecordGround small_record_ok Params.smallRecordRadius).OutB cfg,
      ReturnsO (readerOf smallRecordGround small_record_ok Params.smallRecordRadius cfg) 101 d o ∧
      o.1 = [_root_.Run.bytesToDig v.a.first.root, _root_.Run.bytesToDig v.a.further.root] ∧
      o.2.1.1 = (v.a.first.answers.map E.triple, v.a.further.answers.map E.triple) ∧
      id = stmtId smallRecordGround.q.link.table v.c (o.1.getD 0 default) o.2.1.2.1 o.2.1.1.1 :=
  returnsO_of_prep smallRecordGround small_record_ok Params.stdSmall Params.smallRecordRadius 101
    cfg d id v hp hv h0 hb

/-- At the full size, in the letters of `entry_armO_full`. The same conditional; no run of its
premises is on record. -/
theorem full_returnsO_of_prep (cfg : Cfg) (d : OnBytes.Slice.Shapes.Files) (id : String)
    (v : PrepE)
    (hp : prepE recordGround Params.stdFull false cfg.pol cfg.lay cfg.KL d.key d.ent = .ok v)
    (hv : verifyE recordGround record_ok ⟨id, v.c, v.hc⟩ v.a = true)
    (h0 : (keyAt recordGround.q.link.table v.c d.key).2.2.root.size = 32)
    (hb : d.ent.size + 16 ≤ 2 ^ 32 - 144) :
    ∃ o : (homeOf recordGround record_ok Params.recordRadius).OutB cfg,
      ReturnsO (readerOf recordGround record_ok Params.recordRadius cfg) 142 d o ∧
      o.1 = [_root_.Run.bytesToDig v.a.first.root, _root_.Run.bytesToDig v.a.further.root] ∧
      o.2.1.1 = (v.a.first.answers.map E.triple, v.a.further.answers.map E.triple) ∧
      id = stmtId recordGround.q.link.table v.c (o.1.getD 0 default) o.2.1.2.1 o.2.1.1.1 :=
  returnsO_of_prep recordGround record_ok Params.stdFull Params.recordRadius 142
    cfg d id v hp hv h0 hb

end OnBytes.K.Oracle
