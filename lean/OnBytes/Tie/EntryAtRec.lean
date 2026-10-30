-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/EntryAtRec.lean: the entry's check at a function O in the place of the
hash.

The check is `checkWithR` at the reader and the seeds at O. The seeds at O are
`Slice.recordSeedsW` at `Fmt.HO O`. The tie at the format's own oracle rests on a lemma of
OnBytes/Slice/SeedsAtOracle.lean: at names of tables with roots and a digest of 32 bytes the seeds
at `Fmt.oracle` are the program's `recordSeeds`.

-/
import OnBytes.Tie.EntryCheckRec
import OnBytes.Tie.EntryAt
import OnBytes.Slice.SeedsAtOracle

set_option autoImplicit false

namespace OnBytes.Tie

/-- The seeds of a table's record at O: the text of `recordSeeds` at the hash that O induces
(`Slice.recordSeedsW`). A function of O; it asks no oracle. -/
def seedsAt (O : ByteArray → ByteArray) : Seeds :=
  fun f name bits count => Slice.recordSeedsW (m := Id) (Fmt.HO O) f name bits count

/-- The check of an entry file at O: `checkWithR` with the reader and the
seeds at O. A function of O; it asks no oracle. The program does not call it. The reader is at O but
for one string, that of the digest of the description's parameter bytes, which the format's own
digest answers (`pinned`); the seeds are at O itself (`seedsAt_pinned`: they would be the same at
the pinned function). By its text it computes at most that one value with the format's hash; that is
no theorem. The 32 bytes in params that stand for the digest of the public files are taken as they
are; at answers ≠ 0 they enter the seeds' name too. It does not test the length of the first root.
-/
def checkAtR (O : ByteArray → ByteArray) (params : ByteArray) (first : Params.TableName)
    (file : ByteArray) : Option Params.TableName :=
  checkWithR (readerAt O) (seedsAt O) params first file

/-- Two functions for the seeds give the same seeds at the name of every table with a root of 32
bytes, under the digest and the shape of p. -/
def SeedsSameAt (sd sd' : Seeds) (p : Params.Link) : Prop :=
  ∀ root : ByteArray, root.size = 32 →
    sd p.given.plan.field (Fmt.tableName root p.given.cfg p.link.table.code.logN
        p.link.table.code.ell p.link.table.code.r p.link.table.v p.link.table.answers
        p.link.table.saltBytes) p.link.table.cubeBits p.link.table.answers =
      sd' p.given.plan.field (Fmt.tableName root p.given.cfg p.link.table.code.logN
        p.link.table.code.ell p.link.table.code.r p.link.table.v p.link.table.answers
        p.link.table.saltBytes) p.link.table.cubeBits p.link.table.answers

/-- `keyWith` hangs on sd through its value at the table's name alone. -/
theorem keyWith_same {sd sd' : Seeds} {p : Params.Link} (H : SeedsSameAt sd sd' p)
    (table : Params.TableName) (item : Nat) (h : table.root.size = 32) :
    keyWith sd p.given.plan.field p.given.cfg p.link.table table item =
      keyWith sd' p.given.plan.field p.given.cfg p.link.table table item := by
  unfold keyWith
  rw [H table.root h]

/-- So does `entryPlaceR`, at a first root of 32 bytes: the further table's root, which is read from
the file, has 32 bytes. -/
theorem entryPlaceR_same {sd sd' : Seeds} {p : Params.Link} (H : SeedsSameAt sd sd' p)
    (first : Params.TableName) (file : ByteArray) (h0 : first.root.size = 32) :
    entryPlaceR sd p first file = entryPlaceR sd' p first file := by
  unfold entryPlaceR
  dsimp only
  rw [keyWith_same H first 0 h0]
  cases Proof.readHead p.given.plan.field .entry file with
  | error e => rfl
  | ok i =>
    dsimp only
    split
    · rfl
    · cases ht : readTable p.given.plan.field (p.link.table.rows * p.link.table.answers) file i with
      | error e => rfl
      | ok x =>
        obtain ⟨further, j⟩ := x
        dsimp only
        rw [keyWith_same H further 1 (readTable_root _ _ _ _ _ _ ht)]

/-- At a digest of 32 bytes the seeds at the format's own oracle are the program's, at the name of
every table with a root of 32 bytes (`Slice.recordSeedsW_oracle_table`). -/
theorem seedsSame_oracle (p : Params.Link) (hc : p.given.cfg.size = 32) :
    SeedsSameAt (seedsAt Fmt.oracle) recordSeeds p :=
  fun root hr => Slice.recordSeedsW_oracle_table _ root _ hr hc _ _ _ _ _ _ _ _

/-- **The seeds' calls miss the one string at which the reader's function is pinned**: the seeds ask
calls number 160 and 162; the pinned string is that of a call number 169. So the reader at O
(`readerAt`: at `pinned O params`) and the seeds at O can be taken at ONE function. -/
theorem seedsAt_pinned (O : ByteArray → ByteArray) (prm : ByteArray) :
    seedsAt (pinned O prm) = seedsAt O := by
  funext f name bits count
  exact Slice.recordSeedsW_congr (Fmt.HO (pinned O prm)) (Fmt.HO O) f name bits count
    (HO_pinned O prm 160 0 _ _ _ (by decide)) (fun j => HO_pinned O prm 162 _ 1 _ _ (by decide))

section
variable {q : Params.Link} {first : Params.TableName} {file : ByteArray}

/-- **Reading at the format's own oracle is the program's reading; BOTH
WAYS.** Under a digest and a first root of 32 bytes, and `smallFX` of every description that
`entryPlaceR` gives at the program's own seeds and that is in order. -/
theorem readWithR_oracle (hc : q.given.cfg.size = 32) (h0 : first.root.size = 32)
    (hsm : ∀ P, entryPlaceR recordSeeds q first file = some P → P.spec.ok = true →
      smallFX P.spec file = true) (r : Entry.EntryRead) :
    readWithR (readerAt Fmt.oracle) (seedsAt Fmt.oracle) q first file = some r ↔
      Entry.read q first file = .ok r := by
  have H := seedsSame_oracle q hc
  have hE : Entry.read q first file = .ok r ↔
      readWithR readIn recordSeeds q first file = some r := by
    rw [readWithR_readIn]
    cases Entry.read q first file with
    | error e => exact ⟨fun h => (by cases h), fun h => (by cases h)⟩
    | ok t => exact ⟨fun h => (by cases h; rfl), fun h => (by cases h; rfl)⟩
  rw [hE, readWithR_iff, readWithR_iff, entryPlaceR_same H first file h0]
  constructor
  · rintro ⟨P, hP, hrun, rest⟩
    refine ⟨P, hP, ?_, rest⟩
    unfold InSession.run at hrun ⊢
    have hok : P.spec.ok = true := by
      cases hx : readerAt Fmt.oracle P.spec file P.byte Session.start with
      | none =>
        rw [hx] at hrun
        cases hrun
      | some y =>
        exact readX_ok _ _ _ file P.byte _ (readInAt_read _ _ _ _ _ _ _ hx).1
    rw [← readerAt_oracle P.spec file P.byte Session.start (hsm P hP hok)]
    exact hrun
  · rintro ⟨P, hP, hrun, rest⟩
    refine ⟨P, hP, ?_, rest⟩
    unfold InSession.run at hrun ⊢
    have hok : P.spec.ok = true := by
      cases hx : readIn P.spec file P.byte Session.start with
      | none =>
        rw [hx] at hrun
        cases hrun
      | some y =>
        exact readX_ok Fmt.formatHash _ _ file P.byte _ (readIn_read _ file P.byte _ y.2 y.1 hx).1
    rw [readerAt_oracle P.spec file P.byte Session.start (hsm P hP hok)]
    exact hrun

end

/-- **The check at the format's own oracle is the program's check; BOTH
WAYS.** Under parameter bytes that are read as q, a digest and a first root of 32 bytes, and
`smallFX` of every description that `entryPlaceR` gives at the program's own seeds and that is in
order (`Fmt.SpecX.ok`). -/
theorem entry_check_atR (params : ByteArray) (q : Params.Link) (first further : Params.TableName)
    (file : ByteArray) (hq : Params.Link.read params = some q) (hc : q.given.cfg.size = 32)
    (h0 : first.root.size = 32)
    (hsm : ∀ P, entryPlaceR recordSeeds q first file = some P → P.spec.ok = true →
      smallFX P.spec file = true) :
    checkAtR Fmt.oracle params first file = some further ↔
      Entry.check params first file = .ok further := by
  unfold checkAtR
  rw [checkWithR_iff, entry_check_iff]
  constructor
  · rintro ⟨q', r, hq', hr, rest⟩
    obtain rfl : q' = q := Option.some.inj (hq'.symm.trans hq)
    exact ⟨q', r, hq', (readWithR_oracle hc h0 hsm r).1 hr, rest⟩
  · rintro ⟨q', r, hq', hr, rest⟩
    obtain rfl : q' = q := Option.some.inj (hq'.symm.trans hq)
    exact ⟨q', r, hq', (readWithR_oracle hc h0 hsm r).2 hr, rest⟩

end OnBytes.Tie

#print axioms OnBytes.Tie.entryPlaceR_same
#print axioms OnBytes.Tie.seedsSame_oracle
#print axioms OnBytes.Tie.seedsAt_pinned
#print axioms OnBytes.Tie.readWithR_oracle
#print axioms OnBytes.Tie.entry_check_atR
