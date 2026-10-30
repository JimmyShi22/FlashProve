-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/LinkPlain.lean: what the links of OnBytes/TypedOracleCompiler/Slice/Shapes.lean can take from main, at
the plain functions and at the oracle on bit strings that is made from the format's hash
(`Run.oBits`).

(1) Hash, seeds, check and ID are the same at `Run.oB (Run.oBits ())` as at `Fmt.oracle`.
(2) Total plain readers of the key file (`keyAt`) and of the entry file (`keyCAt`), tied to
    `Key.check`'s table and to `Entry.check`'s: for Shapes' `Θ.key` and `Θ.keyC`.

The tables' shape is an argument of `keyAt` and `keyCAt`: so `zero_keyAt` and `zero_keyCAt` hold
under `ZeroFacts` alone, at the shape in p. The ID in (1) is that of OnBytes/Tie/IdKey.lean: the
string without the record's seeds.

Not claimed. No `Three` is given: no Link• is shown. Nothing on soundness; no probability; the Lean
port.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.Tie.ZeroRecordLines
import OnBytes.Tie.ZeroId
import OnBytes.Slice.OneWorldEntry

set_option autoImplicit false

namespace OnBytes.Tie

open OnBytes.Shell (World)
open OnBytes.Model

/-! ## 1. At the oracle on bit strings that is made from the format's hash -/

/-- The hash that `Run.oB (Run.oBits ())` induces is the hash that `Fmt.oracle` induces: the two
functions agree at the strings of the hash's calls (`Run.ph_oStr`). `HO_pinned_oBits` without the
pin. -/
theorem HO_oBits : Fmt.HO (Run.oB (Run.oBits ())) = Fmt.HO Fmt.oracle := by
  funext n t i st bs
  unfold Fmt.HO
  rw [Run.ph_oStr 0 n t i st bs (Or.inl rfl), Run.ph_oStr 1 n t i st bs (Or.inr rfl)]

/-- So the seeds of a record are the same at both. -/
theorem seedsAt_oBits : seedsAt (Run.oB (Run.oBits ())) = seedsAt Fmt.oracle := by
  unfold seedsAt
  rw [HO_oBits]

/-- So the check of an entry file is the same at both. -/
theorem checkAtR_oBits : checkAtR (Run.oB (Run.oBits ())) = checkAtR Fmt.oracle := by
  unfold checkAtR
  rw [Slice.readerAt_oBits, seedsAt_oBits]

/-- So is the ID without seeds (OnBytes/Tie/IdKey.lean). -/
theorem idAt_oBits (k : IdKey) : idAt (Run.oB (Run.oBits ())) k = idAt Fmt.oracle k := by
  unfold idAt
  rw [HO_oBits]

/-! ## 2. A plain reader of the key file -/

/-- The table at the beginning of a key file, under a shape: the head, the root, the record's
answers. `Key.readTable`'s text without its three tests (on the shape, on the digest, on the number
of answers). It calls no hash. -/
def tableAt (s : Params.IndexShape) (file : ByteArray) : Option Params.TableName :=
  match Proof.readHead .two .key file with
  | .error _ => none
  | .ok i =>
    match OnBytes.readTable .two (s.rows * s.answers) file i with
    | .error _ => none
    | .ok (t, _) => some t

/-- What `Key.readTable` returns, under whatever digest, is `tableAt` of the shape and the file. -/
theorem tableAt_of_readTable {s : Params.IndexShape} {c file : ByteArray} {t : Params.TableName}
    {j : Nat} (h : Key.readTable s c file = .ok (t, j)) : tableAt s file = some t := by
  unfold Key.readTable at h
  unfold tableAt
  split at h
  · cases h
  · split at h
    · cases h
    · rename_i i hi
      rw [hi]
      dsimp only
      split at h
      · cases h
      · rename_i table k ht
        rw [ht]
        dsimp only
        split at h
        · cases h
          rfl
        · cases h

/-- The table that `Key.check` returns is `tableAt` of the shape in the key's one-time chain and the
file. -/
theorem keyCheck_tableAt {k : Params.KeyChains} {file : ByteArray} {table : Params.TableName}
    (h : Key.check k file = .ok table) : tableAt k.oneTime.lin.fold.index file = some table := by
  obtain ⟨j, hj⟩ := Verify.keyCheck_table h
  exact tableAt_of_readTable hj

/-- Under `ZeroFacts`: `tableAt` of the shape that enters the ID and of the key file's bytes is the
table that `Key.check` returned. -/
theorem zero_tableAt {args : List String} {s s' : World} {w : WholeSeen}
    (h : ZeroFacts args s s' w) : tableAt w.p.chains.tableShape w.r.key = some w.table :=
  keyCheck_tableAt h.keyYes

/-- What enters the ID without seeds, read off the key file by a plain, total function, at a tables'
shape sh and a digest c: shape, digest, table (root AND answers). Where the file has no table: the
table with an empty root and no answers, which has no code (`idOk` asks a root of 32 bytes); nor has
a key at a c that has not 32 bytes. THAT DROPPING `Key.readTable`'s THREE TESTS GIVES A PROVER
NOTHING IS NO THEOREM. By its text it calls no hash; that is no theorem. -/
def keyAt (sh : Params.IndexShape) (c key : ByteArray) : IdKey :=
  (sh, c, (tableAt sh key).getD ⟨ByteArray.empty, []⟩)

/-- Under `ZeroFacts` and `SaysRecordLines`: the tables' shape in p is the typed one. -/
theorem zero_record_shape {args : List String} {s s' : World} {w : WholeSeen}
    (h : ZeroFacts args s s' w) (hs : SaysRecordLines w.r.pol) :
    w.p.chains.tableShape = Params.recordRead.link.table := by
  have eb := zero_entry_bytes h (saysRecordLines_bytes hs w.lay w.r.KL)
  have e1 := h.same.2.2
  rw [eb, record_read_at _ (Params.configurationDigest_size _)] at e1
  rw [tableShape_oneTime, h.same.2.1.1, ← Option.some.inj e1]
  rfl

/-- Under `ZeroFacts` ALONE: `keyAt` of the tables' shape in p, the three configuration files'
digest and the key file's bytes is `idKeyOf w`: the shape and the digest in p and THE TABLE THAT
`Key.check` RETURNED, which is the first table of `Entry.check`. -/
theorem zero_keyAt {args : List String} {s s' : World} {w : WholeSeen}
    (h : ZeroFacts args s s' w) :
    keyAt w.p.chains.tableShape (Params.configurationDigest [w.r.pol, w.lay, w.r.KL]) w.r.key =
      idKeyOf w := by
  unfold keyAt idKeyOf
  rw [zero_tableAt h, h.same.1.1]
  rfl

/-! ## 2b. A plain reader of the entry file -/

/-- The table at the beginning of an entry file, under a shape: the head, the root, the record's
answers. `Entry.read`'s text up to there, without its two tests on the parameters. The field is
`.two`, not the parameters' own (`Entry.read` refuses another). By its text it calls no hash; that
is no theorem. It does not take the first table. -/
def furtherAt (s : Params.IndexShape) (file : ByteArray) : Option Params.TableName :=
  match Proof.readHead .two .entry file with
  | .error _ => none
  | .ok i =>
    match OnBytes.readTable .two (s.rows * s.answers) file i with
    | .error _ => none
    | .ok (t, _) => some t

/-- The further table in what `entryPlaceR` returns, whatever the function for the seeds and the
first table, is `furtherAt` of the tables' shape and the file. -/
theorem entryPlaceR_furtherAt {sd : Seeds} {p : Params.Link} {first : Params.TableName}
    {file : ByteArray} {P : EntryPlace} (h : entryPlaceR sd p first file = some P) :
    furtherAt p.link.table file = some P.further := by
  unfold entryPlaceR at h
  dsimp only at h
  split at h
  · cases h
  · rename_i i hi
    split at h
    · cases h
    · rename_i hf
      have e2 : p.given.plan.field = .two :=
        Classical.byContradiction fun hne => hf (by simp [bne_iff_ne, hne])
      rw [e2] at hi h
      split at h
      · cases h
      · rename_i further j ht
        unfold furtherAt
        rw [hi]
        dsimp only
        rw [ht]
        dsimp only
        split at h
        · split at h
          · cases h
          · cases h
            rfl
        · cases h

/-- The further table that `Entry.read` returns is `furtherAt` of the tables' shape and the file. -/
theorem entryRead_furtherAt {p : Params.Link} {first : Params.TableName} {file : ByteArray}
    {r : Entry.EntryRead} (h : Entry.read p first file = .ok r) :
    furtherAt p.link.table file = some r.further := by
  have h1 : readWithR readIn recordSeeds p first file = some r := by
    rw [readWithR_readIn, h]
    rfl
  obtain ⟨P, hP, _, _, e3, _⟩ := (readWithR_iff _ _ _ _ _ _).1 h1
  rw [e3]
  exact entryPlaceR_furtherAt hP

/-- The copy's key, read off the entry file by a plain, total function, at a tables' shape sh
and a digest c: `keyAt`'s like. It does not take the key file. THAT DROPPING `Entry.read`'s TWO
TESTS GIVES A PROVER NOTHING IS NO THEOREM. -/
def keyCAt (sh : Params.IndexShape) (c ent : ByteArray) : IdKey :=
  (sh, c, (furtherAt sh ent).getD ⟨ByteArray.empty, []⟩)

/-- The copy's key of a whole call: the tables' shape and the digest in p, and the table that
`Entry.check` returned. -/
def idKeyCOf (w : WholeSeen) : IdKey := (w.p.chains.tableShape, w.p.cfg, w.further)

/-- Under `ZeroFacts` ALONE: `keyCAt` of the tables' shape in p, the three configuration files'
digest and the entry file's bytes is `idKeyCOf w`: the shape and the digest in p and THE TABLE THAT
`Entry.check` RETURNED, which is the table of `Proof.check`. -/
theorem zero_keyCAt {args : List String} {s s' : World} {w : WholeSeen}
    (h : ZeroFacts args s s' w) :
    keyCAt w.p.chains.tableShape (Params.configurationDigest [w.r.pol, w.lay, w.r.KL]) w.ent =
      idKeyCOf w := by
  obtain ⟨q, r, hq, hr, hf, _⟩ := (entry_check_iff _ _ _ _).1 h.entryYes
  obtain rfl : w.p.chains.link = q := Option.some.inj (h.same.2.2.symm.trans hq)
  have e := entryRead_furtherAt hr
  rw [hf, ← h.same.2.1.1, ← tableShape_oneTime] at e
  unfold keyCAt idKeyCOf
  rw [e, h.same.1.1]
  rfl

end OnBytes.Tie
