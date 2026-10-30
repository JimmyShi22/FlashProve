-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/EntryAskRec.lean: the plain side of a checker that asks.

For `LinkE` (OnBytes/TypedOracleCompiler/Slice/Shapes.lean). `checkAskR O := checkWithR (readInAt O) (seedsAt O)`,
the reader and the record's seeds at O, is the check at O with nothing pinned: the value that a
step which asks would have at O.
No string of O is pinned. The digest c in params is a constant, BLAKE2b's in `zero_record_ask`.

With: its tie at the format's own oracle, both ways; at `Run.oBits`; and from main.

Not claimed. It asks no oracle itself. No part, no bound. Nothing on soundness.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.Tie.LinkPlain
import OnBytes.Tie.StoredAt

set_option autoImplicit false

namespace OnBytes.Tie

open OnBytes.Shell (World)

section
variable {q : Params.Link} {first : Params.TableName} {file : ByteArray}

/-- Reading with the seeds at the format's own oracle and ANY reader rd that (i) agrees with the
program's reader within `smallFX` and (ii) says yes only under a description that is in order: it is
the program's reading; BOTH WAYS. Under a digest and a first root of 32
bytes, and `smallFX` of every description that `entryPlaceR` gives at the program's own seeds and
that is in order. `readWithR_oracle` is its instance at `readerAt Fmt.oracle`. -/
theorem readWithR_reader (rd : Fmt.SpecX → ByteArray → Nat → InSession ChainRead)
    (hrd : ∀ S i, smallFX S file = true → rd S file i Session.start = readIn S file i Session.start)
    (hokrd : ∀ S i y, rd S file i Session.start = some y → S.ok = true)
    (hc : q.given.cfg.size = 32) (h0 : first.root.size = 32)
    (hsm : ∀ P, entryPlaceR recordSeeds q first file = some P → P.spec.ok = true →
      smallFX P.spec file = true) (r : Entry.EntryRead) :
    readWithR rd (seedsAt Fmt.oracle) q first file = some r ↔ Entry.read q first file = .ok r := by
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
      cases hx : rd P.spec file P.byte Session.start with
      | none =>
        rw [hx] at hrun
        cases hrun
      | some y => exact hokrd _ _ y hx
    rw [← hrd P.spec P.byte (hsm P hP hok)]
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
    rw [hrd P.spec P.byte (hsm P hP hok)]
    exact hrun

end

/-- The check of an entry file at O, WITH NOTHING PINNED: `checkWithR`
with the library's strict reader at the hash that O induces and the record's seeds at O. `checkAtR`
is this with the format's own digest of the parameter bytes in the place of O's, for the reader. A
plain function of O: the value that a step which asks would have at O. The program does not call it.
The 32 bytes in params that stand for the digest of the public files are taken as they are. -/
def checkAskR (O : ByteArray → ByteArray) (params : ByteArray) (first : Params.TableName)
    (file : ByteArray) : Option Params.TableName :=
  checkWithR (readInAt O) (seedsAt O) params first file

/-- At the format's own oracle `checkAskR` is the program's check; BOTH
WAYS, under what `entry_check_atR` asks. At another function O nothing ties `checkAskR O` to a
program that hashes by O. -/
theorem entry_check_askR (params : ByteArray) (q : Params.Link) (first further : Params.TableName)
    (file : ByteArray) (hq : Params.Link.read params = some q) (hc : q.given.cfg.size = 32)
    (h0 : first.root.size = 32)
    (hsm : ∀ P, entryPlaceR recordSeeds q first file = some P → P.spec.ok = true →
      smallFX P.spec file = true) :
    checkAskR Fmt.oracle params first file = some further ↔
      Entry.check params first file = .ok further := by
  have key : ∀ r, readWithR (readInAt Fmt.oracle) (seedsAt Fmt.oracle) q first file = some r ↔
      Entry.read q first file = .ok r :=
    readWithR_reader (readInAt Fmt.oracle)
      (fun S i hs => readInAt_oracle S file i Session.start hs)
      (fun S i y hx => readX_ok _ _ _ file i _ (readInAt_read _ _ _ _ _ y.2 y.1 hx).1) hc h0 hsm
  unfold checkAskR
  rw [checkWithR_iff, entry_check_iff]
  constructor
  · rintro ⟨q', r, hq', hr, rest⟩
    obtain rfl : q' = q := Option.some.inj (hq'.symm.trans hq)
    exact ⟨q', r, hq', (key r).1 hr, rest⟩
  · rintro ⟨q', r, hq', hr, rest⟩
    obtain rfl : q' = q := Option.some.inj (hq'.symm.trans hq)
    exact ⟨q', r, hq', (key r).2 hr, rest⟩

/-- `checkAskR` at the function that `Run.oBits` induces is `checkAskR` at the format's oracle. One
fixed oracle: no bound over a drawn oracle says anything of it. -/
theorem checkAskR_oBits : checkAskR (Run.oB (Run.oBits ())) = checkAskR Fmt.oracle := by
  have e : readInAt (Run.oB (Run.oBits ())) = readInAt Fmt.oracle := by
    funext S b i s
    unfold readInAt
    rw [HO_oBits]
  unfold checkAskR
  rw [e, seedsAt_oBits]

/-- FROM THE ENTRY FUNCTION. Under `ZeroFacts` and `SaysRecordLines`, at c := the digest of the
three configuration files as read: `checkAskR`, at the function that the oracle on bit strings made
from the format's hash induces, on `recordBytesAt c`, the table that `Key.check` returned and the
entry file's bytes, returns the table that `Entry.check` returned. At that oracle it is equivalent
to the program's yes: a form, no news. Of `checkAskR` at another function nothing is proved. -/
theorem zero_record_ask {args : List String} {s s' : World} {w : WholeSeen}
    (h : ZeroFacts args s s' w) (hs : SaysRecordLines w.r.pol) :
    checkAskR (Run.oB (Run.oBits ()))
      (recordBytesAt (Params.configurationDigest [w.r.pol, w.lay, w.r.KL])) w.table w.ent =
        some w.further := by
  have hc32 := Params.configurationDigest_size [w.r.pol, w.lay, w.r.KL]
  have eb := zero_entry_bytes h (saysRecordLines_bytes hs w.lay w.r.KL)
  have hy : Entry.check (recordBytesAt (Params.configurationDigest [w.r.pol, w.lay, w.r.KL]))
      w.table w.ent = .ok w.further := by
    rw [← eb]
    exact h.entryYes
  rw [checkAskR_oBits]
  refine (entry_check_askR _ _ w.table w.further w.ent (record_read_at _ hc32) hc32
    (zero_table_root h) ?_).2 hy
  intro P hP hokP
  obtain ⟨_, ⟨rs2, h2, eP⟩, _⟩ := entryPlaceR_spec_any hP
  obtain rfl : Params.recordRounds = rs2 :=
    Option.some.inj ((record_rounds_at _).symm.trans h2)
  rw [eP] at hokP ⊢
  exact smallFX_of_withinX _ hokP (withinX_record_at _ hc32 _ (specX_base _ hokP)) w.ent
    (zero_entry_small h)

end OnBytes.Tie
