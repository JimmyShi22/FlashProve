-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/ChecksWithHashAsArgument/M/Entry/RoadKeepsAt.lean: a property of computations that pure and bind keep passes
through the entry's road over m, if every call of the hash under a number other than 169 has it, and
the only call under 169 that the road makes, once or twice: the digest of the link's chain's
parameter bytes.

After OnBytes/ChecksWithHashAsArgument/M/Entry/RoadKeeps.lean, whose premise speaks of every call; over
OnBytes/ChecksWithHashAsArgument/M/Chain/EngineKeepsAt.lean. The road itself calls the hash at two more places: the
parameters' digest once more, where a refused chain is gone over a second time, and the first value
of a record's seeds (160).

Main names: `ok_readNamed`: for a chain with the description S, under the premise at
`S.base.params`. `ok_tableKey`. `ok_read`, `ok_check`: for an entry file, under the premise at the
link's chain's parameter bytes. `params_of_describe`, `params_of_bind`: the description that the
road makes has these bytes for its parameter bytes.

Limits: a frame over letters: nothing is said of any property or hash. `acceptIn` is not treated.
The readings of a key file and of a proof file are not treated; `ok_readNamed` and `ok_tableKey` are
stated so that they can serve there. For proofs only; no program imports this file.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.ChecksWithHashAsArgument.M.Entry.RoadKeeps
import OnBytes.ChecksWithHashAsArgument.M.Chain.EngineKeepsAt

set_option autoImplicit false

namespace OnBytes.TwoPort.M.RoadKeepsAt

open Fmt (Plan Round Stored SpecX Seen ChainOut RoundOut OpenOut Shape Src Fld)
open OnBytes.TwoPort.M.EngineKeepsAt
open OnBytes.TwoPort.M.RoadKeeps (ok_need ok_needM ok_fromStart)

/-- A description made from parameter bytes has these bytes for its parameter bytes. -/
theorem params_of_describe {g : Params.Given} {label : Nat} {statement : ByteArray}
    {rand : Fmt.Rand} {r : Params.Rounds} {firstTree : Nat} {S : Fmt.SpecX}
    (e : Params.describeWith g label statement rand r firstTree = some S) :
    S.base.params = g.bytes := by
  unfold Params.describeWith Params.Given.describe at e
  dsimp only at e
  split at e
  · rw [← Option.some.inj e]
  · cases e

/-- The same for the description of a link's chain, behind the rounds of its block. -/
theorem params_of_bind {p : Params.Link} {first further : Params.TableName}
    {x : Option Params.Rounds} {S : Fmt.SpecX} (e : x.bind (p.describe first further) = some S) :
    S.base.params = p.given.bytes := by
  cases x with
  | none => cases e
  | some r => exact params_of_describe e

variable {m : Type → Type} [Monad m] (k : Keeps m)

variable (h : HashM m) (hh : ∀ n t i s b, n % 65536 ≠ 169 → k.ok (h n t i s b))
include hh

/-! ## The second pass -/

/-- The property passes through `tryOpening`. -/
theorem ok_tryOpening (cfg : ByteArray) (f : Fld) (salt : Nat) (sh : Shape)
    (start root : ByteArray) (xs : List Nat) (b : ByteArray) (i : Nat) (sn : List Rooted) :
    k.ok (tryOpening h cfg f salt sh start root xs b i sn) := by
  unfold tryOpening
  refine k.ok_bind _ _ (ok_openingM k h hh _ _ _ _ _ _ _ _) fun r => ?_
  cases r with
  | none => exact k.ok_pure _
  | some o =>
    simp only []
    split <;> exact k.ok_pure _

/-- The property passes through `tryStored`. -/
theorem ok_tryStored (cfg statement : ByteArray) (P : Plan) (poss : List Nat) (b : ByteArray) :
    ∀ (ts : List Stored) (sn : List Rooted) (i : Nat),
      k.ok (tryStored h cfg statement P poss b ts sn i)
  | [], _, _ => k.ok_pure _
  | t :: ts, sn, i => by
    unfold tryStored
    split
    · exact k.ok_pure _
    · refine k.ok_bind _ _ (ok_tryOpening k h hh _ _ _ _ _ _ _ _ _ _) fun r => ?_
      cases r with
      | error e => exact k.ok_pure _
      | ok x => exact ok_tryStored cfg statement P poss b ts _ _

/-- The property passes through `tryOpens`. -/
theorem ok_tryOpens (cfg : ByteArray) (P : Plan) (run : Option ByteArray)
    (roots : Array ByteArray) (poss : List Nat) (b : ByteArray) :
    ∀ (os : List (Shape × Src)) (sn : List Rooted) (i : Nat),
      k.ok (tryOpens h cfg P run roots poss b os sn i)
  | [], _, _ => k.ok_pure _
  | (sh, src) :: os, sn, i => by
    unfold tryOpens
    dsimp only
    split
    · exact k.ok_pure _
    · refine k.ok_bind _ _ (ok_tryOpening k h hh _ _ _ _ _ _ _ _ _ _) fun r => ?_
      cases r with
      | error e => exact k.ok_pure _
      | ok x => exact ok_tryOpens cfg P run roots poss b os _ _

/-- The property passes through `whyRound`. -/
theorem ok_whyRound (cfg statement : ByteArray) (P : Plan) (run : Option ByteArray)
    (b : ByteArray) (s : StK (List Rooted)) (r : Round) (ts : List Stored) :
    k.ok (whyRound h cfg statement P run b s r ts) := by
  unfold whyRound
  split
  · exact k.ok_pure _
  · split
    · exact k.ok_pure _
    · split
      · exact k.ok_pure _
      · refine k.ok_bind _ _ (ok_queryW k h hh _ _ _ _ _ _) fun q => ?_
        cases q with
        | none => exact k.ok_pure _
        | some cv =>
          simp only []
          split
          · exact k.ok_pure _
          · refine k.ok_bind _ _ (ok_tryStored k h hh _ _ _ _ _ _ _ _) fun q => ?_
            cases q with
            | error e => exact k.ok_pure _
            | ok x =>
              refine k.ok_bind _ _ (ok_tryOpens k h hh _ _ _ _ _ _ _ _ _) fun q => ?_
              cases q <;> exact k.ok_pure _

/-- The property passes through `whyRounds`. -/
theorem ok_whyRounds (cfg statement : ByteArray) (P : Plan) (run : Option ByteArray)
    (b : ByteArray) :
    ∀ (rs : List (Round × List Stored)) (s : StK (List Rooted)) (j : Nat),
      k.ok (whyRounds h cfg statement P run b rs s j)
  | [], _, _ => k.ok_pure _
  | r :: rs, s, j => by
    unfold whyRounds
    refine k.ok_bind _ _ (ok_whyRound k h hh _ _ _ _ _ _ _ _) fun q => ?_
    cases q with
    | error e => exact k.ok_pure _
    | ok s' => exact ok_whyRounds cfg statement P run b rs s' _

/-- The property passes through `whyRest`. -/
theorem ok_whyRest (S : SpecX) (seen : Seen) (b : ByteArray) (x : Option ByteArray) (i0 : Nat)
    (hpd : k.ok (h 169 0 1 Fmt.zero32 S.base.params)) : k.ok (whyRest h S seen b x i0) := by
  unfold whyRest
  refine k.ok_bind _ _ hpd fun pd => ?_
  refine k.ok_bind _ _ (ok_startChainW k h hh _ _ _ _) fun q => ?_
  cases q with
  | none => exact k.ok_pure _
  | some hd => exact ok_whyRounds k h hh _ _ _ _ _ _ _ _

/-- The property passes through `whyRefused`. -/
theorem ok_whyRefused (S : SpecX) (seen : Seen) (b : ByteArray) (i : Nat)
    (hpd : k.ok (h 169 0 1 Fmt.zero32 S.base.params)) : k.ok (whyRefused h S seen b i) := by
  unfold whyRefused
  split
  · exact k.ok_pure _
  · split
    · split
      · exact k.ok_pure _
      · exact ok_whyRest k h hh S seen b _ _ hpd
    · exact ok_whyRest k h hh S seen b _ _ hpd
    · exact ok_whyRest k h hh S seen b _ _ hpd

/-! ## The reader and the session's steps -/

/-- The property passes through `readChain`. -/
theorem ok_readChain (S : SpecX) (seen : Seen) (b : ByteArray) (i : Nat)
    (hpd : k.ok (h 169 0 1 Fmt.zero32 S.base.params)) : k.ok (readChain h S seen b i) :=
  ok_readChainM k h hh Keeper.indexed S seen b i hpd

/-- The property passes through `readIn`. -/
theorem ok_readIn (S : SpecX) (b : ByteArray) (i : Nat) (s : Session)
    (hpd : k.ok (h 169 0 1 Fmt.zero32 S.base.params)) : k.ok (readIn h S b i s).run := by
  unfold readIn
  simp only [OptionT.run_mk]
  refine k.ok_bind _ _ (ok_readChain k h hh _ _ _ _ hpd) fun r => ?_
  cases r <;> exact k.ok_pure _

/-! ## The named reading -/

open OnBytes.Proof hiding Reading need Reading.fromStart readerName readNamed
open OnBytes.TwoPort.M.Proof

/-- The property passes through `readerName`. -/
theorem ok_readerName (front : String) (S : SpecX) (seen : Seen) (b : ByteArray) (i : Nat)
    (hpd : k.ok (h 169 0 1 Fmt.zero32 S.base.params)) : k.ok (readerName h front S seen b i) := by
  unfold readerName
  refine k.ok_bind _ _ (ok_whyRefused k h hh _ _ _ _ hpd) fun r => ?_
  cases r <;> exact k.ok_pure _

/-- The property passes through `readNamed`. -/
theorem ok_readNamed (front : String) (S : SpecX) (b : ByteArray) (i : Nat)
    (hpd : k.ok (h 169 0 1 Fmt.zero32 S.base.params)) (s : Session) :
    k.ok (readNamed h front S b i s).run := by
  unfold readNamed
  simp only [ExceptT.run_mk]
  refine k.ok_bind _ _ (ok_readIn k h hh _ _ _ _ hpd) fun r => ?_
  cases r with
  | some y => exact k.ok_pure _
  | none => exact k.ok_bind _ _ (ok_readerName k h hh _ _ _ _ _ hpd) fun _ => k.ok_pure _

/-! ## The table's key and the check of an entry file -/

/-- The property passes through `recordSeeds`. -/
theorem ok_recordSeeds (f : Fld) (name : ByteArray) (bits count : Nat) :
    k.ok (recordSeeds h f name bits count) := by
  unfold recordSeeds
  refine k.ok_bind _ _ (hh _ _ _ _ _ (by decide)) fun first => ?_
  refine k.ok_bind _ _ (ok_queryW k h hh _ _ _ _ _ _) fun q => ?_
  cases q <;> exact k.ok_pure _

/-- The property passes through `tableKey`. -/
theorem ok_tableKey (f : Fld) (cfg : ByteArray) (s : Params.IndexShape)
    (table : Params.TableName) (item : Nat) : k.ok (tableKey h f cfg s table item) := by
  unfold tableKey
  dsimp only
  exact k.ok_bind _ _ (ok_recordSeeds k h hh _ _ _ _) fun _ => k.ok_pure _

/-- The property passes through `read`. -/
theorem ok_read (p : Params.Link) (first : Params.TableName) (file : ByteArray)
    (hpd : k.ok (h 169 0 1 Fmt.zero32 p.given.bytes)) : k.ok (Entry.read h p first file) := by
  unfold Entry.read
  dsimp only
  split
  · exact k.ok_pure _
  · split
    · exact k.ok_pure _
    · split
      · exact k.ok_pure _
      · refine k.ok_bind _ _ (ok_tableKey k h hh _ _ _ _ _) fun a0 => ?_
        refine k.ok_bind _ _ (ok_tableKey k h hh _ _ _ _ _) fun a1 => ?_
        split
        · split
          · exact k.ok_pure _
          · rename_i spec hs
            have hp : spec.base.params = p.given.bytes := params_of_bind hs
            refine k.ok_bind _ _
              (ok_fromStart k _ (ok_readNamed k h hh _ spec _ _ (hp ▸ hpd))) fun r => ?_
            cases r <;> exact k.ok_pure _
        · exact k.ok_pure _

/-- The property passes through `check`. -/
theorem ok_check (params : ByteArray) (first : Params.TableName) (file : ByteArray)
    (hpd : ∀ p, Params.Link.read params = some p → k.ok (h 169 0 1 Fmt.zero32 p.given.bytes)) :
    k.ok (Entry.check h params first file) := by
  unfold Entry.check
  split
  · exact k.ok_pure _
  · rename_i p hp
    refine k.ok_bind _ _ (ok_read k h hh _ _ _ (hpd p hp)) fun r => ?_
    cases r with
    | error e => exact k.ok_pure _
    | ok r =>
      simp only []
      split <;> exact k.ok_pure _

end OnBytes.TwoPort.M.RoadKeepsAt
