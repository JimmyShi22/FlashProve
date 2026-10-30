-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/ChecksWithHashAsArgument/M/Entry/RoadKeeps.lean: a property of computations that pure and bind keep passes
through the entry's road over m, if every call of the hash has it.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.ChecksWithHashAsArgument.M.Entry.File
import OnBytes.ChecksWithHashAsArgument.M.Chain.EngineKeeps

set_option autoImplicit false

namespace OnBytes.TwoPort.M.RoadKeeps

open Fmt (Plan Round Stored SpecX Seen ChainOut RoundOut OpenOut Shape Src Fld)
open OnBytes.TwoPort.M.EngineKeeps

variable {m : Type → Type} [Monad m] (k : Keeps m)

/-! ## What takes no hash -/

open OnBytes.Proof hiding Reading need Reading.fromStart readerName readNamed in
open OnBytes.TwoPort.M.Proof in
theorem ok_need {α : Type} (why : String) (x : Option α) (s : Session) :
    k.ok (need (m := m) why x s).run := by
  unfold need
  simp only [ExceptT.run_mk]
  exact k.ok_pure _

open OnBytes.Proof hiding Reading need Reading.fromStart readerName readNamed in
open OnBytes.TwoPort.M.Proof in
theorem ok_needM {α : Type} (why : String) (x : m (Option α)) (hx : k.ok x) (s : Session) :
    k.ok (needM why x s).run := by
  unfold needM
  simp only [ExceptT.run_mk]
  refine k.ok_bind _ _ hx fun r => ?_
  cases r <;> exact k.ok_pure _

open OnBytes.Proof hiding Reading need Reading.fromStart readerName readNamed in
open OnBytes.TwoPort.M.Proof in
theorem ok_fromStart {α : Type} (w : Reading m α) (hw : ∀ s, k.ok (w s).run) :
    k.ok w.fromStart := by
  unfold Reading.fromStart
  exact k.ok_bind _ _ (hw _) fun _ => k.ok_pure _

variable (h : HashM m) (hh : ∀ n t i s b, k.ok (h n t i s b))
include hh

/-! ## The second pass -/

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

theorem ok_whyRest (S : SpecX) (seen : Seen) (b : ByteArray) (x : Option ByteArray) (i0 : Nat) :
    k.ok (whyRest h S seen b x i0) := by
  unfold whyRest
  refine k.ok_bind _ _ (hh _ _ _ _ _) fun pd => ?_
  refine k.ok_bind _ _ (ok_startChainW k h hh _ _ _ _) fun q => ?_
  cases q with
  | none => exact k.ok_pure _
  | some hd => exact ok_whyRounds k h hh _ _ _ _ _ _ _ _

theorem ok_whyRefused (S : SpecX) (seen : Seen) (b : ByteArray) (i : Nat) :
    k.ok (whyRefused h S seen b i) := by
  unfold whyRefused
  split
  · exact k.ok_pure _
  · split
    · split
      · exact k.ok_pure _
      · exact ok_whyRest k h hh S seen b _ _
    · exact ok_whyRest k h hh S seen b _ _
    · exact ok_whyRest k h hh S seen b _ _

/-! ## The reader and the session's steps -/

theorem ok_readChain (S : SpecX) (seen : Seen) (b : ByteArray) (i : Nat) :
    k.ok (readChain h S seen b i) :=
  ok_readChainM k h hh Keeper.indexed S seen b i

theorem ok_readIn (S : SpecX) (b : ByteArray) (i : Nat) (s : Session) :
    k.ok (readIn h S b i s).run := by
  unfold readIn
  simp only [OptionT.run_mk]
  refine k.ok_bind _ _ (ok_readChain k h hh _ _ _ _) fun r => ?_
  cases r <;> exact k.ok_pure _

theorem ok_acceptIn {Y : Type} (c : Chain Y) (y : Y) (b : ByteArray) (i : Nat) (s : Session) :
    k.ok (acceptIn h c y b i s).run := by
  unfold acceptIn
  simp only [OptionT.run_mk]
  refine k.ok_bind _ _ (ok_readChain k h hh _ _ _ _) fun r => ?_
  cases r <;> exact k.ok_pure _

/-! ## The named reading -/

open OnBytes.Proof hiding Reading need Reading.fromStart readerName readNamed
open OnBytes.TwoPort.M.Proof

theorem ok_readerName (front : String) (S : SpecX) (seen : Seen) (b : ByteArray) (i : Nat) :
    k.ok (readerName h front S seen b i) := by
  unfold readerName
  refine k.ok_bind _ _ (ok_whyRefused k h hh _ _ _ _) fun r => ?_
  cases r <;> exact k.ok_pure _

theorem ok_readNamed (front : String) (S : SpecX) (b : ByteArray) (i : Nat) (s : Session) :
    k.ok (readNamed h front S b i s).run := by
  unfold readNamed
  simp only [ExceptT.run_mk]
  refine k.ok_bind _ _ (ok_readIn k h hh _ _ _ _) fun r => ?_
  cases r with
  | some y => exact k.ok_pure _
  | none => exact k.ok_bind _ _ (ok_readerName k h hh _ _ _ _ _) fun _ => k.ok_pure _

/-! ## The table's key and the check of an entry file -/

theorem ok_recordSeeds (f : Fld) (name : ByteArray) (bits count : Nat) :
    k.ok (recordSeeds h f name bits count) := by
  unfold recordSeeds
  refine k.ok_bind _ _ (hh _ _ _ _ _) fun first => ?_
  refine k.ok_bind _ _ (ok_queryW k h hh _ _ _ _ _ _) fun q => ?_
  cases q <;> exact k.ok_pure _

theorem ok_tableKey (f : Fld) (cfg : ByteArray) (s : Params.IndexShape)
    (table : Params.TableName) (item : Nat) : k.ok (tableKey h f cfg s table item) := by
  unfold tableKey
  dsimp only
  exact k.ok_bind _ _ (ok_recordSeeds k h hh _ _ _ _) fun _ => k.ok_pure _

theorem ok_read (p : Params.Link) (first : Params.TableName) (file : ByteArray) :
    k.ok (Entry.read h p first file) := by
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
          · refine k.ok_bind _ _ (ok_fromStart k _ (ok_readNamed k h hh _ _ _ _)) fun r => ?_
            cases r <;> exact k.ok_pure _
        · exact k.ok_pure _

theorem ok_check (params : ByteArray) (first : Params.TableName) (file : ByteArray) :
    k.ok (Entry.check h params first file) := by
  unfold Entry.check
  split
  · exact k.ok_pure _
  · refine k.ok_bind _ _ (ok_read k h hh _ _ _) fun r => ?_
    cases r with
    | error e => exact k.ok_pure _
    | ok r =>
      simp only []
      split <;> exact k.ok_pure _

end OnBytes.TwoPort.M.RoadKeeps
