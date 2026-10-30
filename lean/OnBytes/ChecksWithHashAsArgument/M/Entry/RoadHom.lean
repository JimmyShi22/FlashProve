-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/ChecksWithHashAsArgument/M/Entry/RoadHom.lean: a morphism of monads passes through the entry's road over m:
the second pass, the reader, the session's steps, the named reading, the table's key, the check.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.ChecksWithHashAsArgument.M.Entry.File
import OnBytes.ChecksWithHashAsArgument.M.Chain.EngineHom

set_option autoImplicit false

namespace OnBytes.TwoPort.M.RoadHom

open Fmt (Plan Round Stored SpecX Seen ChainOut RoundOut OpenOut Shape Src Fld)
open OnBytes.TwoPort.M.EngineHom

variable {m n : Type → Type} [Monad m] [Monad n] (φ : Run.Hom m n) (h : HashM m)

/-! ## The second pass -/

theorem app_tryOpening (cfg : ByteArray) (f : Fld) (salt : Nat) (sh : Shape)
    (start root : ByteArray) (xs : List Nat) (b : ByteArray) (i : Nat) (sn : List Rooted) :
    φ.app (tryOpening h cfg f salt sh start root xs b i sn) =
      tryOpening (φ.on h) cfg f salt sh start root xs b i sn := by
  unfold tryOpening
  simp only [φ.app_bind, app_openingM]
  refine congrArg _ (funext fun r => ?_)
  cases r with
  | none => exact φ.app_pure _
  | some o =>
    simp only []
    split <;> exact φ.app_pure _

theorem app_tryStored (cfg statement : ByteArray) (P : Plan) (poss : List Nat) (b : ByteArray) :
    ∀ (ts : List Stored) (sn : List Rooted) (i : Nat),
      φ.app (tryStored h cfg statement P poss b ts sn i) =
        tryStored (φ.on h) cfg statement P poss b ts sn i
  | [], _, _ => φ.app_pure _
  | t :: ts, sn, i => by
    unfold tryStored
    split
    · exact φ.app_pure _
    · simp only [φ.app_bind, app_tryOpening]
      refine congrArg _ (funext fun r => ?_)
      cases r with
      | error e => exact φ.app_pure _
      | ok x => exact app_tryStored cfg statement P poss b ts _ _

theorem app_tryOpens (cfg : ByteArray) (P : Plan) (run : Option ByteArray)
    (roots : Array ByteArray) (poss : List Nat) (b : ByteArray) :
    ∀ (os : List (Shape × Src)) (sn : List Rooted) (i : Nat),
      φ.app (tryOpens h cfg P run roots poss b os sn i) =
        tryOpens (φ.on h) cfg P run roots poss b os sn i
  | [], _, _ => φ.app_pure _
  | (sh, src) :: os, sn, i => by
    unfold tryOpens
    dsimp only
    split
    · exact φ.app_pure _
    · simp only [φ.app_bind, app_tryOpening]
      refine congrArg _ (funext fun r => ?_)
      cases r with
      | error e => exact φ.app_pure _
      | ok x => exact app_tryOpens cfg P run roots poss b os _ _

theorem app_whyRound (cfg statement : ByteArray) (P : Plan) (run : Option ByteArray)
    (b : ByteArray) (s : StK (List Rooted)) (r : Round) (ts : List Stored) :
    φ.app (whyRound h cfg statement P run b s r ts) =
      whyRound (φ.on h) cfg statement P run b s r ts := by
  unfold whyRound
  split
  · exact φ.app_pure _
  · split
    · exact φ.app_pure _
    · split
      · exact φ.app_pure _
      · simp only [φ.app_bind, Run.Hom.queryW]
        refine congrArg _ (funext fun q => ?_)
        cases q with
        | none => exact φ.app_pure _
        | some cv =>
          simp only []
          split
          · exact φ.app_pure _
          · simp only [φ.app_bind, app_tryStored]
            refine congrArg _ (funext fun q => ?_)
            cases q with
            | error e => exact φ.app_pure _
            | ok x =>
              simp only [φ.app_bind, app_tryOpens]
              refine congrArg _ (funext fun q => ?_)
              cases q <;> exact φ.app_pure _

theorem app_whyRounds (cfg statement : ByteArray) (P : Plan) (run : Option ByteArray)
    (b : ByteArray) :
    ∀ (rs : List (Round × List Stored)) (s : StK (List Rooted)) (k : Nat),
      φ.app (whyRounds h cfg statement P run b rs s k) =
        whyRounds (φ.on h) cfg statement P run b rs s k
  | [], _, _ => φ.app_pure _
  | r :: rs, s, k => by
    simp only [whyRounds, φ.app_bind, app_whyRound]
    refine congrArg _ (funext fun q => ?_)
    cases q with
    | error e => exact φ.app_pure _
    | ok s' => exact app_whyRounds cfg statement P run b rs s' _

theorem app_whyRest (S : SpecX) (seen : Seen) (b : ByteArray) (x : Option ByteArray) (i0 : Nat) :
    φ.app (whyRest h S seen b x i0) = whyRest (φ.on h) S seen b x i0 := by
  unfold whyRest
  simp only [φ.app_bind, Run.Hom.startChainW]
  refine congrArg _ (funext fun pd => ?_)
  refine congrArg _ (funext fun q => ?_)
  cases q with
  | none => exact φ.app_pure _
  | some hd => exact app_whyRounds φ h _ _ _ _ _ _ _ _

theorem app_whyRefused (S : SpecX) (seen : Seen) (b : ByteArray) (i : Nat) :
    φ.app (whyRefused h S seen b i) = whyRefused (φ.on h) S seen b i := by
  unfold whyRefused
  split
  · exact φ.app_pure _
  · split
    · split
      · exact φ.app_pure _
      · exact app_whyRest φ h S seen b _ _
    · exact app_whyRest φ h S seen b _ _
    · exact app_whyRest φ h S seen b _ _

/-! ## The reader and the session's steps -/

theorem app_readChain (S : SpecX) (seen : Seen) (b : ByteArray) (i : Nat) :
    φ.app (readChain h S seen b i) = readChain (φ.on h) S seen b i :=
  app_readChainM φ h Keeper.indexed S seen b i

theorem app_readIn (S : SpecX) (b : ByteArray) (i : Nat) (s : Session) :
    φ.app (readIn h S b i s).run = (readIn (φ.on h) S b i s).run := by
  unfold readIn
  simp only [OptionT.run_mk, φ.app_bind, app_readChain]
  refine congrArg _ (funext fun r => ?_)
  cases r <;> exact φ.app_pure _

theorem app_acceptIn {Y : Type} (c : Chain Y) (y : Y) (b : ByteArray) (i : Nat) (s : Session) :
    φ.app (acceptIn h c y b i s).run = (acceptIn (φ.on h) c y b i s).run := by
  unfold acceptIn
  simp only [OptionT.run_mk, φ.app_bind, app_readChain]
  refine congrArg _ (funext fun r => ?_)
  cases r <;> exact φ.app_pure _

/-! ## The named reading -/

open OnBytes.Proof hiding Reading need Reading.fromStart readerName readNamed
open OnBytes.TwoPort.M.Proof

theorem app_need {α : Type} (why : String) (x : Option α) (s : Session) :
    φ.app (need (m := m) why x s).run = (need (m := n) why x s).run := by
  unfold need
  simp only [ExceptT.run_mk]
  exact φ.app_pure _

theorem app_needM {α : Type} (why : String) (x : m (Option α)) (s : Session) :
    φ.app (needM why x s).run = (needM why (φ.app x) s).run := by
  unfold needM
  simp only [ExceptT.run_mk, φ.app_bind]
  refine congrArg _ (funext fun r => ?_)
  cases r <;> exact φ.app_pure _

theorem app_fromStart {α : Type} (w : Reading m α) (w' : Reading n α)
    (hw : ∀ s, φ.app (w s).run = (w' s).run) : φ.app w.fromStart = w'.fromStart := by
  unfold Reading.fromStart
  simp only [φ.app_bind, φ.app_pure, hw]

theorem app_readerName (front : String) (S : SpecX) (seen : Seen) (b : ByteArray) (i : Nat) :
    φ.app (readerName h front S seen b i) = readerName (φ.on h) front S seen b i := by
  unfold readerName
  simp only [φ.app_bind, app_whyRefused]
  refine congrArg _ (funext fun r => ?_)
  cases r <;> exact φ.app_pure _

theorem app_readNamed (front : String) (S : SpecX) (b : ByteArray) (i : Nat) (s : Session) :
    φ.app (readNamed h front S b i s).run = (readNamed (φ.on h) front S b i s).run := by
  unfold readNamed
  simp only [ExceptT.run_mk, φ.app_bind, app_readIn]
  refine congrArg _ (funext fun r => ?_)
  cases r with
  | some y => exact φ.app_pure _
  | none => simp only [φ.app_bind, φ.app_pure, app_readerName]

/-! ## The table's key and the check of an entry file -/

theorem app_recordSeeds (f : Fld) (name : ByteArray) (bits count : Nat) :
    φ.app (recordSeeds h f name bits count) = recordSeeds (φ.on h) f name bits count := by
  unfold recordSeeds
  simp only [φ.app_bind, Run.Hom.queryW]
  refine congrArg _ (funext fun first => ?_)
  refine congrArg _ (funext fun q => ?_)
  cases q <;> exact φ.app_pure _

theorem app_tableKey (f : Fld) (cfg : ByteArray) (s : Params.IndexShape)
    (table : Params.TableName) (item : Nat) :
    φ.app (tableKey h f cfg s table item) = tableKey (φ.on h) f cfg s table item := by
  unfold tableKey
  simp only [φ.app_bind, φ.app_pure, app_recordSeeds]

theorem app_read (p : Params.Link) (first : Params.TableName) (file : ByteArray) :
    φ.app (Entry.read h p first file) = Entry.read (φ.on h) p first file := by
  unfold Entry.read
  dsimp only
  split
  · exact φ.app_pure _
  · split
    · exact φ.app_pure _
    · split
      · exact φ.app_pure _
      · simp only [φ.app_bind, app_tableKey]
        refine congrArg _ (funext fun a0 => ?_)
        refine congrArg _ (funext fun a1 => ?_)
        split
        · split
          · exact φ.app_pure _
          · simp only [φ.app_bind]
            rw [app_fromStart φ _ _ (app_readNamed φ h _ _ _ _)]
            refine congrArg _ (funext fun r => ?_)
            cases r <;> exact φ.app_pure _
        · exact φ.app_pure _

theorem app_check (params : ByteArray) (first : Params.TableName) (file : ByteArray) :
    φ.app (Entry.check h params first file) = Entry.check (φ.on h) params first file := by
  unfold Entry.check
  split
  · exact φ.app_pure _
  · simp only [φ.app_bind, app_read]
    refine congrArg _ (funext fun r => ?_)
    cases r with
    | error e => exact φ.app_pure _
    | ok r =>
      simp only []
      split <;> exact φ.app_pure _

end OnBytes.TwoPort.M.RoadHom
