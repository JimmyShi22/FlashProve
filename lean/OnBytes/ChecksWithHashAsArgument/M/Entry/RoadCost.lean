-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/ChecksWithHashAsArgument/M/Entry/RoadCost.lean: how many questions the entry's road over m asks at most.
MADE BY A PROGRAM from a file of the same name that this project's authors wrote over an earlier
arrangement of these definitions, which is not in this tree: the program turned names, imports,
opens and the spelling of calls alone.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.ChecksWithHashAsArgument.M.Entry.File
import OnBytes.ChecksWithHashAsArgument.M.Chain.EngineCost

set_option autoImplicit false

namespace OnBytes.TwoPort.M.RoadCost

open Fmt (Plan Round Stored SpecX Seen ChainOut RoundOut OpenOut Shape Src Fld)
open OnBytes.Tie.CostX
open OnBytes.TwoPort.M.EngineCost

variable {m : Type → Type} [Monad m] (c : Run.CostP m) (k : Nat)

/-! ## What takes no hash -/

open OnBytes.Proof hiding Reading need Reading.fromStart readerName readNamed in
open OnBytes.TwoPort.M.Proof in
theorem le_need {α : Type} (why : String) (x : Option α) (s : Session) :
    c.le (need (m := m) why x s).run 0 fun _ => True := by
  unfold need
  simp only [ExceptT.run_mk]
  exact c.le_pure _ _ trivial

open OnBytes.Proof hiding Reading need Reading.fromStart readerName readNamed in
open OnBytes.TwoPort.M.Proof in
theorem le_needM {α : Type} (why : String) (x : m (Option α)) (t : Nat)
    (hx : c.le x t fun _ => True) (s : Session) : c.le (needM why x s).run t fun _ => True := by
  unfold needM
  simp only [ExceptT.run_mk]
  refine c.le_bind _ _ t 0 _ _ hx fun r _ => ?_
  cases r <;> exact c.le_pure _ _ trivial

open OnBytes.Proof hiding Reading need Reading.fromStart readerName readNamed in
open OnBytes.TwoPort.M.Proof in
theorem le_fromStart {α : Type} (w : Reading m α) (t : Nat)
    (hw : ∀ s, c.le (w s).run t fun _ => True) : c.le w.fromStart t fun _ => True := by
  unfold Reading.fromStart
  exact c.le_bind _ _ t 0 _ _ (hw _) fun _ _ => c.le_pure _ _ trivial

variable (h : HashM m)
  (hk : ∀ number tree index start bytes, c.le (h number tree index start bytes) k fun _ => True)
include hk

/-! ## The second pass: the same numbers as the first -/

theorem le_tryOpening (cfg : ByteArray) (f : Fld) (salt : Nat) (sh : Shape)
    (start root : ByteArray) (xs : List Nat) (b : ByteArray) (i : Nat) (sn : List Rooted) :
    c.le (tryOpening h cfg f salt sh start root xs b i sn) ((sh.a + 1) * (xs.length * k))
      fun _ => True := by
  unfold tryOpening
  refine c.le_bind _ _ _ 0 _ _ (le_openingM c k h hk _ _ _ _ _ _ _ _) fun r _ => ?_
  cases r with
  | none => exact c.le_pure _ _ trivial
  | some o =>
    simp only []
    split <;> exact c.le_pure _ _ trivial

theorem le_tryStored (cfg statement : ByteArray) (P : Plan) (poss : List Nat) (b : ByteArray) :
    ∀ (ts : List Stored) (sn : List Rooted) (i : Nat),
      c.le (tryStored h cfg statement P poss b ts sn i) (storedN ts * k) fun _ => True
  | [], _, _ => c.pureLe _ _ _ trivial
  | t :: ts, sn, i => by
    unfold tryStored
    have hl : (listOfT ((Fmt.partOf t poss).map (· % 2 ^ t.sh.a))).length ≤ t.count := by
      rw [listOfT_eq]
      refine Nat.le_trans (Run.CostP.listOf_len _) ?_
      unfold Fmt.partOf
      rw [List.length_map, List.length_take]
      exact Nat.min_le_left _ _
    split
    · exact c.pureLe _ _ _ trivial
    · refine c.le_mono _ ((t.sh.a + 1) * (t.count * k) + storedN ts * k) _ _ _
        (c.le_bind _ _ _ _ _ _
          (c.le_mono _ _ _ _ _ (le_tryOpening c k h hk cfg P.field t.salt t.sh _ _ _ b i sn)
            (Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hl)) fun _ h => h) fun r _ => ?_)
        (by simp only [storedN, Nat.add_mul, Nat.mul_assoc]; exact Nat.le_refl _) fun _ h => h
      cases r with
      | error e => exact c.pureLe _ _ _ trivial
      | ok x => exact le_tryStored cfg statement P poss b ts _ _

theorem le_tryOpens (cfg : ByteArray) (P : Plan) (run : Option ByteArray)
    (roots : Array ByteArray) (poss : List Nat) (b : ByteArray) :
    ∀ (os : List (Shape × Src)) (sn : List Rooted) (i : Nat),
      c.le (tryOpens h cfg P run roots poss b os sn i) (Run.opensN poss.length os * k)
        fun _ => True
  | [], _, _ => c.pureLe _ _ _ trivial
  | (sh, src) :: os, sn, i => by
    unfold tryOpens
    have hl : (listOfT (poss.map (· % 2 ^ sh.a))).length ≤ poss.length := by
      rw [listOfT_eq]
      refine Nat.le_trans (Run.CostP.listOf_len _) ?_
      rw [List.length_map]
      exact Nat.le_refl _
    dsimp only
    split
    · exact c.pureLe _ _ _ trivial
    · refine c.le_mono _ ((sh.a + 1) * (poss.length * k) + Run.opensN poss.length os * k) _ _ _
        (c.le_bind _ _ _ _ _ _
          (c.le_mono _ _ _ _ _ (le_tryOpening c k h hk cfg P.field P.salt sh _ _ _ b i sn)
            (Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hl)) fun _ h => h) fun r _ => ?_)
        (by simp only [Run.opensN, Nat.add_mul, Nat.mul_assoc]; exact Nat.le_refl _) fun _ h => h
      cases r with
      | error e => exact c.pureLe _ _ _ trivial
      | ok x => exact le_tryOpens cfg P run roots poss b os _ _

theorem le_whyRound (cfg statement : ByteArray) (P : Plan) (run : Option ByteArray)
    (b : ByteArray) (s : StK (List Rooted)) (r : Round) (ts : List Stored) :
    c.le (whyRound h cfg statement P run b s r ts) (roundNX r ts * k) fun _ => True := by
  unfold whyRound
  split
  · exact c.pureLe _ _ _ trivial
  · split
    · exact c.pureLe _ _ _ trivial
    · split
      · exact c.pureLe _ _ _ trivial
      · refine c.le_mono _
          ((Fmt.firstBlock r.entry.work + (Fmt.wordsAtMost r.entry r.kind + 3) / 4 + 1) / 2 * k +
            (storedN ts * k + (Run.opensN r.entry.poss r.opens * k + 0)))
          _ _ _ (c.le_bind _ _ _ _ _ _ (c.queryW h k hk _ _ _ _ _ _) fun q _ => ?_)
          (by simp only [roundNX, Run.roundN, Nat.add_mul]; omega) fun _ h => h
        cases q with
        | none => exact c.pureLe _ _ _ trivial
        | some cv =>
          simp only []
          split
          · exact c.pureLe _ _ _ trivial
          · refine c.le_bind _ _ _ _ (fun _ => True) _
              (le_tryStored c k h hk cfg statement P _ b ts _ _) fun q _ => ?_
            cases q with
            | error e => exact c.pureLe _ _ _ trivial
            | ok x =>
              refine c.le_bind _ _ _ 0 (fun _ => True) _ ?_ fun q _ => ?_
              · have key : ∀ (roots : Array ByteArray) (sn : List Rooted) (i : Nat),
                    c.le (tryOpens h cfg P run roots
                        (drawRoundT P.field r.entry r.kind (Fmt.rowOf cv.2)).poss b r.opens sn i)
                      (Run.opensN r.entry.poss r.opens * k) fun _ => True := fun roots sn i => by
                  have := le_tryOpens c k h hk cfg P run roots
                    (drawRoundT P.field r.entry r.kind (Fmt.rowOf cv.2)).poss b r.opens sn i
                  rw [drawRoundT_eq, Run.CostP.drawRound_poss] at this
                  rw [drawRoundT_eq]
                  exact this
                exact key _ _ _
              · cases q <;> exact c.le_pure _ _ trivial

theorem le_whyRounds (cfg statement : ByteArray) (P : Plan) (run : Option ByteArray)
    (b : ByteArray) :
    ∀ (rs : List (Round × List Stored)) (s : StK (List Rooted)) (j : Nat),
      c.le (whyRounds h cfg statement P run b rs s j) (roundsNX rs * k) fun _ => True
  | [], _, _ => c.pureLe _ _ _ trivial
  | r :: rs, s, j => by
    unfold whyRounds
    refine c.le_mono _ (roundNX r.1 r.2 * k + roundsNX rs * k) _ _ _
      (c.le_bind _ _ _ _ _ _ (le_whyRound c k h hk cfg statement P run b s r.1 r.2) fun q _ => ?_)
      (by simp only [roundsNX, Nat.add_mul]; exact Nat.le_refl _) fun _ h => h
    cases q with
    | error e => exact c.pureLe _ _ _ trivial
    | ok s' => exact le_whyRounds cfg statement P run b rs s' _

theorem le_whyRest (S : SpecX) (seen : Seen) (b : ByteArray) (x : Option ByteArray) (i0 : Nat) :
    c.le (whyRest h S seen b x i0) (fileNX S * k) fun _ => True := by
  unfold whyRest
  refine c.le_mono _ (k + (2 * k + roundsNX (S.base.rounds.zip S.stored) * k)) _ _ _
    (c.le_bind _ _ k _ _ _ (hk _ _ _ _ _) fun pd _ =>
      c.le_bind _ _ _ _ (fun _ => True) _ (c.startChainW h k hk _ _ _ _) fun q _ => ?_)
    (by simp only [fileNX, Nat.add_mul]; omega) fun _ h => h
  cases q with
  | none => exact c.pureLe _ _ _ trivial
  | some hd =>
    simp only []
    rw [zipT_eq]
    exact le_whyRounds c k h hk _ _ _ _ _ _ _ _

theorem le_whyRefused (S : SpecX) (seen : Seen) (b : ByteArray) (i : Nat) :
    c.le (whyRefused h S seen b i) (fileNX S * k) fun _ => True := by
  unfold whyRefused
  split
  · exact c.pureLe _ _ _ trivial
  · split
    · split
      · exact c.pureLe _ _ _ trivial
      · exact le_whyRest c k h hk S seen b _ _
    · exact le_whyRest c k h hk S seen b _ _
    · exact le_whyRest c k h hk S seen b _ _

/-! ## The reader and the session's steps -/

theorem le_readChain (S : SpecX) (seen : Seen) (b : ByteArray) (i : Nat) :
    c.le (readChain h S seen b i) (fileNX S * k) fun _ => True :=
  le_readChainM c k h hk Keeper.indexed S seen b i

theorem le_readIn (S : SpecX) (b : ByteArray) (i : Nat) (s : Session) :
    c.le (readIn h S b i s).run (fileNX S * k) fun _ => True := by
  unfold readIn
  simp only [OptionT.run_mk]
  refine c.le_bind _ _ _ 0 _ _ (le_readChain c k h hk _ _ _ _) fun r _ => ?_
  cases r <;> exact c.le_pure _ _ trivial

theorem le_acceptIn {Y : Type} (ch : Chain Y) (y : Y) (b : ByteArray) (i : Nat) (s : Session) :
    c.le (acceptIn h ch y b i s).run (fileNX ch.spec * k) fun _ => True := by
  unfold acceptIn
  simp only [OptionT.run_mk]
  refine c.le_bind _ _ _ 0 _ _ (le_readChain c k h hk _ _ _ _) fun r _ => ?_
  cases r <;> exact c.le_pure _ _ trivial

/-! ## The named reading: on a refusal the chain is gone over a second time -/

open OnBytes.Proof hiding Reading need Reading.fromStart readerName readNamed
open OnBytes.TwoPort.M.Proof

theorem le_readerName (front : String) (S : SpecX) (seen : Seen) (b : ByteArray) (i : Nat) :
    c.le (readerName h front S seen b i) (fileNX S * k) fun _ => True := by
  unfold readerName
  refine c.le_bind _ _ _ 0 _ _ (le_whyRefused c k h hk _ _ _ _) fun r _ => ?_
  cases r <;> exact c.le_pure _ _ trivial

theorem le_readNamed (front : String) (S : SpecX) (b : ByteArray) (i : Nat) (s : Session) :
    c.le (readNamed h front S b i s).run (fileNX S * k + fileNX S * k) fun _ => True := by
  unfold readNamed
  simp only [ExceptT.run_mk]
  refine c.le_bind _ _ _ _ _ _ (le_readIn c k h hk _ _ _ _) fun r _ => ?_
  cases r with
  | some y => exact c.pureLe _ _ _ trivial
  | none => exact c.le_bind _ _ _ 0 _ _ (le_readerName c k h hk _ _ _ _ _) fun _ _ =>
      c.le_pure _ _ trivial

/-! ## The table's key and the check of an entry file -/

/-- The questions for the seeds of a table's record, in units of k. -/
def seedsN (bits count : Nat) : Nat :=
  1 + (Fmt.firstBlock 0 + Fmt.blocksFor (count * (bits * 18 + 36)) + 1) / 2

/-- The questions for a table's key, in units of k. -/
def keyN (s : Params.IndexShape) : Nat := seedsN s.cubeBits s.answers

theorem le_recordSeeds (f : Fld) (name : ByteArray) (bits count : Nat) :
    c.le (recordSeeds h f name bits count) (seedsN bits count * k) fun _ => True := by
  unfold recordSeeds
  refine c.le_mono _ (k + ((Fmt.firstBlock 0 + Fmt.blocksFor (count * (bits * 18 + 36)) + 1) / 2 * k
      + 0)) _ _ _
    (c.le_bind _ _ k _ _ _ (hk _ _ _ _ _) fun first _ =>
      c.le_bind _ _ _ 0 (fun _ => True) _ (c.queryW h k hk _ _ _ _ _ _) fun q _ => ?_)
    (by simp only [seedsN, Nat.add_mul]; omega) fun _ h => h
  cases q <;> exact c.le_pure _ _ trivial

theorem le_tableKey (f : Fld) (cfg : ByteArray) (s : Params.IndexShape)
    (table : Params.TableName) (item : Nat) :
    c.le (tableKey h f cfg s table item) (keyN s * k) fun _ => True := by
  unfold tableKey keyN
  dsimp only
  exact c.le_bind _ _ _ 0 _ _ (le_recordSeeds c k h hk _ _ _ _) fun _ _ => c.le_pure _ _ trivial

/-- The description that `Entry.read` makes depends on what it has read off the file (the further
table). N bounds its number whatever was read. -/
def SpecsBelow (p : Params.Link) (first : Params.TableName) (N : Nat) : Prop :=
  ∀ (further : Params.TableName) (k0 k1 : TableKey) (spec : SpecX),
    ((linkVerify p.link k0 k1).rounds (Entry.start p)).bind (p.describe first further) = some spec →
      fileNX spec ≤ N

theorem le_read (p : Params.Link) (first : Params.TableName) (file : ByteArray) (N : Nat)
    (hN : SpecsBelow p first N) :
    c.le (Entry.read h p first file) ((2 * keyN p.link.table + 2 * N) * k) fun _ => True := by
  unfold Entry.read
  dsimp only
  split
  · exact c.pureLe _ _ _ trivial
  · split
    · exact c.pureLe _ _ _ trivial
    · split
      · exact c.pureLe _ _ _ trivial
      · refine c.le_mono _ (keyN p.link.table * k + (keyN p.link.table * k + (N * k + N * k + 0)))
          _ _ _
          (c.le_bind _ _ _ _ (fun _ => True) _ (le_tableKey c k h hk _ _ _ _ _) fun a0 _ =>
            c.le_bind _ _ _ _ (fun _ => True) _ (le_tableKey c k h hk _ _ _ _ _) fun a1 _ => ?_)
          (by simp only [Nat.add_mul, Nat.two_mul]; omega) fun _ h => h
        split
        · split
          · exact c.pureLe _ _ _ trivial
          · rename_i spec hs
            have hle : fileNX spec * k ≤ N * k := Nat.mul_le_mul_right _ (hN _ _ _ _ hs)
            refine c.le_bind _ _ _ 0 (fun _ => True) _
              (le_fromStart c _ _ fun s =>
                c.le_mono _ _ _ _ _ (le_readNamed c k h hk "" spec file _ s)
                  (Nat.add_le_add hle hle) fun _ h => h) fun r _ => ?_
            cases r <;> exact c.le_pure _ _ trivial
        · exact c.pureLe _ _ _ trivial

theorem le_check (params : ByteArray) (first : Params.TableName) (file : ByteArray) (T : Nat)
    (hT : ∀ p, Params.Link.read params = some p →
      ∃ N, SpecsBelow p first N ∧ 2 * keyN p.link.table + 2 * N ≤ T) :
    c.le (Entry.check h params first file) (T * k) fun _ => True := by
  unfold Entry.check
  split
  · exact c.pureLe _ _ _ trivial
  · rename_i p hp
    obtain ⟨N, hN, hle⟩ := hT p hp
    refine c.le_mono _ ((2 * keyN p.link.table + 2 * N) * k + 0) _ _ _
      (c.le_bind _ _ _ 0 (fun _ => True) _ (le_read c k h hk p first file N hN) fun r _ => ?_)
      (by simpa using Nat.mul_le_mul_right k hle) fun _ h => h
    cases r with
    | error e => exact c.le_pure _ _ trivial
    | ok r =>
      simp only []
      split <;> exact c.le_pure _ _ trivial

end OnBytes.TwoPort.M.RoadCost
