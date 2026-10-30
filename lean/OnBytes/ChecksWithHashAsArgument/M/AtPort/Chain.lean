-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/ChecksWithHashAsArgument/M/AtPort/Chain.lean: the twin over a monad, at the identity monad, is the port's own
text. The chain's level: the second pass, the reader, the reading within a session.
At any hash h the twin is the port's function at h and at the step that h induces (`stepOf h`); at
`formatHashFastForm` it is the function that the program runs.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.ChecksWithHashAsArgument.M.Chain.EngineAtId
import OnBytes.ChecksWithHashAsArgument.M.Chain.Why
import OnBytes.ChecksWithHashAsArgument.M.Chain.Session
import OnBytes.Chain.ReaderLaws
import OnBytes.Hash.HEq
import OnBytes.Hash.QueryEq

set_option autoImplicit false

namespace OnBytes.TwoPort.M.AtPort

open Fmt (Qry Hash Plan St Round Stored SpecX Seen Shape Src Fld)

variable (h : Hash)

theorem tryOpening_id (cfg : ByteArray) (f : Fld) (salt : Nat) (sh : Shape)
    (start root : ByteArray) (xs : List Nat) (b : ByteArray) (i : Nat) (sn : List Rooted) :
    M.tryOpening (m := Id) h cfg f salt sh start root xs b i sn =
      OnBytes.tryOpening h cfg f salt sh start root xs b i sn := by
  unfold M.tryOpening OnBytes.tryOpening
  show (match openingM (m := Id) h cfg f salt sh start xs b i with
    | none => _
    | some o => _) = _
  rw [EngineAtId.openingM_id]
  cases openingF h cfg f salt sh start xs b i with
  | none => rfl
  | some o =>
    dsimp only
    cases Keeper.indexed.add root (Fmt.entered o.seen) sn <;> rfl

theorem tryStored_id (cfg statement : ByteArray) (P : Plan) (poss : List Nat) (b : ByteArray) :
    ∀ (ts : List Stored) (sn : List Rooted) (i : Nat),
      M.tryStored (m := Id) h cfg statement P poss b ts sn i =
        OnBytes.tryStored h cfg statement P poss b ts sn i
  | [], _, _ => rfl
  | t :: ts, sn, i => by
    unfold M.tryStored OnBytes.tryStored
    cases Fmt.itemRoot statement t.item with
    | none => rfl
    | some root =>
      dsimp only
      show (match M.tryOpening (m := Id) h cfg P.field t.salt t.sh cfg root _ b i sn with
        | .error e => _
        | .ok (sn', j) => _) = _
      rw [tryOpening_id]
      cases OnBytes.tryOpening h cfg P.field t.salt t.sh cfg root
          (listOfT ((Fmt.partOf t poss).map (· % 2 ^ t.sh.a))) b i sn with
      | error e => rfl
      | ok y => exact tryStored_id cfg statement P poss b ts y.1 y.2

theorem tryOpens_id (cfg : ByteArray) (P : Plan) (run : Option ByteArray)
    (roots : Array ByteArray) (poss : List Nat) (b : ByteArray) :
    ∀ (os : List (Shape × Src)) (sn : List Rooted) (i : Nat),
      M.tryOpens (m := Id) h cfg P run roots poss b os sn i =
        OnBytes.tryOpens h cfg P run roots poss b os sn i
  | [], _, _ => rfl
  | (sh, src) :: os, sn, i => by
    have key : ∀ (root start : ByteArray),
        (match M.tryOpening (m := Id) h cfg P.field P.salt sh start root
            (listOfT (poss.map (· % 2 ^ sh.a))) b i sn with
          | .error e => (pure (.error e) : Id (Except ReaderCheck (List Rooted × Nat)))
          | .ok (sn', j) => M.tryOpens (m := Id) h cfg P run roots poss b os sn' j) =
        (match OnBytes.tryOpening h cfg P.field P.salt sh start root
            (listOfT (poss.map (· % 2 ^ sh.a))) b i sn with
          | .error e => .error e
          | .ok (sn', j) => OnBytes.tryOpens h cfg P run roots poss b os sn' j) := by
      intro root start
      rw [tryOpening_id]
      cases OnBytes.tryOpening h cfg P.field P.salt sh start root
          (listOfT (poss.map (· % 2 ^ sh.a))) b i sn with
      | error e => rfl
      | ok y => exact tryOpens_id cfg P run roots poss b os y.1 y.2
    unfold M.tryOpens OnBytes.tryOpens
    cases src with
    | own n =>
      dsimp only
      cases roots[n]? with
      | none => rfl
      | some r =>
        cases run with
        | none => rfl
        | some s => exact key r s
    | given r s => exact key r s

theorem whyRound_id (cfg statement : ByteArray) (P : Plan) (run : Option ByteArray)
    (b : ByteArray) (s : StK (List Rooted)) (r : Round) (ts : List Stored) :
    M.whyRound (m := Id) h cfg statement P run b s r ts =
      OnBytes.whyRound (stepOf h) h cfg statement P run b s r ts := by
  unfold M.whyRound OnBytes.whyRound
  dsimp only [stepOf]
  cases Fmt.slice b s.pos r.entry.msg with
  | none => rfl
  | some msg =>
    dsimp only
    cases Fmt.whole (readItemsT P.field r.items) msg with
    | none => rfl
    | some vals =>
      dsimp only
      cases Fmt.readNonce P r.entry.work b (s.pos + r.entry.msg) with
      | none => rfl
      | some x =>
        obtain ⟨nonce, i1⟩ := x
        dsimp only
        show (match Fmt.Chain.queryW (m := Id) h s.chain msg r.kind r.entry.work nonce
            ((Fmt.wordsAtMost r.entry r.kind + 3) / 4) with
          | none => _
          | some (c, vb) => _) = _
        cases Fmt.Chain.queryW (m := Id) h s.chain msg r.kind r.entry.work nonce
            ((Fmt.wordsAtMost r.entry r.kind + 3) / 4) with
        | none => rfl
        | some y =>
          obtain ⟨c, vb⟩ := y
          dsimp only
          cases readListT P r.entry.poss
              (listOfT (drawRoundT P.field r.entry r.kind (Fmt.rowOf vb)).poss) b i1 with
          | none => rfl
          | some z =>
            obtain ⟨_, i2⟩ := z
            dsimp only
            show (match M.tryStored (m := Id) h cfg statement P _ b ts s.kept i2 with
              | .error e => _
              | .ok (sn1, i2') => _) = _
            rw [tryStored_id]
            cases OnBytes.tryStored h cfg statement P
                (drawRoundT P.field r.entry r.kind (Fmt.rowOf vb)).poss b ts s.kept i2 with
            | error e => rfl
            | ok w =>
              obtain ⟨sn1, i2'⟩ := w
              dsimp only
              show (match M.tryOpens (m := Id) h cfg P run _ _ b r.opens sn1 i2' with
                | .error e => _
                | .ok (sn, i3) => _) = _
              rw [tryOpens_id]
              cases OnBytes.tryOpens h cfg P run (s.roots ++ (rootsT vals).toArray)
                  (drawRoundT P.field r.entry r.kind (Fmt.rowOf vb)).poss b r.opens sn1 i2' <;> rfl

theorem whyRounds_id (cfg statement : ByteArray) (P : Plan) (run : Option ByteArray)
    (b : ByteArray) :
    ∀ (rs : List (Round × List Stored)) (s : StK (List Rooted)) (k : Nat),
      M.whyRounds (m := Id) h cfg statement P run b rs s k =
        OnBytes.whyRounds (stepOf h) h cfg statement P run b rs s k
  | [], _, _ => rfl
  | r :: rs, s, k => by
    unfold M.whyRounds OnBytes.whyRounds
    show (match M.whyRound (m := Id) h cfg statement P run b s r.1 r.2 with
      | .ok s' => _
      | .error e => _) = _
    rw [whyRound_id]
    cases OnBytes.whyRound (stepOf h) h cfg statement P run b s r.1 r.2 with
    | error e => rfl
    | ok s' => exact whyRounds_id cfg statement P run b rs s' (k + 1)

theorem whyRest_id (S : SpecX) (seen : Seen) (b : ByteArray) (x : Option ByteArray) (i0 : Nat) :
    M.whyRest (m := Id) h S seen b x i0 = OnBytes.whyRest (stepOf h) h S seen b x i0 := by
  unfold M.whyRest OnBytes.whyRest
  show (match Fmt.startChainW (m := Id) h S.base.label
      (Fmt.paramsDigestW (m := Id) h S.base.params) S.base.statement x with
    | none => _
    | some hd => _) = _
  cases Fmt.startChainW (m := Id) h S.base.label
      (Fmt.paramsDigestW (m := Id) h S.base.params) S.base.statement x with
  | none => rfl
  | some hd => exact whyRounds_id h _ _ _ _ _ _ _ _

theorem whyRefused_id (S : SpecX) (seen : Seen) (b : ByteArray) (i : Nat) :
    M.whyRefused (m := Id) h S seen b i = OnBytes.whyRefusedQ (stepOf h) h S seen b i := by
  unfold M.whyRefused OnBytes.whyRefusedQ
  simp only [whyRest_id]
  split
  · rfl
  · cases S.base.rand with
    | inFile =>
      dsimp only
      cases Fmt.slice b i 32 <;> rfl
    | given x => rfl
    | none => rfl

/-- The step that the program's hash induces is the program's step. -/
theorem step_port : stepOf formatHashFastForm = queryH := by
  rw [queryH_eq_query, formatHashFastForm_eq_formatHash]
  rfl

/-- The second pass. -/
theorem whyRefused_port (S : SpecX) (seen : Seen) (b : ByteArray) (i : Nat) :
    M.whyRefused (m := Id) formatHashFastForm S seen b i = OnBytes.whyRefused S seen b i := by
  rw [whyRefused_id, step_port]
  rfl

/-- The strict reader. -/
theorem readChain_port (S : SpecX) (seen : Seen) (b : ByteArray) (i : Nat) :
    M.readChain (m := Id) formatHashFastForm S seen b i = OnBytes.readChain S seen b i := by
  rw [EngineAtId.readChain_id, readChain_eq, formatHashFastForm_eq_formatHash]

/-- A chain read within a session. -/
theorem readIn_port (S : SpecX) (b : ByteArray) (i : Nat) (s : Session) :
    (M.readIn (m := Id) formatHashFastForm S b i s).run = OnBytes.readIn S b i s := by
  unfold M.readIn OnBytes.readIn
  show (match M.readChain (m := Id) formatHashFastForm S s.seen b i with
    | none => _
    | some (o, j) => _) = _
  rw [readChain_port]
  cases OnBytes.readChain S s.seen b i <;> rfl

end OnBytes.TwoPort.M.AtPort
