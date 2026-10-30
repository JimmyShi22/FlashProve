-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Chain/Step.lean: the strict reader's text with the chain's step as an argument.

The strict reader, `Fmt.readChainX`, reads one chain's bytes and refuses what breaks a rule of the
format (OnBytes/Base.lean). It takes the hash as an argument and computes each hash call of a
round's query from the first of the hashed bytes. A round's calls differ only in their last 16
bytes, so a program should hash the round's message once. To allow that, this file states the
reader's text once more, at the identity monad, with two arguments: the step of a chain (a round's
whole query) and the hash for everything else.

Main definitions: `roundQ`, `foldRoundsQ`, `restQ`, `readChainQ`.
Main theorems: `readChainQ_eq`: at the format's own step and hash this text is `Fmt.readChainX`.
-/
import Fmt.Rules8X
import Fmt.Rules8Fast

namespace OnBytes

open Fmt (Qry Hash Plan St Round Stored SpecX Seen ChainOut)

/-- One round: the message, the nonce, the round's query with the test of work, the draws, the
listed positions, the openings of stored trees, the openings of the round's other trees (the
chain's own, and trees given from outside by root and start: `Fmt.Src`). The verifier derives the
positions itself. The listed ones are only compared with the list derived, and no byte is read
for them where the plan lists none (posB = 0) or the round draws none. In a description that is
in order a round opens stored trees or other trees, not both (`Fmt.storedOk`). -/
def roundQ (qry : Qry) (h : Hash) (cfg statement : ByteArray) (P : Plan) (run : Option ByteArray)
    (b : ByteArray) (s : St) (r : Round) (ts : List Stored) : Option St :=
  match Fmt.slice b s.pos r.entry.msg with
  | none => none
  | some msg =>
    match Fmt.whole (Fmt.readItems P.field r.items) msg with
    | none => none
    | some vals =>
      match Fmt.readNonce P r.entry.work b (s.pos + r.entry.msg) with
      | none => none
      | some (nonce, i1) =>
        match qry s.chain msg r.kind r.entry.work nonce
            ((Fmt.wordsAtMost r.entry r.kind + 3) / 4) with
        | none => none
        | some (c, vb) =>
          let drawn := Fmt.drawRound P.field r.entry r.kind (Fmt.rowOf vb)
          let l := Fmt.listOf drawn.poss
          match Fmt.readList P r.entry.poss l b i1 with
          | none => none
          | some (_, i2) =>
            let roots := s.roots ++ (Fmt.rootsOf vals).toArray
            match Fmt.readStored (m := Id) h cfg statement P drawn.poss b ts s.seen i2 with
            | none => none
            | some (colsS, sn1, i2') =>
              match Fmt.readOpens (m := Id) h cfg P run roots drawn.poss b r.opens sn1 i2' with
              | none => none
              | some (cols, sn, i3) =>
                some ⟨i3, c, roots, sn, s.out.push ⟨msg, vals, nonce, drawn, l, colsS ++ cols⟩⟩

/-- All rounds, one after the other. Each comes with the stored trees that it opens. -/
def foldRoundsQ (qry : Qry) (h : Hash) (cfg statement : ByteArray) (P : Plan)
    (run : Option ByteArray) (b : ByteArray) : List (Round × List Stored) → St → Option St
  | [], s => some s
  | r :: rs, s =>
    match roundQ qry h cfg statement P run b s r.1 r.2 with
    | none => none
    | some s' => foldRoundsQ qry h cfg statement P run b rs s'

/-- What follows the chain's random bytes x: the chain's first value is computed, then the rounds
are read from byte i0 on. -/
def restQ (qry : Qry) (h : Hash) (S : SpecX) (seen : Seen) (b : ByteArray)
    (x : Option ByteArray) (i0 : Nat) : Option (ChainOut × Nat) :=
  match Fmt.startChainW (m := Id) h S.base.label (Fmt.paramsDigestW (m := Id) h S.base.params)
      S.base.statement x with
  | none => none
  | some hd =>
    match foldRoundsQ qry h S.base.cfg S.base.statement S.base.plan hd.run b
        (S.base.rounds.zip S.stored) ⟨i0, ⟨S.base.label, hd.rho0, 0⟩, #[], seen, #[]⟩ with
    | none => none
    | some s =>
      some (⟨Fmt.paramsDigestW (m := Id) h S.base.params, hd.run, hd.rho0, s.chain.rho, s.seen,
        s.out⟩, s.pos)

/-- Reads the chain with the description S that begins at byte i of b. Returns what was read and
the place after the chain. Returns none if the description is not in order (`Fmt.SpecX.ok`),
whatever the bytes, or if the bytes break a rule of the format. -/
def readChainQ (qry : Qry) (h : Hash) (S : SpecX) (seen : Seen) (b : ByteArray) (i : Nat) :
    Option (ChainOut × Nat) :=
  if !S.ok then none
  else
    match S.base.rand with
    | .inFile =>
      match Fmt.slice b i 32 with
      | none => none
      | some x => restQ qry h S seen b (some x) (i + 32)
    | .given x => restQ qry h S seen b (some x) i
    | .none => restQ qry h S seen b none i

/-- At the format's own step and hash `roundQ` equals `Fmt.roundX` at the identity monad. -/
theorem roundQ_eq (cfg statement : ByteArray) (P : Plan) (run : Option ByteArray) (b : ByteArray)
    (s : St) (r : Round) (ts : List Stored) :
    roundQ Fmt.Chain.query Fmt.formatHash cfg statement P run b s r ts =
      Fmt.roundX (m := Id) Fmt.formatHash cfg statement P run b s r ts := by
  unfold roundQ Fmt.roundX
  cases Fmt.slice b s.pos r.entry.msg with
  | none => rfl
  | some msg =>
    dsimp only
    cases Fmt.whole (Fmt.readItems P.field r.items) msg with
    | none => rfl
    | some vals =>
      dsimp only
      cases Fmt.readNonce P r.entry.work b (s.pos + r.entry.msg) with
      | none => rfl
      | some x => rfl

/-- At the format's own step and hash `foldRoundsQ` equals `Fmt.foldRoundsX` at the identity
monad. -/
theorem foldRoundsQ_eq (cfg statement : ByteArray) (P : Plan) (run : Option ByteArray)
    (b : ByteArray) : ∀ (rs : List (Round × List Stored)) (s : St),
    foldRoundsQ Fmt.Chain.query Fmt.formatHash cfg statement P run b rs s =
      Fmt.foldRoundsX (m := Id) Fmt.formatHash cfg statement P run b rs s
  | [], _ => rfl
  | r :: rs, s => by
    unfold foldRoundsQ Fmt.foldRoundsX
    rw [roundQ_eq]
    show _ = (match Fmt.roundX (m := Id) Fmt.formatHash cfg statement P run b s r.1 r.2 with
      | none => none
      | some s' => Fmt.foldRoundsX (m := Id) Fmt.formatHash cfg statement P run b rs s')
    cases Fmt.roundX (m := Id) Fmt.formatHash cfg statement P run b s r.1 r.2 with
    | none => rfl
    | some s' => exact foldRoundsQ_eq cfg statement P run b rs s'

/-- At the format's own step and hash `restQ` equals the part of `Fmt.readChainX` that follows the
chain's random bytes. -/
theorem restQ_eq (S : SpecX) (seen : Seen) (b : ByteArray) (x : Option ByteArray) (i0 : Nat) :
    restQ Fmt.Chain.query Fmt.formatHash S seen b x i0 =
      (match Fmt.startChainW (m := Id) Fmt.formatHash S.base.label
          (Fmt.paramsDigestW (m := Id) Fmt.formatHash S.base.params) S.base.statement x with
      | none => none
      | some hd =>
        match Fmt.foldRoundsX (m := Id) Fmt.formatHash S.base.cfg S.base.statement S.base.plan hd.run b
            (S.base.rounds.zip S.stored) ⟨i0, ⟨S.base.label, hd.rho0, 0⟩, #[], seen, #[]⟩ with
        | none => none
        | some s =>
          some (⟨Fmt.paramsDigestW (m := Id) Fmt.formatHash S.base.params, hd.run, hd.rho0, s.chain.rho,
            s.seen, s.out⟩, s.pos)) := by
  unfold restQ
  cases Fmt.startChainW (m := Id) Fmt.formatHash S.base.label
      (Fmt.paramsDigestW (m := Id) Fmt.formatHash S.base.params) S.base.statement x with
  | none => rfl
  | some hd =>
    dsimp only
    rw [foldRoundsQ_eq] <;> rfl

/-- At the format's own step and hash the text of this file is the strict reader. -/
theorem readChainQ_eq (S : SpecX) (seen : Seen) (b : ByteArray) (i : Nat) :
    readChainQ Fmt.Chain.query Fmt.formatHash S seen b i = Fmt.readChainX (m := Id) Fmt.formatHash S seen b i := by
  unfold readChainQ Fmt.readChainX
  cases !S.ok with
  | true => rfl
  | false =>
    rw [if_neg Bool.false_ne_true, if_neg Bool.false_ne_true]
    cases S.base.rand with
    | inFile =>
      dsimp only
      cases Fmt.slice b i 32 with
      | none => rfl
      | some x => exact restQ_eq S seen b (some x) (i + 32)
    | given x => exact restQ_eq S seen b (some x) i
    | none => exact restQ_eq S seen b none i

end OnBytes
