-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Send/Front.lean: THE SHARED "SENDING" (the kind K1), THE PROVER's SIDE: the few names
that its laws are stated with. Definitions alone; no theorem is stated.

  SendFront P d   what the carried record and the place must meet in front of a sending: four
                  clauses, none on a value that is sent or drawn
  numbers         the numbers that the new messages get
  answersAt       the answers of message number k alone, as answers (Core.lean) writes them
  Rows.mainTl     a main row's tail, in E
  skipMain, skipMask   the words of a leaf in front of a part's main symbols, and of its mask
                  symbols: as the description's reader of a column counts them
                  (Own.symbolsAt, Johnson/Desc/Own/Symbols.lean)

The record behind a sending has a name already: K1.behind (Johnson/Desc/K1/Law/Writes3.lean); a
message behind it: K1.wr (Johnson/Desc/K1/Law/Writes.lean); the answers of the messages in front of
message number k: K1.offset (Johnson/Desc/K1/Law/Targets2.lean). No second name is given here.
Nothing on what any entry discloses or does not disclose.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Send.Held
import Johnson.Desc.K1.Law.Targets2

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Prover.Send
open OnBytes OnBytes.Slice OnBytes.Means Cb VerifiableInference.Desc
open _root_.Desc.Plain (DState)

/-- **What stands in front of a sending.** It does not ask Codes.lengthsOk: SendFront.of_lengths
(Form.lean) goes from it to SendFront, not back. On rule (1) of Core.lean's head: at a length that
is no power of two K1's row reads the pad at a place where (1) lays 0. -/
structure SendFront {L : Type} (P : K1.Par) (d : DState L) : Prop where
  /-- the record's codes are the plan's -/
  codes : d.st.codes = P.codes
  /-- the kind's own tests on the plan -/
  plan : K1.planOkOwn P = true
  /-- statement and book are in step -/
  step : d.st.oracles.size = d.book.place.size
  /-- the statement's page finds the pad's places of every sampled message -/
  pads : ∀ s ∈ P.tuple, (Own.padMade P.codes s).isSome = true

/-- The new messages' numbers. -/
def numbers (P : K1.Par) (first : ℕ) : Array ℕ := (Array.range P.sent.size).map (· + first)

/-- The answers of message number k. Where seeds has no entry number i, seeds.getD i default is
read; nothing refuses here. -/
def answersAt (P : K1.Par) (S' : Statement) (first : ℕ) (w' : Words GE)
    (seeds : List (List E × E)) (k : ℕ) : List Fmt.Ext3 :=
  (List.range (shapeAt P k).answers).map fun i =>
    ofE (value rdE S'
      (K1.sampleRow (K1.Msg.of P.codes (shapeAt P k)) (first + k) (seeds.getD i default).1
        (seeds.getD i default).2 i zeroE) w')

/-- A main row's tail, in E. -/
def Rows.mainTl (R : Rows) (overE : Bool) (r q : ℕ) : GE :=
  if overE then R.mainTlE r q else algebraMap GF GE (R.mainTlF r q)

/-- The words of a leaf in front of part p's main symbols. -/
def skipMain (T : TreeShape) (p : ℕ) : ℕ := (T.mainSymbols.extract 0 p).foldl (· + ·) 0

/-- The words of a leaf in front of part p's mask symbols. -/
def skipMask (T : TreeShape) (p : ℕ) : ℕ :=
  T.mainWidth + (T.maskSymbols.extract 0 p).foldl (· + ·) 0

end Johnson.Prover.Send
