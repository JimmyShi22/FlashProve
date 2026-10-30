-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/ConfLetters.lean: the configurations (`Hiop.ConfigurationWithOutOfDomainSample`, Hiop/RecConf.lean)
whose words have length 2 ^ a over the alphabet of a stored table (`SgX`, Run/PlanQX.lean).
Definitions alone.

  `ConfLetters a`: a configuration's fields but for the word length and the alphabet.
  `ConfLetters.conf`: the configuration.
A protocol of the makers of this folder reads stored tables of that kind. At `K.conf` the word
length and the alphabet are 2 ^ a and `SgX` by unfolding, so such a protocol types there without a
cast.


-/
import Hiop.RecConf
import Run.PlanQX

set_option autoImplicit false

namespace OnBytes.Maker

open Iop Hiop _root_.Run _root_.Run.PQ

/-- **A configuration's fields but for the word length and the alphabet.** -/
structure ConfLetters (a : ℕ) where
  /-- indices, instances, cells, the indexed relation and its relaxation: the model's side -/
  I     : Type
  X     : Type
  Cells : Type
  Ryes  : I → X → Cells → Prop
  Rno   : I → X → Cells → Prop
  /-- messages, encoding randomness, encoding of a stored table: the code's side -/
  Msg   : Type
  Rnd   : Type
  [finRnd : Fintype Rnd]
  [neRnd  : Nonempty Rnd]
  enc   : Msg → Rnd → (Fin (2 ^ a) → SgX)
  /-- the pads, and how a message holds an index: the committer's side -/
  Pad   : Type
  [finPad : Fintype Pad]
  [nePad  : Nonempty Pad]
  hold  : I → Pad → Msg
  held  : Msg → Option I
  /-- the record phase: seeds, answers, collisions, decoding with the record -/
  Seed  : Type
  [finSeed : Fintype Seed]
  [neSeed  : Nonempty Seed]
  Ans   : Type
  smp   : Seed → Msg → Ans
  coll  : (Fin (2 ^ a) → SgX) → Seed → Prop
  dcd   : (Fin (2 ^ a) → SgX) → Seed × Ans → Option Msg
  /-- the honest prover's cells, and a fixed value -/
  trace : I → X → Cells
  cells0 : Cells

/-- The configuration: words of length 2 ^ a over `SgX`. -/
@[reducible] def ConfLetters.conf {a : ℕ} (K : ConfLetters a) : ConfigurationWithOutOfDomainSample where
  I := K.I
  X := K.X
  Cells := K.Cells
  Ryes := K.Ryes
  Rno := K.Rno
  n := 2 ^ a
  Sg := SgX
  Msg := K.Msg
  Rnd := K.Rnd
  finRnd := K.finRnd
  neRnd := K.neRnd
  enc := K.enc
  Pad := K.Pad
  finPad := K.finPad
  nePad := K.nePad
  hold := K.hold
  held := K.held
  Seed := K.Seed
  finSeed := K.finSeed
  neSeed := K.neSeed
  Ans := K.Ans
  smp := K.smp
  coll := K.coll
  dcd := K.dcd
  trace := K.trace
  cells0 := K.cells0

end OnBytes.Maker
