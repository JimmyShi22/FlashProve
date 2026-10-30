-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K14/FiveFieldsThru.lean: the linear claim's shared rounds (kind K14):
THE FIVE FACTS ON THE COMMITTED TABLE AND ITS KEY (FiveFields, Honest/K14/FiveFields.lean) CARRY
OVER WHEN THE TWO READERS OF THE PROVER's INPUT ARE COMPOSED WITH MAPS. One theorem: from the
structure at readers `weights`, `rand` to the structure at the readers composed with maps g, rd on
the index and on the committer's randomness, where "valid" and the stored table are read through the
same two maps (Common.thru, Honest/Thru.lean).

Why. The library shows the structure where the index is the matrix itself
(Johnson/Bind/ForProver/FiveFieldsAt.lean). A prover whose index has another type reads the matrix
off it by a function: this theorem carries the structure there.

NOT IN FRONT OF A LAW OVER COINS (the rule: Johnson/Bind/ForProver/FiveFieldsAt.lean's head). The
ground: the premise F is the structure at the letters valid and stored, and each of its five fields
begins "at every valid input": where valid reads the key, it ties the key to the coins (the first
kind of premise). The conclusion keeps both letters, read through the two maps. No lemma here shows
valid at the input that the committer makes, nor stored to be the made table: the bar is flat.

What is not claimed. That the structure holds at any parameters. Nothing on completeness, soundness
or hiding.
-/
import Johnson.Desc.ProofFile.Honest.Thru
import Johnson.Desc.ProofFile.Honest.K14.FiveFields

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open OnBytes (TableKey)
open Desc.K14 (P14)

/-- **FiveFields, read through g and rd.** Each field is the field of F at the input read through:
the key stays, and the rows that the fields name read the input through the two readers alone.
NOT IN FRONT OF A LAW OVER COINS: valid and stored stay letters (the file's head). -/
theorem fiveFields_thru {W₀ W₀' Rc Rc' : Type} (g : W₀' → W₀) (rd : Rc' → Rc) {Q : P14}
    {valid : Common W₀ Rc TableKey → Prop}
    {stored : Common W₀ Rc TableKey → ℕ → ℕ → Option (List UInt64)} {weights : W₀ → Weights}
    {rand : Rc → TableRand} (F : FiveFields Q valid stored weights rand) :
    FiveFields Q (fun v => valid (Common.thru g rd v)) (fun v => stored (Common.thru g rd v))
      (weights ∘ g) (rand ∘ rd) where
  cols w hw := F.cols (Common.thru g rd w) hw
  tab w hw := F.tab (Common.thru g rd w) hw
  key w hw := F.key (Common.thru g rd w) hw
  seeds w hw := F.seeds (Common.thru g rd w) hw
  ans w hw := F.ans (Common.thru g rd w) hw

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.fiveFields_thru
