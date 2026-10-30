-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/K/Arm/CallInj.lean: the two makers of a chain's calls in the page of a file with three
joined chains are one to one (a row's at one kind, work and order of the blocks; a first call's at
digests of one size), and their calls are told apart by number, tree and index.

OnBytes/Maker/Page/Frame.lean makes the call of a typed block of a round's row (`rowCall`) and the
call that makes a chain's first value (`firstCall`). Here equal calls are shown to have equal
arguments, under the bounds that OnBytes/K/Arm/StrInj.lean names; each maker's tree and index are
stated; and the two makers' numbers are shown to differ.

Main names:
  `rowCall_fields`, `firstCall_fields`: tree and index of a call, by the makers' own text.
  `rowCall_place`: equal calls of two rows have one label and one index; no premise.
  `rowCall_inj`: at one kind, one number of bits of work and one order of the blocks: label, index,
    chain value, message, nonce and block.
  `firstCall_inj`: at digests of parameter bytes of one size: label, digest, statement, run's value.
  `rowCall_ne_firstCall`: a row's call is no first call.

Limits: calls alone: for strings see `strOf_inj`. No typed query occurs here. Nothing on any hash.
Nothing on soundness. For proofs only; the program does not import this file.

Terms: lean/GLOSSARY.md.


-/
import OnBytes.K.Arm.StrInj
import OnBytes.Maker.Page.Frame

set_option autoImplicit false

namespace OnBytes.K.Arm
open _root_.Run OnBytes.Maker.Page

/-- Tree and index of a row's call. -/
theorem rowCall_fields (lab idx : Nat) (ρ : List Bool) (msg : ByteArray)
    (kind work nonce ow K : Nat) (j : Fin (K + 1)) :
    (rowCall lab idx ρ msg kind work nonce ow K j).tree = lab ∧
      (rowCall lab idx ρ msg kind work nonce ow K j).index = idx := ⟨rfl, rfl⟩

/-- Tree and index of a first call. -/
theorem firstCall_fields (lab : Nat) (pd stm : ByteArray) (run : List Bool) :
    (firstCall lab pd stm run).tree = 0 ∧ (firstCall lab pd stm run).index = lab := ⟨rfl, rfl⟩

/-- Equal calls of two rows have one label and one index. -/
theorem rowCall_place {lab lab' idx idx' kind kind' work work' nonce nonce' ow ow' K : Nat}
    {ρ ρ' : List Bool} {msg msg' : ByteArray} {j j' : Fin (K + 1)}
    (e : rowCall lab idx ρ msg kind work nonce ow K j =
      rowCall lab' idx' ρ' msg' kind' work' nonce' ow' K j') : lab = lab' ∧ idx = idx' :=
  ⟨congrArg Fmt.OQ.tree e, congrArg Fmt.OQ.index e⟩

/-- **A row's call**, at one kind, one number of bits of work and one order of the blocks. -/
theorem rowCall_inj {lab lab' idx idx' kind work nonce nonce' ow K v v' : Nat}
    {ρ ρ' : List Bool} {msg msg' : ByteArray} {j j' : Fin (K + 1)}
    (hρ : whole ρ = true) (hρ' : whole ρ' = true)
    (hv : kwcTo kind work (blockNo ow K j / 2) = some v)
    (hv' : kwcTo kind work (blockNo ow K j' / 2) = some v')
    (hn : nonce < 2 ^ 64) (hn' : nonce' < 2 ^ 64)
    (e : rowCall lab idx ρ msg kind work nonce ow K j =
      rowCall lab' idx' ρ' msg' kind work nonce' ow K j') :
    lab = lab' ∧ idx = idx' ∧ ρ = ρ' ∧ msg = msg' ∧ nonce = nonce' ∧ j = j' :=
  rowForm_inj hρ hρ' hv hv' hn hn' e

/-- **A first call.** -/
theorem firstCall_inj {lab lab' : Nat} {pd pd' stm stm' : ByteArray} {run run' : List Bool}
    (hp : pd.size = pd'.size) (hs : stm.size < 2 ^ 64) (hs' : stm'.size < 2 ^ 64)
    (hw : whole run = true) (hw' : whole run' = true)
    (e : firstCall lab pd stm run = firstCall lab' pd' stm' run') :
    lab = lab' ∧ pd = pd' ∧ stm = stm' ∧ run = run' :=
  firstForm_inj hp hs hs' hw hw' e

/-- A row's call is no first call: their numbers differ. -/
theorem rowCall_ne_firstCall (lab idx : Nat) (ρ : List Bool) (msg : ByteArray)
    (kind work nonce ow K : Nat) (j : Fin (K + 1)) (lab' : Nat) (pd stm : ByteArray)
    (run : List Bool) :
    rowCall lab idx ρ msg kind work nonce ow K j ≠ firstCall lab' pd stm run := by
  intro e
  have h := congrArg Fmt.OQ.number e
  exact absurd h (by simp [rowCall, firstCall])

end OnBytes.K.Arm
