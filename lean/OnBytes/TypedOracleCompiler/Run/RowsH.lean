-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Run/RowsH.lean: AT THE FORMAT's REALISED ORACLE THE HASH MADE OF THE ORACLE IS THE
FORMAT's OWN HASH, WITHIN ITS DOMAIN: so the values of OnBytes/TypedOracleCompiler/Run/RowsG.lean, at g := the
library's `oBits`, are calls of
`Fmt.formatHash`, which compute.

WHY. RowsG.lean says, at EVERY oracle g on bit strings, that a page's typed family answers with the
hash `hOfG g := Fmt.HO (oB (g ()))` at a row's call. A guard by evaluation, and the tie to the
program, stand at ONE g: the format's realised oracle on bits (library, Run/OracleBits.lean:
`oBits`). There the library has: on the domain the hash over the realised oracle is the direct call
  (Fmt/Rules23Laws.lean:
`HO_oracle`), on byte strings. This file carries that to `hOfG oBits`.

 - `plain_oStr`: the bits of a call's string, of half 0 or 1, are whole bytes whose first byte is
   not the escape 4; `oB_oBits`: so the oracle on bytes that `oBits` induces is the format's
   realised oracle there;
 - `hOfG_oBits`: `Fmt.hDom n t i st bs = true → hOfG oBits n t i st bs = Fmt.formatHash n t i st bs`;
 - `first_oBits`: the first value at `hOfG oBits` is the hash under 160, within the domain;
 - `blockW_oBits`: block b of a round's row at `hOfG oBits` is the format's own `Fmt.block`, if the
   call (b div 2) lies in the domain.

Main theorems: `oB_oBits`, `hOfG_oBits`, `blockW_oBits`.

WHAT IS NOT SAID. THAT ANY ROW's CALL LIES IN THE DOMAIN: `Fmt.hDom` is a hypothesis, a Bool that
computes.
Outside the domain the two differ. Nothing on the hash's text. Nothing on soundness. The sibling is
a second form of the library's soundness road, under OnBytes/TypedOracleCompiler/.
The compiler under OnBytes/TypedOracleCompiler/ is the one that `innerCompiledVerifier` is made with; it builds on
definitions of Compile/.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Run.RowsG
import Run.OracleBits
import Fmt.Rules23Laws

set_option autoImplicit false

namespace TypedOracleCompiler.Run.RowsH
open Rom _root_.Compile TypedOracleCompiler.Run TypedOracleCompiler.Run.RowsG
open _root_.Run

/-- The bits of a call's string, of a half other than 4, are whole bytes whose first byte is not the
escape. -/
theorem plain_oStr (half : UInt8) (hh : (4 : UInt8) ≠ half) (n t i : ℕ) (st bs : ByteArray) :
    plainB (bytesToBits (_root_.Fmt.oStr half n t i st bs)) = true := by
  unfold plainB
  rw [Bool.and_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne]
  refine ⟨(whole_iff _).2 ⟨_, length_bytesToBits _⟩, fun h => ?_⟩
  have hp : bitsOfByte 4 <+: bytesToBits (_root_.Fmt.oStr half n t i st bs) := by
    rw [← h]
    exact List.take_prefix _ _
  rw [oStr_bits] at hp
  exact hdr_not_prefix 4 half hh _ _ _ _ _ hp

/-- The oracle on bytes that the realised oracle on bits induces is the format's realised oracle,
at a call's string of a half other than 4. -/
theorem oB_oBits (half : UInt8) (hh : (4 : UInt8) ≠ half) (n t i : ℕ) (st bs : ByteArray) :
    oB (oBits ()) (_root_.Fmt.oStr half n t i st bs) =
      _root_.Fmt.oracle (_root_.Fmt.oStr half n t i st bs) := by
  show digToBytes (oBits () (bytesToBits (_root_.Fmt.oStr half n t i st bs))) = _
  rw [oBits_bytes _ (plain_oStr half hh n t i st bs)]
  exact TieTree.dig_bytes _ (_root_.Fmt.size_oracle _)

/-- WITHIN THE DOMAIN THE HASH MADE OF THE REALISED ORACLE ON BITS IS THE FORMAT's OWN HASH. -/
theorem hOfG_oBits (n t i : ℕ) (st bs : ByteArray) (hd : _root_.Fmt.hDom n t i st bs = true) :
    hOfG oBits n t i st bs = _root_.Fmt.formatHash n t i st bs := by
  rw [← _root_.Fmt.HO_oracle n t i st bs hd]
  show _root_.Fmt.HO (oB (oBits ())) n t i st bs = _
  unfold _root_.Fmt.HO
  split
  · rw [oB_oBits 0 (by decide), oB_oBits 1 (by decide)]
  · rw [oB_oBits 0 (by decide)]

/-- The first value at the hash made of the realised oracle is the hash under 160, within the
domain.
-/
theorem first_oBits (lab : ℕ) (pd st rec : ByteArray) (run : Option ByteArray)
    (hd : _root_.Fmt.hDom 160 0 lab _root_.Fmt.zero32
        (_root_.Fmt.firstBytes pd st rec run) = true) :
    Id.run (_root_.Fmt.firstValueW (m := Id) (hOfG oBits) lab pd st rec run) =
      _root_.Fmt.formatHash 160 0 lab _root_.Fmt.zero32 (_root_.Fmt.firstBytes pd st rec run) :=
  hOfG_oBits 160 0 lab _ _ hd

/-- Block b of a round's row at the hash made of the realised oracle is the format's own block, if
the call (b div 2) lies in the domain. -/
theorem blockW_oBits (lab : ℕ) (rho : ByteArray) (i : ℕ) (msg : ByteArray) (kind : _root_.Fmt.Kind)
    (w nonce b : ℕ)
    (hd : _root_.Fmt.hDom 162 lab i rho (msg ++ _root_.Fmt.tail kind w nonce (b / 2)) = true) :
    _root_.Fmt.blockW (hOfG oBits) lab rho i msg kind w nonce b =
      _root_.Fmt.block lab rho i msg kind w nonce b := by
  show (hOfG oBits 162 lab i rho (msg ++ _root_.Fmt.tail kind w nonce (b / 2))).extract _ _ =
    (_root_.Fmt.formatHash 162 lab i rho (msg ++ _root_.Fmt.tail kind w nonce (b / 2))).extract _ _
  rw [hOfG_oBits _ _ _ _ _ hd]

end TypedOracleCompiler.Run.RowsH
