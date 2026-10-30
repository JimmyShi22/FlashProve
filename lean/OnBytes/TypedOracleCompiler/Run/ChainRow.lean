-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Run/ChainRow.lean.
TWO: CUT BY PROGRAM out of the library's Run/ChainRow.lean (only what the entry's clause holds and
stands on a declaration that the sibling says again), then turned by hand where it had to be. THE
HEAD BELOW IS THE LIBRARY's AND SPEAKS OF THE LIBRARY's FILE: much of what it announces IS NOT HERE,
and what it says of "one root | one tree a round" is not true of this file. HERE STAND ONLY:
famB_row.

Run/ChainRow.lean: THE TYPED ANSWER TO A ROUND'S CHAIN QUERY, AT THE TYPED ORACLE FUNCTIONS THAT A
FUNCTION O ON THE FORMAT'S STRINGS INDUCES, IS THE FORMAT PAGE'S ROW OF BLOCKS OF THAT ROUND AT THE
HASH OVER O: GENERIC IN ALL DATA. Theorems and proofs. The page: R5.2, R5.4; this file has not been
held against the page as it ships, and may differ from it.

FOR EVERY O WHOSE ANSWERS HAVE 32 BYTES, every interface, spellings D, number of blocks K, round i +
1.
    extract_l, extract_r     the two halves of "x, then y"
    blockW_HO            a block of the page's row at the hash over O (Fmt/Rules5Row.lean: blockW;
                         Fmt/Rules23.lean: HO): O at the string of its half of its call
    roundBytes_tail          the bytes of a call as Run/CodingFn.lean writes them are the message
                             and the page's two words
    blockNo_last, blockNo_test, blockNo_msg0, blockNo_msgW, blockNo_le WHERE THE TYPED BLOCKS STAND
    IN THE PAGE'S ROW: the chain value at (first block of the verifier's message) - 1; with work:
    typed block 0 is the test block, typed block k + 1 is block k of the verifier's message; without
    work: typed block k is block k of the verifier's message famB_row, famB_fetch the typed blocks
    as bytes (Run/CodingFnThin.lean: famB) are the page's blocks at these places; the same against
    the array that the page fetches
    size_blockW_HO, digToBytes_digS;  famP_row      famP's typed answer, as bytes
WHAT IS NOT SAID.  Round 0.  The test bits, the draw: Run/PageIsChain.lean.  Nothing on soundness.

Terms: lean/GLOSSARY.md.

-/
import Run.ChainRow
-- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.CodingFnTag
-- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.CodingFn
-- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.CodingPage160
-- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.CodingPage164
import OnBytes.TypedOracleCompiler.Run.ParseBS  -- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.CodingFnThin
import Fmt.Rules5Row
import Fmt.Rules1Laws
import OnBytes.TypedOracleCompiler.Run.Toy1TieTree

set_option autoImplicit false

namespace TypedOracleCompiler.Run
open _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop Rom
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run
export _root_.Run (extract_l extract_r blockW_HO roundBytes_tail blockNo_last blockNo_msg0
    blockNo_test blockNo_msgW blockNo_le size_blockW_HO digToBytes_digS)

/-! ## Where the typed blocks stand in the page's row -/

variable {I X : Type} (Lf : Unit → BatchProtocolWithLeafBody I X) {tg : Tag}

/-- THE TYPED BLOCKS OF A ROUND'S CHAIN ANSWER ARE THE PAGE'S BLOCKS, at the places that blockNo
names -/
theorem famB_row (O : ByteArray → ByteArray) (hO : ∀ x, (O x).size = 32) (D : PageD (Lf ()) tg)
    (K : ℕ) (i : ℕ) (ρ : List Bool) (rt : List (Dig 256))
    (pl : PlainPart (shapeOf (Lf ()) tg) (annOf (Lf ()) tg)) (kind : _root_.Fmt.Kind)
    (hk : kind.num = D.kind (i + 1)) (j : Fin (K + 1)) :
    (famB Lf O D K (.fb tg) (⟨i + 1, .f2 none ρ, rt, pl⟩ : FbIn 256 (Lf ()) tg)).getD
        j.val ByteArray.empty =
      _root_.Fmt.blockW (_root_.Fmt.HO O) D.label (bitsToBytes ρ) (i + 1)
        (D.msg (i + 1) (rt.map digToBytes) pl) kind (D.work (i + 1))
        (D.nonce (i + 1) pl) (blockNo (D.work (i + 1)) K j) := by
  have e : famB Lf O D K (.fb tg) (⟨i + 1, .f2 none ρ, rt, pl⟩ : FbIn 256 (Lf ()) tg) =
      Array.ofFn (n := K + 1) fun j =>
        bytesP O (fbCallP Lf D K (⟨i + 1, .f2 none ρ, rt, pl⟩ : FbIn 256 (Lf ()) tg) j) := by
    simp only [famB, castTag_self]
    rfl
  rw [e, Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, dif_pos j.isLt,
    blockW_HO O hO, ← roundBytes_tail, hk]
  rfl

end TypedOracleCompiler.Run
