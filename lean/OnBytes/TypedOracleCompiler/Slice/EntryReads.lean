-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Slice/EntryReads.lean: the three equations on the page of an entry's judge from which
the clause `reads` of a part follows: what its partial code writes at a vertex query on two digests,
what it writes at a leaf query on a stored symbol, and what its code `back` writes there.

A part owes `reads`: off a log without a clash it reads the one written reading of a stored table
(OnBytes/TypedOracleCompiler/Slice/ShapesRaw.lean: `rawBy`). That reading goes by three strings: a vertex's
(`nodeStr`), a stored leaf's call where there is one (`callStr`), and a string behind the byte 2
elsewhere (`spareStr`). For a page made by OnBytes/TypedOracleCompiler/Run/PageG.lean it is enough that the page's
two codes write these strings. This file shows it for the page of OnBytes/TypedOracleCompiler/Slice/EntryFill.lean,
with stored symbols written into bodies by the sibling's `bodyS` and `back` the total code of
OnBytes/TypedOracleCompiler/Run/PageEBack.lean. The sibling is a second form of the library's soundness road,
under OnBytes/TypedOracleCompiler/.
 - `leafCode_stored`: GENERAL in the interface: on a stored symbol's body `KeyLeaves.leafCode` at a
   file's salt of 8 n bits writes exactly `callStr`: an equation of options: nothing where `callStr`
   is nothing;
 - `realE_node`, `realE_stored`: the page's partial code at a vertex query on two digests, and at a
   leaf query on a stored symbol;
 - `backE2_stored`: the total code `PageEBack.backE2`, at the serialiser of stored symbols that
   every page uses, at a leaf query on a stored symbol: four marks, the symbol's serial form, the
   typed salt's.

Main theorems: `leafCode_stored`, `realE_node`, `realE_stored`, `backE2_stored`.

Not claimed. `reads` itself: it follows from these three with facts on wiring and reading that name
no string; not drawn here. n is the number of BYTES of a file's salt: the page is taken at 8 n bits.
Nothing on soundness. The compiler under OnBytes/TypedOracleCompiler/ is the one that `innerCompiledVerifier` is
made with; it builds on definitions of Compile/.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Slice.EntryFill
import OnBytes.TypedOracleCompiler.Slice.ShapesRaw
import OnBytes.TypedOracleCompiler.Slice.TieEscape
import OnBytes.TypedOracleCompiler.Run.PageEBack
import OnBytes.TypedOracleCompiler.StringsAt

set_option autoImplicit false

noncomputable section

namespace TypedOracleCompiler.Slice.EntryReads
open Rom _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run TypedOracleCompiler.Slice
open TypedOracleCompiler.Slice.EntryFill TypedOracleCompiler.Run.EntryFb TypedOracleCompiler.Run.EntryPage
open TypedOracleCompiler.Run.PageG TypedOracleCompiler.Strings
open TypedOracleCompiler.Run.FirstAnswers (T3)
open TypedOracleCompiler.Run.PQ (XD bodyS)
open OnBytes.Slice (seedEntry)
open _root_.Run.PQ (SgX serW)
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run

/-- On a stored symbol's body the code of leaf queries writes exactly the stored leaf's call: an
equation of options. a: the stored table's depth; n: the bytes of a file's salt; c: any total code
of symbols. -/
theorem leafCode_stored {I X : Type} (L : _root_.Iop.BatchProtocol I X) (a n : ℕ)
    (c : StrCode (ℕ × List UInt64)) (cfg : ByteArray) (y : SgX) (salt : Bits) :
    (KeyLeaves.leafCode L (8 * n) cfg).put ⟨embX a n c y, salt⟩ =
      OnBytes.Slice.Shapes.callStr cfg a n y salt := by
  have hk : leafOK2 L cfg (⟨embX a n c y, salt⟩ : LeafIn (strung L)) =
      (bitsToBytes (salt.take 256) == cfg) := by
    unfold leafOK2
    rw [storedLike_embX]
    rfl
  show (if leafOK2 L cfg (⟨embX a n c y, salt⟩ : LeafIn (strung L)) = true then
    (pLeaf (L := strung L) (8 * n) (pBody ok2)).put ⟨embX a n c y, salt⟩ else none) = _
  unfold OnBytes.Slice.Shapes.callStr
  rw [hk]
  by_cases h1 : (bitsToBytes (salt.take 256) == cfg) = true
  · rw [if_pos h1, if_pos h1]
    show (if salt.length = 256 + 8 * n then
      ((pBody ok2).put (embX a n c y)).map fun m =>
        pre33 ++ (salt.take 256 ++ (m ++ salt.drop 256)) else none) = _
    rw [put_embX, pStored_same]
  · rw [if_neg h1, if_neg h1]

variable {lg s : ℕ} (D : XD) (d₁ : Sd1 lg s) (cfg : ByteArray) (hcfg : cfg.size = 32)
  (pd : Dig 256) (rest : ByteArray) (n : ℕ)
  (back : StrCode (AllPts 256 (D.K + 1) (Ls D d₁)))

/-- The page's data, at a file's salt of n bytes. -/
abbrev pg : Page (Ls D d₁) (D.K + 1) :=
  pageE (pinsE D d₁ cfg hcfg pd rest) (d₁, d₁) (D.K + 1)
    (KeyLeaves.leavesAt (L0 D d₁) (8 * n) cfg) back

/-- The page's partial code at a vertex query on two digests. -/
theorem realE_node (x y : Dig 256) :
    (pg D d₁ cfg hcfg pd rest n back).real.put (.inr (.inl (List.ofFn x, List.ofFn y))) =
      some (OnBytes.Slice.Shapes.nodeStr cfg (x, y)) :=
  pNode_put256 cfg (List.ofFn x) (List.ofFn y) List.length_ofFn List.length_ofFn

/-- The page's partial code at a leaf query on a stored symbol: the stored leaf's call, exactly
where there is one. a: the stored table's depth. -/
theorem realE_stored (a : ℕ) (y : SgX) (salt : Bits) :
    (pg D d₁ cfg hcfg pd rest n back).real.put (.inl ⟨(bodyS a n).embE y, salt⟩) =
      OnBytes.Slice.Shapes.callStr cfg a n y salt :=
  leafCode_stored (L0 D d₁) a n _ cfg y salt

/-- The total code behind the escape at a leaf query on a stored symbol: four marks, the
symbol's serial form, the typed salt's. ss: any serialiser of what stands in the seeds' place. -/
theorem backE2_stored (a : ℕ) (ss : Ser (Sd1 lg s × Sd1 lg s)) (y : SgX) (salt : Bits) :
    (PageEBack.backE2 D (earlyTwo (A := List T3 × List T3) d₁) (seedEntry lg s) ss (bodyS a n)
        (Ser.prod Ser.natG (Ser.list serW))).put (.inl (.inl ⟨(bodyS a n).embE y, salt⟩)) =
      false :: false :: true :: false ::
        ((Ser.prod Ser.natG (Ser.list serW)).put y ++ serBits.put salt) := by
  show (TypedOracleCompiler.Run.backP _ _ _).put _ = _
  rw [PQ.backP_leaf]
  show false :: false :: (PQ.tiePut (bodyS a n) _ serBits ((bodyS a n).embE y) ++ _) = _
  rw [PQ.tiePut_some (bodyS a n) _ serBits ((bodyS a n).get_e y)]
  rfl

end TypedOracleCompiler.Slice.EntryReads
