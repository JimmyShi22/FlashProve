-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Slice/TieEscape.lean: across the two families of typed oracles: the sibling's encoding
and the library's spell vertices and stored leaves alike, at EVERY salt, the strings behind the
escape among them. The compiler under OnBytes/TypedOracleCompiler/ is the one that `innerCompiledVerifier` is made
with; it builds on definitions of Compile/.

"The line": the files of OnBytes/Slice/ and OnBytes/Tie/, over the library's compiler. "The
sibling": the files of OnBytes/TypedOracleCompiler/: the library's compiler said again, with a list of roots in a
query and a leaf's body of a type that the interface chooses.

WHY. A part's raw string is read off a log of the one oracle through its encoding: a string of the
log counts as the leaf or vertex query that the encoding writes so. For two parts to read one raw
string, both encodings must write a leaf query on a stored symbol as ONE string, whatever the salt.
Where the first 256 bits of the typed salt are the configuration's digest, the salt has the format's
length and the code of the call number 174 writes the symbol, both pages write the format's string.
ELSEWHERE each page writes the byte 2 and its total code's string. On leaf queries the two total
codes (`backP`) are one text, but for the serialiser of the body: the library's writes its tagged
body, the sibling's is a datum of the page (`LeafD.ser`), read nowhere else. At `serTie`
(OnBytes/TypedOracleCompiler/Run/SerTie.lean) the two agree on stored symbols.

ALL NEW (4).
 `pStored_same`       the sibling's and the line's code of the call number 174 write the same. Not
                      by evaluation: by what each writes, and where.
 `back_stored`        behind the escape the two pages write leaf queries on stored symbols alike, if
                      `Lf.ser` is `serTie` at the line's serialiser of stored symbols.
 `code_stored_cross`, `code_node_cross`   A LEAF QUERY ON A STORED SYMBOL HAS ONE STRING IN BOTH
                      FAMILIES, FOR EVERY SYMBOL AND EVERY SALT; so has a vertex query on two
                      digests. At every pd, pd', K, K', every bodies' data and every code of bodies
                      with that serialiser. AT THE PAGE `pageXPd` OF A CHAIN WITH STORED TABLES
                      ALONE: no other page stands over the sibling.

With a serialiser that writes some stored symbol's body otherwise the two pages part at the leaf
queries on that symbol that the format's code does not write (by the two equations; no theorem
here).

WHAT IT IMPORTS OF THE LINE: OnBytes/Slice/SameStoredAt.lean (over OnBytes/Tie/PageXFit.lean).

WHAT IS NOT SAID. Nothing on own leaves or chain queries: the two families spell them as they do,
and no reading of stored tables looks at them. Nothing on soundness; no probability; nothing on any
hash.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Slice.EntryAccept
import OnBytes.TypedOracleCompiler.Run.PageXTop
import OnBytes.TypedOracleCompiler.Run.SerTie
import OnBytes.Slice.SameStoredAt

set_option autoImplicit false

namespace TypedOracleCompiler.Slice
open Rom _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run.PQ (View SgX)
open TypedOracleCompiler.Run
open TypedOracleCompiler.Run.PQ (XD BodyD LeafD StmInv serTie serTie_emb)
open TypedOracleCompiler.Slice.EntryAccept (asTypedCompilerDescription)

/-! ## The two codes of the call number 174 are one -/

/-- The sibling's and the line's code of a stored symbol write the same. -/
theorem pStored_same (a salt : ℕ) (y : SgX) :
    (pStored a salt).put y = (OnBytes.Tie.pStored a salt).put y := by
  cases h : (pStored a salt).put y with
  | some m =>
    obtain ⟨hok, rfl⟩ := pStored_put a salt y m h
    exact (OnBytes.Tie.pStored_some a salt y hok).symm
  | none =>
    cases h' : (OnBytes.Tie.pStored a salt).put y with
    | none => rfl
    | some m' =>
      rw [pStored_some a salt y (OnBytes.Tie.pStored_put a salt y m' h').1] at h
      cases h

/-! ## Across the two families: stored leaves and vertices are spelled alike -/

section
variable {Bd : Type} (B : BodyD Bd) (D : _root_.Run.PQ.XD) (dec : View → Bool)
  (Lf : LeafD (asTypedCompilerDescription D) B) (sb : Ser Bd)
  (hser : Lf.ser = serTie B (Ser.prod Ser.natG (Ser.list _root_.Run.PQ.serW)) sb)
  (pd pd' : Dig 256) (K K' : ℕ) (hcfg : D.base.cfg.size = 32) (V : StmInv (asTypedCompilerDescription D))
  (V' : OnBytes.Tie.StmInv D)

include hser in
/-- Behind the escape the two pages' total codes write leaf queries on stored symbols alike, at
every symbol and every salt, if the sibling's serialiser of bodies is `serTie` at the line's
serialiser of stored symbols. -/
theorem back_stored (x : SgX) (salt : Bits) :
    (PQ.pageXPd (D := asTypedCompilerDescription D) dec pd B Lf K hcfg V).back.put (.inl (.inl ⟨B.embE x, salt⟩)) =
      (OnBytes.Tie.pageXPd (D := D) dec pd' K' hcfg V').back.put
        (.inl (.inl ⟨some (.inl x), salt⟩)) := by
  show false :: false :: (Lf.ser.put (B.embE x) ++ serBits.put salt) =
    false :: false :: ((Ser.option (Ser.sum (Ser.prod Ser.natG (Ser.list _root_.Run.PQ.serW))
      _)).put (some (.inl x)) ++ serBits.put salt)
  rw [hser, serTie_emb]

include hser in
/-- A LEAF QUERY ON A STORED SYMBOL HAS ONE STRING IN BOTH FAMILIES, FOR EVERY SYMBOL AND EVERY
SALT, the strings behind the escape among them. -/
theorem code_stored_cross (x : SgX) (salt : Bits) (j j' : Fin 1) :
    (theImpl (PQ.pageXPd (D := asTypedCompilerDescription D) dec pd B Lf K hcfg V)).code OracleName.leaf ⟨B.embE x, salt⟩ j =
      (OnBytes.Tie.theImplX (OnBytes.Tie.pageXPd (D := D) dec pd' K' hcfg V')).code
        _root_.Compile.Batch.OracleName.leaf ⟨some (.inl x), salt⟩ j' := by
  rw [theImpl_code_leaf, OnBytes.Slice.code_stored,
    back_stored B D dec Lf sb hser pd pd' K K' hcfg V V',
    pLeafC_stored _ (PQ.storedIn_pageXPd dec pd B Lf K hcfg V), pStored_same]
  rfl

/-- A vertex query on two digests has one string in both families. -/
theorem code_node_cross (a b : Dig 256) (j j' : Fin 1) :
    (theImpl (PQ.pageXPd (D := asTypedCompilerDescription D) dec pd B Lf K hcfg V)).code OracleName.node
        (List.ofFn a, List.ofFn b) j =
      (OnBytes.Tie.theImplX (OnBytes.Tie.pageXPd (D := D) dec pd' K' hcfg V')).code
        _root_.Compile.Batch.OracleName.node (List.ofFn a, List.ofFn b) j' := by
  have la : (List.ofFn a).length = 256 := List.length_ofFn
  have lb : (List.ofFn b).length = 256 := List.length_ofFn
  rw [theImpl_node _ _ _ (pNode_put256 _ (List.ofFn a) (List.ofFn b) la lb) j,
    OnBytes.Tie.theImplX_node _ _ _ (OnBytes.Slice.pNode_put _ (List.ofFn a) (List.ofFn b) la lb)
        j']
  rfl

end

end TypedOracleCompiler.Slice
