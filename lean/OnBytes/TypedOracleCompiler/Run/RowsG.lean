-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Run/RowsG.lean: FROM STRINGS TO VALUES, FOR EVERY PAGE: at the family over one oracle
that PageG.lean makes of ANY data (`PageG.implG C`): if a typed query's STRING is the bits of the
format's string of a call, then the typed family's ANSWER there is what the format's hash, made of
the same oracle, gives at that call.

WHY. A page says which string a typed query has (an equation with `Fmt.oStr` on the right). The tie
between a typed verifier and the port's reader of a file compares VALUES: the typed family
`readBlocks (implG C) g`, g the one oracle on bit strings, against the hash `Fmt.HO (oB (g ()))`.
The step from the one to the other is the same for a key's, an entry's and a proof's page. Here it
is said once, over the string equations as hypotheses: no data of any page are named.

 - `famG C g`, `hOfG g`; `famG_leaf` … `famG_fb`: the family's answer is g at the query's string(s),
   by unfolding;
 - `blocksG_le`: an answer has at most K + 1 blocks, at every oracle;
 - `one_of_code`: g at the bits of `oStr 0 n t i st bs`, n ≠ 162, is the hash at (n, t, i, st, bs)
   as a digest; `leaf_of_code`, `node_of_code`, `rleaf_of_code`, `rnode_of_code`: so for a query
   with one block;
 - `first_of_code`: if the tail's block of a chain query has the string of a first value's call, the
   answer's tail is the library's `Fmt.firstValueW` at the hash;
 - `row_of_codes`: if typed block j of a chain query has the string of half (b mod 2) of call
   (b div 2) of a round, b := `blockNo work K j`, for every j, then the answer is ChainFrom.lean's
   `PQ.Row`: the format's row of blocks; with the bytes behind the message as `Fmt.tail`
   (`row_of_codes`) or as the library's `roundBytes` (`row_of_codes'`);
 - `blk_of_code`: one block alone;
 - `seedsPage_of_codes`: the law `SeedsPage` (OnBytes/TypedOracleCompiler/Slice/SeedsBridge.lean) from the two
 codes' equations.

Main definitions: `famG`, `hOfG`.
Main theorems: `blocksG_le`, `one_of_code`, `first_of_code`, `row_of_codes`, `seedsPage_of_codes`.

WHAT IS NOT SAID. NO STRING EQUATION IS SHOWN HERE: they are each page's own. No domain of the
format's hash is asked: these are equations at EVERY g; that `Fmt.HO` at the format's realised
oracle is the format's hash holds within its domain alone (library, Fmt/Rules23Laws.lean:
`HO_oracle`). Values under oracle FUNCTIONS: the order of asking does not enter. Nothing on
soundness. The sibling is a second form of the library's soundness road, under OnBytes/TypedOracleCompiler/.
The compiler under OnBytes/TypedOracleCompiler/ is the one that `innerCompiledVerifier` is made with; it builds on
definitions of Compile/.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Run.PageG
import OnBytes.TypedOracleCompiler.Run.ChainFrom
import OnBytes.TypedOracleCompiler.Slice.SeedsBridge

set_option autoImplicit false

namespace TypedOracleCompiler.Run.RowsG
open Rom _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run
open TypedOracleCompiler.Run.PageG
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run

variable {I X : Type} {L : BatchProtocolWithLeafBody I X} {K : ℕ}

/-! ## The family and the hash, of one oracle -/

/-- The typed family that a page makes of the one oracle. -/
def famG (C : Page L K) (g : Fam (rom 256)) : Fam (typedOracleFamily 256 K L) := readBlocks (implG C) g

/-- The format's hash, made of the same oracle. -/
def hOfG (g : Fam (rom 256)) : _root_.Fmt.Hash := _root_.Fmt.HO (oB (g ()))

/-- The oracle on bytes, as a digest, is the oracle on bits. -/
theorem dig_oB (g : Fam (rom 256)) (s : ByteArray) :
    bytesToDig (oB (g ()) s) = g () (bytesToBits s) := TieTree.bytes_dig _

/-- It gives 32 bytes. -/
theorem size_oB (g : Fam (rom 256)) (s : ByteArray) : (oB (g ()) s).size = 32 := size_digToBytes _

variable (C : Page L K) (g : Fam (rom 256))

/-- The family at a leaf query. -/
theorem famG_leaf (q : LeafIn L) :
    (famG C g .leaf q : Dig 256) = g () ((implG C).code .leaf q (0 : Fin 1)) := rfl

/-- At a vertex query. -/
theorem famG_node (q : Bits × Bits) :
    (famG C g .node q : Dig 256) = g () ((implG C).code .node q (0 : Fin 1)) := rfl

/-- At a leaf query of the request tree. -/
theorem famG_rleaf (q : Bits) :
    (famG C g .rleaf q : Dig 256) = g () ((implG C).code .rleaf q (0 : Fin 1)) := rfl

/-- At a vertex query of the request tree. -/
theorem famG_rnode (q : Bits × Bits) :
    (famG C g .rnode q : Dig 256) = g () ((implG C).code .rnode q (0 : Fin 1)) := rfl

/-- At a joining round's query. -/
theorem famG_g (t : Tag) (q : JoiningRoundQuery 256 L t) :
    (famG C g (.g t) q : Dig 256) = g () ((implG C).code (.g t) q (0 : Fin 1)) := rfl

/-- At a chain query: the K blocks of the verifier's message, and the tail. -/
theorem famG_fb (t : Tag) (q : FbIn 256 L t) :
    (famG C g (.fb t) q : (Fin K → Dig 256) × Dig 256) =
      (fun k : Fin K => g () ((implG C).code (.fb t) q k.castSucc),
        g () ((implG C).code (.fb t) q (Fin.last K))) := rfl

/-- An answer has at most K + 1 blocks, at every oracle. -/
theorem blocksG_le (o : TypedOracleCompiler.Compile.Batch.OracleName) : (implG C).blocks o ≤ K + 1 := by
  cases o <;> first
    | exact Nat.le_refl _
    | exact Nat.succ_le_succ (Nat.zero_le _)
    | exact Nat.zero_le _

/-! ## One block -/

/-- FROM A STRING TO A VALUE: g at the bits of the string of a call of a number other than 162 is
the hash at that call, as a digest. -/
theorem one_of_code (n t i : ℕ) (st bs : ByteArray) (hn : n ≠ 162) :
    g () (bytesToBits (_root_.Fmt.oStr 0 n t i st bs)) = bytesToDig (hOfG g n t i st bs) := by
  have e : hOfG g n t i st bs = oB (g ()) (_root_.Fmt.oStr 0 n t i st bs) := if_neg hn
  rw [e, dig_oB]

/-- A leaf query. -/
theorem leaf_of_code (q : LeafIn L) (n t i : ℕ) (st bs : ByteArray) (hn : n ≠ 162)
    (h : (implG C).code .leaf q (0 : Fin 1) = bytesToBits (_root_.Fmt.oStr 0 n t i st bs)) :
    (famG C g .leaf q : Dig 256) = bytesToDig (hOfG g n t i st bs) := by
  rw [famG_leaf, h]
  exact one_of_code g n t i st bs hn

/-- A vertex query. -/
theorem node_of_code (q : Bits × Bits) (n t i : ℕ) (st bs : ByteArray) (hn : n ≠ 162)
    (h : (implG C).code .node q (0 : Fin 1) = bytesToBits (_root_.Fmt.oStr 0 n t i st bs)) :
    (famG C g .node q : Dig 256) = bytesToDig (hOfG g n t i st bs) := by
  rw [famG_node, h]
  exact one_of_code g n t i st bs hn

/-- A leaf query of the request tree. -/
theorem rleaf_of_code (q : Bits) (n t i : ℕ) (st bs : ByteArray) (hn : n ≠ 162)
    (h : (implG C).code .rleaf q (0 : Fin 1) = bytesToBits (_root_.Fmt.oStr 0 n t i st bs)) :
    (famG C g .rleaf q : Dig 256) = bytesToDig (hOfG g n t i st bs) := by
  rw [famG_rleaf, h]
  exact one_of_code g n t i st bs hn

/-- A vertex query of the request tree. -/
theorem rnode_of_code (q : Bits × Bits) (n t i : ℕ) (st bs : ByteArray) (hn : n ≠ 162)
    (h : (implG C).code .rnode q (0 : Fin 1) = bytesToBits (_root_.Fmt.oStr 0 n t i st bs)) :
    (famG C g .rnode q : Dig 256) = bytesToDig (hOfG g n t i st bs) := by
  rw [famG_rnode, h]
  exact one_of_code g n t i st bs hn

/-! ## A chain's first value -/

/-- If the tail's block of a chain query has the string of a first value's call, the answer's tail
is the library's first value at the hash. -/
theorem first_of_code (t : Tag) (q : FbIn 256 L t) (lab : ℕ) (pd st rec : ByteArray)
    (run : Option ByteArray)
    (h : (implG C).code (.fb t) q (Fin.last K) =
      bytesToBits (_root_.Fmt.oStr 0 160 0 lab _root_.Fmt.zero32
        (_root_.Fmt.firstBytes pd st rec run))) :
    (famG C g (.fb t) q : (Fin K → Dig 256) × Dig 256).2 =
      bytesToDig (Id.run (_root_.Fmt.firstValueW (m := Id) (hOfG g) lab pd st rec run)) := by
  show g () ((implG C).code (.fb t) q (Fin.last K)) = _
  rw [h]
  exact one_of_code g 160 0 lab _ _ (by decide)

/-! ## A round's row of blocks -/

/-- g at the bits of the string of half (b mod 2) of call (b div 2) of a round is the format's block
b of that round's row, at the hash made of g. -/
theorem blk_of_str (lab : ℕ) (rho : ByteArray) (i : ℕ) (msg : ByteArray) (kind : _root_.Fmt.Kind)
    (w nonce b : ℕ) :
    g () (bytesToBits (_root_.Fmt.oStr (UInt8.ofNat (b % 2)) 162 lab i rho
        (msg ++ _root_.Fmt.tail kind w nonce (b / 2)))) =
      bytesToDig (_root_.Fmt.blockW (hOfG g) lab rho i msg kind w nonce b) := by
  show _ = bytesToDig (_root_.Fmt.blockW (_root_.Fmt.HO (oB (g ()))) lab rho i msg kind w nonce b)
  rw [blockW_HO _ (size_oB g), dig_oB]

/-- One block of a chain query's answer. -/
theorem blk_of_code (t : Tag) (q : FbIn 256 L t) (j : Fin (K + 1)) (lab : ℕ) (rho : ByteArray)
    (i : ℕ) (msg : ByteArray) (kind : _root_.Fmt.Kind) (w nonce b : ℕ)
    (h : (implG C).code (.fb t) q j =
      bytesToBits (_root_.Fmt.oStr (UInt8.ofNat (b % 2)) 162 lab i rho
        (msg ++ _root_.Fmt.tail kind w nonce (b / 2)))) :
    g () ((implG C).code (.fb t) q j) =
      bytesToDig (_root_.Fmt.blockW (hOfG g) lab rho i msg kind w nonce b) := by
  rw [h]
  exact blk_of_str g lab rho i msg kind w nonce b

/-- THE ROW: if every typed block j of a chain query has the string of the format's block number
`blockNo w K j` of a round's row, the typed answer is that row (ChainFrom.lean's `PQ.Row`). -/
theorem row_of_codes (t : Tag) (q : FbIn 256 L t) (lab : ℕ) (rho : ByteArray) (i : ℕ)
    (msg : ByteArray) (kind : _root_.Fmt.Kind) (w nonce : ℕ)
    (h : ∀ j : Fin (K + 1), (implG C).code (.fb t) q j =
      bytesToBits (_root_.Fmt.oStr (UInt8.ofNat (blockNo w K j % 2)) 162 lab i rho
        (msg ++ _root_.Fmt.tail kind w nonce (blockNo w K j / 2)))) :
    PQ.Row (oB (g ())) K lab rho i msg kind w nonce (famG C g (.fb t) q) :=
  ⟨fun k => blk_of_code C g t q k.castSucc lab rho i msg kind w nonce _ (h _), by
    rw [← _root_.Run.blockNo_last w K]
    exact blk_of_code C g t q (Fin.last K) lab rho i msg kind w nonce _ (h _)⟩

/-- The same, with the bytes behind the message as the library's `roundBytes`. -/
theorem row_of_codes' (t : Tag) (q : FbIn 256 L t) (lab : ℕ) (rho : ByteArray) (i : ℕ)
    (msg : ByteArray) (kind : _root_.Fmt.Kind) (w nonce : ℕ)
    (h : ∀ j : Fin (K + 1), (implG C).code (.fb t) q j =
      bytesToBits (_root_.Fmt.oStr (UInt8.ofNat (blockNo w K j % 2)) 162 lab i rho
        (roundBytes msg kind.num w (blockNo w K j / 2) nonce))) :
    PQ.Row (oB (g ())) K lab rho i msg kind w nonce (famG C g (.fb t) q) :=
  row_of_codes C g t q lab rho i msg kind w nonce fun j => by
    rw [h j, _root_.Run.roundBytes_tail]

/-! ## The seeds' chain -/

/-- SeedsBridge.lean's law on an implementation at the seeds' tag, from the two codes' equations:
the first query's tail has the string of the name's first value; typed block i of the drawing
round's query behind ρ has the string of block i + 1 of the seeds' round at the start ρ. -/
theorem seedsPage_of_codes (tg : Tag) (name : ByteArray) (q₀ : FbIn 256 L tg)
    (q₁ : Bits → FbIn 256 L tg)
    (h0 : (implG C).code (.fb tg) q₀ (Fin.last K) =
      bytesToBits (OnBytes.Slice.seedFirst name))
    (h1 : ∀ (ρ : Dig 256) (i : Fin K), (implG C).code (.fb tg) (q₁ (List.ofFn ρ)) i.castSucc =
      bytesToBits (OnBytes.Slice.blockStr (digToBytes ρ) (i.val + 1))) :
    TypedOracleCompiler.Slice.SeedsPage (implG C) tg name q₀ q₁ where
  first := fun g => by
    show g () ((implG C).code (.fb tg) q₀ (Fin.last K)) = _
    rw [h0]
  round := fun g ρ i => by
    show g () ((implG C).code (.fb tg) (q₁ (List.ofFn ρ)) i.castSucc) = _
    rw [h1]

end TypedOracleCompiler.Run.RowsG
