-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Run/RowsE3.lean: FROM STRINGS TO VALUES AT AN ENTRY's PAGE: THE LEAVES: what the family
that the entry's page makes of ONE oracle answers at a leaf query, at bodies that are strings, IS
the format's own leaf call at the hash made of the same oracle: for a stored table's symbol (174,
under either root: a leaf query names no root) and for a symbol of the chain's own trees (164).

WHY. The forests' half of the tie from the port's yes to the typed verifier's yes asks, opening by
opening, "the digest that g gives at the typed leaf is the format's own leaf call"
(OnBytes/TypedOracleCompiler/Slice/Batch3SRead.lean: `ownOk_of_read`, `stoOk_of_read`: "the page's row law at
leaves"; `leafAtH`). The entry's page takes OnBytes/TypedOracleCompiler/Run/KeyLeaves.lean's code of leaves: the
identity on the bodies that pass `Strings.ok2`, under the test `Strings.leafOK2 cfg`, at a file's
salt of n bits.

 - `leafCode_at`: IT WRITES, AND WHAT: for a body b that passes `ok2` and from which `rd2` reads
   (n, t, i, z), a typed salt "32 bytes st, then k bytes sa", n := 8 k bits, and the test passed:
   the bits of `Fmt.oStr 0 n t i st (z ++ sa)`;
 - `VE`: the entry's code of leaves; `leafE_val`: so the family's answer is the hash at
   (n, t, i, st, z ++ sa), as a digest;
 - `startIs_cfg`, `leafOK2_cfg`: under the start cfg the test passes at every body;
 - `stoE_val`: A STORED SYMBOL (x, col), as the body `Strings.embX a sB c (x, col)`, under the typed
 salt
   `leafSalt cfg sa`: the format's leaf call under 174: tree 0, the column's and the salt's words,
   2 ^ a + x, the start cfg, column, fill and salt: Batch3SRead.lean's `leafAtH h sh cfg x col sa`
   at a form sh that is stored, of the tree 0 and the depth a (`stoE_leafAtH`). Asked: OnBytes/TypedOracleCompiler's
   `storedOK`; sa has sB bytes;
 - `storedOK_of`; `stoE_law`: THE LAW AT STORED LEAVES IN Batch3SRead.lean's LETTERS: at every place
   within the tree, every column of the form's width, every salt of sB bytes; `ownE_law`: the law at
   a leaf of an own tree in the same letters, for a body that is spelled as the format spells that
   leaf;
 - `ownE_val`: A SYMBOL OF THE CHAIN's OWN TREES, as the body `embTail sB C ds p a` (which
   `StringsList.embT` writes behind the front), under `leafSalt st sa`: the hash under 164 at
   OnBytes/TypedOracleCompiler's own spelling `PQ.leafSL` of the leaf. Asked: the conditions on the trees and the
   salt of OnBytes/TypedOracleCompiler/StringsBounds.lean.

Main definition: `VE`.
Main theorems: `leafCode_at`, `leafE_val`, `stoE_val`, `stoE_leafAtH`, `stoE_law`, `ownE_law`,
`ownE_val`.

WHAT IS NOT SAID. NO LAW AT ALL SALTS, PLACES AND COLUMNS: a page writes a leaf at ONE length of
salt, a place's word below 2 ^ 48 and an index below 2 ^ 64: whoever asks the law of a family behind
a page must ask it under the reader's own facts. `PQ.leafSL`'s value in terms of a tree's form, a
place and a column is not unfolded here. That a reader's start for an own tree is the sender's run.
No domain of the format's hash is asked. What the heads of RowsE.lean, KeyLeaves.lean,
StringsBoth.lean and StringsStoredAt.lean do not say. Nothing on soundness. The sibling is a second
form of the library's soundness road, under OnBytes/TypedOracleCompiler/.
The compiler under OnBytes/TypedOracleCompiler/ is the one that `innerCompiledVerifier` is made with; it builds on
definitions of Compile/.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Run.RowsE
import OnBytes.TypedOracleCompiler.Run.KeyLeaves

set_option autoImplicit false

noncomputable section

namespace TypedOracleCompiler.Run.RowsE3
open Rom _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run TypedOracleCompiler.Slice
open TypedOracleCompiler.Run.EntryFb TypedOracleCompiler.Run.EntryPage TypedOracleCompiler.Run.PageG TypedOracleCompiler.Run.RowsG
open TypedOracleCompiler.Run.RowsE TypedOracleCompiler.Strings
open TypedOracleCompiler.Run.FirstAnswers (T3)
open TypedOracleCompiler.Run.PQ (XD)
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run

/-! ## What the code of leaves writes -/

section
variable {I X : Type} (L : _root_.Iop.BatchProtocol I X)

/-- The first 256 bits of "32 bytes, then bytes". -/
theorem take_salt (st sa : ByteArray) (hst : st.size = 32) :
    (bytesToBits st ++ bytesToBits sa).take 256 = bytesToBits st :=
  List.take_left' (by rw [length_bytesToBits, hst])

/-- What stands behind them. -/
theorem drop_salt (st sa : ByteArray) (hst : st.size = 32) :
    (bytesToBits st ++ bytesToBits sa).drop 256 = bytesToBits sa :=
  List.drop_left' (by rw [length_bytesToBits, hst])

/-- THE CODE OF LEAVES WRITES, AND WHAT: the bits of the format's string of the call that the body
and the typed salt spell. -/
theorem leafCode_at (nb k : ℕ) (hn : nb = 8 * k) (cfg : ByteArray) (b : List Bool) (n t i : ℕ)
    (z : ByteArray) (hok : ok2 b = true) (hrd : rd2 b = (n, t, i, z)) (st sa : ByteArray)
    (hst : st.size = 32) (hsa : sa.size = k)
    (hk : leafOK2 L cfg ⟨b, bytesToBits st ++ bytesToBits sa⟩ = true) :
    (KeyLeaves.leafCode L nb cfg).put ⟨b, bytesToBits st ++ bytesToBits sa⟩ =
      some (bytesToBits (_root_.Fmt.oStr 0 n t i st (z ++ sa))) := by
  have hl : (bytesToBits st ++ bytesToBits sa).length = 256 + nb := by
    rw [List.length_append, length_bytesToBits, length_bytesToBits, hst, hsa, hn]
  have hw : (pLeaf (L := strung L) nb (pBody ok2)).put ⟨b, bytesToBits st ++ bytesToBits sa⟩ =
      some (pre33 ++ ((bytesToBits st ++ bytesToBits sa).take 256 ++
        (b ++ (bytesToBits st ++ bytesToBits sa).drop 256))) := by
    show (if (bytesToBits st ++ bytesToBits sa).length = 256 + nb then
        ((if ok2 b then some b else none : Option (List Bool))).map
          (fun m => pre33 ++ ((bytesToBits st ++ bytesToBits sa).take 256 ++
            (m ++ (bytesToBits st ++ bytesToBits sa).drop 256)))
      else none) = _
    rw [if_pos hl, if_pos hok]
    rfl
  obtain ⟨c, hc, hs⟩ := pLeaf2_put L nb k hn _ _ hw
  have hc' : c = ⟨0, n, t, i, st, z ++ sa⟩ := by
    have h0 : (if ok2 b then
        some (⟨0, (rd2 b).1, (rd2 b).2.1, (rd2 b).2.2.1,
          bitsToBytes ((bytesToBits st ++ bytesToBits sa).take 256),
          (rd2 b).2.2.2 ++ bitsToBytes ((bytesToBits st ++ bytesToBits sa).drop 256)⟩ :
          _root_.Fmt.OQ)
      else none) = some c := hc
    rw [if_pos hok, hrd, take_salt st sa hst, drop_salt st sa hst, bitsToBytes_bytesToBits,
      bitsToBytes_bytesToBits] at h0
    exact (Option.some.inj h0).symm
  show (if leafOK2 L cfg ⟨b, bytesToBits st ++ bytesToBits sa⟩ = true then
    (pLeaf (L := strung L) nb (pBody ok2)).put ⟨b, bytesToBits st ++ bytesToBits sa⟩
    else none) = _
  rw [if_pos hk, hw, hs, hc']
  rfl

/-- Under the start cfg OnBytes/TypedOracleCompiler's test on the start passes. -/
theorem startIs_cfg (cfg sa : ByteArray) (hcfg : cfg.size = 32) (b : List Bool) :
    startIs (L := strung L) cfg ⟨b, bytesToBits cfg ++ bytesToBits sa⟩ = true := by
  show (bitsToBytes ((bytesToBits cfg ++ bytesToBits sa).take 256) == cfg) = true
  rw [take_salt cfg sa hcfg, bitsToBytes_bytesToBits]
  rcases cfg with ⟨d⟩
  exact beq_self_eq_true d

/-- So the test on body and salt passes at every body. -/
theorem leafOK2_cfg (cfg sa : ByteArray) (hcfg : cfg.size = 32) (b : List Bool) :
    leafOK2 L cfg ⟨b, bytesToBits cfg ++ bytesToBits sa⟩ = true := by
  unfold leafOK2
  split
  · exact startIs_cfg L cfg sa hcfg b
  · rfl

end

/-! ## At the entry's page -/

variable {Sd : Type} {D : XD}
  {early : (List T3 × List T3) × Sd → (List T3 × List T3) × Sd} {e : _root_.Fmt.Entry}
  (P : PinsE D early e) (dd : Sd) (K : ℕ) (nb : ℕ)

/-- The entry's code of leaves: OnBytes/TypedOracleCompiler/Run/KeyLeaves.lean's, at the pins' configuration digest
and a file's salt of nb bits. -/
def VE : Leaves (Le D early e) := KeyLeaves.leavesAt (Le D early e).toBatchProtocol nb P.cfg

variable (back : StrCode (AllPts 256 K (Le D early e))) (g : Fam (rom 256))

/-- A LEAF, AS A VALUE: for a body that passes `ok2`, from which `rd2` reads (n, t, i, z): the hash
at (n, t, i), with the typed salt's first 32 bytes as the start, on z and then the salt's other
bytes. -/
theorem leafE_val (k : ℕ) (hn : nb = 8 * k) (b : List Bool) (n t i : ℕ) (z : ByteArray)
    (hok : ok2 b = true) (hrd : rd2 b = (n, t, i, z)) (st sa : ByteArray) (hst : st.size = 32)
    (hsa : sa.size = k)
    (hk : leafOK2 (Le D early e).toBatchProtocol P.cfg ⟨b, bytesToBits st ++ bytesToBits sa⟩ = true) :
    (famE P dd K (VE P nb) back g .leaf ⟨b, leafSalt st sa⟩ : Dig 256) =
      bytesToDig (hOfG g n t i st (z ++ sa)) := by
  have h162 : n ≠ 162 := by
    have h := ((ok2_iff b).1 hok).2.1
    rw [hrd] at h
    rcases h with h | h <;> rw [show n = _ from h] <;> decide
  exact rowE_leaf P dd K (VE P nb) back g ⟨b, leafSalt st sa⟩ n t i st (z ++ sa) h162
    (leafCode_at (Le D early e).toBatchProtocol nb k hn P.cfg b n t i z hok hrd st sa hst hsa hk)

/-- A STORED SYMBOL's LEAF, AS A VALUE: the format's leaf call under 174. -/
theorem stoE_val (a sB : ℕ) (c : StrCode (ℕ × List UInt64)) (hn : nb = 8 * sB) (x : ℕ)
    (col : List UInt64) (hs : storedOK a sB (x, col)) (sa : ByteArray) (hsa : sa.size = sB) :
    (famE P dd K (VE P nb) back g .leaf ⟨embX a sB c (x, col), leafSalt P.cfg sa⟩ : Dig 256) =
      bytesToDig (hOfG g 174 (_root_.Fmt.leafPlace 0 col.length (sB / 8)) (2 ^ a + x) P.cfg
        (_root_.Fmt.colBytes col ++ _root_.Fmt.zeroBytes (_root_.Fmt.fillLen col.length sB) ++
          sa)) :=
  leafE_val P dd K nb back g sB hn _ _ _ _ _ (ok2_rd2_embX a sB c (x, col) hs).1
    (ok2_rd2_embX a sB c (x, col) hs).2 P.cfg sa P.hcfg hsa
    (leafOK2_cfg _ P.cfg sa P.hcfg _)

/-- The same in Batch3SRead.lean's letters: the leaf's digest as the format's reader computes it, at
a form that is stored, of the tree 0 and the depth a. (The right side is Batch3SRead.lean's `leafAtH
(hOfG g) sh P.cfg x col sa`, unfolded.) -/
theorem stoE_leafAtH (sB : ℕ) (c : StrCode (ℕ × List UInt64)) (hn : nb = 8 * sB)
    (sh : _root_.Fmt.Shape) (h1 : sh.stored = true) (h2 : sh.tree = 0) (x : ℕ) (col : List UInt64)
    (hs : storedOK sh.a sB (x, col)) (sa : ByteArray) (hsa : sa.size = sB) :
    (famE P dd K (VE P nb) back g .leaf ⟨embX sh.a sB c (x, col), leafSalt P.cfg sa⟩ : Dig 256) =
      bytesToDig (hOfG g (_root_.Fmt.leafNo sh.stored)
        (_root_.Fmt.leafPlace sh.tree col.length (sa.size / 8)) (2 ^ sh.a + x) P.cfg
        (_root_.Fmt.leafBytes col sa)) := by
  have e1 : _root_.Fmt.leafNo true = 174 := rfl
  rw [stoE_val P dd K nb back g sh.a sB c hn x col hs sa hsa, h1, h2, e1]
  unfold _root_.Fmt.leafBytes
  rw [hsa]

/-- OnBytes/TypedOracleCompiler's test on a stored symbol, from a place within the tree, a depth of at most 63, a
width below 2 ^ 24 and a salt of fewer than 2 ^ 11 bytes. -/
theorem storedOK_of (a sB x : ℕ) (col : List UInt64) (hx : x < 2 ^ a) (ha : 2 ^ a + 2 ^ a ≤ 2 ^ 64)
    (hW : col.length < 2 ^ 24) (h8 : sB / 8 < 2 ^ 8) : storedOK a sB (x, col) := by
  have hp := _root_.Fmt.leafPlace_lt 0 col.length (sB / 8) (by decide) hW h8
  exact ⟨hW, by show 174 + 65536 * _root_.Fmt.leafPlace 0 col.length (sB / 8) < 2 ^ 64; omega,
    by show 2 ^ a + x < 2 ^ 64; omega⟩

/-- THE LAW AT STORED LEAVES, IN Batch3SRead.lean's LETTERS: for a form sh that is
stored, of the tree 0: at every place within the tree, every column of the form's width and every
salt of sB bytes. In front: the width is below 2 ^ 24; the depth at most 63; sB / 8 below 2 ^ 8. -/
theorem stoE_law (sB : ℕ) (c : StrCode (ℕ × List UInt64)) (hn : nb = 8 * sB)
    (sh : _root_.Fmt.Shape) (h1 : sh.stored = true) (h2 : sh.tree = 0) (hW : sh.W < 2 ^ 24)
    (ha : 2 ^ sh.a + 2 ^ sh.a ≤ 2 ^ 64) (h8 : sB / 8 < 2 ^ 8) :
    ∀ (x : ℕ) (col : List UInt64) (sa : ByteArray), x < 2 ^ sh.a → col.length = sh.W →
      sa.size = sB →
      (famE P dd K (VE P nb) back g .leaf ⟨embX sh.a sB c (x, col), leafSalt P.cfg sa⟩ : Dig 256) =
        bytesToDig (hOfG g (_root_.Fmt.leafNo sh.stored)
          (_root_.Fmt.leafPlace sh.tree col.length (sa.size / 8)) (2 ^ sh.a + x) P.cfg
          (_root_.Fmt.leafBytes col sa)) :=
  fun x col sa hx hc hsa => stoE_leafAtH P dd K nb back g sB c hn sh h1 h2 x col
    (storedOK_of sh.a sB x col hx ha (by rw [hc]; exact hW) h8) sa hsa

/-- THE LAW AT A LEAF OF AN OWN TREE, IN Batch3SRead.lean's LETTERS: for a body that is spelled as
the format spells the leaf of the form s at the place x with the column col (the label under 164
with the place's word of tree, width and the salt's words, and 2 ^ depth + x; column and fill):
under the typed salt "start, then a salt of sB bytes". -/
theorem ownE_law (sB : ℕ) (hn : nb = 8 * sB) (s : _root_.Fmt.Shape) (h1 : s.stored = false) (x : ℕ)
    (col : List UInt64) (b : List Bool)
    (hb : b = spell2 164 (_root_.Fmt.leafPlace s.tree col.length (sB / 8), 2 ^ s.a + x,
      _root_.Fmt.colBytes col ++ _root_.Fmt.zeroBytes (_root_.Fmt.fillLen col.length sB)))
    (hp : _root_.Fmt.leafPlace s.tree col.length (sB / 8) < 2 ^ 48) (hi : 2 ^ s.a + x < 2 ^ 64)
    (st sa : ByteArray) (hst : st.size = 32) (hsa : sa.size = sB) :
    (famE P dd K (VE P nb) back g .leaf ⟨b, leafSalt st sa⟩ : Dig 256) =
      bytesToDig (hOfG g (_root_.Fmt.leafNo s.stored)
        (_root_.Fmt.leafPlace s.tree col.length (sa.size / 8)) (2 ^ s.a + x) st
        (_root_.Fmt.leafBytes col sa)) := by
  have e1 : _root_.Fmt.leafNo false = 164 := rfl
  have hv := leafE_val P dd K nb back g sB hn b 164 _ _ _
    (by rw [hb]; exact ok2_spell 164 _ _ _ (Or.inl rfl) hp hi)
    (by rw [hb]; exact rd2_spell 164 _ _ _ (by decide) hp hi) st sa hst hsa
    (leafOK2_own _ P.cfg _ (by
      show List.take 16 b = t164
      rw [hb]
      exact (spell2_take 164 _).2))
  rw [hv, h1, e1]
  unfold _root_.Fmt.leafBytes
  rw [hsa]

/-- A LEAF OF THE CHAIN's OWN TREES, AS A VALUE: the hash under 164 at OnBytes/TypedOracleCompiler's own spelling of
the leaf. -/
theorem ownE_val (sB : ℕ) (hn : nb = 8 * sB) (h8 : sB / 8 < 2 ^ 8) (C : PQ.CK) (ds : List PQ.RD)
    (hS : SmallL ds) (p : OPos (PQ.uL C ds)) (a : OSym (PQ.uL C ds) p) (st sa : ByteArray)
    (hst : st.size = 32) (hsa : sa.size = sB) :
    (famE P dd K (VE P nb) back g .leaf ⟨embTail sB C ds p a, leafSalt st sa⟩ : Dig 256) =
      bytesToDig (hOfG g 164 (PQ.leafSL C sB ds ⟨p, a⟩).1 (PQ.leafSL C sB ds ⟨p, a⟩).2.1 st
        ((PQ.leafSL C sB ds ⟨p, a⟩).2.2 ++ sa)) := by
  have h := ok2_rd2_embTail sB C h8 ds hS p a
  refine leafE_val P dd K nb back g sB hn _ 164 _ _ _ h.1 h.2 st sa hst hsa
    (leafOK2_own _ P.cfg _ ?_)
  have ht := spell2_take (rd2 (embTail sB C ds p a)).1 (rd2 (embTail sB C ds p a)).2
  rw [← ((ok2_iff _).1 h.1).2.2, h.2] at ht
  exact ht.2

end TypedOracleCompiler.Run.RowsE3
