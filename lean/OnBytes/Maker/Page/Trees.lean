-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/Page/Trees.lean: the rows of the page (OnBytes/Maker/Page/Frame.lean) for the leaves
and the vertices of the trees: the value of the page's field `leaf`, and what the typed oracle
functions `gJ P O` answer at a leaf's body and at a vertex.

A body of a leaf is a string of bits: the format's label (two words) and then the bytes that the
format hashes before the salt (OnBytes/Flat/LeafBodies.lean, StoredBodies.lean). The page must find
the call's number, the label's place and index and these bytes from the body alone. The start of the
call is the first 256 bits of the typed salt; the file's salt is the rest.

Main names.
  `hO O`: O at the format's string of (number, place, index, start, bytes), at half 0: at every
    number but 162 the library's `Fmt.HO O` (`hO_eq_HO`, OnBytes/Maker/Page/Request.lean); at 162
    the first half alone.
  `readBody b`: number, place, index and bytes of a body; nothing below 128 bits. `readBody_label`:
    at the bits of a label and of bytes it gives these back, for a number below 2^16 and words below
    2^64.
  `leafCall body salt`: the format's call of a leaf query. `leafOf bd`: the value for `PageJ.leaf`,
    at a reading bd of the interface's bodies as strings of bits.
  `leafCall_own`, `leafCall_stored`: the call at the body of a symbol of a run's tree, and of a
    stored table's symbol, under the typed salt "start, then the file's salt".
  `gJ_leaf`: what `gJ P O` answers at a leaf query for which the taken spelling `leafX` writes
    nothing.
  `leafIs_own_gJ`, `leafIs_stored_gJ`: there it is the digest of the format's leaf hash (`Fmt.leafW`
    by its body).
  `gJ_node`, `nodeIs_gJ`: `NodeIs (gJ P O) (hO O) P.cfg` (OnBytes/Maker/RecNodes.lean).

Limits: identities of computations, for every function O. `gJ` is a function of the typed query, no
one-to-one coding: bodies that read back alike, and all bodies below 128 bits, have one answer; and
`leafCall` tests no number, so a leaf query whose body begins with another row's label gets that
row's string. `leafIs_own_gJ` and `leafIs_stored_gJ` ask that `leafX` writes nothing at the query:
at a page whose `leafX` is a code of leaf queries over both numbers (`pageV`,
Johnson/Maker/Page/Values.lean [not in this library]) that premise is false at a file's own leaves;
nobody calls these two; the laws that are used are those of OnBytes/Maker/Page/LeafAgree.lean. A
stored symbol's leaf stands at the symbol's own position. A run's tree must not be marked as stored.
Nothing on soundness.


-/
import OnBytes.Maker.Page.Frame
import OnBytes.Maker.RecNodes
import OnBytes.Flat.LeafBodies
import OnBytes.Flat.StoredBodies
import Run.ParserHashProofs

set_option autoImplicit false

namespace OnBytes.Maker.Page
open Rom _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run _root_.Run.PQ OnBytes.Flat

/-- O at the format's string, at half 0: `Fmt.HO O` at every number but 162. -/
def hO (O : ByteArray → ByteArray) (n place ix : ℕ) (start bytes : ByteArray) : ByteArray :=
  O (Fmt.oStr 0 n place ix start bytes)

/-! ## The read-back from a body -/

/-- The number that 64 bits spell as a word. -/
def wordOf (s : List Bool) : ℕ := (Fmt.wordAt (bitsToBytes s) 0).toNat

theorem wordOf_u64n (x : ℕ) (hx : x < 2 ^ 64) : wordOf (bytesToBits (Fmt.u64n x)) = x := by
  have h := pWord.parse_put x (bytesToBits (Fmt.u64n x)) (if_pos hx)
  have h2 : (if (bytesToBits (Fmt.u64n x)).length = 64 then
      some (Fmt.wordAt (bitsToBytes (bytesToBits (Fmt.u64n x))) 0).toNat else none) = some x := h
  rw [if_pos (by rw [length_bytesToBits]; rfl)] at h2
  exact Option.some.inj h2

/-- Number, place, index and bytes of a body. -/
def readBody (b : List Bool) : Option (ℕ × ℕ × ℕ × ByteArray) :=
  if 128 ≤ b.length then
    some (wordOf (b.take 64) % 65536, wordOf (b.take 64) / 65536, wordOf ((b.drop 64).take 64),
      bitsToBytes (b.drop 128))
  else none

/-- At the bits of a label and of bytes the read-back gives these. -/
theorem readBody_label (n place ix : ℕ) (bs : ByteArray) (hn : n < 65536)
    (h0 : n + 65536 * place < 2 ^ 64) (h1 : ix < 2 ^ 64) :
    readBody (bytesToBits (Fmt.label n place ix) ++ bytesToBits bs) = some (n, place, ix, bs) := by
  have l0 : (bytesToBits (Fmt.u64n (n + 65536 * place))).length = 64 := by
    rw [length_bytesToBits]; rfl
  have l1 : (bytesToBits (Fmt.u64n ix)).length = 64 := by rw [length_bytesToBits]; rfl
  have e : bytesToBits (Fmt.label n place ix) ++ bytesToBits bs =
      bytesToBits (Fmt.u64n (n + 65536 * place)) ++
        (bytesToBits (Fmt.u64n ix) ++ bytesToBits bs) := by
    unfold Fmt.label
    rw [bytesToBits_append, List.append_assoc]
  rw [e]
  unfold readBody
  rw [if_pos (by simp only [List.length_append, l0, l1]; omega), List.take_left' l0,
    List.drop_left' l0, List.take_left' l1, wordOf_u64n _ h0, wordOf_u64n _ h1]
  have d : (bytesToBits (Fmt.u64n (n + 65536 * place)) ++
      (bytesToBits (Fmt.u64n ix) ++ bytesToBits bs)).drop 128 = bytesToBits bs := by
    rw [← List.append_assoc]
    exact List.drop_left' (by rw [List.length_append, l0, l1])
  rw [d, bitsToBytes_bytesToBits]
  have m1 : (n + 65536 * place) % 65536 = n := by omega
  have m2 : (n + 65536 * place) / 65536 = place := by omega
  rw [m1, m2]

/-! ## The leaf's call -/

/-- The format's call of a leaf query: the start is the typed salt's first 256 bits. -/
def leafCall (body : List Bool) (salt : Bits) : Option Fmt.OQ :=
  (readBody body).map fun z =>
    ⟨0, z.1, z.2.1, z.2.2.1, bitsToBytes (salt.take 256), z.2.2.2 ++ bitsToBytes (salt.drop 256)⟩

/-- The typed salt "start, then the file's salt", cut again. -/
theorem salt_cut (start s0 : ByteArray) (hs : start.size = 32) :
    bitsToBytes ((bytesToBits start ++ bytesToBits s0).take 256) = start ∧
      bitsToBytes ((bytesToBits start ++ bytesToBits s0).drop 256) = s0 := by
  have l : (bytesToBits start).length = 256 := by rw [length_bytesToBits, hs]
  rw [List.take_left' l, List.drop_left' l, bitsToBytes_bytesToBits, bitsToBytes_bytesToBits]
  exact ⟨rfl, rfl⟩

/-- The call at the body of a symbol of a run's tree. -/
theorem leafCall_own (s : ℕ) (sh : Fmt.Shape) (hd : 2 ^ sh.a + 2 ^ sh.a ≤ 2 ^ 64)
    (hp : 164 + 65536 * Fmt.leafPlace sh.tree sh.W (s / 8) < 2 ^ 64) (x : Fin (2 ^ sh.a))
    (col : Fin sh.W → UInt64) (start s0 : ByteArray) (hs : start.size = 32) :
    leafCall (emb1 s (some sh) x col) (bytesToBits start ++ bytesToBits s0) =
      some ⟨0, 164, Fmt.leafPlace sh.tree sh.W (s / 8), 2 ^ sh.a + x.val, start,
        Fmt.colBytes (List.ofFn col) ++ Fmt.zeroBytes (Fmt.fillLen sh.W s) ++ s0⟩ := by
  have hx : 2 ^ sh.a + x.val < 2 ^ 64 := by have := x.isLt; omega
  unfold leafCall
  rw [emb1_fit s (some sh) hd x col]
  show (readBody (bytesToBits (Fmt.label 164 (Fmt.leafPlace sh.tree sh.W (s / 8))
    (2 ^ sh.a + x.val)) ++ _)).map _ = _
  rw [readBody_label 164 _ _ _ (by decide) hp hx, (salt_cut start s0 hs).1,
    (salt_cut start s0 hs).2]
  rfl

/-- The call at the body of a stored table's symbol. -/
theorem leafCall_stored (a s : ℕ) (y : ℕ × List UInt64) (hy : TypedOracleCompiler.Run.storedOK a s y)
    (start s0 : ByteArray) (hs : start.size = 32) :
    leafCall (embStored a s y) (bytesToBits start ++ bytesToBits s0) =
      some ⟨0, 174, Fmt.leafPlace 0 y.2.length (s / 8), 2 ^ a + y.1, start,
        Fmt.colBytes y.2 ++ Fmt.zeroBytes (Fmt.fillLen y.2.length s) ++ s0⟩ := by
  unfold leafCall
  rw [embStored_fit a s y hy]
  unfold TypedOracleCompiler.Run.storedStr
  rw [readBody_label 174 _ _ _ (by decide) hy.2.1 hy.2.2, (salt_cut start s0 hs).1,
    (salt_cut start s0 hs).2]
  rfl

/-! ## At the page -/

variable {I X : Type} {L : BatchProtocolWithLeafBody I X} {K : ℕ}

/-- The value for the page's field `leaf`. bd: the interface's bodies, read as strings of bits. -/
def leafOf (bd : L.Bd → List Bool) (q : LeafIn L) : Option Fmt.OQ := leafCall (bd q.body) q.salt

/-- What `gJ P O` answers at a leaf query at which the taken spelling writes nothing and the page's
own row has a call. -/
theorem gJ_leaf (P : PageJ L K) (O : ByteArray → ByteArray) (q : LeafIn L) (c : Fmt.OQ)
    (hX : P.leafX q = none) (hc : P.leaf q = some c) :
    gJ P O OracleName.leaf q = bytesToDig (O (strOf c)) := by
  show ansJ O (codeJ P .leaf q (0 : Fin 1)) = _
  have e : codeJ P .leaf q (0 : Fin 1) = some (strOf c) := by
    unfold codeJ
    show (match P.leafX q with
      | some s => some (bitsToBytes s)
      | none => (P.leaf q).map strOf) = _
    rw [hX, hc]
    rfl
  rw [e]
  rfl

/-- At the body of a symbol of a run's tree: the digest of the format's leaf hash. -/
theorem leafIs_own_gJ (P : PageJ L K) (O : ByteArray → ByteArray) (bd : L.Bd → List Bool)
    (hP : P.leaf = leafOf bd) (sh : Fmt.Shape) (hst : sh.stored = false)
    (hd : 2 ^ sh.a + 2 ^ sh.a ≤ 2 ^ 64) (x : Fin (2 ^ sh.a)) (col : Fin sh.W → UInt64)
    (start s0 : ByteArray) (hs : start.size = 32)
    (hp : 164 + 65536 * Fmt.leafPlace sh.tree sh.W (s0.size / 8) < 2 ^ 64) (b : L.Bd)
    (hb : bd b = emb1 s0.size (some sh) x col)
    (hX : P.leafX ⟨b, bytesToBits start ++ bytesToBits s0⟩ = none) :
    gJ P O OracleName.leaf ⟨b, bytesToBits start ++ bytesToBits s0⟩ =
      bytesToDig (hO O (Fmt.leafNo sh.stored)
        (Fmt.leafPlace sh.tree (List.ofFn col).length (s0.size / 8)) (2 ^ sh.a + x.val) start
        (Fmt.leafBytes (List.ofFn col) s0)) := by
  rw [gJ_leaf P O _ _ hX (by
    rw [hP]
    show leafCall (bd b) _ = _
    rw [hb]
    exact leafCall_own s0.size sh hd hp x col start s0 hs)]
  simp only [Fmt.leafBytes, List.length_ofFn, hst]
  rfl

/-- At the body of a stored table's symbol: the digest of the format's leaf hash under 174, at the
symbol's own position. -/
theorem leafIs_stored_gJ (P : PageJ L K) (O : ByteArray → ByteArray) (bd : L.Bd → List Bool)
    (hP : P.leaf = leafOf bd) (a : ℕ) (y : ℕ × List UInt64) (start s0 : ByteArray)
    (hy : TypedOracleCompiler.Run.storedOK a s0.size y) (hs : start.size = 32) (b : L.Bd)
    (hb : bd b = embStored a s0.size y)
    (hX : P.leafX ⟨b, bytesToBits start ++ bytesToBits s0⟩ = none) :
    gJ P O OracleName.leaf ⟨b, bytesToBits start ++ bytesToBits s0⟩ =
      bytesToDig (hO O 174 (Fmt.leafPlace 0 y.2.length (s0.size / 8)) (2 ^ a + y.1) start
        (Fmt.leafBytes y.2 s0)) := by
  rw [gJ_leaf P O _ _ hX (by
    rw [hP]
    show leafCall (bd b) _ = _
    rw [hb]
    exact leafCall_stored a s0.size y hy start s0 hs)]
  rfl

/-- What `gJ P O` answers at a vertex. -/
theorem gJ_node (P : PageJ L K) (O : ByteArray → ByteArray) (q : Bits × Bits) :
    gJ P O OracleName.node q = bytesToDig (hO O 166 0 0 P.cfg (bitsToBytes q.1 ++ bitsToBytes q.2)) := rfl

/-- The same at two digests. -/
theorem nodeAt_gJ (P : PageJ L K) (O : ByteArray → ByteArray) (u v : Dig 256) :
    TypedOracleCompiler.Joined.nodeAt (gJ P O) u v =
      bytesToDig (hO O 166 0 0 P.cfg (digToBytes u ++ digToBytes v)) := by
  unfold TypedOracleCompiler.Joined.nodeAt digToBytes
  generalize List.ofFn u = a
  generalize List.ofFn v = b
  exact gJ_node P O (a, b)

/-- The vertices: at every page and every O. -/
theorem nodeIs_gJ (P : PageJ L K) (O : ByteArray → ByteArray) :
    NodeIs (gJ P O) (hO O) P.cfg := by
  intro l r hl hr
  rw [nodeAt_gJ, digToBytes_bytesToDig l hl, digToBytes_bytesToDig r hr]

end OnBytes.Maker.Page
