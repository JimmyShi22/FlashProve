-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/Page/LeafAgree.lean: the laws on the leaves of OnBytes/Maker/Page/Trees.lean under a
weaker premise on the page's taken spelling of leaves (`PageJ.leafX`): it writes nothing at the
query, or it writes the string of the page's own call.

The page asks the taken spelling first (`takenJ`, OnBytes/Maker/Page/Frame.lean). A typed leaf query
bears no tag, and the bodies of the three files' leaves have one form: so a code of the entry file's
leaves may write at a key file's or a proof file's leaf too.

Main names.
  `gJ_leaf'`: what `gJ P O` answers at a leaf query at which the taken spelling writes nothing or
    writes the string of the page's own call.
  `leafIs_own_gJ'`, `leafIs_stored_gJ'`: the two laws of Trees.lean under that premise.

Limits: whether a code of leaves agrees with the page's own call where it writes is shown of none.
`gJ P O` is a function of the typed query, no one-to-one coding. Nothing on soundness.


-/
import OnBytes.Maker.Page.Trees

set_option autoImplicit false

namespace OnBytes.Maker.Page
open Rom _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run OnBytes.Flat

variable {I X : Type} {L : BatchProtocolWithLeafBody I X} {K : ℕ}

/-- What `gJ P O` answers at a leaf query at which the taken spelling writes nothing, or the string
of the page's own call. -/
theorem gJ_leaf' (P : PageJ L K) (O : ByteArray → ByteArray) (q : LeafIn L) (c : Fmt.OQ)
    (hc : P.leaf q = some c) (hX : ∀ s, P.leafX q = some s → bitsToBytes s = strOf c) :
    gJ P O OracleName.leaf q = bytesToDig (O (strOf c)) := by
  cases hx : P.leafX q with
  | none => exact gJ_leaf P O q c hx hc
  | some s =>
    show ansJ O (codeJ P .leaf q (0 : Fin 1)) = _
    have e : codeJ P .leaf q (0 : Fin 1) = some (strOf c) := by
      unfold codeJ
      show (match P.leafX q with
        | some s => some (bitsToBytes s)
        | none => (P.leaf q).map strOf) = _
      rw [hx]
      show some (bitsToBytes s) = _
      rw [hX s hx]
    rw [e]
    rfl

/-- At the body of a symbol of a run's tree. -/
theorem leafIs_own_gJ' (P : PageJ L K) (O : ByteArray → ByteArray) (bd : L.Bd → List Bool)
    (hP : P.leaf = leafOf bd) (sh : Fmt.Shape) (hst : sh.stored = false)
    (hd : 2 ^ sh.a + 2 ^ sh.a ≤ 2 ^ 64) (x : Fin (2 ^ sh.a)) (col : Fin sh.W → UInt64)
    (start s0 : ByteArray) (hs : start.size = 32)
    (hp : 164 + 65536 * Fmt.leafPlace sh.tree sh.W (s0.size / 8) < 2 ^ 64) (b : L.Bd)
    (hb : bd b = emb1 s0.size (some sh) x col)
    (hX : ∀ s, P.leafX ⟨b, bytesToBits start ++ bytesToBits s0⟩ = some s →
      bitsToBytes s = Fmt.oStr 0 164 (Fmt.leafPlace sh.tree sh.W (s0.size / 8)) (2 ^ sh.a + x.val)
        start (Fmt.colBytes (List.ofFn col) ++ Fmt.zeroBytes (Fmt.fillLen sh.W s0.size) ++ s0)) :
    gJ P O OracleName.leaf ⟨b, bytesToBits start ++ bytesToBits s0⟩ =
      bytesToDig (hO O (Fmt.leafNo sh.stored)
        (Fmt.leafPlace sh.tree (List.ofFn col).length (s0.size / 8)) (2 ^ sh.a + x.val) start
        (Fmt.leafBytes (List.ofFn col) s0)) := by
  rw [gJ_leaf' P O _ _ (by
    rw [hP]
    show leafCall (bd b) _ = _
    rw [hb]
    exact leafCall_own s0.size sh hd hp x col start s0 hs) hX]
  simp only [Fmt.leafBytes, List.length_ofFn, hst]
  rfl

/-- At the body of a stored table's symbol, at the symbol's own position. -/
theorem leafIs_stored_gJ' (P : PageJ L K) (O : ByteArray → ByteArray) (bd : L.Bd → List Bool)
    (hP : P.leaf = leafOf bd) (a : ℕ) (y : ℕ × List UInt64) (start s0 : ByteArray)
    (hy : TypedOracleCompiler.Run.storedOK a s0.size y) (hs : start.size = 32) (b : L.Bd)
    (hb : bd b = embStored a s0.size y)
    (hX : ∀ s, P.leafX ⟨b, bytesToBits start ++ bytesToBits s0⟩ = some s →
      bitsToBytes s = Fmt.oStr 0 174 (Fmt.leafPlace 0 y.2.length (s0.size / 8)) (2 ^ a + y.1) start
        (Fmt.colBytes y.2 ++ Fmt.zeroBytes (Fmt.fillLen y.2.length s0.size) ++ s0)) :
    gJ P O OracleName.leaf ⟨b, bytesToBits start ++ bytesToBits s0⟩ =
      bytesToDig (hO O 174 (Fmt.leafPlace 0 y.2.length (s0.size / 8)) (2 ^ a + y.1) start
        (Fmt.leafBytes y.2 s0)) := by
  rw [gJ_leaf' P O _ _ (by
    rw [hP]
    show leafCall (bd b) _ = _
    rw [hb]
    exact leafCall_stored a s0.size y hy start s0 hs) hX]
  rfl

end OnBytes.Maker.Page
