-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Run/PageOf.lean: from a function that writes some typed points of the compiled
verifier's oracles as strings, one to one where it writes, to an encoding of all typed oracles into
one hash function (`Rom.OracleCoding`, Rom/Family.lean); and what that encoding reads out of a hash function
at a typed query whose points are written.

OnBytes/TypedOracleCompiler/Run/PageG.lean makes an encoding `implG C` of a page C: a partial code `real` of the
real points with a parser, of whose strings no byte other than 0 and 1 is a prefix, and any total
code `back`. It says which STRING a typed query has (`implG_leaf` and its like). Two tools are added
here. (1) A partial code asks a parser that reads back what is written and refuses all else. For a
function that is one to one where it writes, such a parser exists: it is taken by choice, so no
program is given for it. (2) What `readBlocks` of that encoding returns, block by block, for each
kind of real point. For proofs only; the program does not import this file.

Main definitions: `ofInj`, `pageOf`, `implOf`.
Main theorems.
 `ofInj_put`      the partial code writes what the function writes.
 `reads_leaf`     with `reads_node`, `reads_rleaf`, `reads_rnode`, `reads_g`: where `real` writes
                  the string s at the query, the typed answer that is read out of g is g's answer at
                  s.
 `reads_fb`       with `reads_fb_last`: the same for digest k of a chain query's answer, and for its
                  chain value, which is the last block.
 `implOf_leaf`    with its six like: the same at `implOf put inj hd back`, with `put` in the place
                  of `real.put`.

What is not claimed. That any function is one to one where it writes, or that no byte other than 0
and 1 is a prefix of one of its strings. That a total code `back` exists at any interface. That the
strings are those that any program hashes. That the function writes at every typed point that a
verifier asks. At a typed point where the function does not write, the string is `back`'s behind an
escape, and nothing is said here of what is read there: the laws on reading say nothing. `ofInj`,
`pageOf` and `implOf` are noncomputable: the parser, and so the encoding's inverse, is had by
choice. So what the library's comment on the field `inv` of `Rom.OracleCoding` says (Rom/Family.lean: the
inverse is data, so that the extractor and the simulator over f use no choice either) does not hold
of an encoding that is made here. Nothing on any hash function; nothing on soundness.


-/
import OnBytes.TypedOracleCompiler.Run.PageG

set_option autoImplicit false

namespace TypedOracleCompiler.Run.PageOf
open Rom _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run
open TypedOracleCompiler.Run.PageG
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run

/-! ## A partial code from a function that is one to one where it writes -/

section
variable {A : Type} (put : A → Option (List Bool))
  (inj : ∀ a b s, put a = some s → put b = some s → a = b)

open Classical in
/-- **The partial code of a function that is one to one where it writes.** The parser is taken by
choice: some point at which the string is written, if there is one. -/
noncomputable def ofInj : PCode A where
  put := put
  parse := fun s => if h : ∃ a, put a = some s then some h.choose else none
  parse_put := fun a s h => by
    have hx : ∃ a, put a = some s := ⟨a, h⟩
    rw [dif_pos hx]
    exact congrArg some (inj _ _ s hx.choose_spec h)
  put_parse := fun s a h => by
    by_cases hx : ∃ a, put a = some s
    · rw [dif_pos hx] at h
      rw [← Option.some.inj h]
      exact hx.choose_spec
    · rw [dif_neg hx] at h
      cases h

/-- It writes what the function writes. -/
theorem ofInj_put : (ofInj put inj).put = put := rfl

end

/-! ## What the encoding of a page reads out of a hash function -/

variable {I X : Type} {L : BatchProtocolWithLeafBody I X} {K : ℕ}

section
variable (C : Page L K) (g : Fam (rom 256))

/-- A leaf query at which `real` writes. -/
theorem reads_leaf (q : LeafIn L) (s : List Bool) (h : C.real.put (.inl q) = some s) :
    (readBlocks (implG C) g .leaf q : Dig 256) = g () s := by
  show g () ((implG C).code .leaf q (0 : Fin 1)) = _
  rw [implG_leaf C q s h]

/-- A vertex query at which `real` writes. -/
theorem reads_node (q : Bits × Bits) (s : List Bool) (h : C.real.put (.inr (.inl q)) = some s) :
    (readBlocks (implG C) g .node q : Dig 256) = g () s := by
  show g () ((implG C).code .node q (0 : Fin 1)) = _
  rw [implG_node C q s h]

/-- A request tree's leaf query at which `real` writes. -/
theorem reads_rleaf (q : Bits) (s : List Bool) (h : C.real.put (.inr (.inr (.inl q))) = some s) :
    (readBlocks (implG C) g .rleaf q : Dig 256) = g () s := by
  show g () ((implG C).code .rleaf q (0 : Fin 1)) = _
  rw [implG_rleaf C q s h]

/-- A request tree's vertex query at which `real` writes. -/
theorem reads_rnode (q : Bits × Bits) (s : List Bool)
    (h : C.real.put (.inr (.inr (.inr (.inl q)))) = some s) :
    (readBlocks (implG C) g .rnode q : Dig 256) = g () s := by
  show g () ((implG C).code .rnode q (0 : Fin 1)) = _
  rw [implG_rnode C q s h]

/-- **Digest k of a chain query's answer**, where `real` writes at that block. -/
theorem reads_fb (t : Tag) (q : FbIn 256 L t) (k : Fin K) (s : List Bool)
    (h : C.real.put (.inr (.inr (.inr (.inr (.inl ⟨t, q, k.castSucc⟩))))) = some s) :
    (readBlocks (implG C) g (.fb t) q : (Fin K → Dig 256) × Dig 256).1 k = g () s := by
  show g () ((implG C).code (.fb t) q k.castSucc) = _
  rw [implG_fb C t q k.castSucc s h]

/-- **The chain value of a chain query's answer**: the last block, where `real` writes at it. -/
theorem reads_fb_last (t : Tag) (q : FbIn 256 L t) (s : List Bool)
    (h : C.real.put (.inr (.inr (.inr (.inr (.inl ⟨t, q, Fin.last K⟩))))) = some s) :
    (readBlocks (implG C) g (.fb t) q : (Fin K → Dig 256) × Dig 256).2 = g () s := by
  show g () ((implG C).code (.fb t) q (Fin.last K)) = _
  rw [implG_fb C t q (Fin.last K) s h]

/-- A query to g at which `real` writes. -/
theorem reads_g (t : Tag) (q : JoiningRoundQuery 256 L t) (s : List Bool)
    (h : C.real.put (.inr (.inr (.inr (.inr (.inr ⟨t, q⟩))))) = some s) :
    (readBlocks (implG C) g (.g t) q : Dig 256) = g () s := by
  show g () ((implG C).code (.g t) q (0 : Fin 1)) = _
  rw [implG_g C t q s h]

end

/-! ## The page and the encoding of a function -/

section
variable (put : RealPts 256 K L → Option (List Bool))
  (inj : ∀ a b s, put a = some s → put b = some s → a = b)
  (hd : ∀ a s, put a = some s → ∀ e : UInt8, e ≠ 0 → e ≠ 1 → ¬ bitsOfByte e <+: s)
  (back : StrCode (AllPts 256 K L))

/-- **The page of a function on the real points**: one to one where it writes; no byte other than 0
and 1 is a prefix of one of its strings. -/
noncomputable def pageOf : Page L K where
  real := ofInj put inj
  hd := hd
  back := back

/-- **The encoding of the typed oracles into one hash function.** -/
noncomputable def implOf : OracleCoding (typedOracleFamily 256 K L) 256 := implG (pageOf put inj hd back)

variable (g : Fam (rom 256))

/-- A leaf query that is written. -/
theorem implOf_leaf (q : LeafIn L) (s : List Bool) (h : put (.inl q) = some s) :
    (readBlocks (implOf put inj hd back) g .leaf q : Dig 256) = g () s :=
  reads_leaf (pageOf put inj hd back) g q s h

/-- A vertex query that is written. -/
theorem implOf_node (q : Bits × Bits) (s : List Bool) (h : put (.inr (.inl q)) = some s) :
    (readBlocks (implOf put inj hd back) g .node q : Dig 256) = g () s :=
  reads_node (pageOf put inj hd back) g q s h

/-- A request tree's leaf query that is written. -/
theorem implOf_rleaf (q : Bits) (s : List Bool) (h : put (.inr (.inr (.inl q))) = some s) :
    (readBlocks (implOf put inj hd back) g .rleaf q : Dig 256) = g () s :=
  reads_rleaf (pageOf put inj hd back) g q s h

/-- A request tree's vertex query that is written. -/
theorem implOf_rnode (q : Bits × Bits) (s : List Bool)
    (h : put (.inr (.inr (.inr (.inl q)))) = some s) :
    (readBlocks (implOf put inj hd back) g .rnode q : Dig 256) = g () s :=
  reads_rnode (pageOf put inj hd back) g q s h

/-- Digest k of a chain query's answer, where that block is written. -/
theorem implOf_fb (t : Tag) (q : FbIn 256 L t) (k : Fin K) (s : List Bool)
    (h : put (.inr (.inr (.inr (.inr (.inl ⟨t, q, k.castSucc⟩))))) = some s) :
    (readBlocks (implOf put inj hd back) g (.fb t) q : (Fin K → Dig 256) × Dig 256).1 k = g () s :=
  reads_fb (pageOf put inj hd back) g t q k s h

/-- The chain value of a chain query's answer, where the last block is written. -/
theorem implOf_fb_last (t : Tag) (q : FbIn 256 L t) (s : List Bool)
    (h : put (.inr (.inr (.inr (.inr (.inl ⟨t, q, Fin.last K⟩))))) = some s) :
    (readBlocks (implOf put inj hd back) g (.fb t) q : (Fin K → Dig 256) × Dig 256).2 = g () s :=
  reads_fb_last (pageOf put inj hd back) g t q s h

/-- A query to g that is written. -/
theorem implOf_g (t : Tag) (q : JoiningRoundQuery 256 L t) (s : List Bool)
    (h : put (.inr (.inr (.inr (.inr (.inr ⟨t, q⟩))))) = some s) :
    (readBlocks (implOf put inj hd back) g (.g t) q : Dig 256) = g () s :=
  reads_g (pageOf put inj hd back) g t q s h

end

end TypedOracleCompiler.Run.PageOf
