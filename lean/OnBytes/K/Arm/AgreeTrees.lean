-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/K/Arm/AgreeTrees.lean: two encodings of the typed oracles of one interface into one hash
function that give every leaf query and every vertex query the same string.

The compiled verifier has three parts, one for each file that the prover sends. Each part may have
an encoding of its own (`Rom.OracleCoding`, Rom/Family.lean). A leaf query and a vertex query bear no mark
of the part that asks them, and a root that one part has checked is handed to another. So the
encodings must read the same two typed oracles out of a hash function. Here that is a statement on
the encodings' strings, with what is enough for it at two pages (OnBytes/TypedOracleCompiler/Run/PageG.lean) and
what follows from it. For proofs only; the program does not import this file.

Main definition.
 `AgreeTrees m m'`   every leaf query has one string under m and m', block for block, and so has
                    every vertex query.
Main theorems.
 `agree_of_pages`    it holds of `implG C` and `implG C'`, if the two pages' partial codes write the
                    same at every leaf and at every vertex (both a string, the same; or both
                    nothing), and their total codes write the same there.
 `agree_of_back`     the same with one total code.
 `agree_implOf`      the same against the encoding of a function (`implOf`,
                    OnBytes/TypedOracleCompiler/Run/PageOf.lean).
 `agree_symm`, `agree_trans`   the relation turns round; at three pages it goes through.
 `AgreeTrees.leaf`, `AgreeTrees.node`   then, out of every hash function g, both encodings read the
                    same answer at every leaf query and at every vertex query.

Not claimed. That any two pages meet what is asked. Where a page's partial code does not write, the
string is the total code's behind an escape: so the total codes are asked to agree as well. Nothing
on the request tree's two oracles, on chain queries or on the queries for a slot value. Nothing on
any hash function. Nothing on soundness.


-/
import OnBytes.TypedOracleCompiler.Run.PageOf

set_option autoImplicit false

namespace OnBytes.K.Arm
open Rom _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run
open TypedOracleCompiler.Run.PageG TypedOracleCompiler.Run.PageOf
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run

variable {I X : Type} {L : BatchProtocolWithLeafBody I X} {K : ℕ}

/-- **Two encodings give every leaf query and every vertex query the same string**, block for
block. The blocks' numbers are compared as numbers, since the two encodings may count them in two
types. -/
def AgreeTrees (m m' : OracleCoding (typedOracleFamily 256 K L) 256) : Prop :=
  (∀ (q : LeafIn L) (j : Fin (m.blocks .leaf)) (j' : Fin (m'.blocks .leaf)), j.val = j'.val →
    m.code .leaf q j = m'.code .leaf q j') ∧
  ∀ (q : Bits × Bits) (j : Fin (m.blocks .node)) (j' : Fin (m'.blocks .node)), j.val = j'.val →
    m.code .node q j = m'.code .node q j'

/-- It turns round. -/
theorem agree_symm {m m' : OracleCoding (typedOracleFamily 256 K L) 256} (h : AgreeTrees m m') : AgreeTrees m' m :=
  ⟨fun q j j' e => (h.1 q j' j e.symm).symm, fun q j j' e => (h.2 q j' j e.symm).symm⟩

section
variable (C C' : Page L K)

/-- The total codes of two pages write the same at a real point, if the partial codes do and the
codes behind the escape do. -/
theorem totalG_same (a : RealPts 256 K L) (h : C.real.put a = C'.real.put a)
    (hb : C.back.put (.inl a) = C'.back.put (.inl a)) :
    (totalG C).put (.inl a) = (totalG C').put (.inl a) := by
  cases e : C.real.put a with
  | some s => rw [totalG_real C a s e, totalG_real C' a s (h.symm.trans e)]
  | none => rw [totalG_none C a e, totalG_none C' a (h.symm.trans e), hb]

/-- **Two pages' encodings agree on the trees.** -/
theorem agree_of_pages
    (hl : ∀ q : LeafIn L, C.real.put (.inl q) = C'.real.put (.inl q))
    (hn : ∀ q : Bits × Bits, C.real.put (.inr (.inl q)) = C'.real.put (.inr (.inl q)))
    (hbl : ∀ q : LeafIn L, C.back.put (.inl (.inl q)) = C'.back.put (.inl (.inl q)))
    (hbn : ∀ q : Bits × Bits,
      C.back.put (.inl (.inr (.inl q))) = C'.back.put (.inl (.inr (.inl q)))) :
    AgreeTrees (implG C) (implG C') :=
  ⟨fun q _ _ _ => totalG_same C C' (.inl q) (hl q) (hbl q),
    fun q _ _ _ => totalG_same C C' (.inr (.inl q)) (hn q) (hbn q)⟩

/-- The same with one total code. -/
theorem agree_of_back
    (hl : ∀ q : LeafIn L, C.real.put (.inl q) = C'.real.put (.inl q))
    (hn : ∀ q : Bits × Bits, C.real.put (.inr (.inl q)) = C'.real.put (.inr (.inl q)))
    (hb : C.back = C'.back) : AgreeTrees (implG C) (implG C') :=
  agree_of_pages C C' hl hn (fun _ => by rw [hb]) fun _ => by rw [hb]

/-- **Against the encoding of a function** that is one to one where it writes, with the page's own
total code. -/
theorem agree_implOf (put : RealPts 256 K L → Option (List Bool))
    (inj : ∀ a b s, put a = some s → put b = some s → a = b)
    (hd : ∀ a s, put a = some s → ∀ e : UInt8, e ≠ 0 → e ≠ 1 → ¬ bitsOfByte e <+: s)
    (hl : ∀ q : LeafIn L, C.real.put (.inl q) = put (.inl q))
    (hn : ∀ q : Bits × Bits, C.real.put (.inr (.inl q)) = put (.inr (.inl q))) :
    AgreeTrees (implG C) (implOf put inj hd C.back) :=
  agree_of_back C (pageOf put inj hd C.back) hl hn rfl

variable {C C'}

/-- At three pages it goes through. -/
theorem agree_trans {C'' : Page L K} (h : AgreeTrees (implG C) (implG C'))
    (h' : AgreeTrees (implG C') (implG C'')) : AgreeTrees (implG C) (implG C'') :=
  ⟨fun q j j'' e => (h.1 q j j rfl).trans (h'.1 q j j'' e),
    fun q j j'' e => (h.2 q j j rfl).trans (h'.2 q j j'' e)⟩

/-- **Both encodings read the same answer at every leaf query**, out of every hash function. -/
theorem AgreeTrees.leaf (h : AgreeTrees (implG C) (implG C')) (g : Fam (rom 256)) (q : LeafIn L) :
    (readBlocks (implG C) g .leaf q : Dig 256) = readBlocks (implG C') g .leaf q := by
  show g () ((implG C).code .leaf q (0 : Fin 1)) = g () ((implG C').code .leaf q (0 : Fin 1))
  rw [h.1 q (0 : Fin 1) (0 : Fin 1) rfl]

/-- **And at every vertex query.** -/
theorem AgreeTrees.node (h : AgreeTrees (implG C) (implG C')) (g : Fam (rom 256))
    (q : Bits × Bits) :
    (readBlocks (implG C) g .node q : Dig 256) = readBlocks (implG C') g .node q := by
  show g () ((implG C).code .node q (0 : Fin 1)) = g () ((implG C').code .node q (0 : Fin 1))
  rw [h.2 q (0 : Fin 1) (0 : Fin 1) rfl]

end

end OnBytes.K.Arm
