-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Run/CodingImpl.lean.
Run/CodingImpl.lean: THE FAMILY OF ORACLES OF THE COMPILED SCHEME WITH BATCHES OVER A SINGLE ORACLE
ON STRINGS, IN WHICH A POINT OF A REAL ORACLE IS WRITTEN AS ITS OWN CODE, WITH NOTHING IN FRONT.
Definitions, theorems. Generic in the code; all data compute (no definition here is marked as
without code).
Compile/Batch/ImplOf.lean builds such a family (Rom.OracleCoding) from a code c of the typed points of the
real oracles; there a point is written true :: c.put ... A format that fixes the oracle's strings to
the byte leaves no room for that bit. Here the same construction with the hotel of
Run/HotelEsc.lean: an escape e, a string with which no code begins, makes room for the spare
strings.
   codeEquivE, implE lam K L c cG e he hp : OracleCoding (typedOracleFamily lam K L) lam blocks and answers as in
   Compile/Batch/ImplOf.lean (blk K, rngEquiv)
   codeE_real, codeE_leaf, codeE_node, codeE_fb, codeE_g the string of a real point IS c.put of it
   (by definition)
   codeE_other          a spare string is written AS ITSELF unless it is copies of e and then a
                        code, or is of the form that makes room for a ghost point
   implE_leaf, implE_node      one block for a leaf, one for a node (what the top theorems ask of an
                               encoding)
   implA lam K L c e he hp      THE SAME FROM ONE CODE c OF THE REAL AND THE GHOST POINTS TOGETHER,
                                WITH ONE HOTEL. WHY: in implE the ghost points get their room among
                                the spare strings by Rom/Hotel.lean, so that a spare string of the
                                form false .. false true (a ghost point's code) is moved; whether a
                                given string of the format is of that form hangs on the ghost
                                points' code. In implA a spare string is written as itself under ONE
                                condition, which can be read off its first bytes: it is no code, and
                                does not begin with the escape (codeA_other, freeE_of). So the calls
                                of the hash that no typed query of the verifier makes (a parser's)
                                are queries to the spare oracle AT THE FORMAT'S OWN STRINGS.
IN WHICH ORDER THE BLOCKS OF A CHAIN ANSWER STAND IN THE FORMAT is no matter of this file: a point
of a chain query is (protocol, query, number of a block), and c.put may write any block of the
format for it, as long as it stays a code.
   blockAt work K       the order that the format in hand has: the typed answer is K blocks of
                        verifier message and then the chain's next value; the format has the next
                        value FIRST, or, in a round with work, SECOND behind the test block, which
                        is taken to be the first of the K. A permutation of the K + 1 numbers, with
                        its inverse.
WHAT IS NOT SAID.  Which code; which escape; that the single oracle is any hash.

Terms: lean/GLOSSARY.md.

-/
/- Limits: that a proof file is accepted or refused is no theorem of this library. It is the outcome
   of a `#guard` line, or of an evaluation outside the library: a test by Lean's evaluator, which
   leaves no declaration. So nothing that is checked of declarations is checked of such a run. No
   clause of a soundness theorem of this library speaks of a run. -/
import Run.CodingImpl
import OnBytes.TypedOracleCompiler.Compile.Batch.ImplOf
import Run.HotelEsc

set_option autoImplicit false

namespace TypedOracleCompiler.Compile.Batch
open TypedOracleCompiler.Iop Rom _root_.Compile TypedOracleCompiler.Compile.Batch
open _root_.Iop hiding BatchProtocol
export _root_.Compile.Batch (blockTo blockOf blockOf_blockTo blockTo_blockOf blockAt)

variable {I X : Type}

/-- how a point is written as a string -/
def codeEquivE (lam K : ℕ) (L : BatchProtocolWithLeafBody I X) (c : StrCode (RealPts lam K L))
    (cG : StrCode (GhostPts lam K L)) (e : List Bool) (he : e ≠ []) (hp : ∀ a t, c.put a ≠ e ++ t) :
    Pts lam K L ≃ List Bool :=
  (ptsEquiv lam K L).trans ((Equiv.sumCongr (Equiv.refl _) cG.hotel).trans (c.hotelE e he hp))

/-- The family over one oracle. -/
def implE (lam K : ℕ) (L : BatchProtocolWithLeafBody I X) (c : StrCode (RealPts lam K L))
    (cG : StrCode (GhostPts lam K L)) (e : List Bool) (he : e ≠ []) (hp : ∀ a t, c.put a ≠ e ++ t) :
    OracleCoding (typedOracleFamily lam K L) lam where
  blocks := blk K
  rng := rngEquiv lam K
  code := fun o q j => codeEquivE lam K L c cG e he hp ⟨o, q, j⟩
  inv := (codeEquivE lam K L c cG e he hp).symm
  inv_code := fun x => (codeEquivE lam K L c cG e he hp).symm_apply_apply x
  code_inv := fun s => (codeEquivE lam K L c cG e he hp).apply_symm_apply s

section
variable (lam K : ℕ) (L : BatchProtocolWithLeafBody I X) (c : StrCode (RealPts lam K L)) (cG : StrCode (GhostPts lam K L))
  (e : List Bool) (he : e ≠ []) (hp : ∀ a t, c.put a ≠ e ++ t)

/-- THE STRING OF A REAL POINT IS ITS CODE. -/
theorem codeE_real (x : RealPts lam K L) :
    codeEquivE lam K L c cG e he hp (ptsOf lam K L (.inl x)) = c.put x := by
  rcases x with (q | (q | (q | (q | (⟨t, q, j⟩ | ⟨t, q⟩))))) <;> rfl

theorem codeE_leaf (q : LeafIn L) (j : Fin 1) :
    (implE lam K L c cG e he hp).code .leaf q j = c.put (.inl q) := rfl

theorem codeE_node (q : Bits × Bits) (j : Fin 1) :
    (implE lam K L c cG e he hp).code .node q j = c.put (.inr (.inl q)) := rfl

theorem codeE_fb (t : Tag) (q : FbIn lam L t) (j : Fin (K + 1)) :
    (implE lam K L c cG e he hp).code (.fb t) q j =
      c.put (.inr (.inr (.inr (.inr (.inl ⟨t, q, j⟩))))) := rfl

theorem codeE_g (t : Tag) (q : JoiningRoundQuery lam L t) (j : Fin 1) :
    (implE lam K L c cG e he hp).code (.g t) q j =
      c.put (.inr (.inr (.inr (.inr (.inr ⟨t, q⟩))))) := rfl

/-- A spare string is written as itself, unless room had to be made at it. -/
theorem codeE_other (s : List Bool) (j : Fin 1)
    (hG : cG.free s = true) (hf : c.freeE e he s = true) :
    (implE lam K L c cG e he hp).code .other s j = s := by
  show c.hotelE e he hp (.inr (cG.enc (.inr s))) = s
  rw [show cG.enc (.inr s) = s from if_pos hG]
  exact c.hotelE_free e he hp s hf

theorem implE_leaf : (implE lam K L c cG e he hp).blocks .leaf = 1 := rfl

theorem implE_node : (implE lam K L c cG e he hp).blocks .node = 1 := rfl

end

/-! ## The same with the ghost points on the code's side -/

/-- real and ghost points together -/
abbrev AllPts (lam K : ℕ) (L : BatchProtocolWithLeafBody I X) : Type := RealPts lam K L ⊕ GhostPts lam K L

/-- how a point is written as a string, from ONE code of the real and the ghost points -/
def codeEquivA (lam K : ℕ) (L : BatchProtocolWithLeafBody I X) (c : StrCode (AllPts lam K L)) (e : List Bool)
    (he : e ≠ []) (hp : ∀ a t, c.put a ≠ e ++ t) : Pts lam K L ≃ List Bool :=
  (ptsEquiv lam K L).trans ((Equiv.sumAssoc _ _ _).symm.trans (c.hotelE e he hp))

/-- The family over one oracle, ONE hotel. -/
def implA (lam K : ℕ) (L : BatchProtocolWithLeafBody I X) (c : StrCode (AllPts lam K L)) (e : List Bool)
    (he : e ≠ []) (hp : ∀ a t, c.put a ≠ e ++ t) : OracleCoding (typedOracleFamily lam K L) lam where
  blocks := blk K
  rng := rngEquiv lam K
  code := fun o q j => codeEquivA lam K L c e he hp ⟨o, q, j⟩
  inv := (codeEquivA lam K L c e he hp).symm
  inv_code := fun x => (codeEquivA lam K L c e he hp).symm_apply_apply x
  code_inv := fun s => (codeEquivA lam K L c e he hp).apply_symm_apply s

section
variable (lam K : ℕ) (L : BatchProtocolWithLeafBody I X) (c : StrCode (AllPts lam K L)) (e : List Bool)
  (he : e ≠ []) (hp : ∀ a t, c.put a ≠ e ++ t)

theorem codeA_leaf (q : LeafIn L) (j : Fin 1) :
    (implA lam K L c e he hp).code .leaf q j = c.put (.inl (.inl q)) := rfl

theorem codeA_node (q : Bits × Bits) (j : Fin 1) :
    (implA lam K L c e he hp).code .node q j = c.put (.inl (.inr (.inl q))) := rfl

theorem codeA_fb (t : Tag) (q : FbIn lam L t) (j : Fin (K + 1)) :
    (implA lam K L c e he hp).code (.fb t) q j =
      c.put (.inl (.inr (.inr (.inr (.inr (.inl ⟨t, q, j⟩)))))) := rfl

/-- A spare string is written as itself, unless it is copies of the escape and then a code: ONE
condition. -/
theorem codeA_other (s : List Bool) (j : Fin 1) (hf : c.freeE e he s = true) :
    (implA lam K L c e he hp).code .other s j = s :=
  c.hotelE_free e he hp s hf

/-- a string that is no code and does not begin with the escape is free -/
theorem freeE_of (s : List Bool) (h : c.parse s = none) (hs : StrCode.strip e s = none) :
    c.freeE e he s = true :=
  StrCode.freeE_none he h hs

theorem implA_leaf : (implA lam K L c e he hp).blocks .leaf = 1 := rfl

theorem implA_node : (implA lam K L c e he hp).blocks .node = 1 := rfl

end

end TypedOracleCompiler.Compile.Batch
