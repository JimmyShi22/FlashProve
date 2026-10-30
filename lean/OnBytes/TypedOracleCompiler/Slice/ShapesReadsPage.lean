-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Slice/ShapesReadsPage.lean: when an implementation that is made of a page's data spells
vertices and stored leaves as the one written reading reads them; and the clause `reads` in the form
in which it is owed for a part by the way "type, then run".

`Spells` (OnBytes/TypedOracleCompiler/Slice/ShapesReads.lean) is two equations on an implementation's strings. The
general implementation `PageG.implG C` (OnBytes/TypedOracleCompiler/Run/PageG.lean) is made of a partial code `real`
of the real points and a total code `back` behind the byte 2. Here `Spells` is brought down to three
equations on these two codes.

Main theorems.
 `spells_implG`        `implG C` spells, if `real` writes a vertex query as `nodeStr`, writes a
                       leaf query on a stored symbol exactly where and as `callStr` does, and `back`
                       writes such a query as four marks and the two serial forms.
 `PlainRead.withTyping`, `reads_ofTyping`   a part with another checker reads as the part does; the
                       clause `reads` for `FileSpec.ofTyping`.

What is not claimed. That any page's codes meet the three equations. THE THIRD IS A DEBT ON `back`,
which is therefore not free: it is met by a total code that serialises a leaf query as a mark for
"real point", a mark for "leaf", the body and the salt, with a serialiser of bodies that writes a
stored symbol as "some", "left" and `Ser.prod Ser.natG (Ser.list serW)` of it
(OnBytes/TypedOracleCompiler/Run/SerTie.lean); no theorem here says so. No probability. Nothing on any hash
function. The compiler under OnBytes/TypedOracleCompiler/ is the one that `innerCompiledVerifier` is made with; it
builds on definitions of Compile/.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Slice.ShapesReadsPart
import OnBytes.TypedOracleCompiler.Slice.ShapesTyping
import OnBytes.TypedOracleCompiler.Run.PageG

set_option autoImplicit false

namespace OnBytes.Slice.Shapes
open Rom _root_.Run _root_.Compile
open _root_.Iop (Dig Ser)
open _root_.Run.PQ (SgX serW)
open TypedOracleCompiler.Run.PageG (implG)

/-- THE GENERAL IMPLEMENTATION SPELLS, if its partial code writes a vertex query on two digests
as the vertex's string; writes a leaf query on a stored symbol, with any salt, exactly where there
is a call's string, and as that string; and its total code behind the byte 2 writes such a query as
the four marks and the serial forms of symbol and salt. -/
theorem spells_implG {I X : Type} {K : ℕ} {L : TypedOracleCompiler.Iop.BatchProtocolWithLeafBody I X}
    (C : TypedOracleCompiler.Run.PageG.Page L K) (e : SgX → L.Bd) (c : ByteArray) (a n : ℕ)
    (hn : ∀ x y : Dig 256,
      C.real.put (.inr (.inl (List.ofFn x, List.ofFn y))) = some (nodeStr c (x, y)))
    (hl : ∀ y salt, C.real.put (.inl ⟨e y, salt⟩) = callStr c a n y salt)
    (hb : ∀ y salt, C.back.put (.inl (.inl ⟨e y, salt⟩)) = false :: false :: true :: false ::
      ((Ser.prod Ser.natG (Ser.list serW)).put y ++ serBits.put salt)) :
    Spells (implG C) e c a n where
  node := fun x y j => TypedOracleCompiler.Run.PageG.implG_node C _ _ (hn x y) j
  stored := fun y salt j => by
    rw [TypedOracleCompiler.Run.PageG.implG_code_leaf C ⟨e y, salt⟩ j, hl, hb]
    rfl

/-- A part with another checker and count reads plainly if the part does. -/
theorem PlainRead.withTyping {p : TypedOracleCompiler.Slice.Part 256 Files SgX} {a : ℕ}
    (h : PlainRead p a) (typ : Files → OComp (rom 256) (Option p.Out)) (tT B : ℕ) :
    PlainRead (withTyping p typ tT B) a :=
  ⟨h.depth, h.len, h.fill, h.byLeaves, h.back, h.only⟩

/-- THE CLAUSE `reads` FOR A PART BY THE WAY "TYPE, THEN RUN", at `rdAt z dg`: from facts on
`base` alone. Asked at all tables: the part reads plainly at z's depth; one block; the
implementation spells at the digest off the first table, z's depth and salt length. -/
theorem reads_ofTyping (base : Tab → Tab → TypedOracleCompiler.Slice.Part 256 Files SgX)
    (typ : ∀ T₀ T₁, Files → OComp (rom 256) (Option (base T₀ T₁).Out))
    (pre : ∀ T₀ T₁, (o : (TypedOracleCompiler.Compile.Batch.typedOracleFamily 256 (base T₀ T₁).W.K (base T₀ T₁).L).ι) →
      (TypedOracleCompiler.Compile.Batch.typedOracleFamily 256 (base T₀ T₁).W.K (base T₀ T₁).L).Dom o →
      TypedOracleCompiler.Compile.Batch.TypedOracleComputation 256 (base T₀ T₁).W.K (base T₀ T₁).L Unit)
    (n tT B : ℕ) (z : Size) (dg : Tab → ByteArray) (hdg : ∀ T₀, (dg T₀).size = 32)
    (hP : ∀ T₀ T₁, PlainRead (base T₀ T₁) z.T.a)
    (one : ∀ T₀ T₁, TypedOracleCompiler.Run.OneBlock (base T₀ T₁).m)
    (hS : ∀ T₀ T₁, Spells (base T₀ T₁).m
      (fun y => (base T₀ T₁).W.embE ((base T₀ T₁).u.symm y)) (dg T₀) z.T.a z.shape.saltBytes) :
    ∀ T₀ T₁ σ, NoClash σ → ∀ cm,
      ((FileSpec.ofTyping base typ pre n tT B).part T₀ T₁).raw σ cm = rdAt z dg T₀ T₁ σ cm :=
  FileSpec.reads_of_spells (FileSpec.ofTyping base typ pre n tT B) z dg hdg
    (fun T₀ T₁ => (hP T₀ T₁).withTyping (typ T₀ T₁) tT B) one hS

end OnBytes.Slice.Shapes
