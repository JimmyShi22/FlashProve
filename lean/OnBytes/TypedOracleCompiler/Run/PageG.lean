-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Run/PageG.lean: from ANY partial code of the typed oracles' points whose strings begin
with the byte 0 or 1, to a total one-to-one code of all points and the family over one oracle; and a
partial code of chain queries under all three tags from one code for each tag.

The sibling's page (`PageC`, OnBytes/TypedOracleCompiler/Run/CodingPage.lean; the sibling is a second form of
the library's soundness road, under OnBytes/TypedOracleCompiler/) builds its partial code from data of a fixed form:
one tag, one chain with one label, one first call. A file with several chains, typed as one chain,
and a second typed chain under another tag do not fit that form. What `PageC` does behind its
partial code does not hang on the form: a point that the format writes has its string of the format;
every other point has the byte 2 and then its string under any total code `back`; the byte 3 is the
escape of the spare strings. This file says that part again for any partial code.
 - `Page L K`: the data: `real`, a partial code of the real points; `hd`: its strings begin with no
   byte other than 0 and 1; `back`;
 - `pAllG`, `totalG : StrCode (AllPts 256 K L)`, `implG : OracleCoding (typedOracleFamily 256 K L) 256`: the family over
   one oracle, with its inverse and both laws by the library's `implA`;
 - `implG_leaf`, `implG_node`, `implG_rleaf`, `implG_rnode`, `implG_fb`, `implG_g`: the string of a
   typed query that `real` writes IS that string;
 - `totalG_none`, `totalG_ghost`: a real point that `real` does not write, and every ghost point,
   has the byte 2 and then its string under `back`; `implG_code_leaf`: so the string of EVERY leaf
   query;
 - `implG_leaf1`, `implG_node1`, `implG_fbK`, `oneBlock_implG`: a leaf's and a vertex's answer is
   one block, taken as it is (`OneBlock`, OnBytes/TypedOracleCompiler/Run/PageXJoin.lean); a chain query's has K +
   1;
 - `implG_other`, `implG_other'`: a string that `real` does not parse (that it writes at no point)
   and that begins with neither escape is a point of the spare oracle, written as itself: BY PARSE,
   not by tag: also a string under one of the format's numbers that no typed point has;
 - `implG_not_public`: no point of an oracle other than the spare one has a string that `real` does
   not parse and that does not begin with the byte 2;
 - `byTag pT pL pO`: the code of chain queries with a block under all tags, from one code a tag,
   given that no two of them have a string in common; `byTag_put`, `byTag_some`;
 - `Leaves`, `realOf V cfg hcfg fb hfb`: the real points from a code of leaf queries (tags of 164,
   174), the library's code of vertices and a code of chain queries (tags of 160, 162, 173; first
   byte 0 or 1): for a judge that asks nothing else; `realOf_hd`, `realOf_tag`.

Main definitions: `Page`, `pAllG`, `totalG`, `implG`, `byTag`, `Leaves`, `realOf`.
Main theorems: `implG_leaf`, `implG_node`, `implG_rleaf`, `implG_rnode`, `implG_fb`, `implG_g`,
`totalG_none`, `oneBlock_implG`, `implG_code_leaf`, `implG_other`, `implG_not_public`, `byTag_put`,
`byTag_some`, `realOf_hd`, `realOf_tag`.

Not claimed. No data: which points the format writes, and how. That `real`'s strings are the
format's. One-to-one-ness of `real` lies in its being a partial code: whoever gives it has shown it.
Nothing on any hash. Nothing on soundness.
The compiler under OnBytes/TypedOracleCompiler/ is the one that `innerCompiledVerifier` is made with; it builds on
definitions of Compile/.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Run.PageXJoin
import OnBytes.TypedOracleCompiler.Run.Apart

set_option autoImplicit false

namespace TypedOracleCompiler.Run.PageG
open Rom _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run
open TypedOracleCompiler.Run.Apart
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run

variable {I X : Type}

/-- The data: a partial code of the real points, whose strings begin with the byte 0 or 1; any
total code of the real and the ghost points. -/
structure Page (L : BatchProtocolWithLeafBody I X) (K : ℕ) where
  /-- the partial code: what it writes is meant to be the format's strings -/
  real : PCode (RealPts 256 K L)
  /-- its strings begin with no byte other than 0 and 1 -/
  hd : ∀ a s, real.put a = some s → ∀ e : UInt8, e ≠ 0 → e ≠ 1 → ¬ bitsOfByte e <+: s
  /-- it writes, behind an escape, all points at which `real` does not write -/
  back : StrCode (AllPts 256 K L)

variable {L : BatchProtocolWithLeafBody I X} {K : ℕ} (C : Page L K)

/-- A real point among all points. -/
def selA : AllPts 256 K L → Option (RealPts 256 K L)
  | .inl a => some a
  | .inr _ => none

/-- Reading undoes putting in. -/
theorem selA_inl (a : RealPts 256 K L) : selA (L := L) (K := K) (.inl a) = some a := rfl

/-- Putting in undoes reading. -/
theorem inl_selA (b : AllPts 256 K L) (a : RealPts 256 K L) (h : selA b = some a) :
    Sum.inl a = b := by
  rcases b with b | b
  · exact congrArg Sum.inl (Option.some.inj h).symm
  · cases h

/-- What `real` writes, as a partial code of the real and the ghost points. -/
def pAllG : PCode (AllPts 256 K L) := C.real.via selA Sum.inl selA_inl inl_selA

/-- Whatever it writes, `real` writes. -/
theorem pAllG_put (a : AllPts 256 K L) (s : List Bool) (h : (pAllG C).put a = some s) :
    ∃ b, C.real.put b = some s := by
  obtain ⟨b, -, hb⟩ := PCode.via_put' _ _ _ _ _ a s h
  exact ⟨b, hb⟩

/-- Its strings begin with no byte other than 0 and 1. -/
theorem pAllG_hd (a : AllPts 256 K L) (s : List Bool) (h : (pAllG C).put a = some s) (e : UInt8)
    (h0 : e ≠ 0) (h1 : e ≠ 1) : ¬ bitsOfByte e <+: s := by
  obtain ⟨b, hb⟩ := pAllG_put C a s h
  exact C.hd b s hb e h0 h1

/-- None begins with the byte 2. -/
theorem pAllG_no2 (a : AllPts 256 K L) (s : List Bool) (h : (pAllG C).put a = some s) :
    ¬ bitsOfByte 2 <+: s := pAllG_hd C a s h 2 (by decide) (by decide)

/-- The total code: a point at which `real` writes: that string; every other point: the byte 2
and then its string under `back`. -/
def totalG : StrCode (AllPts 256 K L) := (pAllG C).orElse C.back (bitsOfByte 2) (pAllG_no2 C)

/-- No string of the total code begins with the byte 3. -/
theorem totalG_esc (a : AllPts 256 K L) (t : List Bool) :
    (totalG C).put a ≠ bitsOfByte 3 ++ t := fun h =>
  PCode.orElse_not_prefix (pAllG C) C.back (bitsOfByte 2) (pAllG_no2 C) (bitsOfByte 3)
    (fun a s h => pAllG_hd C a s h 3 (by decide) (by decide))
    (fun r => byte_prefix 3 2 (by decide) r) a ⟨t, h.symm⟩

/-- The family over one oracle. -/
def implG : OracleCoding (typedOracleFamily 256 K L) 256 :=
  implA 256 K L (totalG C) (bitsOfByte 3) esc_ne (totalG_esc C)

/-- The total code at a real point at which `real` writes. -/
theorem totalG_real (a : RealPts 256 K L) (s : List Bool) (h : C.real.put a = some s) :
    (totalG C).put (.inl a) = s :=
  PCode.orElse_put_some (pAllG C) C.back (bitsOfByte 2) (pAllG_no2 C) (a := .inl a) h

/-- The total code at a real point at which `real` does not write: the byte 2, then the point's
string under `back`. -/
theorem totalG_none (a : RealPts 256 K L) (h : C.real.put a = none) :
    (totalG C).put (.inl a) = bitsOfByte 2 ++ C.back.put (.inl a) :=
  PCode.orElse_put_none (pAllG C) C.back (bitsOfByte 2) (pAllG_no2 C) (a := .inl a) h

/-- The total code at a ghost point: the byte 2, then the point's string under `back`. -/
theorem totalG_ghost (a : GhostPts 256 K L) :
    (totalG C).put (.inr a) = bitsOfByte 2 ++ C.back.put (.inr a) :=
  PCode.orElse_put_none (pAllG C) C.back (bitsOfByte 2) (pAllG_no2 C) (a := .inr a) rfl

/-- A leaf's answer is one block. -/
theorem implG_leaf1 : (implG C).blocks .leaf = 1 := rfl

/-- A vertex's answer is one block. -/
theorem implG_node1 : (implG C).blocks .node = 1 := rfl

/-- A chain query's answer has K + 1 blocks. -/
theorem implG_fbK (t : Tag) : (implG C).blocks (.fb t) = K + 1 := rfl

/-- A leaf's and a vertex's answer is one block, taken as it is. For all data. -/
theorem oneBlock_implG : OneBlock (implG C) := ⟨rfl, rfl, fun _ => rfl, fun _ => rfl⟩

/-- The string of EVERY leaf query: what `real` writes, where it writes; elsewhere the byte 2
and the string under `back`. -/
theorem implG_code_leaf (q : LeafIn L) (j : Fin 1) :
    (implG C).code .leaf q j =
      (C.real.put (.inl q)).getD (bitsOfByte 2 ++ C.back.put (.inl (.inl q))) := by
  cases h : C.real.put (.inl q) with
  | some s => exact totalG_real C _ s h
  | none => exact totalG_none C _ h

/-- The string of a leaf query at which `real` writes. -/
theorem implG_leaf (q : LeafIn L) (s : List Bool) (h : C.real.put (.inl q) = some s) (j : Fin 1) :
    (implG C).code .leaf q j = s := totalG_real C _ s h

/-- The string of a node query at which `real` writes. -/
theorem implG_node (q : Bits × Bits) (s : List Bool) (h : C.real.put (.inr (.inl q)) = some s)
    (j : Fin 1) : (implG C).code .node q j = s := totalG_real C _ s h

/-- The string of a request tree's leaf query at which `real` writes. -/
theorem implG_rleaf (q : Bits) (s : List Bool) (h : C.real.put (.inr (.inr (.inl q))) = some s)
    (j : Fin 1) : (implG C).code .rleaf q j = s := totalG_real C _ s h

/-- The string of a request tree's node query at which `real` writes. -/
theorem implG_rnode (q : Bits × Bits) (s : List Bool)
    (h : C.real.put (.inr (.inr (.inr (.inl q)))) = some s) (j : Fin 1) :
    (implG C).code .rnode q j = s := totalG_real C _ s h

/-- The string of a chain query with a block at which `real` writes. -/
theorem implG_fb (t : Tag) (q : FbIn 256 L t) (j : Fin (K + 1)) (s : List Bool)
    (h : C.real.put (.inr (.inr (.inr (.inr (.inl ⟨t, q, j⟩))))) = some s) :
    (implG C).code (.fb t) q j = s := totalG_real C _ s h

/-- The string of a query to g at which `real` writes. -/
theorem implG_g (t : Tag) (q : JoiningRoundQuery 256 L t) (s : List Bool)
    (h : C.real.put (.inr (.inr (.inr (.inr (.inr ⟨t, q⟩))))) = some s) (j : Fin 1) :
    (implG C).code (.g t) q j = s := totalG_real C _ s h

/-- A string that `real` does not parse, and with neither escape in front, is a point
of the spare oracle, written as itself. -/
theorem implG_other (s : List Bool) (j : Fin 1) (hp : C.real.parse s = none)
    (h2 : ¬ bitsOfByte 2 <+: s) (h3 : ¬ bitsOfByte 3 <+: s) :
    (implG C).code .other s j = s := by
  refine codeA_other 256 K L (totalG C) (bitsOfByte 3) esc_ne (totalG_esc C) s j
    (freeE_of 256 K L (totalG C) (bitsOfByte 3) esc_ne s ?_ ?_)
  · cases hq : (totalG C).parse s with
    | none => rfl
    | some a =>
        exfalso
        have hs := (totalG C).put_parse s a hq
        cases ha : (pAllG C).put a with
        | some u =>
            have e : u = s :=
              (PCode.orElse_put_some (pAllG C) C.back (bitsOfByte 2) (pAllG_no2 C) ha).symm.trans hs
            rw [e] at ha
            obtain ⟨b, hb⟩ := pAllG_put C a s ha
            rw [C.real.parse_put b s hb] at hp
            cases hp
        | none =>
          exact h2 ⟨_,
            (PCode.orElse_put_none (pAllG C) C.back (bitsOfByte 2) (pAllG_no2 C) ha).symm.trans hs⟩
  · cases hs : StrCode.strip (bitsOfByte 3) s with
    | none => rfl
    | some t => exact absurd ⟨t, (StrCode.strip_some hs).symm⟩ h3

/-- The same, for a string that `real` writes at no point. -/
theorem implG_other' (s : List Bool) (j : Fin 1) (hp : ∀ a, C.real.put a ≠ some s)
    (h2 : ¬ bitsOfByte 2 <+: s) (h3 : ¬ bitsOfByte 3 <+: s) :
    (implG C).code .other s j = s := by
  refine implG_other C s j ?_ h2 h3
  cases h : C.real.parse s with
  | none => rfl
  | some a => exact absurd (C.real.put_parse s a h) (hp a)

/-- The total code's string at any point is none that `real` does not parse and that does
not begin with the byte 2. -/
theorem totalG_ne (a : AllPts 256 K L) (s : List Bool) (hp : C.real.parse s = none)
    (h2 : ¬ bitsOfByte 2 <+: s) : (totalG C).put a ≠ s := by
  intro h
  cases ha : (pAllG C).put a with
  | some u =>
      have e : u = s :=
        (PCode.orElse_put_some (pAllG C) C.back (bitsOfByte 2) (pAllG_no2 C) ha).symm.trans h
      rw [e] at ha
      obtain ⟨b, hb⟩ := pAllG_put C a s ha
      rw [C.real.parse_put b s hb] at hp
      cases hp
  | none =>
      exact h2 ⟨_,
        (PCode.orElse_put_none (pAllG C) C.back (bitsOfByte 2) (pAllG_no2 C) ha).symm.trans h⟩

/-- No point of an oracle other than the spare one has a string that `real` does not
parse and that does not begin with the byte 2. So a set of such strings (the public strings of a
part) holds the string of no typed query but the spare oracle's. -/
theorem implG_not_public (o : TypedOracleCompiler.Compile.Batch.OracleName) (ho : o ≠ .other)
    (q : domOf 256 L o) (j : Fin (blk K o))
    (s : List Bool) (hp : C.real.parse s = none) (h2 : ¬ bitsOfByte 2 <+: s) :
    (implG C).code o q j ≠ s := by
  cases o with
  | other => exact absurd rfl ho
  | ann => exact j.elim0
  | leaf => exact totalG_ne C _ s hp h2
  | node => exact totalG_ne C _ s hp h2
  | rleaf => exact totalG_ne C _ s hp h2
  | rnode => exact totalG_ne C _ s hp h2
  | fb t => exact totalG_ne C _ s hp h2
  | g t => exact totalG_ne C _ s hp h2
  | fbw t k => exact totalG_ne C (.inr ⟨t, k, q, j⟩) s hp h2

/-! ## Chain queries under all three tags -/

section
variable (pT : PCode (FbIn 256 L .test × Fin (K + 1))) (pL : PCode (FbIn 256 L .link × Fin (K + 1)))
  (pO : PCode (FbIn 256 L .onl × Fin (K + 1)))
  (hLO : ∀ a b s, pL.put a = some s → pO.put b ≠ some s)
  (hTL : ∀ a b s, pT.put a = some s → pL.put b ≠ some s)
  (hTO : ∀ a b s, pT.put a = some s → pO.put b ≠ some s)

/-- The three kinds side by side. -/
abbrev Fb3 (L : BatchProtocolWithLeafBody I X) (K : ℕ) : Type :=
  (FbIn 256 L .test × Fin (K + 1)) ⊕ ((FbIn 256 L .link × Fin (K + 1)) ⊕
    (FbIn 256 L .onl × Fin (K + 1)))

/-- A chain query under a tag, by the tag. -/
def selTag : (Σ t : Tag, FbIn 256 L t × Fin (K + 1)) → Option (Fb3 L K)
  | ⟨.test, x⟩ => some (.inl x)
  | ⟨.link, x⟩ => some (.inr (.inl x))
  | ⟨.onl, x⟩ => some (.inr (.inr x))

/-- And back. -/
def mkTag : Fb3 L K → (Σ t : Tag, FbIn 256 L t × Fin (K + 1))
  | .inl x => ⟨.test, x⟩
  | .inr (.inl x) => ⟨.link, x⟩
  | .inr (.inr x) => ⟨.onl, x⟩

/-- Reading undoes making. -/
theorem selTag_mkTag (y : Fb3 L K) : selTag (mkTag y) = some y := by
  rcases y with y | y | y <;> rfl

/-- Making undoes reading. -/
theorem mkTag_selTag (b : Σ t : Tag, FbIn 256 L t × Fin (K + 1)) (y : Fb3 L K)
    (h : selTag b = some y) : mkTag y = b := by
  obtain ⟨t, x⟩ := b
  cases t <;> (rw [← Option.some.inj h]; rfl)

/-- The code of chain queries with a block under all tags, from one code for each tag. -/
def byTag : PCode (Σ t : Tag, FbIn 256 L t × Fin (K + 1)) :=
  (pT.sum (pL.sum pO hLO) (fun a b s h1 h2 => by
    rcases b with b | b
    · exact hTL a b s h1 h2
    · exact hTO a b s h1 h2)).via selTag mkTag selTag_mkTag mkTag_selTag

/-- What it writes under each tag. -/
theorem byTag_some :
    (∀ x, (byTag pT pL pO hLO hTL hTO).put ⟨.test, x⟩ = pT.put x) ∧
      (∀ x, (byTag pT pL pO hLO hTL hTO).put ⟨.link, x⟩ = pL.put x) ∧
      (∀ x, (byTag pT pL pO hLO hTL hTO).put ⟨.onl, x⟩ = pO.put x) :=
  ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

/-- Whatever it writes, one of the three writes. -/
theorem byTag_put (b : Σ t : Tag, FbIn 256 L t × Fin (K + 1)) (s : List Bool)
    (h : (byTag pT pL pO hLO hTL hTO).put b = some s) :
    (∃ x, pT.put x = some s) ∨ (∃ x, pL.put x = some s) ∨ (∃ x, pO.put x = some s) := by
  obtain ⟨t, x⟩ := b
  cases t
  · exact Or.inl ⟨x, h⟩
  · exact Or.inr (Or.inl ⟨x, h⟩)
  · exact Or.inr (Or.inr ⟨x, h⟩)

end

/-! ## The real points from leaves, vertices and chain queries -/

/-- A partial code of leaf queries whose strings have the tag of the leaves' number or of the stored
leaves' number and begin with the byte 0. -/
structure Leaves (L : BatchProtocolWithLeafBody I X) where
  /-- the code -/
  lf : PCode (LeafIn L)
  /-- its strings' tag and first byte -/
  hlf : ∀ q s, lf.put q = some s →
    (tag16 s = t164 ∨ tag16 s = t174) ∧ ∀ b : UInt8, b ≠ 0 → ¬ bitsOfByte b <+: s

/-- What stands behind leaves and vertices among the real points. -/
abbrev Tail4 (K : ℕ) (L : BatchProtocolWithLeafBody I X) : Type :=
  Bits ⊕ (Bits × Bits) ⊕ (Σ t : Tag, FbIn 256 L t × Fin (K + 1)) ⊕ (Σ t : Tag, JoiningRoundQuery 256 L t)

section
variable (V : Leaves L) (cfg : ByteArray) (hcfg : cfg.size = 32)
  (fb : PCode (Σ t : Tag, FbIn 256 L t × Fin (K + 1)))
  (hfb : ∀ b s, fb.put b = some s → (tag16 s = t160 ∨ tag16 s = t162 ∨ tag16 s = t173) ∧
    ∀ c : UInt8, c ≠ 0 → c ≠ 1 → ¬ bitsOfByte c <+: s)

/-- Nothing at the request tree's two oracles and at g; the chain queries. -/
def tail4 : PCode (Tail4 K L) :=
  (PCode.empty Bits).sum ((PCode.empty (Bits × Bits)).sum
    (fb.sum (PCode.empty _) (fun _ _ _ _ h => by cases h))
    (fun _ _ _ h => by cases h)) (fun _ _ _ h => by cases h)

/-- Whatever it writes, the code of chain queries writes. -/
theorem tail4_put (y : Tail4 K L) (s : List Bool) (h : (tail4 fb).put y = some s) :
    ∃ b, fb.put b = some s := by
  rcases y with y | y | y | y
  · cases h
  · cases h
  · exact ⟨y, h⟩
  · cases h

include hcfg hfb in
/-- Vertices and chain queries have no string in common. -/
theorem node_tail4 (a : Bits × Bits) (b : Tail4 K L) (s : List Bool)
    (h1 : (pNode cfg).put a = some s) : (tail4 fb).put b ≠ some s := by
  intro h2
  obtain ⟨c, hc⟩ := tail4_put fb b s h2
  have e1 := pNode_tag cfg hcfg a s h1
  rcases (hfb c s hc).1 with e2 | e2 | e2
  · exact tags_differ.2.2.1 (e2.symm.trans e1)
  · exact tags_differ.2.2.2.2.1 (e2.symm.trans e1)
  · exact t173_differs.2.2.2.1 (e2.symm.trans e1)

/-- A partial code of the real points, for a judge that asks leaves, vertices and chain
queries alone: nothing at the request tree's two oracles and at g. Asked of the chain queries'
code: its strings have the tag of 160, 162 or 173 and begin with the byte 0 or 1. -/
def realOf : PCode (RealPts 256 K L) :=
  V.lf.sum ((pNode cfg).sum (tail4 fb) (node_tail4 cfg hcfg fb hfb))
    (fun a b s h1 h2 => by
      have e1 := (V.hlf a s h1).1
      rcases b with b | b
      · have e2 := pNode_tag cfg hcfg b s h2
        rcases e1 with e1 | e1
        · exact tags_differ.2.2.2.2.2 (e1.symm.trans e2)
        · exact t174_differs.2.2.2 (e1.symm.trans e2)
      · obtain ⟨c, hc⟩ := tail4_put fb b s h2
        rcases e1 with e1 | e1 <;> rcases (hfb c s hc).1 with e2 | e2 | e2
        · exact tags_differ.2.1 (e2.symm.trans e1)
        · exact tags_differ.2.2.2.1 (e2.symm.trans e1)
        · exact t173_differs.2.2.1 (e2.symm.trans e1)
        · exact t174_differs.1 (e1.symm.trans e2)
        · exact t174_differs.2.1 (e1.symm.trans e2)
        · exact t173_differs.2.2.2.2.1 (e2.symm.trans e1))

/-- Its strings begin with no byte other than 0 and 1. -/
theorem realOf_hd (a : RealPts 256 K L) (s : List Bool)
    (h : (realOf V cfg hcfg fb hfb).put a = some s) (c : UInt8) (h0 : c ≠ 0) (h1 : c ≠ 1) :
    ¬ bitsOfByte c <+: s := by
  rcases a with a | a | a
  · exact (V.hlf a s h).2 c h0
  · obtain ⟨x, rfl⟩ := pNode_hdr cfg a s h
    exact hdr_not_prefix c 0 h0 166 0 0 cfg x
  · obtain ⟨b, hb⟩ := tail4_put fb a s h
    exact (hfb b s hb).2 c h0 h1

/-- Its strings have one of six tags. -/
theorem realOf_tag (a : RealPts 256 K L) (s : List Bool)
    (h : (realOf V cfg hcfg fb hfb).put a = some s) :
    tag16 s = t160 ∨ tag16 s = t162 ∨ tag16 s = t164 ∨ tag16 s = t166 ∨ tag16 s = t173 ∨
      tag16 s = t174 := by
  rcases a with a | a | a
  · rcases (V.hlf a s h).1 with e | e
    · exact Or.inr (Or.inr (Or.inl e))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr e))))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (pNode_tag cfg hcfg a s h))))
  · obtain ⟨b, hb⟩ := tail4_put fb a s h
    rcases (hfb b s hb).1 with e | e | e
    · exact Or.inl e
    · exact Or.inr (Or.inl e)
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl e))))

end

end TypedOracleCompiler.Run.PageG
