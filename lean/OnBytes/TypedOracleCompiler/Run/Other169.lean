-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Run/Other169.lean: under the encoding that is made of a page with the seeds' code
(`SeedPage.implS`, OnBytes/TypedOracleCompiler/Run/SeedPage.lean), at all its data, the string of a hash call with
the number 169 is a point of the spare oracle, written as itself.

Why. The format computes two public digests by calls with the number 169: the configuration's digest
and a chain's parameters' digest (library, Fmt/Rules4.lean: `configDigestW`, `paramsDigestW`). A
bound in which these digests are answers of the drawn function asks that their strings code no typed
query. OnBytes/TypedOracleCompiler/Run/PageXJoin.lean has the statement for the encoding `theImpl`
(`code_call169`, `inv_call169`); here it is said for `PageG.implG` and `SeedPage.implS`, by the
same steps.

Main theorems.
 `t169_ne_t173`    the tag of 169 is not the tag of 173.
 `implG_call169`   for a page whose partial code writes strings of the six tags (160, 162, 164, 166,
                   173, 174) alone: the string of a call 169 is the spare oracle's point, as itself.
 `implG_inv169`    so it is read back as that point.
 `implS_call169`, `implS_inv169`   the same at `SeedPage.implS`, at all its data.

What is not claimed. Nothing on any hash: a statement on strings and codes. That a program asks such
a string. Nothing on calls with another number. Nothing on soundness; no probability. The compiler
under OnBytes/TypedOracleCompiler/ is the one that `innerCompiledVerifier` is made with; it builds on definitions of
Compile/.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Run.SeedPage
import OnBytes.TypedOracleCompiler.Run.PageXJoin

set_option autoImplicit false

namespace TypedOracleCompiler.Run.Other169
open Rom _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run
open TypedOracleCompiler.Run.Apart TypedOracleCompiler.Run.PageG TypedOracleCompiler.Run.SeedPage
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run

variable {I X : Type}

/-- The tag of the number 169 is not the tag of the number 173. -/
theorem t169_ne_t173 : t169 ≠ t173 := by decide +kernel

section
variable {L : BatchProtocolWithLeafBody I X} {K : ℕ} (C : Page L K)

/-- The string of a call with the number 169 is a point of the spare oracle, written as itself,
under the encoding of a page whose partial code writes strings of the six tags alone. -/
theorem implG_call169
    (htag : ∀ a s, C.real.put a = some s →
      tag16 s = t160 ∨ tag16 s = t162 ∨ tag16 s = t164 ∨ tag16 s = t166 ∨ tag16 s = t173 ∨
        tag16 s = t174)
    (s : List Bool) (hs : IsCall169 s) (j : Fin 1) : (implG C).code .other s j = s := by
  obtain ⟨half, t, i, st, bs, hh, hst, rfl⟩ := hs
  rw [oStr_bits half 169 t i st bs]
  have n2 : (2 : UInt8) ≠ half := by rcases hh with rfl | rfl <;> decide
  have n3 : (3 : UInt8) ≠ half := by rcases hh with rfl | rfl <;> decide
  refine implG_other' C _ j ?_ (hdr_not_prefix 2 half n2 _ _ _ _ _)
    (hdr_not_prefix 3 half n3 _ _ _ _ _)
  intro a ha
  have ht : tag16 (hdr half 169 t i st ++ bytesToBits bs) = t169 :=
    (tag16_hdr half 169 t i st hst (bytesToBits bs)).trans (tag_low 169 t)
  obtain ⟨d0, d2, d4, d6, d7⟩ := t169_differs
  have h := htag a _ ha
  rw [ht] at h
  rcases h with h | h | h | h | h | h
  · exact d0 h
  · exact d2 h
  · exact d4 h
  · exact d6 h
  · exact t169_ne_t173 h
  · exact d7 h

/-- So it is read back as that point. -/
theorem implG_inv169
    (htag : ∀ a s, C.real.put a = some s →
      tag16 s = t160 ∨ tag16 s = t162 ∨ tag16 s = t164 ∨ tag16 s = t166 ∨ tag16 s = t173 ∨
        tag16 s = t174)
    (s : List Bool) (hs : IsCall169 s) :
    (implG C).inv s = ⟨OracleName.other, (s, (0 : Fin 1))⟩ := by
  have h := (implG C).inv_code ⟨OracleName.other, (s, (0 : Fin 1))⟩
  rw [implG_call169 C htag s hs 0] at h
  exact h

end

section
variable (L : BatchProtocolWithLeafBody I X) (p0 p1 : PlainPart (shapeOf L .test) (annOf L .test))
  (isP0 isP1 : PlainPart (shapeOf L .test) (annOf L .test) → Bool) (cfgL : List (Dig 256)) (sh : Bits)
  (hp0 : ∀ p, isP0 p = true ↔ p = p0) (hp1 : ∀ p, isP1 p = true ↔ p = p1) (rest : ByteArray)
  (K : ℕ) (Lk : LinkCode L K) (V : Leaves L) (cfg : ByteArray) (hcfg : cfg.size = 32)
  (back : StrCode (AllPts 256 K L))

/-- At the encoding of a page with the seeds' code, at all its data: the string of a call with the
number 169 is a point of the spare oracle, written as itself. -/
theorem implS_call169 (s : List Bool) (hs : IsCall169 s) (j : Fin 1) :
    (implS L p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest K Lk V cfg hcfg back).code .other s j = s :=
  implG_call169 (pageS L p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest K Lk V cfg hcfg back)
    (fun a s h => realOf_tag V cfg hcfg (fbAll L p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest K Lk)
      (fbAll_facts L p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest K Lk) a s h) s hs j

/-- So it is read back as that point. -/
theorem implS_inv169 (s : List Bool) (hs : IsCall169 s) :
    (implS L p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest K Lk V cfg hcfg back).inv s =
      ⟨OracleName.other, (s, (0 : Fin 1))⟩ :=
  implG_inv169 (pageS L p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest K Lk V cfg hcfg back)
    (fun a s h => realOf_tag V cfg hcfg (fbAll L p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest K Lk)
      (fbAll_facts L p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest K Lk) a s h) s hs

end

end TypedOracleCompiler.Run.Other169
