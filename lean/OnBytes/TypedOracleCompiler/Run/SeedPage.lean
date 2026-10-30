-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Run/SeedPage.lean: a page, and so an encoding of the typed oracles into one hash
function, that writes the two queries of a record's seed as the programs hash them, beside any code
of the link's chain queries under another label.

OnBytes/TypedOracleCompiler/Run/SeedPoints.lean has the seeds' two queries as one partial code `fbSeeds`, and says
what an encoding reads out of the single oracle at them if its page takes that code in (`TakesIn`).
Here such a page is written, by the tools of OnBytes/TypedOracleCompiler/Run/PageG.lean: the seeds' code under the
tag "test", a given code pL under the tag "link", nothing under the tag "onl"; a given code of
leaves; the library's code of vertices; any total code `back` behind the escape.

Main definitions.
 `LinkCode L K`   a code of the link's chain queries with a block, whose strings have the form of a
                  call 160 or 162 under a label l other than the seeds', below 2 ^ 48.
 `fbAll`, `pageS`, `implS`   the chain queries under all tags; the page; the encoding.
Main theorems.
 `takesIn_pageS`  the page takes the seeds' code in.
 `implS_link`     the string of a link's chain query at which pL writes is pL's string.
 `implS_q0`, `implS_q1`   `read_q0`, `read_q1` at that encoding.

The seeds' tag is fixed here: "test". A verifier whose tag for the seeds is a field is met only if
that field is "test" by definition, and its number of blocks is K by definition: with an equation
alone the queries lie in two types.

Not claimed. No code of the link's queries and no code of leaves is given: they are letters. So is
`back`, a one-to-one code of ALL typed points with a parser: the encoding is one to one through it,
and none is given at any interface here. At a typed point where the partial codes do not write, the
string is `back`'s behind the escape: no string of the programs. That a verifier asks these queries.
Nothing under the tag "onl", so nothing for a session; under the tag "test" nothing but the seeds'
two queries, so nothing for a key's own chains. Nothing on soundness.


-/
import OnBytes.TypedOracleCompiler.Run.SeedPoints

set_option autoImplicit false

namespace TypedOracleCompiler.Run.SeedPage
open Rom _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run
open TypedOracleCompiler.Run.Apart TypedOracleCompiler.Run.PageG TypedOracleCompiler.Run.SeedPoints
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run

variable {I X : Type}

/-- A code of the link's chain queries with a block: every string has the form of a call 160 or 162
under one label, which is not the seeds'. -/
structure LinkCode (L : BatchProtocolWithLeafBody I X) (K : ℕ) where
  /-- the code -/
  pL : PCode (FbIn 256 L .link × Fin (K + 1))
  /-- the link's label -/
  l : ℕ
  /-- it fits its field -/
  hlt : l < 2 ^ 48
  /-- it is not the seeds' -/
  hne : l ≠ _root_.Fmt.recordLabel
  /-- the strings' form -/
  his : ∀ x s, pL.put x = some s → Is160 l s ∨ Is162 l s

variable (L : BatchProtocolWithLeafBody I X) (p0 p1 : PlainPart (shapeOf L .test) (annOf L .test))
  (isP0 isP1 : PlainPart (shapeOf L .test) (annOf L .test) → Bool) (cfgL : List (Dig 256)) (sh : Bits)
  (hp0 : ∀ p, isP0 p = true ↔ p = p0) (hp1 : ∀ p, isP1 p = true ↔ p = p1) (rest : ByteArray)
  (K : ℕ) (Lk : LinkCode L K)

/-- No string is written under both tags. -/
theorem seeds_link_apart (a : FbIn 256 L .test × Fin (K + 1))
    (b : FbIn 256 L .link × Fin (K + 1)) (s : List Bool)
    (h1 : (fbSeeds L .test p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest K).put a = some s) :
    Lk.pL.put b ≠ some s := by
  intro h2
  have hr : _root_.Fmt.recordLabel < 2 ^ 48 := by decide
  rcases fbSeeds_is L .test p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest K a s h1 with g1 | g1 <;>
    rcases Lk.his b s h2 with g2 | g2
  · exact no_160_160 _ _ Lk.hlt hr Lk.hne s g2 g1
  · exact no_160_162 _ _ Lk.hlt s g1 g2
  · exact no_160_162 _ _ hr s g2 g1
  · exact no_162_162 _ _ Lk.hlt hr Lk.hne s g2 g1

/-- The chain queries under all tags: the seeds' under "test", the link's under "link", none under
"onl". -/
def fbAll : PCode (Σ t : Tag, FbIn 256 L t × Fin (K + 1)) :=
  byTag (fbSeeds L .test p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest K) Lk.pL (PCode.empty _)
    (fun _ _ _ _ h => by cases h)
    (seeds_link_apart L p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest K Lk)
    (fun _ _ _ _ h => by cases h)

/-- Every string of it has the tag of 160 or 162 and begins with the byte 0 or 1. -/
theorem fbAll_facts (b : Σ t : Tag, FbIn 256 L t × Fin (K + 1)) (s : List Bool)
    (h : (fbAll L p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest K Lk).put b = some s) :
    (tag16 s = t160 ∨ tag16 s = t162 ∨ tag16 s = t173) ∧
      ∀ c : UInt8, c ≠ 0 → c ≠ 1 → ¬ bitsOfByte c <+: s := by
  have f160 : ∀ l, Is160 l s → (tag16 s = t160 ∨ tag16 s = t162 ∨ tag16 s = t173) ∧
      ∀ c : UInt8, c ≠ 0 → c ≠ 1 → ¬ bitsOfByte c <+: s := fun l g =>
    ⟨Or.inl (tag_160 l s g), fun c h0 _ => g.2.2 c h0⟩
  have f162 : ∀ l, Is162 l s → (tag16 s = t160 ∨ tag16 s = t162 ∨ tag16 s = t173) ∧
      ∀ c : UInt8, c ≠ 0 → c ≠ 1 → ¬ bitsOfByte c <+: s := fun l g =>
    ⟨Or.inr (Or.inl (tag_162 l s g)), g.2⟩
  rcases byTag_put _ _ _ _ _ _ b s h with ⟨x, hx⟩ | ⟨x, hx⟩ | ⟨x, hx⟩
  · rcases fbSeeds_is L .test p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest K x s hx with g | g
    · exact f160 _ g
    · exact f162 _ g
  · rcases Lk.his x s hx with g | g
    · exact f160 _ g
    · exact f162 _ g
  · cases hx

variable (V : Leaves L) (cfg : ByteArray) (hcfg : cfg.size = 32)
  (back : StrCode (AllPts 256 K L))

/-- **The page.** -/
def pageS : Page L K where
  real := realOf V cfg hcfg (fbAll L p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest K Lk)
    (fbAll_facts L p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest K Lk)
  hd := realOf_hd V cfg hcfg _ _
  back := back

/-- **The encoding of the typed oracles into one hash function.** -/
def implS : OracleCoding (typedOracleFamily 256 K L) 256 :=
  implG (pageS L p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest K Lk V cfg hcfg back)

/-- **The page takes the seeds' code in.** -/
theorem takesIn_pageS :
    TakesIn L .test p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest K
      (pageS L p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest K Lk V cfg hcfg back) :=
  fun _ _ h => h

/-- The string of a link's chain query at which the link's code writes is that code's string. -/
theorem implS_link (q : FbIn 256 L .link) (j : Fin (K + 1)) (s : List Bool)
    (h : Lk.pL.put (q, j) = some s) :
    (implS L p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest K Lk V cfg hcfg back).code (.fb .link) q j = s :=
  implG_fb _ .link q j s h

/-- **The first query of a seed at the encoding.** -/
theorem implS_q0 (cm : Dig 256) (hr : rest.size < 2 ^ 32) :
    (readBlocks (implS L p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest K Lk V cfg hcfg back) oBits
        (.fb .test) (q0 L .test p0 cfgL sh cm) : (Fin K → Dig 256) × Dig 256).2 =
      bytesToDig (_root_.Fmt.oracle (_root_.Fmt.oStr 0 160 0 _root_.Fmt.recordLabel
        _root_.Fmt.zero32
        (_root_.Fmt.firstBytes _root_.Fmt.zero32 (digToBytes cm ++ rest) ByteArray.empty none))) :=
  read_q0 L .test p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest K _
    (takesIn_pageS L p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest K Lk V cfg hcfg back) cm hr

/-- **The second query of a seed at the encoding.** -/
theorem implS_q1 (hK : K < 2 ^ 48) (v : Bits) (hv : v.length = 256) (k : Fin K) :
    (readBlocks (implS L p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest K Lk V cfg hcfg back) oBits
        (.fb .test) (q1 L .test p1 v) : (Fin K → Dig 256) × Dig 256).1 k =
      bytesToDig (_root_.Fmt.oracle (_root_.Fmt.oStr (UInt8.ofNat ((k.val + 1) % 2)) 162
        _root_.Fmt.recordLabel 1 (bitsToBytes v)
        (ByteArray.empty ++ _root_.Fmt.tail .seeds 0 0 ((k.val + 1) / 2)))) :=
  read_q1 L .test p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest K _
    (takesIn_pageS L p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest K Lk V cfg hcfg back) hK v hv k

end TypedOracleCompiler.Run.SeedPage
