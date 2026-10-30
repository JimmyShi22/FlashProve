-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Run/KeyFb.lean: two partial codes of chain queries for a key's judge: under the tag of
the key's own typed chain, and under the tag of the seeds' typed chain; with the facts that a page
asks of them.

The judge of OnBytes/TypedOracleCompiler/Slice/Plain3XSeeds.lean asks typed chain queries under two tags. Under the
tag `.onl` its one typed chain runs through the three chains of a key file, with four seams
(OnBytes/TypedOracleCompiler/Slice/Plain3.lean). Under the tag `.test` the seeds' protocol has two queries. This
file joins the codes of all these queries, each with the number of a block of its answer, into one
code for each tag. The sibling is a second form of the library's soundness road, under
OnBytes/TypedOracleCompiler/.
 - `Pins`: what the strings hold and no typed query does: the configuration's digest; the three
   chains' parameter digests and labels; the two numbers in the label of the hash under 173 and the
   binding salt's bytes; the item's name; what stands behind the root in the table's name; and how
   the plain parts of the seams s1, s2, s3 are a salt, (root, answers, run value), (first seal, run
   value);
 - `d1`, `d2`, `d3`: the three seams' data (OnBytes/TypedOracleCompiler/Run/SeamAt.lean);
 - `c0` .. `c3`, `c162`: the first value of chain 1 (FirstAnswers.lean); the hash under 173; the
   first values of chains 2 and 3 (FirstLater.lean); all rounds of the three chains (Chain162G.lean
   at KeyRanges.lean's data and PlainAt.lean's `rcG`);
 - `fbOnl`: these five by the typed round; `fbTest`: the seeds' two codes (FirstName.lean,
   SeedRound.lean) by the typed round;
 - `at_lt`; `fbOnl_at0`, `_at1`, `_at2`, `_at3`, `fbOnl_else`, `fbTest_at0`, `fbTest_else`: what the
   two codes write at each typed round: the summand's string. No summand's point is cut off by a
   test: each of the first four writes at its own round alone, the fifth at rounds that are on,
   which are none of the four (OnBytes/TypedOracleCompiler/Run/PlainIn.lean: `on_iff`, `rdAt_seam`);
 - `fbOnl_is`, `fbTest_is`: what is known of every string: the label's words and the first byte
   (`Apart.Is160`, `Is162`, `Is173`); `fb_apart`: no string is written under both tags; `fb_facts`:
   every string has the tag of 160, 162 or 173 and begins with the byte 0 or 1.

Main definitions: `Pins`, `fbOnl`, `fbTest`.
Main theorems: `fbOnl_at0` to `fbOnl_else`, `fbTest_at0`, `fbTest_else`, `fbOnl_is`, `fbTest_is`,
`fb_apart`, `fb_facts`.

Not claimed. CODES, NO PAGE YET: leaves and vertices are not here. What each summand writes is said
in its own file: as an equation with the format's `Fmt.oStr` for the four first values; for the hash
under 173 up to the leaf's bytes; for the rounds under a condition on `rcG` (met in
OnBytes/TypedOracleCompiler/Run/KeyPageRounds.lean); At a seam and at round 0 only the block of the typed tail has a
string. No pins are given here (a file of this project that is not in this library has some).
Nothing ties `above` to
`sB`, nor `rest` to `cfg`. What the heads of the seven files named do not claim. Nothing on
soundness. The compiler under OnBytes/TypedOracleCompiler/ is the one that `innerCompiledVerifier` is made with; it
builds on definitions of Compile/.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Run.KeyRanges
import OnBytes.TypedOracleCompiler.Run.FirstLater
import OnBytes.TypedOracleCompiler.Run.FirstName
import OnBytes.TypedOracleCompiler.Run.SeedRound
import OnBytes.TypedOracleCompiler.Run.Apart
import OnBytes.TypedOracleCompiler.Slice.JudgeOffRun

set_option autoImplicit false

noncomputable section

namespace TypedOracleCompiler.Run.KeyFb
open Rom _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run TypedOracleCompiler.Slice
open TypedOracleCompiler.Run.Chain162G TypedOracleCompiler.Run.KeyRanges TypedOracleCompiler.Run.PlainAt
open TypedOracleCompiler.Run.SeamAt TypedOracleCompiler.Run.FirstLater TypedOracleCompiler.Run.Apart
open TypedOracleCompiler.Run.FirstAnswers (T3)
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run

variable {Sd : Type} (G : Stretches)
  (dec : List T3 × Sd → PQ.View → PQ.View → PQ.View → Bool) (d : Sd) (e : _root_.Fmt.Entry)

/-- The interface: the key's frame with the seeds' protocol as its Test. -/
abbrev Lk := LXs G dec d e

/-- What the strings hold and no typed query does. The decision, the fixed value d and the
seeds' entry stand in the type alone: they name the interface for which the pins are meant. -/
structure Pins {Sd : Type} (G : Stretches)
    (_dec : List T3 × Sd → PQ.View → PQ.View → PQ.View → Bool) (_d : Sd)
    (_e : _root_.Fmt.Entry) where
  /-- the configuration's digest: the start of the hash under 173 -/
  cfg : ByteArray
  /-- it has 32 bytes -/
  hcfg : cfg.size = 32
  /-- the three chains' parameter digests -/
  pd₁ : Dig 256
  /-- of the second chain -/
  pd₂ : Dig 256
  /-- of the third chain -/
  pd₃ : Dig 256
  /-- the three chains' labels -/
  l₁ : ℕ
  /-- of the second chain -/
  l₂ : ℕ
  /-- of the third chain -/
  l₃ : ℕ
  /-- the labels differ, also from the seeds' chain's, and are below 2 ^ 48 -/
  h12 : l₁ ≠ l₂
  /-- see `h12` -/
  h13 : l₁ ≠ l₃
  /-- see `h12` -/
  h23 : l₂ ≠ l₃
  /-- see `h12` -/
  hR : l₁ ≠ _root_.Fmt.recordLabel ∧ l₂ ≠ _root_.Fmt.recordLabel ∧ l₃ ≠ _root_.Fmt.recordLabel
  /-- see `h12` -/
  hlt : l₁ < 2 ^ 48 ∧ l₂ < 2 ^ 48 ∧ l₃ < 2 ^ 48
  /-- the number above 173 in the first word of the label of the hash under 173 (in the format:
  `Fmt.leafPlace 0 4 (the salt's words)`; not the leaf's place among the leaves, which goes into the
  index) -/
  above : ℕ
  /-- the index in that label -/
  index : ℕ
  /-- the binding salt's number of bytes -/
  sB : ℕ
  /-- the name of the table's item in the statements -/
  name : String
  /-- it has fewer than 2 ^ 32 bytes -/
  hname : (_root_.Fmt.ascii name).size < 2 ^ 32
  /-- what stands behind the root in the table's name -/
  rest : ByteArray
  /-- the seam s1's plain part is the binding salt -/
  e₁ : G.s1.r.Plain ≃ Bits
  /-- the seam s2's plain part is (root, answers) and the second chain's run value -/
  e₂ : G.s2.r.Plain ≃ ((Dig 256 × List T3) × Bits)
  /-- the seam s3's plain part is the first seal and the third chain's run value -/
  e₃ : G.s3.r.Plain ≃ (Dig 256 × Bits)

variable {G dec d e} (P : Pins G dec d e)

open Classical in
/-- The test "is a", by classical logic: nothing here is run. -/
def isEq {α : Type} (a : α) : α → Bool := fun x => decide (x = a)

open Classical in
/-- It tells a. -/
theorem isEq_iff {α : Type} (a x : α) : isEq a x = true ↔ x = a := by
  unfold isEq
  exact decide_eq_true_iff

/-- The seam s1's data. -/
def d1 : SeamD (Lk G dec d e) .onl Bits where
  round := at1 G
  mkH := mkF2
  selH := selF2
  hsel := selF2_mkF2
  hmk := mkF2_selF2
  inS := fun z => in1 G (P.e₁.symm z)
  outS := fun y => (out1 G y).map P.e₁
  hout := fun z => by
    show (out1 G (in1 G (P.e₁.symm z))).map P.e₁ = some z
    rw [out1_in1]
    exact congrArg some (P.e₁.apply_symm_apply z)
  hin := fun y z h => by
    obtain ⟨w, hw, rfl⟩ := Option.map_eq_some_iff.1 h
    show in1 G (P.e₁.symm (P.e₁ w)) = y
    rw [P.e₁.symm_apply_apply]
    exact in1_out1 G y w hw

/-- The seam s2's data. -/
def d2 : SeamD (Lk G dec d e) .onl ((Dig 256 × List T3) × Bits) where
  round := at2 G
  mkH := mkF2
  selH := selF2
  hsel := selF2_mkF2
  hmk := mkF2_selF2
  inS := fun z => in2 G (P.e₂.symm z)
  outS := fun y => (out2 G y).map P.e₂
  hout := fun z => by
    show (out2 G (in2 G (P.e₂.symm z))).map P.e₂ = some z
    rw [out2_in2]
    exact congrArg some (P.e₂.apply_symm_apply z)
  hin := fun y z h => by
    obtain ⟨w, hw, rfl⟩ := Option.map_eq_some_iff.1 h
    show in2 G (P.e₂.symm (P.e₂ w)) = y
    rw [P.e₂.symm_apply_apply]
    exact in2_out2 G y w hw

/-- The seam s3's data. -/
def d3 : SeamD (Lk G dec d e) .onl (Dig 256 × Bits) where
  round := at3 G
  mkH := mkF2
  selH := selF2
  hsel := selF2_mkF2
  hmk := mkF2_selF2
  inS := fun z => in3 G (P.e₃.symm z)
  outS := fun y => (out3 G y).map P.e₃
  hout := fun z => by
    show (out3 G (in3 G (P.e₃.symm z))).map P.e₃ = some z
    rw [out3_in3]
    exact congrArg some (P.e₃.apply_symm_apply z)
  hin := fun y z h => by
    obtain ⟨w, hw, rfl⟩ := Option.map_eq_some_iff.1 h
    show in3 G (P.e₃.symm (P.e₃ w)) = y
    rw [P.e₃.symm_apply_apply]
    exact in3_out3 G y w hw

/-- The first value of chain 1. -/
def c0 : PCode (FbIn 256 (Lk G dec d e) .onl) :=
  FirstAnswers.firstPA P.name (Lk G dec d e) .onl (in0 G G.s0.r.dPlain) (isEq _) d (isEq d) P.pd₁
    (isEq_iff _) (isEq_iff d) P.l₁ P.hname

/-- The hash under 173. -/
def c1 : PCode (FbIn 256 (Lk G dec d e) .onl) :=
  seamP (d1 P) (p173 (head173 P.cfg P.above P.index) (8 * P.sB))

/-- The first value of chain 2. -/
def c2 : PCode (FbIn 256 (Lk G dec d e) .onl) :=
  seamP (d2 P) (pFirstAt P.l₂ (stm2 P.name) (unstm2 P.name) (unstm_stm2 P.name P.hname)
    (stm_unstm2 P.name) P.pd₂)

/-- The first value of chain 3. -/
def c3 : PCode (FbIn 256 (Lk G dec d e) .onl) :=
  seamP (d3 P) (pFirstAt P.l₃ stm3 unstm3 unstm_stm3 stm_unstm3 P.pd₃)

variable (K : ℕ)

/-- All rounds of the three chains. -/
def c162 : PCode (FbIn 256 (Lk G dec d e) .onl × Fin (K + 1)) :=
  p162G (keyChain (L := Lk G dec d e) (tg := .onl) G P.l₁ P.l₂ P.l₃ P.h12 P.h13 P.h23 (rcG G)
    (rcG_ge G)) K

/-- What `c0` writes is a string under 160 with the first label. -/
theorem c0_is (q : FbIn 256 (Lk G dec d e) .onl) (s : List Bool) (h : (c0 P).put q = some s) :
    Is160 P.l₁ s := is160_of_hdr _ _ (FirstAnswers.firstPA_hdr _ _ _ _ _ _ _ _ _ _ _ _ q s h)

/-- What `c2` writes is a string under 160 with the second label. -/
theorem c2_is (q : FbIn 256 (Lk G dec d e) .onl) (s : List Bool) (h : (c2 P).put q = some s) :
    Is160 P.l₂ s := by
  obtain ⟨a, ha⟩ := seamP_put _ _ q s h
  exact is160_of_hdr _ _ (pFirstAt_hdr _ _ _ _ _ _ a s ha)

/-- What `c3` writes is a string under 160 with the third label. -/
theorem c3_is (q : FbIn 256 (Lk G dec d e) .onl) (s : List Bool) (h : (c3 P).put q = some s) :
    Is160 P.l₃ s := by
  obtain ⟨a, ha⟩ := seamP_put _ _ q s h
  exact is160_of_hdr _ _ (pFirstAt_hdr _ _ _ _ _ _ a s ha)

/-- What `c1` writes is a string under 173. -/
theorem c1_is (q : FbIn 256 (Lk G dec d e) .onl) (s : List Bool) (h : (c1 P).put q = some s) :
    Is173 P.above s := by
  obtain ⟨a, ha⟩ := seamP_put _ _ q s h
  obtain ⟨r, rfl⟩ := PCode.pre_put _ _ a s ha
  exact is173_of_head P.cfg P.hcfg P.above P.index r

/-- The label at a typed round is one of the three. -/
theorem lab_mem (T : Three) (i : ℕ) : T.lab i = T.l₁ ∨ T.lab i = T.l₂ ∨ T.lab i = T.l₃ := by
  unfold Three.lab
  split_ifs
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)

/-- What `c162` writes is a string under 162 with one of the three labels. -/
theorem c162_is (x : FbIn 256 (Lk G dec d e) .onl × Fin (K + 1)) (s : List Bool)
    (h : (c162 P K).put x = some s) : Is162 P.l₁ s ∨ Is162 P.l₂ s ∨ Is162 P.l₃ s := by
  obtain ⟨hb, ρ, r, hρ, rfl⟩ := p162G_shape _ K x s h
  have h1 := is162_of_shape ((threeOf G P.l₁ P.l₂ P.l₃).lab x.1.round)
    ((threeOf G P.l₁ P.l₂ P.l₃).idx x.1.round) hb ρ r hρ
  rcases lab_mem (threeOf G P.l₁ P.l₂ P.l₃) x.1.round with e1 | e1 | e1
  · exact Or.inl ⟨h1.1.trans (congrArg (fun l => Wd (162 + 65536 * l)) e1), h1.2⟩
  · exact Or.inr (Or.inl ⟨h1.1.trans (congrArg (fun l => Wd (162 + 65536 * l)) e1), h1.2⟩)
  · exact Or.inr (Or.inr ⟨h1.1.trans (congrArg (fun l => Wd (162 + 65536 * l)) e1), h1.2⟩)

/-! ## The key's chain: five codes by the typed round -/

/-- What is known of a string of the key's rounds. -/
def IsR (s : List Bool) : Prop := Is162 P.l₁ s ∨ Is162 P.l₂ s ∨ Is162 P.l₃ s

/-- The first value of chain 3, or a round. -/
def j3 : PCode (FbIn 256 (Lk G dec d e) .onl × Fin (K + 1)) :=
  split (tailP (c3 P) K) (c162 P K) (fun x => decide (x.1.round = at3 G)) (fun a b s h1 h2 => by
    have g1 := c3_is P _ s (tailP_put _ K a s h1).1
    rcases c162_is P K b s h2 with g2 | g2 | g2
    · exact no_160_162 _ _ P.hlt.1 s g1 g2
    · exact no_160_162 _ _ P.hlt.2.1 s g1 g2
    · exact no_160_162 _ _ P.hlt.2.2 s g1 g2)

/-- What is known of every string of `j3`. -/
theorem j3_is (x : FbIn 256 (Lk G dec d e) .onl × Fin (K + 1)) (s : List Bool)
    (h : (j3 P K).put x = some s) : Is160 P.l₃ s ∨ IsR P s := by
  rcases split_put _ _ _ _ x s h with h1 | h1
  · exact Or.inl (c3_is P _ s (tailP_put _ K x s h1).1)
  · exact Or.inr (c162_is P K x s h1)

/-- The first value of chain 2, or one of these. -/
def j2 : PCode (FbIn 256 (Lk G dec d e) .onl × Fin (K + 1)) :=
  split (tailP (c2 P) K) (j3 P K) (fun x => decide (x.1.round = at2 G)) (fun a b s h1 h2 => by
    have g1 := c2_is P _ s (tailP_put _ K a s h1).1
    rcases j3_is P K b s h2 with g2 | g2 | g2 | g2
    · exact no_160_160 _ _ P.hlt.2.1 P.hlt.2.2 P.h23 s g1 g2
    · exact no_160_162 _ _ P.hlt.1 s g1 g2
    · exact no_160_162 _ _ P.hlt.2.1 s g1 g2
    · exact no_160_162 _ _ P.hlt.2.2 s g1 g2)

/-- What is known of every string of `j2`. -/
theorem j2_is (x : FbIn 256 (Lk G dec d e) .onl × Fin (K + 1)) (s : List Bool)
    (h : (j2 P K).put x = some s) : Is160 P.l₂ s ∨ Is160 P.l₃ s ∨ IsR P s := by
  rcases split_put _ _ _ _ x s h with h1 | h1
  · exact Or.inl (c2_is P _ s (tailP_put _ K x s h1).1)
  · exact Or.inr (j3_is P K x s h1)

/-- The hash under 173, or one of these. -/
def j1 : PCode (FbIn 256 (Lk G dec d e) .onl × Fin (K + 1)) :=
  split (tailP (c1 P) K) (j2 P K) (fun x => decide (x.1.round = at1 G)) (fun a b s h1 h2 => by
    have g1 := c1_is P _ s (tailP_put _ K a s h1).1
    rcases j2_is P K b s h2 with g2 | g2 | g2 | g2 | g2
    · exact no_173_160 _ _ s g1 g2
    · exact no_173_160 _ _ s g1 g2
    · exact no_173_162 _ _ s g1 g2
    · exact no_173_162 _ _ s g1 g2
    · exact no_173_162 _ _ s g1 g2)

/-- What is known of every string of `j1`. -/
theorem j1_is (x : FbIn 256 (Lk G dec d e) .onl × Fin (K + 1)) (s : List Bool)
    (h : (j1 P K).put x = some s) :
    Is173 P.above s ∨ Is160 P.l₂ s ∨ Is160 P.l₃ s ∨ IsR P s := by
  rcases split_put _ _ _ _ x s h with h1 | h1
  · exact Or.inl (c1_is P _ s (tailP_put _ K x s h1).1)
  · exact Or.inr (j2_is P K x s h1)

/-- The code of chain queries under the key's tag, each with a block: five codes by the typed
round. -/
def fbOnl : PCode (FbIn 256 (Lk G dec d e) .onl × Fin (K + 1)) :=
  split (tailP (c0 P) K) (j1 P K) (fun x => decide (x.1.round = 0)) (fun a b s h1 h2 => by
    have g1 := c0_is P _ s (tailP_put _ K a s h1).1
    rcases j1_is P K b s h2 with g2 | g2 | g2 | g2 | g2 | g2
    · exact no_173_160 _ _ s g2 g1
    · exact no_160_160 _ _ P.hlt.1 P.hlt.2.1 P.h12 s g1 g2
    · exact no_160_160 _ _ P.hlt.1 P.hlt.2.2 P.h13 s g1 g2
    · exact no_160_162 _ _ P.hlt.1 s g1 g2
    · exact no_160_162 _ _ P.hlt.2.1 s g1 g2
    · exact no_160_162 _ _ P.hlt.2.2 s g1 g2)

/-- What is known of every string of `fbOnl`. -/
theorem fbOnl_is (x : FbIn 256 (Lk G dec d e) .onl × Fin (K + 1)) (s : List Bool)
    (h : (fbOnl P K).put x = some s) :
    Is160 P.l₁ s ∨ Is173 P.above s ∨ Is160 P.l₂ s ∨ Is160 P.l₃ s ∨ IsR P s := by
  rcases split_put _ _ _ _ x s h with h1 | h1
  · exact Or.inl (c0_is P _ s (tailP_put _ K x s h1).1)
  · exact Or.inr (j1_is P K x s h1)

/-! ## The seeds' chain: two codes by the typed round -/

/-- The seeds' chain's first value. -/
def t0 : PCode (FbIn 256 (Lk G dec d e) .test) :=
  FirstName.firstPN P.rest (Lk G dec d e) .test (p0S (L := Lk G dec d e) .test G.C e _ id) (isEq _)
    FirstName.zeroPd (isEq_iff _) _root_.Fmt.recordLabel

/-- The drawing round. It hangs on no pin. -/
def t1 : PCode (FbIn 256 (Lk G dec d e) .test × Fin (K + 1)) :=
  SeedRound.secondPS (Lk G dec d e) .test (p1S (L := Lk G dec d e) .test G.C e _ id) (isEq _)
    (isEq_iff _) K

/-- What `t0` writes is a string under 160 with the seeds' chain's label. -/
theorem t0_is (q : FbIn 256 (Lk G dec d e) .test) (s : List Bool) (h : (t0 P).put q = some s) :
    Is160 _root_.Fmt.recordLabel s :=
  is160_of_hdr _ _ (FirstName.firstPN_hdr _ _ _ _ _ _ _ _ q s h)

/-- What `t1` writes is a string under 162 with the seeds' chain's label. -/
theorem t1_is (x : FbIn 256 (Lk G dec d e) .test × Fin (K + 1)) (s : List Bool)
    (h : (t1 K).put x = some s) : Is162 _root_.Fmt.recordLabel s := by
  obtain ⟨hb, ρ, r, hρ, rfl⟩ := p162_shape _ K x s h
  refine ⟨?_, fun b h0 h1 => ?_⟩
  · unfold lw1
    rw [← List.append_assoc, ← List.append_assoc, List.drop_left'
      (by rw [List.length_append, List.length_append, length_bitsOfByte, length_mid32, hρ])]
    exact List.take_left' (length_u64n _)
  · cases hb
    · exact byte_prefix b 0 h0 _
    · exact byte_prefix b 1 h1 _

/-- The code of chain queries under the seeds' tag, each with a block: two codes by the typed
round. -/
def fbTest : PCode (FbIn 256 (Lk G dec d e) .test × Fin (K + 1)) :=
  split (tailP (t0 P) K) (t1 K) (fun x => decide (x.1.round = 0)) (fun a b s h1 h2 =>
    no_160_162 _ _ (by decide) s (t0_is P _ s (tailP_put _ K a s h1).1) (t1_is K b s h2))

/-- What is known of every string of `fbTest`. -/
theorem fbTest_is (x : FbIn 256 (Lk G dec d e) .test × Fin (K + 1)) (s : List Bool)
    (h : (fbTest P K).put x = some s) :
    Is160 _root_.Fmt.recordLabel s ∨ Is162 _root_.Fmt.recordLabel s := by
  rcases split_put _ _ _ _ x s h with h1 | h1
  · exact Or.inl (t0_is P _ s (tailP_put _ K x s h1).1)
  · exact Or.inr (t1_is K x s h1)

/-! ## What the two codes write at each typed round -/

omit P in
/-- The four seams' typed rounds are different. -/
theorem at_lt (G : Stretches) : 0 < at1 G ∧ at1 G < at2 G ∧ at2 G < at3 G := by
  unfold at1 at2 at3 n₁ n₂
  omega

/-- At the typed round 0: the first value of chain 1, at the tail's block. -/
theorem fbOnl_at0 (x : FbIn 256 (Lk G dec d e) .onl × Fin (K + 1)) (h : x.1.round = 0) :
    (fbOnl P K).put x = (tailP (c0 P) K).put x :=
  split_true _ _ _ _ x (decide_eq_true h)

/-- At the seam s1's typed round: the hash under 173, at the tail's block. -/
theorem fbOnl_at1 (x : FbIn 256 (Lk G dec d e) .onl × Fin (K + 1)) (h : x.1.round = at1 G) :
    (fbOnl P K).put x = (tailP (c1 P) K).put x := by
  have g := at_lt G
  rw [fbOnl, split_false _ _ _ _ x (decide_eq_false (by omega)), j1,
    split_true _ _ _ _ x (decide_eq_true h)]

/-- At the seam s2's typed round: the first value of chain 2, at the tail's block. -/
theorem fbOnl_at2 (x : FbIn 256 (Lk G dec d e) .onl × Fin (K + 1)) (h : x.1.round = at2 G) :
    (fbOnl P K).put x = (tailP (c2 P) K).put x := by
  have g := at_lt G
  rw [fbOnl, split_false _ _ _ _ x (decide_eq_false (by omega)), j1,
    split_false _ _ _ _ x (decide_eq_false (by omega)), j2,
    split_true _ _ _ _ x (decide_eq_true h)]

/-- At the seam s3's typed round: the first value of chain 3, at the tail's block. -/
theorem fbOnl_at3 (x : FbIn 256 (Lk G dec d e) .onl × Fin (K + 1)) (h : x.1.round = at3 G) :
    (fbOnl P K).put x = (tailP (c3 P) K).put x := by
  have g := at_lt G
  rw [fbOnl, split_false _ _ _ _ x (decide_eq_false (by omega)), j1,
    split_false _ _ _ _ x (decide_eq_false (by omega)), j2,
    split_false _ _ _ _ x (decide_eq_false (by omega)), j3,
    split_true _ _ _ _ x (decide_eq_true h)]

/-- At every other typed round: the code of the three chains' rounds. -/
theorem fbOnl_else (x : FbIn 256 (Lk G dec d e) .onl × Fin (K + 1)) (h0 : x.1.round ≠ 0)
    (h1 : x.1.round ≠ at1 G) (h2 : x.1.round ≠ at2 G) (h3 : x.1.round ≠ at3 G) :
    (fbOnl P K).put x = (c162 P K).put x := by
  rw [fbOnl, split_false _ _ _ _ x (decide_eq_false h0), j1,
    split_false _ _ _ _ x (decide_eq_false h1), j2,
    split_false _ _ _ _ x (decide_eq_false h2), j3,
    split_false _ _ _ _ x (decide_eq_false h3)]

/-- Under the seeds' tag at the typed round 0: the seeds' chain's first value, at the tail's
block. -/
theorem fbTest_at0 (x : FbIn 256 (Lk G dec d e) .test × Fin (K + 1)) (h : x.1.round = 0) :
    (fbTest P K).put x = (tailP (t0 P) K).put x :=
  split_true _ _ _ _ x (decide_eq_true h)

/-- Under the seeds' tag at every other typed round: the drawing round's code. -/
theorem fbTest_else (x : FbIn 256 (Lk G dec d e) .test × Fin (K + 1)) (h : x.1.round ≠ 0) :
    (fbTest P K).put x = (t1 K).put x :=
  split_false _ _ _ _ x (decide_eq_false h)

/-- No string is written under both tags. -/
theorem fb_apart (a : FbIn 256 (Lk G dec d e) .test × Fin (K + 1))
    (b : FbIn 256 (Lk G dec d e) .onl × Fin (K + 1)) (s : List Bool)
    (h1 : (fbTest P K).put a = some s) : (fbOnl P K).put b ≠ some s := by
  intro h2
  have hr : _root_.Fmt.recordLabel < 2 ^ 48 := by decide
  rcases fbTest_is P K a s h1 with g1 | g1 <;>
    rcases fbOnl_is P K b s h2 with g2 | g2 | g2 | g2 | g2 | g2 | g2
  · exact no_160_160 _ _ P.hlt.1 hr P.hR.1 s g2 g1
  · exact no_173_160 _ _ s g2 g1
  · exact no_160_160 _ _ P.hlt.2.1 hr P.hR.2.1 s g2 g1
  · exact no_160_160 _ _ P.hlt.2.2 hr P.hR.2.2 s g2 g1
  · exact no_160_162 _ _ P.hlt.1 s g1 g2
  · exact no_160_162 _ _ P.hlt.2.1 s g1 g2
  · exact no_160_162 _ _ P.hlt.2.2 s g1 g2
  · exact no_160_162 _ _ hr s g2 g1
  · exact no_173_162 _ _ s g2 g1
  · exact no_160_162 _ _ hr s g2 g1
  · exact no_160_162 _ _ hr s g2 g1
  · exact no_162_162 _ _ P.hlt.1 hr P.hR.1 s g2 g1
  · exact no_162_162 _ _ P.hlt.2.1 hr P.hR.2.1 s g2 g1
  · exact no_162_162 _ _ P.hlt.2.2 hr P.hR.2.2 s g2 g1

/-- Every string of either code has the tag of 160, 162 or 173 and begins with the byte 0 or
1. -/
theorem fb_facts (s : List Bool)
    (h : (∃ x, (fbOnl P K).put x = some s) ∨ (∃ x, (fbTest P K).put x = some s)) :
    (tag16 s = t160 ∨ tag16 s = t162 ∨ tag16 s = t173) ∧
      ∀ b : UInt8, b ≠ 0 → b ≠ 1 → ¬ bitsOfByte b <+: s := by
  have f160 : ∀ l, Is160 l s → (tag16 s = t160 ∨ tag16 s = t162 ∨ tag16 s = t173) ∧
      ∀ b : UInt8, b ≠ 0 → b ≠ 1 → ¬ bitsOfByte b <+: s := fun l g =>
    ⟨Or.inl (tag_of_lw1 160 0 s g.1), fun b h0 _ => g.2.2 b h0⟩
  have f162 : ∀ l, Is162 l s → (tag16 s = t160 ∨ tag16 s = t162 ∨ tag16 s = t173) ∧
      ∀ b : UInt8, b ≠ 0 → b ≠ 1 → ¬ bitsOfByte b <+: s := fun l g =>
    ⟨Or.inr (Or.inl (tag_of_lw1 162 l s g.1)), g.2⟩
  have f173 : ∀ p, Is173 p s → (tag16 s = t160 ∨ tag16 s = t162 ∨ tag16 s = t173) ∧
      ∀ b : UInt8, b ≠ 0 → b ≠ 1 → ¬ bitsOfByte b <+: s := fun p g =>
    ⟨Or.inr (Or.inr (tag_of_lw1 173 p s g.1)), fun b h0 _ => g.2 b h0⟩
  rcases h with ⟨x, hx⟩ | ⟨x, hx⟩
  · rcases fbOnl_is P K x s hx with g | g | g | g | g | g | g
    · exact f160 _ g
    · exact f173 _ g
    · exact f160 _ g
    · exact f160 _ g
    · exact f162 _ g
    · exact f162 _ g
    · exact f162 _ g
  · rcases fbTest_is P K x s hx with g | g
    · exact f160 _ g
    · exact f162 _ g

end TypedOracleCompiler.Run.KeyFb
