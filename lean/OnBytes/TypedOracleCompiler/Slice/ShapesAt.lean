-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Slice/ShapesAt.lean: THE SIZES AS ONE RECORD, and the readings of a key that hang on no
file's part: the record of a key under an oracle, the one written reading of the raw string, the
keys' shape. GENERAL IN THE SIZES: no number of any setting stands in a definition here.

In this file "the commitment ID" ("the ID"), where it stands by itself, is not the format's. It is
the hash function's answer at a shorter string, the format's string for its ID without the record's
seed (`idCode`, OnBytes/Tie/IdKey.lean). The format's rule (R4.11; `Fmt.publishedBytes`,
Fmt/Rules4.lean) hashes the string with the seed.

`Three` (OnBytes/TypedOracleCompiler/Slice/Shapes.lean) has three fields in which "fine" is said: `recU`, `rawU`,
`okKey`. `Three.Beside` (OnBytes/TypedOracleCompiler/Slice/ShapesFrom.lean) asks eight clauses beside what three
files' parts deliver. Here the three fields are written, as functions of a `Size`, and three of the
eight clauses are shown of every `Three` that has them and whose public strings are strings of calls
with the number 169.

ONE SOURCE FOR EVERY SIZE OF A STORED TABLE. A `Size` is a stored table's shape, as the programs
have it, and the radius in columns. The code, the number of row variables, the answers a row, the
coordinates of a seed's point, the tree's depth and the bytes of a leaf's salt are all read off that
one shape. Rounds, labels, work, and the depths of trees that are made in a run are no part of it.

Main definitions.
 `Size`; `Size.T`, `v`, `s`, `lg`, `D`   the sizes; the decoder's data at them.
 `Size.Fit`            the conditions on numbers under which the record's bound over the oracle is
                       shown, with the programs' own test on a shape; `coll_at`: that bound.
 `recUAt z`            the record of a key under an oracle: the seeds that the oracle gives at the
                       key's table's name; the answers in the key.
 `rawZ z`              the one written reading: `rawBy` (OnBytes/TypedOracleCompiler/Slice/ShapesRaw.lean) at the
                       key's configuration digest, the shape's depth and salt length.
 `okKeyAt z`           the keys that hold z's shape.
 `Three.At z Θ`        Θ has these three, and its public strings are strings of calls number 169.
Main theorems.
 `recUAt_iff`, `measR_recUAt`   a key's record, unfolded; every property of it is a measurable set
                       of oracles.
 `rawZ_offSet`         the reading does not see entries at strings of calls number 169.
 `Three.At.apart`, `rawOff`, `measR`   the three clauses.
 `Three.At.beside`     ALL OF `Beside` FROM THE THREE LANGUAGES, THE FILES' KEY'S SHAPE AND "THE
                       PARTS' READING IS `rawZ` AT THE FILES' KEY".
 `Three.At.soundB_of_delivers`   (a) at z, from three times `Delivers`, these five, that the parts
                       are made of the specifications, and a bound on each checker's strings.
 `Three.At.fineB_iff`  what is fine, written out at these readings.
 `Three.ofSpecsAt`, `ofSpecsAt_at`   three parts made of three specifications at z; they are `At z`.

What is not claimed. No `Three` is given, and nothing is shown of any part. That a shape is that of
any setting: a `Size` is any shape with any radius; at a shape whose message is too short for its
pads, or a radius beyond the code's distance, the definitions still type and say little
(`Size.Fit` shuts these out; no theorem here but `coll_at` asks it). A key's record is nothing
unless the key holds exactly 2^v * s answers. THE SEEDS ARE READ AT z's NUMBERS OF COORDINATES AND
ANSWERS, NOT AT THOSE OF THE SHAPE IN THE KEY: the two are the same for the keys with `okKeyAt`.
THE FIELD IN WHICH THE SEEDS ARE DRAWN IS THE SECOND, a constant of `seedUnder`: a `Size` has no
place for it. THAT EACH FILE'S ANALYSIS BRINGS A TABLE WITHIN THE ONE RADIUS eM. The one probability
here (`coll_at`) is for one table and one key fixed beforehand: a committer picks its table after
queries, and that is paid in the key's analysis, not by this; `coll_at` is used by nothing. Nothing
on any hash function.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Slice.ShapesFrom
import OnBytes.TypedOracleCompiler.Slice.ShapesRaw
import OnBytes.Slice.SeedOracle
import OnBytes.Slice.OffSetGlue

set_option autoImplicit false

namespace OnBytes.Slice.Shapes
open Iop Rom Prob MeasureTheory
open OnBytes.Tie (IdKey idCode firstId)
open scoped ENNReal

/-! ## The sizes -/

/-- The sizes, as one record: the shape of the stored tables, as the programs have it (the code
of a row, the number of row variables, the answers a row, the bytes of a leaf's salt), and the
radius in columns within which a table is decoded. -/
structure Size where
  /-- the stored tables' shape -/
  shape : Params.IndexShape
  /-- the radius, in columns -/
  eM : ℕ

namespace Size
variable (z : Size)

/-- The code of a row: the logarithm of the word's length (which is the tree's depth), the entries
of a row's message, the entries of the random tail. -/
def T : Fmt.M1.Code := ⟨z.shape.code.logN, z.shape.code.ell, z.shape.code.r⟩

/-- The number of row variables: a table has 2^v rows. -/
def v : ℕ := z.shape.v

/-- The answers for each row. -/
def s : ℕ := z.shape.answers

/-- The coordinates of a seed's point, as the programs take them at the shape. -/
def lg : ℕ := z.shape.cubeBits

/-- The data of a decoder with the programs' record, at these sizes. -/
@[reducible] noncomputable def D : DecR := decRec z.T z.v z.eM z.lg z.s

/-- The conditions on numbers under which the record's bound over the oracle is shown
(`coll_measure_oracle`, OnBytes/Slice/SeedOracle.lean), the programs' own test on a shape, and that
there is an answer a row (asked by `RecNums`, OnBytes/TypedOracleCompiler/Slice/ThreeDelivers.lean; `coll_at` does
not use it). A
`Size` is any shape with any radius; this says that it is one at which the definitions mean what
they are meant to. -/
structure Fit : Prop where
  /-- the shape passes the programs' test on a table's shape (no theorem here uses it) -/
  ok : z.shape.ok = true
  /-- there is an answer a row: the tables have a record -/
  pos : 0 < z.s
  /-- the tree's depth is at most 32 (that theorem's bound, not a setting's number) -/
  depth : z.T.a ≤ 32
  /-- message and random tail fit into a word -/
  dim : z.T.r + z.T.l ≤ 2 ^ z.T.a
  /-- the radius is below the code's distance -/
  radius : z.eM < 2 ^ z.T.a - (z.T.r + z.T.l) + 1
  /-- the radius is within the Johnson bound -/
  johnson : Cb.InJohnson (2 ^ z.T.a) (2 ^ z.T.a - (z.T.r + z.T.l) + 1) z.eM
  /-- the message has room for its pads -/
  pads : 3 * z.s ≤ z.T.l
  /-- the entries before the pads are at most 2^lg -/
  cube : z.T.l - 3 * z.s ≤ 2 ^ z.lg
  /-- the blocks of the seeds' round are few enough for their strings to differ (that theorem's
  bound, not a setting's number) -/
  blocks : (seedBS z.lg z.s).b + 1 < 2 ^ 48

end Size

/-! ## The three readings -/

/-- THE RECORD OF A KEY UNDER AN ORACLE: the seeds that the programs' draw gives under g on the
key's table's name (root, configuration digest, six words of the shape: not the answers), with z's
numbers of coordinates and answers; and the answers that stand in the key. Nothing, unless the key
holds exactly 2^v * s answers. -/
noncomputable def recUAt (z : Size) (g : Fam (rom 256)) (k : IdKey) : Option z.D.Rec :=
  (seedUnder z.lg z.s k g).bind fun ρ => (recAns z.v z.s k).map fun a => (ρ, a)

/-- THE ONE WRITTEN READING of the raw string under a root off a log, at a key: `rawBy` at the
configuration digest in the key, at the depth of z's shape and its salt's length. Of the key it
reads the digest alone. It is said by strings: a vertex is the format's call number 166 from that
digest on two digests; a stored leaf is the format's call number 174, or a string behind the byte 2
that is no call of the format. WHERE A LOG HAS TWO STRINGS WITH ONE ANSWER, THIS READING AND A
PART'S OWN MAY PART: a part's walk ends at the first entry with the wanted answer that its
implementation reads as ANY leaf, also one that holds no stored symbol, and then reads (0, no word);
this reading knows stored leaves alone and passes such an entry by. -/
noncomputable def rawZ (z : Size) (k : IdKey) (σ : Trace (rom 256)) (cm : Dig 256) :
    Raw Run.PQ.SgX :=
  rawBy k.2.1 z.T.a z.shape.saltBytes σ cm

/-- The keys at whose shape the raw string is read and decoded: those that hold z's shape. -/
def okKeyAt (z : Size) (k : IdKey) : Prop := k.1 = z.shape

/-- A key's record under an oracle, unfolded. -/
theorem recUAt_iff (z : Size) (g : Fam (rom 256)) (k : IdKey) (rec : z.D.Rec) :
    recUAt z g k = some rec ↔
      seedUnder z.lg z.s k g = some rec.1 ∧ recAns z.v z.s k = some rec.2 := by
  unfold recUAt
  constructor
  · intro h
    obtain ⟨ρ, hρ, h1⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨a, ha, h2⟩ := Option.map_eq_some_iff.1 h1
    rw [← h2]
    exact ⟨hρ, ha⟩
  · rintro ⟨h1, h2⟩
    rw [h1, h2]
    rfl

/-- Every property of a key's record under the oracle is a measurable set of oracles. -/
theorem measR_recUAt (z : Size) (k : IdKey) (Q : z.D.Rec → Prop) :
    MeasurableSet {g | ∃ rec, recUAt z g k = some rec ∧ Q rec} := by
  have key : ∀ o, recAns z.v z.s k = o →
      MeasurableSet {g | ∃ rec, recUAt z g k = some rec ∧ Q rec} := by
    intro o ho
    cases o with
    | none =>
      have e : {g | ∃ rec, recUAt z g k = some rec ∧ Q rec} = ∅ := by
        ext g
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        rintro ⟨rec, hr, -⟩
        have h2 := ((recUAt_iff z g k rec).1 hr).2
        rw [ho] at h2
        cases h2
      rw [e]
      exact MeasurableSet.empty
    | some a =>
      have e : {g | ∃ rec, recUAt z g k = some rec ∧ Q rec} =
          {g | ∃ ρ, seedUnder z.lg z.s k g = some ρ ∧ Q (ρ, a)} := by
        ext g
        constructor
        · rintro ⟨rec, hr, hq⟩
          obtain ⟨h1, h2⟩ := (recUAt_iff z g k rec).1 hr
          rw [ho] at h2
          refine ⟨rec.1, h1, ?_⟩
          rw [Option.some.inj h2]
          exact hq
        · rintro ⟨ρ, h1, hq⟩
          exact ⟨(ρ, a), (recUAt_iff z g k (ρ, a)).2 ⟨h1, ho⟩, hq⟩
      rw [e]
      exact measurableSet_seedUnder z.lg z.s k fun ρ => Q (ρ, a)
  exact key _ rfl

/-- For ONE table f and ONE key k, both fixed before the oracle is drawn, at sizes that fit: the
measure of the oracles at whose seeds for k's table the record does not single one table out of f's
list is at most the bound of `coll_measure_oracle`. f and k are not tied. No number on the right is
evaluated. -/
theorem coll_at (z : Size) (h : z.Fit) (f : Fin (2 ^ z.T.a) → Run.PQ.SgX) (k : IdKey) :
    U (rom 256) {g | ∃ ρ, seedUnder z.lg z.s k g = some ρ ∧ z.D.coll f ρ} ≤
      kapSl 128 ^ (seedBS z.lg z.s).b *
        ((((Cb.listMax (2 ^ z.T.a) (2 ^ z.T.a - (z.T.r + z.T.l) + 1) z.eM).choose 2 *
          (recZ z.T.l z.lg z.s).err : ℕ) : ℝ≥0∞) / Fintype.card (recZ z.T.l z.lg z.s).D) :=
  coll_measure_oracle z.T z.v z.eM z.lg z.s h.depth h.dim h.radius h.johnson h.pads h.cube
    h.blocks f k

/-- The written reading does not see the entries at strings of calls with the number 169. No
condition on the key or on the log. -/
theorem rawZ_offSet (z : Size) (S : Finset (List Bool)) (hS : ∀ s ∈ S, IsCall169 s) (k : IdKey)
    (σ : Trace (rom 256)) (cm : Dig 256) : rawZ z k (offSet S σ) cm = rawZ z k σ cm :=
  rawBy_offSet _ _ _ S hS σ cm

/-! ## What `Beside` asks, of every `Three` with these readings -/

/-- Three parts at the sizes z: the two readings and the keys' shape are those above, and all public
strings are strings of calls with the number 169 (`OnBytes.Slice.IsCall169`). A part that holds a
value of the second hash function as a constant cannot be so: its string is no call number 169. -/
structure Three.At (z : Size) {Xi : Type} (Θ : Three z.D Xi) : Prop where
  /-- the record of a key under an oracle is `recUAt z` -/
  recU : Θ.recU = recUAt z
  /-- the one written reading is `rawZ z` -/
  rawU : Θ.rawU = rawZ z
  /-- the keys' shape is z's -/
  okKey : Θ.okKey = okKeyAt z
  /-- the first public strings are strings of calls with the number 169 -/
  pub₀ : ∀ s ∈ Θ.S₀, IsCall169 s
  /-- so are those that hang on the values at the first -/
  pub₁ : ∀ T₀, ∀ s ∈ Θ.S₁ T₀, IsCall169 s

namespace Three.At
variable {z : Size} {Xi : Type} {Θ : Three z.D Xi}

/-- The clause `apart`: no key's string is a public string. -/
theorem apart (h : Θ.At z) (k : IdKey) (s : List Bool) (hs : idCode k = some s) :
    s ∉ Θ.S₀ ∧ ∀ T₀, s ∉ Θ.S₁ T₀ :=
  ⟨fun hm => idCode_ne_call169 k (h.pub₀ s hm) hs,
    fun T₀ hm => idCode_ne_call169 k (h.pub₁ T₀ s hm) hs⟩

/-- The clause `rawOff`: the written reading does not see the entries at public strings. -/
theorem rawOff (h : Θ.At z) (S : Finset (List Bool)) (k : IdKey) (σ : Trace (rom 256))
    (cm : Dig 256) (hS : S = Θ.S₀ ∨ ∃ T₀, S = Θ.S₁ T₀) :
    Θ.rawU k (offSet S σ) cm = Θ.rawU k σ cm := by
  rw [h.rawU]
  refine rawZ_offSet z S ?_ k σ cm
  rcases hS with rfl | ⟨T₀, rfl⟩
  · exact h.pub₀
  · exact h.pub₁ T₀

/-- The clause `measR`: every property of a key's record under the oracle is a measurable set of
oracles. -/
theorem measR (h : Θ.At z) (k : IdKey) (Q : z.D.Rec → Prop) :
    MeasurableSet {g | ∃ rec, Θ.recU g k = some rec ∧ Q rec} := by
  rw [h.recU]
  exact measR_recUAt z k Q

/-- ALL OF `Beside`, IN ONE TERM: from the three languages, that the files' key holds z's shape,
and that the parts' one written reading is `rawZ z` at the files' key. -/
theorem beside (h : Θ.At z) {rd : Tab → Tab → Trace (rom 256) → Dig 256 → Raw Run.PQ.SgX}
    (langK : ∀ T₀ T₁ oK Y, (Θ.K T₀ T₁).Lang oK [Y] →
      DecR.LangK Θ.A (DecR.wayColl z.D) (Θ.recK T₀ T₁ oK) Y)
    (langE : ∀ T₀ T₁ oE Y₀ Y₁, (Θ.E T₀ T₁).Lang oE [Y₀, Y₁] →
      DecR.LangE (DecR.wayColl z.D) (Θ.recE₀ T₀ T₁ oE) (Θ.recE₁ T₀ T₁ oE) Y₀ Y₁)
    (langF : ∀ T₀ T₁ oF Y, (Θ.F T₀ T₁).Lang oF [Y] →
      DecR.LangP Θ.A (DecR.wayColl z.D) (Θ.xOf T₀ T₁ oF) (Θ.recF T₀ T₁ oF) Y)
    (keyOK : ∀ T₀ T₁ d, (Θ.key T₀ T₁ d).1 = z.shape)
    (rawRd : ∀ T₀ T₁ d σ cm, rd T₀ T₁ σ cm = rawZ z (Θ.key T₀ T₁ d) σ cm) : Θ.Beside rd where
  langK := langK
  langE := langE
  langF := langF
  apart := h.apart
  keyOK := fun T₀ T₁ d => by
    rw [h.okKey]
    exact keyOK T₀ T₁ d
  rawRd := fun T₀ T₁ d σ cm => by
    rw [h.rawU]
    exact rawRd T₀ T₁ d σ cm
  rawOff := fun S k σ cm hS => h.rawOff S k σ cm hS
  measR := h.measR

/-- WHAT IS FINE, WRITTEN OUT AT THESE READINGS. The committer's own log shows a first key k for
the ID; k holds z's shape; ρ are the seeds that the oracle gives at k's table's name; a are the
answers in k; the raw string that `rawZ` reads off the committer's own log under k's root decodes,
at the record (ρ, a), to u; the matrix of u is in range, and the claim of the instance read off
request and reply holds of it. That k's configuration digest is the oracle's value at the string of
any configuration is not said. -/
theorem fineB_iff (h : Θ.At z) (St : Type) (g : Fam (rom 256)) (w : Outcome St) :
    Θ.FineB St g w ↔ ∃ k ρ a u, firstId w.1.1.1.1 w.1.1.2 = some k ∧ k.1 = z.shape ∧
      seedUnder z.lg z.s k g = some ρ ∧ recAns z.v z.s k = some a ∧
      z.D.dcdRaw (rawZ z k w.1.1.2 (Run.bytesToDig k.2.2.root)) (ρ, a) = some u ∧
      Θ.A.inRange (Θ.A.mat u) ∧ Θ.A.Rel (Θ.A.mat u) (Θ.xReq w.1.2) := by
  unfold Three.FineB goodDecR
  rw [h.recU, h.rawU, h.okKey]
  constructor
  · rintro ⟨k, rec, hk, ho, hr, u, hu, h1, h2⟩
    obtain ⟨e1, e2⟩ := (recUAt_iff z g k rec).1 hr
    exact ⟨k, rec.1, rec.2, u, hk, ho, e1, e2, hu, h1, h2⟩
  · rintro ⟨k, ρ, a, u, hk, ho, e1, e2, hu, h1, h2⟩
    exact ⟨k, (ρ, a), hk, ho, (recUAt_iff z g k (ρ, a)).2 ⟨e1, e2⟩, u, hu, h1, h2⟩

/-- (a) AT THE SIZES z, FROM WHAT THREE FILES' PARTS DELIVER, the three languages, the files'
key's shape and "the parts' reading is `rawZ` at the files' key": `Three.soundB_of_delivers` with
`beside` put in. -/
theorem soundB_of_delivers (h : Θ.At z) {φK φE φF : FileSpec}
    (mK : ∀ T₀ T₁, Θ.K T₀ T₁ = φK.toO Θ.S₀ Θ.S₁ T₀ T₁)
    (mE : ∀ T₀ T₁, Θ.E T₀ T₁ = φE.toO Θ.S₀ Θ.S₁ T₀ T₁)
    (mF : ∀ T₀ T₁, Θ.F T₀ T₁ = φF.toO Θ.S₀ Θ.S₁ T₀ T₁)
    {rd : Tab → Tab → Trace (rom 256) → Dig 256 → Raw Run.PQ.SgX} {bK bE bF : ℕ → ℝ≥0∞}
    (hK : φK.Delivers Θ.S₀ Θ.S₁ rd bK) (hE : φE.Delivers Θ.S₀ Θ.S₁ rd bE)
    (hF : φF.Delivers Θ.S₀ Θ.S₁ rd bF) (rK rE rF : ℕ)
    (qK : ∀ T₀ T₁, (φK.part T₀ T₁).tR ≤ rK) (qE : ∀ T₀ T₁, (φE.part T₀ T₁).tR ≤ rE)
    (qF : ∀ T₀ T₁, (φF.part T₀ T₁).tR ≤ rF)
    (langK : ∀ T₀ T₁ oK Y, (Θ.K T₀ T₁).Lang oK [Y] →
      DecR.LangK Θ.A (DecR.wayColl z.D) (Θ.recK T₀ T₁ oK) Y)
    (langE : ∀ T₀ T₁ oE Y₀ Y₁, (Θ.E T₀ T₁).Lang oE [Y₀, Y₁] →
      DecR.LangE (DecR.wayColl z.D) (Θ.recE₀ T₀ T₁ oE) (Θ.recE₁ T₀ T₁ oE) Y₀ Y₁)
    (langF : ∀ T₀ T₁ oF Y, (Θ.F T₀ T₁).Lang oF [Y] →
      DecR.LangP Θ.A (DecR.wayColl z.D) (Θ.xOf T₀ T₁ oF) (Θ.recF T₀ T₁ oF) Y)
    (keyOK : ∀ T₀ T₁ d, (Θ.key T₀ T₁ d).1 = z.shape)
    (rawRd : ∀ T₀ T₁ d σ cm, rd T₀ T₁ σ cm = rawZ z (Θ.key T₀ T₁ d) σ cm) :
    Θ.SoundB (Three.eps bK bE bF (Three.bClash rK rE rF) Three.bStable) :=
  Three.soundB_of_delivers mK mE mF hK hE hF rK rE rF qK qE qF
    (h.beside langK langE langF keyOK rawRd)

end Three.At

/-- Three parts made of three files' specifications, AT THE SIZES z: `Three.ofSpecs` with the
two readings and the keys' shape of this file. -/
noncomputable def Three.ofSpecsAt (z : Size) {Xi : Type} (S₀ : Finset (List Bool))
    (S₁ : Tab → Finset (List Bool)) (φK φE φF : FileSpec) (key keyC : Tab → Tab → Files → IdKey)
    (recK : ∀ T₀ T₁, (φK.part T₀ T₁).Out → z.D.Rec)
    (recE₀ recE₁ : ∀ T₀ T₁, (φE.part T₀ T₁).Out → z.D.Rec)
    (recF : ∀ T₀ T₁, (φF.part T₀ T₁).Out → z.D.Rec) (xOf : ∀ T₀ T₁, (φF.part T₀ T₁).Out → Xi)
    (xReq : Files → Xi) (A : z.D.Claims Xi) : Three z.D Xi :=
  Three.ofSpecs S₀ S₁ φK φE φF key keyC recK recE₀ recE₁ recF xOf xReq A (recUAt z) (rawZ z)
    (okKeyAt z)

/-- They are at the sizes z, if all public strings are strings of calls with the number 169. -/
theorem Three.ofSpecsAt_at (z : Size) {Xi : Type} (S₀ : Finset (List Bool))
    (S₁ : Tab → Finset (List Bool)) (φK φE φF : FileSpec) (key keyC : Tab → Tab → Files → IdKey)
    (recK : ∀ T₀ T₁, (φK.part T₀ T₁).Out → z.D.Rec)
    (recE₀ recE₁ : ∀ T₀ T₁, (φE.part T₀ T₁).Out → z.D.Rec)
    (recF : ∀ T₀ T₁, (φF.part T₀ T₁).Out → z.D.Rec) (xOf : ∀ T₀ T₁, (φF.part T₀ T₁).Out → Xi)
    (xReq : Files → Xi) (A : z.D.Claims Xi) (h₀ : ∀ s ∈ S₀, IsCall169 s)
    (h₁ : ∀ T₀, ∀ s ∈ S₁ T₀, IsCall169 s) :
    (Three.ofSpecsAt z S₀ S₁ φK φE φF key keyC recK recE₀ recE₁ recF xOf xReq A).At z where
  recU := rfl
  rawU := rfl
  okKey := rfl
  pub₀ := h₀
  pub₁ := h₁

end OnBytes.Slice.Shapes
