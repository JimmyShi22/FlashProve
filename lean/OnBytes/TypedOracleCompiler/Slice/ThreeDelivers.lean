-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Slice/ThreeDelivers.lean: the verifier on bytes is sound, AS AN IMPLICATION FROM A
WRITTEN LIST: what is owed for each of the three files, and beside them, as structures with one
named field for each debt; and one theorem from these to `Three.SoundB`
(OnBytes/TypedOracleCompiler/Slice/Shapes.lean).

In this file "the commitment ID" ("the ID"), where it stands by itself, is not the format's. It is
the hash function's answer at a shorter string, the format's string for its ID without the record's
seed (`idCode`, OnBytes/Tie/IdKey.lean). The format's rule (R4.11; `Fmt.publishedBytes`,
Fmt/Rules4.lean) hashes the string with the seed.

THIS IS WHAT WOULD BE CLAIMED; NOTHING IS SHOWN. No field of the lists is met by anybody. The use of
the file: whoever fills a field can read off what is owed, in Lean's letters, and a debt that is
paid is a term of a field's type.

The lists.
 `RecNums`              the numbers of a table's record, at an error: 8 fields.
 `FileDebts`            for every file: the page, the numbers of the bound, the typing: 10 fields.
 `KeyDebts`             the key's: `RecNums`; blocks enough; shallow trees; a lawful wiring;
                        SOUNDNESS RECORD BY RECORD; `FileDebts`: 6 fields, two of them lists.
 `EntryDebts`           the entry's: `RecNums`; the stored tables' depth is the code's; the field;
                        blocks enough; a lawful wiring; SOUNDNESS RECORD BY RECORD; `FileDebts`: 7
                        fields, two of them lists.
 `ProofDebts`           the proof's: "THE PROVER HAS LOST AT THE START" (`ReplyLost`); five on the
                        interface and the writing; four on the second protocol and its lane;
                        `FileDebts`: 11 fields, one of them a list.
 `TopDebts`             beside the three: the keys and the ID's string; the two readings in which
                        "fine" is said; bounds on the three checkers' strings: 8 fields.
Main definition.
 `threeAt`              the three files' parts at letters: `Three.ofSpecs`
                        (OnBytes/TypedOracleCompiler/Slice/ShapesFrom.lean) at `keySpecL`, `entrySpec`, `proofSpec`;
                        records and the claim's instance are read off the instances in the checkers'
                        values. ALL THREE JUDGES ARE `judgeEL` (OnBytes/TypedOracleCompiler/Slice/JudgeE.lean): the
                        compiled verifier without the test of the strict format.
Main theorems.
 `KeyDebts.delivers`, `EntryDebts.delivers`, `ProofDebts.delivers`   a file's list gives
                        `FileSpec.Delivers` (by `key_deliversL`, `entry_delivers`,
                        `proof_delivers`).
 `soundB_three`         THE FOUR LISTS GIVE `Three.SoundB` OF `threeAt`, with the bound of
                        `Three.soundB_of_delivers`.

NOT AMONG THE DEBTS: the three languages that the join asks: `langK_of_judgeE`
(OnBytes/TypedOracleCompiler/Slice/KeyDeliversL.lean), `langE_of_judgeE_out` (OnBytes/TypedOracleCompiler/Slice/EntryXRun.lean),
`langP_of_judgeE` (OnBytes/TypedOracleCompiler/Slice/ProofDelivers.lean). And, of `FileSpec.Delivers`, what the
three files named above prove.

Where a file's typing is a plain function of the files (`pureTyp`,
OnBytes/TypedOracleCompiler/Slice/ShapesConv.lean) the five fields of `FileDebts` on the typing are discharged once
for all: for the entry's file in OnBytes/TypedOracleCompiler/Slice/EntryHome.lean (`Left.debts`); for the key's and
the proof's nothing of the kind is written. The verifier on bytes of which `Three.SoundB` speaks
says yes also where a checker's own log shows a clash; a verifier without that limb says yes more
seldom, so the bound holds of it too, with a term that it need not pay.

Not claimed. THAT THE LISTS CAN BE MET, EACH OR TOGETHER. One code, one radius, one fixed value d
and one written reading rd stand in all three. NOTHING SHUTS AN EMPTY FILLING OUT: typings that
never return meet every field on typings; the verifier on bytes then says yes only at a clash, and
the theorem is true and says little: that some files are accepted is another matter. A claim `Ac`
that holds of everything makes all outcomes with a key fine; `Ac` is a letter. That `recU`, `rawU`,
`okKey`, `key`, `keyC`, `xReq` are the readings of any program: they are letters. That a yes of the
verifier on bytes follows from a run of the program: nothing here. NOT IN THE LISTS, for they belong
to the other half (a run's yes gives a yes of the verifier on bytes): the three links or a clash;
the law on a typing's log; what leads from the realised oracle to the oracle of that half; that each
part's public strings lie in the one union; the guards. NO LIST HAS ROOM FOR PROOF OF WORK BESIDE
THE COUNTS: `Err.Below` is over a protocol's own verifier's messages, test bits among them; a credit
is had only where the counts count the messages that pass. No number is evaluated; the bound says
nothing once it reaches 1. The three counts are multiplied by 3, 5 and 3 inside the parts' bounds.
What the heads of KeyDeliversL.lean, EntryDelivers.lean, ProofDelivers.lean, ShapesFrom.lean,
ShapesTop.lean and Shapes.lean do not claim. The compiler under OnBytes/TypedOracleCompiler/ is the one that
`innerCompiledVerifier` is made with; it builds on definitions of Compile/.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Slice.KeyDeliversL
import OnBytes.TypedOracleCompiler.Slice.EntryDelivers
import OnBytes.TypedOracleCompiler.Slice.ProofDelivers
import OnBytes.TypedOracleCompiler.Slice.ShapesFrom

set_option autoImplicit false

noncomputable section

namespace TypedOracleCompiler.Slice
open Rom Prob Cb _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run.PQ (SgX)
open _root_.Run (ckP chalP)
open OnBytes.Slice (DecR decRec recZ seedBS GE NZ Tab NoClash Raw ReplyLost offSet)
open OnBytes.Slice.Shapes (Files FileSpec Three)
open OnBytes.Tie (IdKey idCode)
open scoped ENNReal

/-! ## The lists of what is owed -/

/-- OWED: THE NUMBERS OF A TABLE'S RECORD, at an error εs. -/
structure RecNums (T : _root_.Fmt.M1.Code) (eM lg s : ℕ) (εs : ℝ≥0∞) : Prop where
  /-- there is an answer -/
  pos : 0 < s
  /-- the tree's depth is at most 32 -/
  depth : T.a ≤ 32
  /-- the code's dimension is at most its length -/
  dim : T.r + T.l ≤ 2 ^ T.a
  /-- the radius is below the distance -/
  radius : eM < 2 ^ T.a - (T.r + T.l) + 1
  /-- the radius is below the Johnson radius -/
  johnson : InJohnson (2 ^ T.a) (2 ^ T.a - (T.r + T.l) + 1) eM
  /-- a row has room for the pads -/
  pads : 3 * s ≤ T.l
  /-- the cube holds a row's message before the pads -/
  cube : T.l - 3 * s ≤ 2 ^ lg
  /-- the bound of `collRaw_pr` (OnBytes/Slice/SeedBias.lean) is at most the error -/
  price : kapSl 128 ^ (seedBS lg s).b *
    ((((listMax (2 ^ T.a) (2 ^ T.a - (T.r + T.l) + 1) eM).choose 2 * (recZ T.l lg s).err : ℕ) :
      ℝ≥0∞) / Fintype.card (recZ T.l lg s).D) ≤ εs

/-- OWED FOR EVERY FILE: THE PAGE, THE NUMBERS OF THE BOUND, THE TYPING, for a part by the way
"type, then run" (`FileSpec.ofTyping`, OnBytes/TypedOracleCompiler/Slice/ShapesTyping.lean). -/
structure FileDebts (base : Tab → Tab → Part 256 Files SgX)
    (typ : ∀ T₀ T₁, Files → OComp (rom 256) (Option (base T₀ T₁).Out))
    (pre : ∀ T₀ T₁, (o : (typedOracleFamily 256 (base T₀ T₁).W.K (base T₀ T₁).L).ι) →
      (typedOracleFamily 256 (base T₀ T₁).W.K (base T₀ T₁).L).Dom o →
      TypedOracleComputation 256 (base T₀ T₁).W.K (base T₀ T₁).L Unit)
    (n tT Bk : ℕ) (S₀ : Finset (List Bool)) (S₁ : Tab → Finset (List Bool))
    (rd : Tab → Tab → Trace (rom 256) → Dig 256 → Raw SgX) (b : ℕ → ℝ≥0∞) : Prop where
  /-- THE PAGE: a leaf's and a vertex's answer is one block, taken as it is -/
  one : ∀ T₀ T₁, OneBlock (base T₀ T₁).m
  /-- off a log without a clash the part reads the one written reading -/
  reads : ∀ T₀ T₁ σ, NoClash σ → ∀ cm,
    ((FileSpec.ofTyping base typ pre n tT Bk).part T₀ T₁).raw σ cm = rd T₀ T₁ σ cm
  /-- an answer has at most Bk blocks -/
  blocks : ∀ T₀ T₁ o, (base T₀ T₁).m.blocks o ≤ Bk
  /-- no typed query of the judge's run has a public string -/
  clean : ∀ T₀ T₁ (F : Fam (typedOracleFamily 256 (base T₀ T₁).W.K (base T₀ T₁).L)) (o : (base T₀ T₁).Out),
    ∀ e ∈ (((base T₀ T₁).J.run o).withTrace.det F).2,
      ∀ j, (base T₀ T₁).m.code e.1 e.2.1 j ∉ S₀ ∪ S₁ T₀
  /-- THE NUMBERS: one expression bounds the bound at all tables -/
  flat : ∀ T₀ T₁ t, ((FileSpec.ofTyping base typ pre n tT Bk).toO S₀ S₁ T₀ T₁).bound t ≤ b t
  /-- THE TYPING tosses no coin -/
  typNoCoin : ∀ T₀ T₁ x, (typ T₀ T₁ x).NoCoin
  /-- it asks at most tT strings -/
  typQueries : ∀ T₀ T₁ x, (typ T₀ T₁ x).QueryBound tT
  /-- at most a roots are read off the files -/
  few : ∀ T₀ T₁ x, ((base T₀ T₁).rts x).length ≤ (base T₀ T₁).a
  /-- the roots of what the typing returns are among these -/
  typNamed : ∀ T₀ T₁ (g : Fam (rom 256)) (x : Files) (o : (base T₀ T₁).Out),
    (typ T₀ T₁ x).det g = some o → ∀ r ∈ (base T₀ T₁).J.roots o, r ∈ (base T₀ T₁).rts x
  /-- what the typing returns is what the judge asks of an output beside the run's yes -/
  okT : ∀ T₀ T₁ (g : Fam (rom 256)) (x : Files) (o : (base T₀ T₁).Out),
    (typ T₀ T₁ x).det g = some o → (base T₀ T₁).J.ok o

/-! ## The key -/

section
variable {An : Type} {lg s : ℕ} [DecidableEq (SdK lg s)] {d : SdK lg s} {Xi : Type}
  (T : _root_.Fmt.M1.Code) (v eM : ℕ)
  (an : An → (decRec T v eM lg s).ix.Row × (decRec T v eM lg s).Z.S → GE)
  (Ac : (decRec T v eM lg s).Claims Xi) (Θ : Tab → Tab → KeyAt An lg s d) (εs : ℝ≥0∞)
  (typ : ∀ T₀ T₁, Files → OComp (rom 256) (Option ((Θ T₀ T₁).baseL T v eM an Ac εs).Out))
  (tT Bk : ℕ) (S₀ : Finset (List Bool)) (S₁ : Tab → Finset (List Bool))
  (rd : Tab → Tab → Trace (rom 256) → Dig 256 → Raw SgX) (b : ℕ → ℝ≥0∞)

/-- ALL THAT IS OWED FOR THE KEY'S FILE. -/
structure KeyDebts : Prop where
  /-- the record's numbers -/
  nums : RecNums T eM lg s εs
  /-- blocks enough for the seeds' sampler -/
  enough : ∀ T₀ T₁, (seedBS lg s).b ≤ (Θ T₀ T₁).K
  /-- no tree is deeper than 63 -/
  shallow : ∀ T₀ T₁, (atBlocks (Θ T₀ T₁).G).Shallow
  /-- the wiring is lawful -/
  wiring : ∀ T₀ T₁, (wq3X (atBlocks (Θ T₀ T₁).G) (Θ T₀ T₁).dec (Θ T₀ T₁).K
    (chalP .two (Θ T₀ T₁).K) (Θ T₀ T₁).o).OKG
  /-- SOUNDNESS RECORD BY RECORD, with one list of counts, each at most the error -/
  sound : ∀ T₀ T₁, ∃ ε : Err (atBlocks (Θ T₀ T₁).G).sh,
    (∀ x, (Plain3 (atBlocks (Θ T₀ T₁).G) ((Θ T₀ T₁).dec x)).Sound
      (fun _ => DecR.LgK (D := decRec T v eM lg s) (Equiv.refl _) an id Ac x) ε) ∧ Err.Below ε εs
  /-- the page, the numbers of the bound, the typing -/
  file : FileDebts (fun T₀ T₁ => (Θ T₀ T₁).baseL T v eM an Ac εs) typ
    (fun T₀ T₁ => (Θ T₀ T₁).preL) 2 tT Bk S₀ S₁ rd b

/-- Then the key's file delivers. -/
theorem KeyDebts.delivers (h : KeyDebts T v eM an Ac Θ εs typ tT Bk S₀ S₁ rd b) :
    (keySpecL T v eM an Ac Θ εs typ tT Bk).Delivers S₀ S₁ rd b := by
  choose ε hS hb using h.sound
  exact key_deliversL T v eM an Ac Θ εs typ tT Bk S₀ S₁ rd b h.nums.pos h.nums.depth
    h.nums.dim h.nums.radius h.nums.johnson h.nums.pads h.nums.cube h.nums.price h.enough h.shallow
    h.wiring ε hS hb h.file.one h.file.reads h.file.blocks h.file.clean h.file.flat
    h.file.typNoCoin h.file.typQueries h.file.few h.file.typNamed h.file.okT

end

/-! ## The entry -/

section
variable {An : Type} {lg s : ℕ} [DecidableEq (Sd1 lg s)] {d₁ : Sd1 lg s}
  (T : _root_.Fmt.M1.Code) (v eM : ℕ)
  (an : An → (decRec T v eM lg s).ix.Row × (decRec T v eM lg s).Z.S → GE)
  (Θ : Tab → Tab → EntryAt An lg s d₁) (εs : ℝ≥0∞)
  (typ : ∀ T₀ T₁, Files → OComp (rom 256) (Option ((Θ T₀ T₁).base T v eM an εs).Out))
  (tT Bk : ℕ) (S₀ : Finset (List Bool)) (S₁ : Tab → Finset (List Bool))
  (rd : Tab → Tab → Trace (rom 256) → Dig 256 → Raw SgX) (b : ℕ → ℝ≥0∞)

/-- ALL THAT IS OWED FOR THE ENTRY'S FILE. -/
structure EntryDebts : Prop where
  /-- the record's numbers -/
  nums : RecNums T eM lg s εs
  /-- the depth of the description's stored tables is the code's: elsewhere the entry's language
  holds of everything -/
  depthIs : ∀ T₀ T₁, (Θ T₀ T₁).D.a = T.a
  /-- the description's field is the second -/
  field : ∀ T₀ T₁, (Θ T₀ T₁).D.base.plan.field = .two
  /-- blocks enough for the seeds' sampler -/
  enough : ∀ T₀ T₁, (seedBS lg s).b ≤ (Θ T₀ T₁).D.K
  /-- the link's wiring is lawful -/
  wiring : ∀ T₀ T₁, (wq0 (Θ T₀ T₁).D fun _ => true).OKG
  /-- SOUNDNESS RECORD BY RECORD, with one list of counts, each at most the error -/
  sound : ∀ T₀ T₁, ∃ ε : Err (Link0 (Θ T₀ T₁).D fun _ => true).shape,
    (∀ x, (Link0 (Θ T₀ T₁).D ((Θ T₀ T₁).dec x)).Sound
      (fun _ => lgEX T v eM lg s (Θ T₀ T₁).D an x) ε) ∧ Err.Below ε εs
  /-- the page, the numbers of the bound, the typing -/
  file : FileDebts (fun T₀ T₁ => (Θ T₀ T₁).base T v eM an εs) typ
    (fun T₀ T₁ => (Θ T₀ T₁).pre) 4 tT Bk S₀ S₁ rd b

/-- Then the entry's file delivers. -/
theorem EntryDebts.delivers (h : EntryDebts T v eM an Θ εs typ tT Bk S₀ S₁ rd b) :
    (entrySpec T v eM an Θ εs typ tT Bk).Delivers S₀ S₁ rd b := by
  choose ε hS hb using h.sound
  exact entry_delivers T v eM an Θ εs typ tT Bk S₀ S₁ rd b h.nums.pos h.nums.depth
    h.nums.dim h.nums.radius h.nums.johnson h.nums.pads h.nums.cube h.nums.price h.depthIs h.field
    h.enough h.wiring ε hS hb h.file.one h.file.reads h.file.blocks h.file.clean h.file.flat
    h.file.typNoCoin h.file.typQueries h.file.few h.file.typNamed h.file.okT

end

/-! ## The proof -/

section
variable {A : Type} {lg s : ℕ} [DecidableEq (SdF lg s)] {Xi : Type} (T : _root_.Fmt.M1.Code)
  (v eM : ℕ) (an : A → (decRec T v eM lg s).ix.Row × (decRec T v eM lg s).Z.S → GE)
  (Ac : (decRec T v eM lg s).Claims Xi) (xOf : A → Xi) (Θ : Tab → Tab → ProofAt A lg s)
  (εs : ℝ≥0∞)
  (typ : ∀ T₀ T₁, Files →
    OComp (rom 256) (Option ((Θ T₀ T₁).base T v eM an Ac xOf εs).Out))
  (tT Bk : ℕ) (S₀ : Finset (List Bool)) (S₁ : Tab → Finset (List Bool))
  (rd : Tab → Tab → Trace (rom 256) → Dig 256 → Raw SgX) (b : ℕ → ℝ≥0∞) (d₁ : SdF lg s)

/-- ALL THAT IS OWED FOR THE PROOF'S FILE. -/
structure ProofDebts : Prop where
  /-- THE INTERACTIVE PROTOCOL: for every early part and every external string the prover has lost
  at the start towards "every instance with this early part that the verifier accepts is in the
  language", with counts whose shares are at most the error -/
  lost : ∀ T₀ T₁, ∃ ε : Err (Θ T₀ T₁).Z.Q.loc.shape,
    ReplyLost (Θ T₀ T₁).Z.Q.loc ε (fun x => ((Θ T₀ T₁).e x.1, x.2))
      ((Θ T₀ T₁).Lg T v eM an Ac xOf) ∧
    Err.Below (Err.timesShared (Θ T₀ T₁).L.maxBatchSize (Θ T₀ T₁).Z.Q.ann ε) εs
  /-- a string has 2 ^ a symbols: elsewhere the proof's language holds of everything -/
  lengthIs : ∀ T₀ T₁, (Θ T₀ T₁).L.wordLength = 2 ^ T.a
  /-- the writing is lawful -/
  written : ∀ T₀ T₁, (Θ T₀ T₁).Z.OK
  /-- there are as many slots as the request tree under the writing's tag has leaves -/
  slots : ∀ T₀ T₁, (Θ T₀ T₁).L.maxBatchSize = 2 ^ ((Θ T₀ T₁).W.dReq (Θ T₀ T₁).Z.t)
  /-- a first query holds what e leaves of the first part, and the fixed value -/
  early : ∀ T₀ T₁ x, (Θ T₀ T₁).L.early x = ((Θ T₀ T₁).e x.1, d₁)
  /-- no later query holds the instance -/
  late : ∀ T₀ T₁, (Θ T₀ T₁).L.late = none
  /-- THE SECOND PROTOCOL stands under another tag -/
  tags : ∀ T₀ T₁, (Θ T₀ T₁).ZT.t ≠ (Θ T₀ T₁).Z.t
  /-- it has two rounds -/
  two : ∀ T₀ T₁, (Θ T₀ T₁).ZT.P.shape.length = 2
  /-- what it writes of a plain part is read back -/
  back : ∀ T₀ T₁ z, (Θ T₀ T₁).ZT.prjP ((Θ T₀ T₁).ZT.embP z) = some z
  /-- the lane whose state is "the record does not single one table out" obeys the laws of a lane,
  at as many slots as the request tree under the second protocol's tag has leaves, with counts at
  most the error -/
  lane : ∀ T₀ T₁, ∃ εT : Err (Θ T₀ T₁).ZT.P.shape,
    ((Θ T₀ T₁).ZT.laneBad (Θ T₀ T₁).R εT fun y ρ =>
      DecR.badK (D := decRec T v eM lg s) (Θ T₀ T₁).u id y
        ((Θ T₀ T₁).seedOf ρ)).OK (2 ^ ((Θ T₀ T₁).W.dReq (Θ T₀ T₁).ZT.t)) ∧ Err.Below εT εs
  /-- the page, the numbers of the bound, the typing -/
  file : FileDebts (fun T₀ T₁ => (Θ T₀ T₁).base T v eM an Ac xOf εs) typ
    (fun T₀ T₁ => (Θ T₀ T₁).pre) 2 tT Bk S₀ S₁ rd b

/-- Then the proof's file delivers. -/
theorem ProofDebts.delivers
    (h : ProofDebts T v eM an Ac xOf Θ εs typ tT Bk S₀ S₁ rd b d₁) :
    (proofSpec T v eM an Ac xOf Θ εs typ tT Bk).Delivers S₀ S₁ rd b := by
  choose ε hL hb using h.lost
  choose εT oT bT using h.lane
  exact proof_delivers T v eM an Ac xOf Θ εs typ tT Bk S₀ S₁ rd b d₁ ε hL hb h.lengthIs
    h.written h.slots h.early h.late h.tags h.two h.back εT oT bT h.file.one h.file.reads
        h.file.blocks
    h.file.clean h.file.flat h.file.typNoCoin h.file.typQueries h.file.few h.file.typNamed
    h.file.okT

end

/-! ## The three together -/

section
variable {An AF Xi : Type} {lg s : ℕ} [DecidableEq (Fin s → (Fin lg → GE) × NZ)]
  {d : Fin s → (Fin lg → GE) × NZ} (T : _root_.Fmt.M1.Code) (v eM : ℕ)
  (an : An → (decRec T v eM lg s).ix.Row × (decRec T v eM lg s).Z.S → GE)
  (anF : AF → (decRec T v eM lg s).ix.Row × (decRec T v eM lg s).Z.S → GE)
  (Ac : (decRec T v eM lg s).Claims Xi) (xOf : AF → Xi)
  (ΘK : Tab → Tab → KeyAt An lg s d) (ΘE : Tab → Tab → EntryAt An lg s d)
  (ΘF : Tab → Tab → ProofAt AF lg s) (eK eE eF : ℝ≥0∞)
  (typK : ∀ T₀ T₁, Files →
    OComp (rom 256) (Option ((ΘK T₀ T₁).baseL T v eM an Ac eK).Out))
  (typE : ∀ T₀ T₁, Files → OComp (rom 256) (Option ((ΘE T₀ T₁).base T v eM an eE).Out))
  (typF : ∀ T₀ T₁, Files →
    OComp (rom 256) (Option ((ΘF T₀ T₁).base T v eM anF Ac xOf eF).Out))
  (tK tE tF BK BE BF : ℕ) (S₀ : Finset (List Bool)) (S₁ : Tab → Finset (List Bool))
  (key keyC : Tab → Tab → Files → IdKey) (xReq : Files → Xi)
  (recU : Fam (rom 256) → IdKey → Option (decRec T v eM lg s).Rec)
  (rawU : IdKey → Trace (rom 256) → Dig 256 → Raw SgX) (okKey : IdKey → Prop)

/-- THE THREE FILES' PARTS, AT LETTERS: `Three.ofSpecs` (OnBytes/TypedOracleCompiler/Slice/ShapesFrom.lean) at
`keySpecL`, `entrySpec`, `proofSpec`. The records and the claim's instance are read off the
instances in the checkers' values: seeds as they stand there; answers by `an`, `anF` (the entry's
two records: `recE₀`, `recE₁`, OnBytes/TypedOracleCompiler/Slice/EntryXRun.lean); the claim's instance by `xOf`. -/
def threeAt : Three (decRec T v eM lg s) Xi :=
  Three.ofSpecs S₀ S₁ (keySpecL T v eM an Ac ΘK eK typK tK BK)
    (entrySpec T v eM an ΘE eE typE tE BE)
    (proofSpec T v eM anF Ac xOf ΘF eF typF tF BF) key keyC
    (fun T₀ T₁ (o : OutE (ΘK T₀ T₁).ZE) => (o.2.1.2, an o.2.1.1))
    (fun T₀ T₁ (o : OutE (ΘE T₀ T₁).Z) => recE₀ T v eM an o)
    (fun T₀ T₁ (o : OutE (ΘE T₀ T₁).Z) => recE₁ T v eM an o)
    (fun T₀ T₁ (o : OutE (ΘF T₀ T₁).Z) => (o.2.1.2, anF o.2.1.1))
    (fun T₀ T₁ (o : OutE (ΘF T₀ T₁).Z) => xOf o.2.1.1) xReq Ac recU rawU okKey

/-- OWED BESIDE THE THREE FILES: the keys and the ID's string; the two readings in which "fine"
is said; bounds on the three checkers' strings at all tables. -/
structure TopDebts (rd : Tab → Tab → Trace (rom 256) → Dig 256 → Raw SgX) (rK rE rF : ℕ) :
    Prop where
  /-- no key's string is a public string -/
  apart : ∀ k x, idCode k = some x → x ∉ S₀ ∧ ∀ T₀, x ∉ S₁ T₀
  /-- the files' key has the right shape -/
  keyOK : ∀ T₀ T₁ f, okKey (key T₀ T₁ f)
  /-- the parts' one written reading is the reading in which "fine" is said, at the files' key -/
  rawRd : ∀ T₀ T₁ f σ cm, rd T₀ T₁ σ cm = rawU (key T₀ T₁ f) σ cm
  /-- the written reading does not see the entries at public strings -/
  rawOff : ∀ S k σ cm, (S = S₀ ∨ ∃ T₀, S = S₁ T₀) → rawU k (offSet S σ) cm = rawU k σ cm
  /-- every property of a key's record under the oracle is a measurable set of oracles -/
  measR : ∀ k (Q : (decRec T v eM lg s).Rec → Prop),
    MeasurableSet {g | ∃ rec, recU g k = some rec ∧ Q rec}
  /-- the key's checker asks at most rK strings, at all tables -/
  countK : ∀ T₀ T₁, ((keySpecL T v eM an Ac ΘK eK typK tK BK).part T₀ T₁).tR ≤ rK
  /-- the entry's at most rE -/
  countE : ∀ T₀ T₁, ((entrySpec T v eM an ΘE eE typE tE BE).part T₀ T₁).tR ≤ rE
  /-- the proof's at most rF -/
  countF : ∀ T₀ T₁, ((proofSpec T v eM anF Ac xOf ΘF eF typF tF BF).part T₀ T₁).tR ≤ rF

/-- THE VERIFIER ON BYTES IS SOUND, AS AN IMPLICATION FROM A WRITTEN LIST: THIS IS WHAT WOULD BE
CLAIMED; NOTHING IS SHOWN. IF all that is owed for the key's, the entry's and the proof's file is
paid (`KeyDebts`, `EntryDebts`, `ProofDebts`), at one written reading rd, and what is owed beside
(`TopDebts`), THEN `Three.SoundB` (OnBytes/TypedOracleCompiler/Slice/Shapes.lean) holds of `threeAt`, with the bound
of `Three.soundB_of_delivers`. The three languages are no debts: `langK_of_judgeE`,
`langE_of_judgeE_out`, `langP_of_judgeE`. -/
theorem soundB_three (rd : Tab → Tab → Trace (rom 256) → Dig 256 → Raw SgX)
    (bK bE bF : ℕ → ℝ≥0∞) (rK rE rF : ℕ)
    (hK : KeyDebts T v eM an Ac ΘK eK typK tK BK S₀ S₁ rd bK)
    (hE : EntryDebts T v eM an ΘE eE typE tE BE S₀ S₁ rd bE)
    (hF : ProofDebts T v eM anF Ac xOf ΘF eF typF tF BF S₀ S₁ rd bF d)
    (hT : TopDebts T v eM an anF Ac xOf ΘK ΘE ΘF eK eE eF typK typE typF tK tE tF BK BE BF
      S₀ S₁ key recU rawU okKey rd rK rE rF) :
    (threeAt T v eM an anF Ac xOf ΘK ΘE ΘF eK eE eF typK typE typF tK tE tF BK BE BF S₀ S₁
      key keyC xReq recU rawU okKey).SoundB
      (Three.eps bK bE bF (Three.bClash rK rE rF) Three.bStable) :=
  Three.soundB_of_delivers (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) hK.delivers
    hE.delivers hF.delivers rK rE rF hT.countK hT.countE hT.countF
    { langK := fun T₀ T₁ oK Y h =>
        langK_of_judgeE T v eM an Ac (show OutE (ΘK T₀ T₁).ZE from oK).2.1 Y h
      langE := fun T₀ T₁ oE Y₀ Y₁ h =>
        langE_of_judgeE_out T v eM an (ΘE T₀ T₁).D (show OutE (ΘE T₀ T₁).Z from oE) Y₀ Y₁ h
      langF := fun T₀ T₁ oF Y h =>
        langP_of_judgeE T v eM anF Ac xOf (ΘF T₀ T₁) (show OutE (ΘF T₀ T₁).Z from oF).2.1 Y h
      apart := hT.apart
      keyOK := hT.keyOK
      rawRd := hT.rawRd
      rawOff := hT.rawOff
      measR := hT.measR }

end

end TypedOracleCompiler.Slice
