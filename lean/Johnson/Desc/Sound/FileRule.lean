-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/FileRule.lean: the rule of composition ACROSS THE THREE HASH CHAINS of a file,
for one request, stated of the three chains' own decisions. A SHEET OF STATEMENTS: definitions, and
propositions written as `def … : Prop`. NOTHING IS PROVED IN THIS FILE.

The setting. Johnson/Desc/Sound/ChainRule.lean has one chain: its decision is the fold of its
blocks' verifiers, and `ChainRule` says that this decision is knowledge sound if every block is. A
file has three chains, each behind one round that sends a plain message and draws nothing (the
front, the joining round, the seam). The library has, for ANY three decisions on what the verifier
is shown of the three chains: the three chains as three interactive oracle reductions in a row
(`rowOf`, OnBytes/Maker/Row.lean), each handing on an explicit part and the trees that later chains
open; that where the file's one verifier over all rounds says yes, the row does (`rowOf_of_whole`,
OnBytes/Maker/RowWhole.lean); the row as the data of which the top theorems speak (`Row.links`,
OnBytes/TypedOracleCompiler/Joined/OfLinks.lean); and the list of what these theorems ask of such data
(`Links.Knows`, OnBytes/TypedOracleCompiler/Joined/Top.lean: a clause of knowledge soundness for each chain, and
that each chain hands on statements of which the next clause speaks).

What is said. `Three`: three chains' blocks with their stretches, over one list of all the file's
trees, with the functions that make a chain's first record and that pack what a chain hands on.
`Three.row`: the library's row at the three folds. `FileKnows`: if every block of the three chains
is good, the stretches tile each chain, and the relations at the chains' ends fit together, the
row's data meet `Links.Knows`. `FileDecides`: where the file's one verifier, whose decision is the
three folds in a row, says yes, the three reductions in a row put out.

Main names.
  `frameAt`; `Three`, `Three.run₁`, `Three.run₂`, `Three.run₃`, `Three.ofStarts` (the filling that
    is meant), `Three.row`; `extOwn`, `errOwn` (a chain's composed extractor and errors, carried to
    the chain's own list of rounds); `Three.Fits`; `Places`, `Three.mid₁`, `Three.mid₂`,
    `Three.Glue₁`, `Three.Glue₂`, `Three.Ends`, `Three.Glued`; `Three.snd`.
  THE STATEMENTS: `FileKnows` · `FileDecides`.

Who pays which field of `Links.Knows`. `know₁`, `know₂`, `know₃`: `ChainRule` at the first, the
second, the third chain, carried to the chain's own list of rounds, behind the silent round, and
along the functions that make and pack the records: that is `FileKnows`. `hands₁`, `hands₂`: free:
the conditions between the chains are `True`, and what they guarded is taken into the relations (a
statement outside the next chain's condition counts as having every witness: `orOff`,
Ior/KnowColl.lean; `KnowInto` is `Know` at such a relation). For several requests that share the
second chain the list is `Links.KnowsMid` (OnBytes/TypedOracleCompiler/Joined/Mid.lean): its `know₁`, `know₃`,
`hands₁`, `hands₂` are these; its clause on the shared chain and its law on keys are another
sheet's. WHAT STAYS A PREMISE OF THE TOP THEOREM (`proofSound_top_links`,
Johnson/TypedOracleCompiler/Joined/ProofLinksTop.lean; the example at the end feeds the value in): `decides` (from
`FileDecides`, where the three runs read of the instance only what does not change under `early`),
`tieR` (from the relation at the first boundary to the interface's), `worst` (the errors' size).

What a chain's record holds. A relation reads a statement and nothing else. IN THE FILLING THAT IS
MEANT (`Three.ofStarts`) A CHAIN'S RECORD HOLDS, BESIDE THE CHAIN'S OWN RECORD, WHAT WAS HANDED TO
THE CHAIN; THE BLOCKS ARE LIFTED; SO A RELATION AT ANY BOUNDARY CAN SPEAK OF IT, AND NO BLOCK CAN
READ OR CHANGE IT. Two things want that. The first relation has to speak of the instance's public
part. And the first chain's end leaves claims open that the third chain closes: they are carried
past the second chain as a conjunct of its relations at every boundary, under each block's own
extractor and errors. WHAT THAT COSTS: WHOEVER PROVES A BLOCK OF THE SECOND CHAIN GOOD OWES GOODNESS
AT "THE BLOCK'S OWN RELATION AND THE CARRIED CLAIM", NOT AT THE BLOCK'S OWN RELATION ALONE; AND THE
FIRST DOES NOT FOLLOW FROM THE SECOND: a clause into a condition on' says nothing of leaving on' at
a statement whose front relation holds anyway; and applied to such a clause the library's frame rule
(`know_frame`, Ior/Frame.lean) gives the output relation "(the relation, or outside on') and the
carried claim", where "(the relation and the carried claim), or outside on'" is asked. A form of a
block's clause from which it does follow is in Johnson/Desc/Sound/GoodIn.lean.

The relation at the first boundary. `Q.R₁ 0`, read at the first chain's first record and the stored
table with no tree sent, is the file's relation R₀ (`Three.snd`, field `R₀`). It is a PARAMETER
here: the rule asks nothing of it, and no text that this file's writer has read fixes its words. It
is fixed by whoever proves the first chain's first block good: it is the front relation of that
block's clause; and `tieR` of the top theorem is typed against it. It reads the instance through
`in₁` alone: so the first record has to hold whatever of the instance the relation of the top
theorems' interface is tied to; at the filling that is meant that is the public part, and that `pub`
keeps enough is owed where `tieR` is shown.

Limits. (1) Those of ChainRule.lean: nothing on acceptance; the degenerate cases; a rule, whose
premises are met by no block here. (2) ONE REQUEST: for several requests that share the second chain
the clause on that chain (the field `l₂` of `Links.KnowsJ`, the field `mid` of `Links.KnowsMid`)
comes from Johnson/Desc/Sound/SharedRule.lean. (3) `Glued` is a premise: that what the second chain
claims at its start implies what the first claims at its end is the protocol's matter. In `Glue₁`
and `Glue₂` what was handed to the chain and the chain's last statement are two variables, tied by
nothing: so a filling whose `out₁` or `out₂` reads the first, while the chain's last relation speaks
of a copy of it in the second, cannot meet them; at the filling that is meant both read the last
statement alone. (4) Nothing bounds the errors. (5) `FileDescription.run` (Johnson/Desc/Block.lean) is not
named: that its yes gives the yes of the three folds in a row is owed where a `FileDescription` is made.
(6) The test that every word is below the prime is not named: it is in the runs where the pieces
hold the blocks `below b` (`FoldBelow`, ChainRule.lean). (7) The three silent rounds' tests are
parameters; at tests that always say yes `FileDecides`' three laws on them are free.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.ChainRule
import OnBytes.Maker.RowWhole
import OnBytes.TypedOracleCompiler.Joined.OfLinks
import Johnson.TypedOracleCompiler.Joined.ProofLinksTop
import Johnson.EntryRec.AtFiles

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open _root_.Iop (Reduction Err Shape IOR ExtSpec oneExternalString)
open _root_.Iop.Reduction (orOff)
open _root_.TypedOracleCompiler.Joined (Links)

/-! ## 1 Three chains -/

/-- What is fixed for one chain of a file with the data D: the stored table's depth is the file's;
`all` lists the trees of the whole file; the keys and the number ft are the chain's. -/
abbrev frameAt (D : WholeD) (all : List LeftT) (key : ℕ → ℕ) (ft : ℕ) : Frame := ⟨D.a, all, key, ft⟩

/-- The oracles at every boundary of the three chains: the stored table and all the file's trees.
-/
abbrev EAll (D : WholeD) (all : List LeftT) : ExtSpec := (oneExternalString (2 ^ D.a) SgX).prod (EjOf all)

/-- **Three chains' blocks with their stretches.** D: the data of the file's written rounds. all:
every tree of the file, with its number through the whole file and its depth. Y: the file's
instances. S₁, S₂, S₃: the records that the verifier carries along the first, the second, the third
chain. X₁, X₂: what the first and the second chain hand on. -/
structure Three (C : CK) (D : WholeD) (all : List LeftT) (Y S₁ S₂ S₃ X₁ X₂ Cl W : Type) where
  ft₁ : ℕ
  ft₂ : ℕ
  ft₃ : ℕ
  /-- the first chain's first block with its stretch, and the others -/
  p₁ : Piece C (frameAt D all D.key₁ ft₁) S₁ Cl W
  l₁ : List (Piece C (frameAt D all D.key₁ ft₁) S₁ Cl W)
  p₂ : Piece C (frameAt D all D.key₂ ft₂) S₂ Cl W
  l₂ : List (Piece C (frameAt D all D.key₂ ft₂) S₂ Cl W)
  p₃ : Piece C (frameAt D all D.key₃ ft₃) S₃ Cl W
  l₃ : List (Piece C (frameAt D all D.key₃ ft₃) S₃ Cl W)
  /-- the chains' names, for a refusal's words -/
  n₁ : String
  n₂ : String
  n₃ : String
  /-- the first chain's first record, of the instance -/
  in₁ : Y → S₁
  /-- what the first chain hands on, of the instance and its last record -/
  out₁ : Y → S₁ → X₁
  /-- the second chain's first record, of what the first has handed on -/
  in₂ : X₁ → S₂
  /-- what the second chain hands on -/
  out₂ : X₁ → S₂ → X₂
  /-- the third chain's first record, or a refusal -/
  in₃ : X₂ → Option S₃
  /-- the last test, on what the second chain has handed on and the third chain's last record -/
  fin : X₂ → S₃ → Bool
  /-- the extractors' value where a block refuses -/
  d : W
  /-- the witness of the last statement: behind the last block nothing is left to be claimed, and
  the last relation is meant to hold of this value wherever the last test says yes (`Glued.ends`) -/
  wEnd : W

variable {C : CK} {D : WholeD} {all : List LeftT} {Y S₁ S₂ S₃ X₁ X₂ Cl W : Type}

/-- The first chain's decision: its fold, from the first record that the instance gives. -/
def Three.run₁ (T : Three C D all Y S₁ S₂ S₃ X₁ X₂ Cl W) : Y → Fmt.View → Option X₁ := fun x v =>
  (foldRun (frameAt D all D.key₁ T.ft₁) T.n₁ ((T.p₁ :: T.l₁).map (·.b)) (rowBack T.p₁ T.l₁)
    (T.in₁ x) v).map (T.out₁ x)

/-- The second chain's. -/
def Three.run₂ (T : Three C D all Y S₁ S₂ S₃ X₁ X₂ Cl W) : X₁ → Fmt.View → Option X₂ := fun a v =>
  (foldRun (frameAt D all D.key₂ T.ft₂) T.n₂ ((T.p₂ :: T.l₂).map (·.b)) (rowBack T.p₂ T.l₂)
    (T.in₂ a) v).map (T.out₂ a)

/-- The third chain's: its fold, and the last test on the record that it leaves. -/
def Three.run₃ (T : Three C D all Y S₁ S₂ S₃ X₁ X₂ Cl W) : X₂ → Fmt.View → Bool := fun a v =>
  match (T.in₃ a).bind fun s =>
      foldRun (frameAt D all D.key₃ T.ft₃) T.n₃ ((T.p₃ :: T.l₃).map (·.b)) (rowBack T.p₃ T.l₃) s
        v with
  | some s' => T.fin a s'
  | none => false

/-- **The filling that is meant**, written out so that a reader can ask of each premise below
whether it can be met there. P: the instance's public part; the three chains read the instance
through `pub` alone. ONE RULE FOR ALL THREE CHAINS: A CHAIN'S RECORD HOLDS, BESIDE THE CHAIN'S OWN
RECORD (S₁', S₂', S₃'), WHAT WAS HANDED TO THE CHAIN: the public part, at the first chain; the
public part and the first chain's last own record, at the second; these and the second chain's last
own record, at the third. The chain's blocks are meant to be blocks on its own record that are
lifted to the pair (`Block.lift`): such a block can neither read nor change the first part. THIS
DEFINITION LAYS THE SIX FUNCTIONS ALONE: it takes the pieces as they are given and lifts nothing. So
a relation at any boundary can speak of what was handed to the chain: the first relation of the
public part; the second chain's relations of a claim that the first chain's end leaves open for the
third. A chain's own record starts from the public part (the third chain's: from the public part and
both last own records, or it is refused). WHAT A CHAIN HANDS ON IS READ OFF ITS LAST RECORD ALONE,
the copy in it too: so in `Glue₁` and `Glue₂`, in which what was handed to the chain and the chain's
last statement are two variables, the last statement's own copy is spoken of. No last test stands in
the row. -/
def Three.ofStarts {P S₁' S₂' S₃' : Type} (pub : Y → P) (start₁ : P → S₁') (start₂ : P → S₂')
    (start₃ : P → S₁' → S₂' → Option S₃')
    (T : Three C D all Y (P × S₁') ((P × S₁') × S₂') ((P × S₁' × S₂') × S₃') X₁ X₂ Cl W) :
    Three C D all Y (P × S₁') ((P × S₁') × S₂') ((P × S₁' × S₂') × S₃') (P × S₁') (P × S₁' × S₂')
      Cl W :=
  { T with
    in₁ := fun x => (pub x, start₁ (pub x))
    out₁ := fun _ s => s
    in₂ := fun a => (a, start₂ a.1)
    out₂ := fun _ s => (s.1.1, s.1.2, s.2)
    in₃ := fun a => (start₃ a.1 a.2.1 a.2.2).map fun s => (a, s)
    fin := fun _ _ => true }

section Silent
variable {TF TJ T3 : Type} (tF : TF) (tJ : TJ) (t3 : T3)

/-- **The library's row at the three folds.** Behind the first and behind the second chain all the
file's trees are left. okF, okJ, ok3: the tests on what the three silent rounds send. -/
def Three.row (T : Three C D all Y S₁ S₂ S₃ X₁ X₂ Cl W) (okF : Y → TF → Bool)
    (okJ : X₁ → TJ → Bool) (ok3 : X₂ → T3 → Bool) :
    _root_.CompileK.Joined.Row (chainsOf C D tF tJ t3) Y (oneExternalString (2 ^ D.a) SgX) :=
  rowOf C D tF tJ t3 all all okF okJ ok3 T.run₁ T.run₂ T.run₃

end Silent

/-! ## 2 A chain's extractor and errors at the chain's own list of rounds -/

/-- The blocks' extractors composed (`rowExt`), carried along h to the chain's own list of rounds.
-/
def extOwn {S : Type} {F : Frame} (p : Piece C F S Cl W) (l : List (Piece C F S Cl W))
    (ds : List RDT) (h : (rowIOR p l).shape = uLT C ds) (d : W) :
    S × F.E.Str → Iop.Tr (uLT C ds) → W → W := fun a τ w =>
  rowExt d p l a (cast (congrArg Iop.Tr h.symm) τ) w

/-- The blocks' errors in a row (`rowErr`), carried likewise. -/
def errOwn {S : Type} {F : Frame} (p : Piece C F S Cl W) (l : List (Piece C F S Cl W))
    (ds : List RDT) (h : (rowIOR p l).shape = uLT C ds) : Err (uLT C ds) :=
  cast (congrArg Err h) (rowErr p l)

/-! ## 3 The premises -/

/-- **The three rows of pieces are the file's three chains.** The stretches' data in a row are the
chain's data; the first tree of each chain has the number that the file gives it; and the stretches
tile each chain. -/
structure Three.Fits (T : Three C D all Y S₁ S₂ S₃ X₁ X₂ Cl W) : Prop where
  data₁ : rowData T.p₁ T.l₁ = D.ds₁
  data₂ : rowData T.p₂ T.l₂ = D.ds₂
  data₃ : rowData T.p₃ T.l₃ = D.ds₃
  base₁ : T.p₁.base = 0
  base₂ : T.p₂.base = D.t₁
  base₃ : T.p₃.base = D.t₁ + D.t₂
  tiled₁ : Tiled T.p₁ T.l₁
  tiled₂ : Tiled T.p₂ T.l₂
  tiled₃ : Tiled T.p₃ T.l₃

/-- The conditions and the relations at the boundaries of the three chains (a boundary lies between
two blocks, in front of the first, or behind the last), by the boundary's number. -/
structure Places (D : WholeD) (all : List LeftT) (S₁ S₂ S₃ W : Type) where
  on₁ : ℕ → S₁ × (EAll D all).Str → Prop
  R₁ : ℕ → S₁ × (EAll D all).Str → W → Prop
  on₂ : ℕ → S₂ × (EAll D all).Str → Prop
  R₂ : ℕ → S₂ × (EAll D all).Str → W → Prop
  on₃ : ℕ → S₃ × (EAll D all).Str → Prop
  R₃ : ℕ → S₃ × (EAll D all).Str → W → Prop

/-- What is claimed of what the first chain has handed on: the relation at the second chain's first
boundary, at the record that the second chain makes of it; a statement outside the condition there
counts as having every witness. -/
def Three.mid₁ (T : Three C D all Y S₁ S₂ S₃ X₁ X₂ Cl W) (Q : Places D all S₁ S₂ S₃ W) :
    X₁ × (EAll D all).Str → W → Prop := fun a w =>
  orOff (Q.on₂ 0) (Q.R₂ 0) (T.in₂ a.1, a.2) w

/-- What is claimed of what the second chain has handed on: THE THIRD CHAIN HAS A FIRST RECORD, and
the like holds at its first boundary. Where the third chain has no first record the file is refused:
what was handed on then counts as having no witness. -/
def Three.mid₂ (T : Three C D all Y S₁ S₂ S₃ X₁ X₂ Cl W) (Q : Places D all S₁ S₂ S₃ W) :
    X₂ × (EAll D all).Str → W → Prop := fun a w =>
  ∃ s, T.in₃ a.1 = some s ∧ orOff (Q.on₃ 0) (Q.R₃ 0) (s, a.2) w

/-- What is claimed of what the first chain hands on implies what is claimed at the first chain's
last boundary. (Each relation is read with the statements outside its condition counted as having
every witness.) -/
def Three.Glue₁ (T : Three C D all Y S₁ S₂ S₃ X₁ X₂ Cl W) (Q : Places D all S₁ S₂ S₃ W) :
    Prop :=
  ∀ (x : Y) (b : S₁ × (EAll D all).Str) (w : W), T.mid₁ Q (T.out₁ x b.1, b.2) w →
    orOff (Q.on₁ (1 + T.l₁.length)) (Q.R₁ (1 + T.l₁.length)) b w

/-- The like at the second chain's last boundary. -/
def Three.Glue₂ (T : Three C D all Y S₁ S₂ S₃ X₁ X₂ Cl W) (Q : Places D all S₁ S₂ S₃ W) :
    Prop :=
  ∀ (a : X₁) (b : S₂ × (EAll D all).Str) (w : W), T.mid₂ Q (T.out₂ a b.1, b.2) w →
    orOff (Q.on₂ (1 + T.l₂.length)) (Q.R₂ (1 + T.l₂.length)) b w

/-- Where the last test says yes, `wEnd` is a witness of the last statement. In the filling that is
meant no last test stands in the row (`fin` always says yes): there the last relation is meant to be
"true": nothing is left to be claimed behind the last block, and the last block's goodness into
"true" still has its whole content. -/
def Three.Ends (T : Three C D all Y S₁ S₂ S₃ X₁ X₂ Cl W) (Q : Places D all S₁ S₂ S₃ W) :
    Prop :=
  ∀ (a : X₂) (b : S₃ × (EAll D all).Str), T.fin a b.1 = true →
    orOff (Q.on₃ (1 + T.l₃.length)) (Q.R₃ (1 + T.l₃.length)) b T.wEnd

/-- **The relations at the chains' ends fit together.** -/
structure Three.Glued (T : Three C D all Y S₁ S₂ S₃ X₁ X₂ Cl W)
    (Q : Places D all S₁ S₂ S₃ W) : Prop where
  glue₁ : T.Glue₁ Q
  glue₂ : T.Glue₂ Q
  ends : T.Ends Q

section Silent
variable {TF TJ T3 : Type} (tF : TF) (tJ : TJ) (t3 : T3)

/-- **The data of which the three clauses of knowledge soundness speak**, in the library's form
(`Row.Snd`). A statement of the file is an instance with the stored table; it is read as the first
chain's first statement: no tree holds a column yet. Each silent round has the error 0. Where the
third chain has no first record its extractor's value is d. -/
def Three.snd (T : Three C D all Y S₁ S₂ S₃ X₁ X₂ Cl W) (Q : Places D all S₁ S₂ S₃ W)
    (okF : Y → TF → Bool) (okJ : X₁ → TJ → Bool) (ok3 : X₂ → T3 → Bool)
    (h₁ : (rowIOR T.p₁ T.l₁).shape = uLT C D.ds₁) (h₂ : (rowIOR T.p₂ T.l₂).shape = uLT C D.ds₂)
    (h₃ : (rowIOR T.p₃ T.l₃).shape = uLT C D.ds₃) : (T.row tF tJ t3 okF okJ ok3).Snd where
  W₀ := W
  W₁ := W
  W₂ := W
  on₀ := fun a => Q.on₁ 0 (T.in₁ a.1, (a.2, fun _ => []))
  on₁ := fun _ => True
  on₂ := fun _ => True
  R₀ := fun a w => Q.R₁ 0 (T.in₁ a.1, (a.2, fun _ => [])) w
  R₁ := T.mid₁ Q
  R₂ := T.mid₂ Q
  e₁ := fun a τ w => extOwn T.p₁ T.l₁ D.ds₁ h₁ T.d (T.in₁ a.1, (a.2, fun _ => [])) τ.2.2 w
  e₂ := fun a τ w => extOwn T.p₂ T.l₂ D.ds₂ h₂ T.d (T.in₂ a.1, a.2) τ.2.2 w
  e₃ := fun a τ _ =>
    ((T.in₃ a.1).map fun s => extOwn T.p₃ T.l₃ D.ds₃ h₃ T.d (s, a.2) τ.2.2 T.wEnd).getD T.d
  ε₁ := (0, errOwn T.p₁ T.l₁ D.ds₁ h₁)
  ε₂ := (0, errOwn T.p₂ T.l₂ D.ds₂ h₂)
  ε₃ := (0, errOwn T.p₃ T.l₃ D.ds₃ h₃)
  d₀ := T.d
  d₁ := T.d

end Silent

/-! ## 4 The statements -/

/-- **The rule of composition across the three chains, for one request.** If the three rows of
pieces are the file's three chains, every block of each chain is good between its two boundaries,
and the relations at the chains' ends fit together, then the library's row at the three folds meets
what the top theorems ask of a file's description: a clause of knowledge soundness for each chain,
at the blocks' errors in a row behind an error 0 for the silent round. -/
def FileKnows : Prop :=
  ∀ (C : CK) (D : WholeD) (all : List LeftT) (Y S₁ S₂ S₃ X₁ X₂ Cl W TF TJ T3 : Type) (tF : TF)
    (tJ : TJ) (t3 : T3) (T : Three C D all Y S₁ S₂ S₃ X₁ X₂ Cl W)
    (Q : Places D all S₁ S₂ S₃ W)
    (okF : Y → TF → Bool) (okJ : X₁ → TJ → Bool) (ok3 : X₂ → T3 → Bool)
    (h₁ : (rowIOR T.p₁ T.l₁).shape = uLT C D.ds₁) (h₂ : (rowIOR T.p₂ T.l₂).shape = uLT C D.ds₂)
    (h₃ : (rowIOR T.p₃ T.l₃).shape = uLT C D.ds₃),
    T.Fits → EachGood Q.on₁ Q.R₁ 0 (T.p₁ :: T.l₁) → EachGood Q.on₂ Q.R₂ 0 (T.p₂ :: T.l₂) →
    EachGood Q.on₃ Q.R₃ 0 (T.p₃ :: T.l₃) → T.Glued Q →
    ((T.row tF tJ t3 okF okJ ok3).links (T.snd tF tJ t3 Q okF okJ ok3 h₁ h₂ h₃)).Knows

/-- **Where the file's one verifier says yes, the three reductions in a row put out.** The file's
verifier is the library's reduction over all the file's rounds (`reductionOfWholeFile`), with the three folds in
a row as its decision (`runRow`). `RowFit`: what the library asks of the data and of the list of
trees. The three laws on `silent`: where the file's test on what the three silent rounds send says
yes, so do the row's three tests. It is the library's `rowOf_of_whole` with `Row.all_out`. -/
def FileDecides : Prop :=
  ∀ (C : CK) (D : WholeD) (all : List LeftT) (Y S₁ S₂ S₃ X₁ X₂ Cl W TF TJ T3 : Type) (tF : TF)
    (tJ : TJ) (t3 : T3) (T : Three C D all Y S₁ S₂ S₃ X₁ X₂ Cl W) (okF : Y → TF → Bool)
    (okJ : X₁ → TJ → Bool) (ok3 : X₂ → T3 → Bool) (silent : Y → TF → TJ → T3 → Bool)
    (P : (T.row tF tJ t3 okF okJ ok3).Snd),
    RowFit D all all →
    (∀ x a b c, silent x a b c = true → okF x a = true) →
    (∀ x a b c v x₁, silent x a b c = true → T.run₁ x v = some x₁ → okJ x₁ b = true) →
    (∀ x a b c v v' x₁ x₂, silent x a b c = true → T.run₁ x v = some x₁ →
      T.run₂ x₁ v' = some x₂ → ok3 x₂ c = true) →
    ∀ (x : Y) (y : (oneExternalString (2 ^ D.a) SgX).Str) (τ : Iop.Tr (chainsOf C D tF tJ t3).sh),
      (reductionOfWholeFile C D tF tJ t3 silent (runRow T.run₁ T.run₂ T.run₃)).out x y τ = some () →
      (((T.row tF tJ t3 okF okJ ok3).links P).all.out (x, y) τ).isSome = true


/-! ## 5 Does the value fit the top theorem? -/

section Top
open VerifiableInference.OnPublicFiles OnBytes.RunA
open _root_.Run (ckP)

variable {a : ℕ} (Kc : ConfLetters a) (DK DP : WholeD) {TFk TJk T3k TFp TJp T3p : Type} (tFk : TFk)
  (tJk : TJk) (t3k : T3k) (tFp : TFp) (tJp : TJp) (t3p : T3p)
  (silK : Kc.conf.Rec → TFk → TJk → T3k → Bool)
  (runK : Kc.conf.Rec → Fmt.View → Fmt.View → Fmt.View → Bool)
  (silP : Kc.conf.X × Kc.conf.Rec → TFp → TJp → T3p → Bool) (eL : LinkProtocolWithLeafCoding Kc.conf.Rec a) (N : ℕ)
  (early : Kc.conf.X → Kc.conf.X) (all : List LeftT) {S₁ S₂ S₃ X₁ X₂ Cl W κ₁ κ₂ : Type}
  (T : Three (ckP .two) (DP.at a) all (Kc.conf.X × Kc.conf.Rec) S₁ S₂ S₃ X₁ X₂ Cl W)
  (Q : Places (DP.at a) all S₁ S₂ S₃ W)
  (okF : Kc.conf.X × Kc.conf.Rec → TFp → Bool)
  (okJ : X₁ → TJp → Bool) (ok3 : X₂ → T3p → Bool)
  (h₁ : (rowIOR T.p₁ T.l₁).shape = uLT (ckP .two) (DP.at a).ds₁)
  (h₂ : (rowIOR T.p₂ T.l₂).shape = uLT (ckP .two) (DP.at a).ds₂)
  (h₃ : (rowIOR T.p₃ T.l₃).shape = uLT (ckP .two) (DP.at a).ds₃)
  (P : (filesOf Kc .two DK DP tFk tJk t3k tFp tJp t3p silK runK silP
    (runRow T.run₁ T.run₂ T.run₃) eL N early none).Provers)
  (Tl : InnerCompilerInputFieldsOverThreeProtocols (filesOf Kc .two DK DP tFk tJk t3k tFp tJp t3p silK runK silP
                                    (runRow T.run₁ T.run₂ T.run₃) eL N early none) P)
  (U : SoundnessAnalysisFieldsOverThreeProtocols (filesOf Kc .two DK DP tFk tJk t3k tFp tJp t3p silK runK silP
                                     (runRow T.run₁ T.run₂ T.run₃) eL N early none) P)
  (k₁ : X₁ × (EAll (DP.at a) all).Str → κ₁) (k₂ : X₂ × (EAll (DP.at a) all).Str → κ₂)
  (toW : W → Kc.conf.Cells)

-- The top theorem for a proof file given as data, whose decision is the three folds in a row, AT
-- THE VALUE OF THIS SHEET: Lean prints what is left to be shown: `late = none` (by rfl), `knows`,
-- `decides`, `tieR`, `worst`.
#check proofSound_top_links
  (filesOf Kc .two DK DP tFk tJk t3k tFp tJp t3p silK runK silP (runRow T.run₁ T.run₂ T.run₃) eL N
    early none) P Tl U
  (wholeDesc (ckP .two) (DP.at a) tFp tJp t3p silP (runRow T.run₁ T.run₂ T.run₃)) rfl
  (KJ := (T.row tFp tJp t3p okF okJ ok3).links (T.snd tFp tJp t3p Q okF okJ ok3 h₁ h₂ h₃))
  (k₁ := k₁) (k₂ := k₂) toW

end Top

end VerifiableInference.Desc.Sound
