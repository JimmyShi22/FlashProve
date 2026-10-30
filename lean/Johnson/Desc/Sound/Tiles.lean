-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/Tiles.lean: THE STRETCHES TILE THE CHAINS, BY THE MAKE OF THE DATA. A SHEET OF
STATEMENTS: definitions, and propositions written as `def … : Prop`. NOTHING IS PROVED IN THIS FILE.

The setting. The rule of composition (ChainRule.lean, FileRule.lean) takes a chain's blocks each
with its stretch of the written rounds' data (a `Piece`) and asks, beside one law of soundness for
each block, FACTS ABOUT THE FOLD: `Tiled` (each block is owed just its stretch, `Owed`; its trees
are listed, `Listed`; the trees are numbered on; only the last block has a round put back),
`Three.Fits` (the stretches' data in a row are the file's; the chains' first trees have the file's
numbers), and `RowFit D all all`. This sheet says that these are no premises on a protocol: THEY
HOLD OF EVERY DESCRIPTION, WHATEVER BLOCKS STAND IN IT, where the data are made of the description's
own declared rounds by `dataOf` and the makers' tests say yes. No premise `planOk` stands in
the statements: the data are made of the very rounds that the blocks declare, and the makers' tests,
whose yes stands in `FileDescription.data`'s yes, ask all that the tiling rests on, BUT FOR ONE THING,
which Block.lean's `planOk` asks (`sealLast`) and the makers' tests do not; here it is a premise by
itself, since no other clause of `planOk` is leant on: the first chain's last block has a round
(Limits, 1).

What is laid.
  `Rest`, `pieceOf`, `cutRow`: THE MAKER OF THE PIECES. A chain's blocks, in order, each with the
    next `b.rounds.length` rounds of the chain's data; the last block takes what is left, and it
    alone has the rounds `putBack` put behind its own. A piece's first tree has the number of the
    trees sent so far. Of a block the maker reads its number of declared rounds, and nothing else.
    The extractor and the errors come in as a family (`rest`): their types hang on the cut.
  `allOf D`: every tree of the file, once, under its number through the file, at the depth that the
    data give it.
  `RoundMatch`, `Matches`, `InTime`, `lastRounds`, `ChainFit`: what the tiling rests on, for one
    chain: a declared round and a round's data open the same stored parts, at the stored table's
    depth, and tree by tree the declared shape's depth is the tree's; declared rounds beyond the
    data read nothing; no round opens a tree that is sent in a later round; the rounds put back lie
    in the last block; the list of all trees has each tree once, at its depth.
  `WrittenAs`: declared rounds as written rounds, round by round (`Fmt.DeclaredRound.round`).
  `Three.IsCut`: the three rows of pieces of a `Three` are the maker's.
THE STATEMENTS.
  `CutBlocks` · `CutData` · `CutBack` · `CutBase`: the maker's pieces hold the blocks, in order;
    their data in a row are the chain's data; the last has `putBack` put back; the first has the
    base given.
  `TiledOfFit`: under `ChainFit` the maker's pieces tile the chain.
  `FitOfOk`: where three lists of declared rounds are written as R and the makers' tests (`okAt`)
    say yes of R, `ChainFit` holds at the three chains of the data made of R, at `allOf`, for any
    blocks whose declared rounds in a row are these lists, if the first chain's last block has a
    round.
  `RowFitOfOk`: there `RowFit D (allOf D) (allOf D)`.
  `FitsOfOk`: there `Three.Fits`, at every `Three` whose pieces are the maker's.
(The same at `FileDescription.data`: Johnson/Desc/Sound/TilesData.lean.)

Limits. (1) THE FIRST CHAIN's LAST BLOCK MUST ITSELF DECLARE THE SEALING ROUND. `Tiled` lets the
last piece alone have rounds put back. If a block without a round stood behind the block that
declares the seal, `Three.Fits` could not be met by any pieces, as it is typed. Block.lean's
`planOk` asks it (`FileDescription.sealLast`: the first chain's last block has a round). Here it is a
premise by itself (`1 ≤ lastRounds b₁ l₁`), a test on the plan.
The premise says only that the last block has a round; that this round is the sealing round follows
from `count` and `Matches`: the one declared round beyond the data is the row's last. No name of a
round is compared. (2) NO CLAUSE OF `FileDescription.planOk` IS LEANT ON: the tiling counts rounds, opened
leaves and trees; it compares no key, no label, no entry, no tenant. (3) THAT THESE DATA ARE THE
PLAN's DATA IS NOT SAID: the data follow the blocks' own declared rounds, and no clause of `planOk`
is a premise here. SO A BLOCK THAT DECLARES ITS READS
SHORT (fewer openings than the plan's errors count on) MEETS EVERY STATEMENT HERE: the data are then
short with it. It is a hole of FIT, not of these statements: for soundness a short declaration costs
the block's own law its numbers (fewer queries, larger errors). It is closed where the declared
rounds are held against the plan's, whole: a clause of Block.lean's `planOk`;
its law, that the data are then the plan's data: `dataIsPlans`,
Johnson/Desc/Sound/ReadsOkProofs.lean. (4) THE TILING COUNTS: IT COMPARES NO KEY. Where the frame's
keys parted from the declared labels, every block that reads a tree would refuse every transcript of
its stage, its law would be free, and the rule of composition would say nothing at these data: the
tiling does not shut that out. WHAT SHUTS IT OUT: at every description every piece's view shows just
the keys and positions that `Block.step` looks for: `readsOfData`,
Johnson/Desc/Sound/ReadsOfData.lean. The columns' WIDTHS are said nowhere yet. (5) Nothing on
soundness: `EachGood` stays owed, block by block. (6) That `okAt` says yes at any file is a premise.
(7) A description whose blocks say yes to all, and one whose blocks say no to all, both meet every
statement here, and rightly: nothing is claimed of what a block decides: the maker and the premises
read of a block its declared rounds alone. (8) ON WHICH SIDE OF A VIEW: `Owed` speaks of typed
transcripts, and of the views that a stage makes of them. `count_match` holds AT ALL DRAWS, in their
range or not: the declared rounds and the data both take a drawn position modulo the tree's length.
So nothing here leans on a drawn position's range, and nothing here says that a view with a position
out of its range is refused.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.FileRule
import Johnson.Desc.Sound.Cuts
import OnBytes.Maker.Files
import Fmt.Parsed

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open _root_.Iop (Reduction Err Shape IOR ExtSpec oneExternalString)
open OnBytes.Params (Rounds)

/-! ## 1 The maker of the pieces -/

/-- What a piece holds beside its block and its stretch: the extractor and the errors, at the
stretch's data. -/
structure Rest (C : CK) (F : Frame) (S W : Type) (ds : List RDT) where
  ext : S × F.E.Str → Iop.Tr (uLT C ds) → W → W
  err : Err (uLT C ds)

variable {C : CK} {F : Frame} {S Cl W : Type}

/-- A piece, of its parts. -/
def pieceOf (b : Block S Cl) (base : ℕ) (ds : List RDT) (back : List Fmt.RoundView)
    (x : Rest C F S W ds) : Piece C F S Cl W :=
  ⟨b, base, ds, back, x.ext, x.err⟩

/-- **The maker of the pieces.** i: the first block's number in its chain. base: the number, through
the whole file, of the next tree. ds: the data of the rounds that are left. Each block but the last
takes as many rounds off the front as it declares; the last takes what is left, and has `putBack`
put behind its own rounds. -/
def cutRow (rest : (i : ℕ) → (ds : List RDT) → Rest C F S W ds) (putBack : List Fmt.RoundView) :
    ℕ → ℕ → List RDT → Block S Cl → List (Block S Cl) →
      Piece C F S Cl W × List (Piece C F S Cl W)
  | i, base, ds, b, [] => (pieceOf b base ds putBack (rest i ds), [])
  | i, base, ds, b, b' :: l =>
    (pieceOf b base (ds.take b.rounds.length) [] (rest i (ds.take b.rounds.length)),
      (cutRow rest putBack (i + 1) (base + nTrees (ds.take b.rounds.length))
        (ds.drop b.rounds.length) b' l).1 ::
      (cutRow rest putBack (i + 1) (base + nTrees (ds.take b.rounds.length))
        (ds.drop b.rounds.length) b' l).2)

/-- The number of trees that the three chains send. -/
def nAll (D : WholeD) : ℕ := D.t₁ + D.t₂ + nTrees D.ds₃

/-- **Every tree of the file**, once, under its number through the file, at the depth that the data
give it. -/
def allOf (D : WholeD) : List LeftT := (List.range (nAll D)).map fun j => ⟨j, (D.depth j).getD 0⟩

/-! ## 2 What the tiling rests on, for one chain -/

/-- A declared round against a round's data. a: the stored table's depth. dep: the trees' depths, by
their numbers through the file. The same stored parts, each at the depth a; as many trees opened,
and tree by tree the declared shape's depth is the tree's. -/
def RoundMatch (a : ℕ) (dep : ℕ → Option ℕ) (r : Fmt.DeclaredRound) (d : RDT) : Prop :=
  d.stored = r.stored ∧ (∀ s ∈ r.stored, s.sh.a = a) ∧
    List.Forall₂ (fun (o : Fmt.Shape × Fmt.TreeSource) (j : ℕ) => dep j = some o.1.a) r.opens d.opens

/-- Declared rounds against rounds' data, round by round; declared rounds beyond the data read
nothing; there are no data beyond the declared rounds. -/
def Matches (a : ℕ) (dep : ℕ → Option ℕ) : List Fmt.DeclaredRound → List RDT → Prop
  | [], [] => True
  | r :: rs, [] => (r.stored = [] ∧ r.opens = []) ∧ Matches a dep rs []
  | [], _ :: _ => False
  | r :: rs, d :: ds => RoundMatch a dep r d ∧ Matches a dep rs ds

/-- No round opens a tree that is sent in a later round. B: the number of the next tree. -/
def InTime : ℕ → List RDT → Prop
  | _, [] => True
  | B, d :: ds => (∀ j ∈ d.opens, j < B + d.trees.length) ∧ InTime (B + d.trees.length) ds

/-- The number of rounds that the last block of a row declares. -/
def lastRounds : Block S Cl → List (Block S Cl) → ℕ
  | b, [] => b.rounds.length
  | _, b' :: l => lastRounds b' l

/-- **What the tiling rests on.** -/
structure ChainFit (F : Frame) (dep : ℕ → Option ℕ) (base : ℕ) (b : Block S Cl)
    (l : List (Block S Cl)) (ds : List RDT) (putBack : List Fmt.RoundView) : Prop where
  /-- the blocks' declared rounds in a row, against the chain's data -/
  rounds : Matches F.a dep ((b :: l).flatMap (·.rounds)) ds
  /-- the data and the rounds put back are as many as the declared rounds -/
  count : ds.length + putBack.length = ((b :: l).flatMap (·.rounds)).length
  /-- the rounds put back lie in the last block -/
  sealLast : putBack.length ≤ lastRounds b l
  inTime : InTime base ds
  /-- the chain's own trees have the depths that dep says -/
  own : ∀ n sh, treeShT ds n = some sh → dep (base + n) = some sh.a
  /-- a tree that has a depth stands once in the frame's list, at that depth -/
  listed : ∀ j a', dep j = some a' → (F.all.filter (·.no == j)).map (·.a) = [a']

/-! ## 3 The statements on the maker -/

/-- The maker's pieces hold the blocks, in order. -/
def CutBlocks : Prop :=
  ∀ (C : CK) (F : Frame) (S Cl W : Type) (rest : (i : ℕ) → (ds : List RDT) → Rest C F S W ds)
    (putBack : List Fmt.RoundView) (l : List (Block S Cl)) (b : Block S Cl) (i base : ℕ) (ds : List RDT),
    ((cutRow rest putBack i base ds b l).1 :: (cutRow rest putBack i base ds b l).2).map (·.b) =
      b :: l

/-- Their data in a row are the data that were cut. -/
def CutData : Prop :=
  ∀ (C : CK) (F : Frame) (S Cl W : Type) (rest : (i : ℕ) → (ds : List RDT) → Rest C F S W ds)
    (putBack : List Fmt.RoundView) (l : List (Block S Cl)) (b : Block S Cl) (i base : ℕ) (ds : List RDT),
    rowData (cutRow rest putBack i base ds b l).1 (cutRow rest putBack i base ds b l).2 = ds

/-- The last piece has `putBack` put back. -/
def CutBack : Prop :=
  ∀ (C : CK) (F : Frame) (S Cl W : Type) (rest : (i : ℕ) → (ds : List RDT) → Rest C F S W ds)
    (putBack : List Fmt.RoundView) (l : List (Block S Cl)) (b : Block S Cl) (i base : ℕ) (ds : List RDT),
    rowBack (cutRow rest putBack i base ds b l).1 (cutRow rest putBack i base ds b l).2 = putBack

/-- The first piece's first tree has the number given. -/
def CutBase : Prop :=
  ∀ (C : CK) (F : Frame) (S Cl W : Type) (rest : (i : ℕ) → (ds : List RDT) → Rest C F S W ds)
    (putBack : List Fmt.RoundView) (l : List (Block S Cl)) (b : Block S Cl) (i base : ℕ) (ds : List RDT),
    (cutRow rest putBack i base ds b l).1.base = base

/-- **Under `ChainFit` the maker's pieces tile the chain.** -/
def TiledOfFit : Prop :=
  ∀ (C : CK) (F : Frame) (S Cl W : Type) (rest : (i : ℕ) → (ds : List RDT) → Rest C F S W ds)
    (putBack : List Fmt.RoundView) (dep : ℕ → Option ℕ) (l : List (Block S Cl)) (b : Block S Cl)
    (i base : ℕ) (ds : List RDT),
    ChainFit F dep base b l ds putBack →
    Tiled (cutRow rest putBack i base ds b l).1 (cutRow rest putBack i base ds b l).2

/-! ## 4 At the data of a file -/

/-- Declared rounds as written rounds, round by round. e: the earlier chains' roots and run values.
-/
def WrittenAs (e : List (List ByteArray × ByteArray)) (l : List Fmt.DeclaredRound) (R : Rounds) :
    Prop :=
  List.Forall₂ (fun r x => r.round e = some x.1 ∧ x.2 = r.stored) l R

/-- The data of three lists of written rounds, by the library's `WholeD.of` and `wholeAt`. -/
abbrev dataOf (a : ℕ) (R₁ R₂ R₃ : Rounds) : WholeD := WholeD.of a (wholeAt (some (R₁, R₂, R₃)))

/-- **Where the makers' tests say yes, `ChainFit` holds at the three chains**, for any blocks whose
declared rounds in a row are the three lists; r: the sealing round that is put back. -/
def FitOfOk : Prop :=
  ∀ (a : ℕ) (R₁ R₂ R₃ : Rounds) (e₁ e₂ e₃ : List (List ByteArray × ByteArray))
    (d₁ d₂ d₃ : List Fmt.DeclaredRound),
    WrittenAs e₁ d₁ R₁ → WrittenAs e₂ d₂ R₂ → WrittenAs e₃ d₃ R₃ →
    okAt a (some (R₁, R₂, R₃)) = true →
    ∀ (S₁ S₂ S₃ Cl : Type) (b₁ : Block S₁ Cl) (l₁ : List (Block S₁ Cl)) (b₂ : Block S₂ Cl)
      (l₂ : List (Block S₂ Cl)) (b₃ : Block S₃ Cl) (l₃ : List (Block S₃ Cl)) (r : Fmt.RoundView)
      (k₁ k₂ k₃ : ℕ → ℕ) (ft₁ ft₂ ft₃ : ℕ),
      (b₁ :: l₁).flatMap (·.rounds) = d₁ → (b₂ :: l₂).flatMap (·.rounds) = d₂ →
      (b₃ :: l₃).flatMap (·.rounds) = d₃ → 1 ≤ lastRounds b₁ l₁ →
      ChainFit (frameAt (dataOf a R₁ R₂ R₃) (allOf (dataOf a R₁ R₂ R₃)) k₁ ft₁)
          (dataOf a R₁ R₂ R₃).depth 0 b₁ l₁ (dataOf a R₁ R₂ R₃).ds₁ [r] ∧
        ChainFit (frameAt (dataOf a R₁ R₂ R₃) (allOf (dataOf a R₁ R₂ R₃)) k₂ ft₂)
          (dataOf a R₁ R₂ R₃).depth (dataOf a R₁ R₂ R₃).t₁ b₂ l₂ (dataOf a R₁ R₂ R₃).ds₂ [] ∧
        ChainFit (frameAt (dataOf a R₁ R₂ R₃) (allOf (dataOf a R₁ R₂ R₃)) k₃ ft₃)
          (dataOf a R₁ R₂ R₃).depth ((dataOf a R₁ R₂ R₃).t₁ + (dataOf a R₁ R₂ R₃).t₂) b₃ l₃
          (dataOf a R₁ R₂ R₃).ds₃ []

/-- **What the comparison of the three stages with the whole file asks**, at the list of all trees
behind the first and behind the second chain. -/
def RowFitOfOk : Prop :=
  ∀ (a : ℕ) (R₁ R₂ R₃ : Rounds), okAt a (some (R₁, R₂, R₃)) = true →
    RowFit (dataOf a R₁ R₂ R₃) (allOf (dataOf a R₁ R₂ R₃)) (allOf (dataOf a R₁ R₂ R₃))

variable {D : WholeD} {all : List LeftT} {Y S₁ S₂ S₃ X₁ X₂ : Type}

/-- The three rows of pieces of T are the maker's: at these blocks, these families of extractors and
errors, and the sealing round r put back behind the first chain. -/
structure Three.IsCut (T : Three C D all Y S₁ S₂ S₃ X₁ X₂ Cl W)
    (b₁ : Block S₁ Cl) (l₁ : List (Block S₁ Cl)) (b₂ : Block S₂ Cl) (l₂ : List (Block S₂ Cl))
    (b₃ : Block S₃ Cl) (l₃ : List (Block S₃ Cl))
    (rest₁ : (i : ℕ) → (ds : List RDT) → Rest C (frameAt D all D.key₁ T.ft₁) S₁ W ds)
    (rest₂ : (i : ℕ) → (ds : List RDT) → Rest C (frameAt D all D.key₂ T.ft₂) S₂ W ds)
    (rest₃ : (i : ℕ) → (ds : List RDT) → Rest C (frameAt D all D.key₃ T.ft₃) S₃ W ds)
    (r : Fmt.RoundView) : Prop where
  c₁ : (T.p₁, T.l₁) = cutRow rest₁ [r] 0 0 D.ds₁ b₁ l₁
  c₂ : (T.p₂, T.l₂) = cutRow rest₂ [] 0 D.t₁ D.ds₂ b₂ l₂
  c₃ : (T.p₃, T.l₃) = cutRow rest₃ [] 0 (D.t₁ + D.t₂) D.ds₃ b₃ l₃

/-- **The three rows of pieces are the file's three chains**: `Three.Fits`, at every `Three` over
the data made of R and the list of all trees whose pieces are the maker's. -/
def FitsOfOk : Prop :=
  ∀ (a : ℕ) (R₁ R₂ R₃ : Rounds) (e₁ e₂ e₃ : List (List ByteArray × ByteArray))
    (d₁ d₂ d₃ : List Fmt.DeclaredRound),
    WrittenAs e₁ d₁ R₁ → WrittenAs e₂ d₂ R₂ → WrittenAs e₃ d₃ R₃ →
    okAt a (some (R₁, R₂, R₃)) = true →
    ∀ (C : CK) (Y S₁ S₂ S₃ X₁ X₂ Cl W : Type)
      (T : Three C (dataOf a R₁ R₂ R₃) (allOf (dataOf a R₁ R₂ R₃)) Y S₁ S₂ S₃ X₁ X₂ Cl W)
      (b₁ : Block S₁ Cl) (l₁ : List (Block S₁ Cl)) (b₂ : Block S₂ Cl) (l₂ : List (Block S₂ Cl))
      (b₃ : Block S₃ Cl) (l₃ : List (Block S₃ Cl)) rest₁ rest₂ rest₃ (r : Fmt.RoundView),
      (b₁ :: l₁).flatMap (·.rounds) = d₁ → (b₂ :: l₂).flatMap (·.rounds) = d₂ →
      (b₃ :: l₃).flatMap (·.rounds) = d₃ → 1 ≤ lastRounds b₁ l₁ →
      T.IsCut b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ r → T.Fits


end VerifiableInference.Desc.Sound
