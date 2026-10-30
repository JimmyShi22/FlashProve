-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/CoverageLotsNamed.lean: the kind "lookup" (K3): each of this
folder's 25 lots that are made of `rowLotAt` or `rowLotKeepAt` at named letters has, at every public
part, the halves of `rowLot` or `rowLotKeep` at its letters at that public part; these are a `lotBy`
(Honest/K3/Lot.lean). 26 theorems, each by unfolding; no definition.

Why. The laws of Honest/K3/Law/Coverage.lean and Honest/K3/Law/Thread/CoverageAtHead.lean speak of
`lotBy` at every row. `every_look_has_half_of` carries them to a lot of which such an equation is
had.

What is shown, at every public part Z and every G.
  `rowLotAt_halves`: the halves of `rowLotAt` (Honest/K3/LotFilled.lean) are those of a `lotBy`
    whose row is made at Z.
  For each lot L of the 25: `L_halves`: its halves are those of `rowLot` or `rowLotKeep` at L's
    letters at Z, which are a `lotBy` by `rowLot_is` (Coverage.lean) and `rowLotKeep_is`
    (Honest/K3/Law/CoverageLots.lean [not in this library]).

Which lots. Two programs, written apart within this project, each cutting a definition's head at the
first ":=" outside brackets, listed every definition in a tree of this project (not this library)
whose stated type is `HLot`, test files with bent text left out: 45, one list. Treated: `lotBy`
itself; `lotBySeat`, `rowLot`, `lookLot`, `lookLotFast` (Coverage.lean); `rowLotKeep`,
`rowLotKeepAt` (CoverageLots.lean [not in this library]); `rowLotAt` and the 25 here. Left out,
because they drop halves: `fitHalves` and the four lots made by it (`theLotFit`, `theLotSpecFit`,
`theLotInstFit`, `theLotInstSpecFit`): they give a half only where tests accept. Left out, as
made-up data of tests: `bentLot`, `lotK`, `lotKz`, `lotE`, `lotF`, `lotS`: each is one of the
treated lots, or `rowLotKeep`, at made-up letters; and `lotZ`, which is `theLotFit` at made-up
letters and drops halves.

Limits. None of these lots is a `lotBy` as a term: their letters read the public part. The list is a
program's, by the stated type: a lot that is stated under another type's name would be missed. All
these lots bear one lot's name; they are meant in one another's place, not two in one list: a
caution of their own files; nothing here shows or tests it.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.LotFilled
import Johnson.Desc.ProofFile.Honest.K3.RowKeepHot
import Johnson.Desc.ProofFile.Honest.K3.LotInstKeep
import Johnson.Desc.ProofFile.Honest.K3.LotInst
import Johnson.Desc.ProofFile.Honest.K3.Tab.TabAll2
import Johnson.Desc.ProofFile.Honest.K3.Tab.HotTabAll2
import Johnson.Desc.ProofFile.Honest.K3.Tab.TabAll
import Johnson.Desc.ProofFile.Honest.K3.LotInstKeepCode
import Johnson.Desc.ProofFile.Honest.K3.WitTab
import Johnson.Desc.ProofFile.Honest.K3.Tab.LotTabG
import Johnson.Desc.ProofFile.Honest.K3.LotInstFast
import Johnson.Desc.ProofFile.Honest.K3.WitNamed
import Johnson.Desc.ProofFile.Honest.K3.LotInstKeepBound

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law
open OnBytes (E)
open ProofFile.Honest.K3.TabG (theLotKeepTabG theLotInstKeepTabG tabWitG)

variable {V W X W₀ Rc Xi Tr : Type}

/-- The halves of `rowLotAt` at Z are those of a `lotBy` whose row is made at Z. -/
theorem rowLotAt_halves (A : Pub → Fill W) (Z : Pub) (G : Ground) :
    (rowLotAt A : HLot V W X).halves Z G =
      (lotBy fun s => (proverSideOfLookupInChainAtOneOwner theReads ((A Z).jobs s).asked ((A Z).wit s) s.at_).parts).halves Z
        G :=
  rfl

/-- The halves of `theLot` at Z are those of `rowLot` at its letters at Z. -/
theorem theLot_halves (cells : Tr → Cells) (weights : W₀ → Weights)
    (req : Xi → OnBytes.Model.Head.Covered × Array Nat) (Z : Pub) (G : Ground) :
    (theLot cells weights req : HLot (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X).halves Z G =
      (rowLot (fastFill (sourcesAt cells weights req Z))).halves Z G :=
  rfl

/-- The halves of `theLotSpec` at Z are those of `rowLot` at its letters at Z. -/
theorem theLotSpec_halves (cells : Tr → Cells) (weights : W₀ → Weights)
    (req : Xi → OnBytes.Model.Head.Covered × Array Nat) (Z : Pub) (G : Ground) :
    (theLotSpec cells weights req : HLot (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X).halves Z G =
      (rowLot (specFill (sourcesAt cells weights req Z))).halves Z G :=
  rfl

/-- The halves of `theLotKeepHot` at Z are those of `rowLotKeep` at its letters at Z. -/
theorem theLotKeepHot_halves (cells : Tr → Cells) (weights : W₀ → Weights)
    (req : Xi → OnBytes.Model.Head.Covered × Array Nat) (get : X → RowOwn) (set : X → RowOwn → X)
    (Z : Pub) (G : Ground) :
    (theLotKeepHot cells weights req get set :
      HLot (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X).halves Z G =
      (rowLotKeep (hotFillKeep (codeRows Z) (boundWit cells weights req Z)) get set).halves Z G :=
  rfl

/-- The halves of `theLotInstKeepHot` at Z are those of `rowLotKeep` at its letters at Z. -/
theorem theLotInstKeepHot_halves (cells : Tr → Cells) (weights : W₀ → Weights) (get : X → RowOwn)
    (set : X → RowOwn → X) (Z : Pub) (G : Ground) :
    (theLotInstKeepHot cells weights get set :
      HLot (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X).halves Z G =
      (rowLotKeep (hotFillKeep (codeRows Z) (boundWit cells weights (reqAt Z) Z)) get
        set).halves Z G :=
  rfl

/-- The halves of `theLotKeep` at Z are those of `rowLotKeep` at its letters at Z. -/
theorem theLotKeep_halves_rowLotKeep (row : Pub → Site → E → Nat → E) (cells : Tr → Cells)
    (weights : W₀ → Weights) (req : Xi → OnBytes.Model.Head.Covered × Array Nat) (get : X → RowOwn)
    (set : X → RowOwn → X) (Z : Pub) (G : Ground) :
    (theLotKeep row cells weights req get set :
      HLot (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X).halves Z G =
      (rowLotKeep (fastFillKeep (row Z) (fastWit cells weights req Z)) get set).halves Z G :=
  rfl

/-- The halves of `theLotInstKeep` at Z are those of `rowLotKeep` at its letters at Z. -/
theorem theLotInstKeep_halves (row : Pub → Site → E → Nat → E) (cells : Tr → Cells)
    (weights : W₀ → Weights) (get : X → RowOwn) (set : X → RowOwn → X) (Z : Pub) (G : Ground) :
    (theLotInstKeep row cells weights get set :
      HLot (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X).halves Z G =
      (rowLotKeep (fastFillKeep (row Z) (fastWit cells weights (reqAt Z) Z)) get set).halves Z G :=
  rfl

/-- The halves of `theLotInst` at Z are those of `rowLot` at its letters at Z. -/
theorem theLotInst_halves (cells : Tr → Cells) (weights : W₀ → Weights) (Z : Pub) (G : Ground) :
    (theLotInst cells weights : HLot (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X).halves Z G =
      (rowLot (fastFill (sourcesAt cells weights (reqAt Z) Z))).halves Z G :=
  rfl

/-- The halves of `theLotInstSpec` at Z are those of `rowLot` at its letters at Z. -/
theorem theLotInstSpec_halves (cells : Tr → Cells) (weights : W₀ → Weights) (Z : Pub) (G : Ground) :
    (theLotInstSpec cells weights : HLot (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X).halves Z G =
      (rowLot (specFill (sourcesAt cells weights (reqAt Z) Z))).halves Z G :=
  rfl

/-- The halves of `theLotKeepTabAll2` at Z are those of `rowLotKeep` at its letters at Z. -/
theorem theLotKeepTabAll2_halves (cells : Tr → Cells) (weights : W₀ → Weights)
    (req : Xi → OnBytes.Model.Head.Covered × Array Nat) (get : X → RowOwn) (set : X → RowOwn → X)
    (Z : Pub) (G : Ground) :
    (theLotKeepTabAll2 cells weights req get set :
      HLot (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X).halves Z G =
      (rowLotKeep (fastFillKeep (codeRows Z) (tabWitAll2 cells weights req Z)) get
        set).halves Z G :=
  rfl

/-- The halves of `theLotInstKeepTabAll2` at Z are those of `rowLotKeep` at its letters at Z. -/
theorem theLotInstKeepTabAll2_halves (cells : Tr → Cells) (weights : W₀ → Weights)
    (get : X → RowOwn) (set : X → RowOwn → X) (Z : Pub) (G : Ground) :
    (theLotInstKeepTabAll2 cells weights get set :
      HLot (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X).halves Z G =
      (rowLotKeep (fastFillKeep (codeRows Z) (tabWitAll2 cells weights (reqAt Z) Z)) get
        set).halves Z G :=
  rfl

/-- The halves of `theLotKeepHotTabAll2` at Z are those of `rowLotKeep` at its letters at Z. -/
theorem theLotKeepHotTabAll2_halves (cells : Tr → Cells) (weights : W₀ → Weights)
    (req : Xi → OnBytes.Model.Head.Covered × Array Nat) (get : X → RowOwn) (set : X → RowOwn → X)
    (Z : Pub) (G : Ground) :
    (theLotKeepHotTabAll2 cells weights req get set :
      HLot (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X).halves Z G =
      (rowLotKeep (hotFillKeep (codeRows Z) (tabWitAll2 cells weights req Z)) get set).halves Z G :=
  rfl

/-- The halves of `theLotInstKeepHotTabAll2` at Z are those of `rowLotKeep` at its letters at Z. -/
theorem theLotInstKeepHotTabAll2_halves (cells : Tr → Cells) (weights : W₀ → Weights)
    (get : X → RowOwn) (set : X → RowOwn → X) (Z : Pub) (G : Ground) :
    (theLotInstKeepHotTabAll2 cells weights get set :
      HLot (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X).halves Z G =
      (rowLotKeep (hotFillKeep (codeRows Z) (tabWitAll2 cells weights (reqAt Z) Z)) get
        set).halves Z G :=
  rfl

/-- The halves of `theLotKeepTabAll` at Z are those of `rowLotKeep` at its letters at Z. -/
theorem theLotKeepTabAll_halves (cells : Tr → Cells) (weights : W₀ → Weights)
    (req : Xi → OnBytes.Model.Head.Covered × Array Nat) (get : X → RowOwn) (set : X → RowOwn → X)
    (Z : Pub) (G : Ground) :
    (theLotKeepTabAll cells weights req get set :
      HLot (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X).halves Z G =
      (rowLotKeep (fastFillKeep (codeRows Z) (tabWitAll cells weights req Z)) get set).halves Z G :=
  rfl

/-- The halves of `theLotInstKeepTabAll` at Z are those of `rowLotKeep` at its letters at Z. -/
theorem theLotInstKeepTabAll_halves (cells : Tr → Cells) (weights : W₀ → Weights) (get : X → RowOwn)
    (set : X → RowOwn → X) (Z : Pub) (G : Ground) :
    (theLotInstKeepTabAll cells weights get set :
      HLot (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X).halves Z G =
      (rowLotKeep (fastFillKeep (codeRows Z) (tabWitAll cells weights (reqAt Z) Z)) get
        set).halves Z G :=
  rfl

/-- The halves of `theLotKeepCode` at Z are those of `rowLotKeep` at its letters at Z. -/
theorem theLotKeepCode_halves (cells : Tr → Cells) (weights : W₀ → Weights)
    (req : Xi → OnBytes.Model.Head.Covered × Array Nat) (get : X → RowOwn) (set : X → RowOwn → X)
    (Z : Pub) (G : Ground) :
    (theLotKeepCode cells weights req get set :
      HLot (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X).halves Z G =
      (rowLotKeep (fastFillKeep (codeRows Z) (fastWit cells weights req Z)) get set).halves Z G :=
  rfl

/-- The halves of `theLotInstKeepCode` at Z are those of `rowLotKeep` at its letters at Z. -/
theorem theLotInstKeepCode_halves (cells : Tr → Cells) (weights : W₀ → Weights) (get : X → RowOwn)
    (set : X → RowOwn → X) (Z : Pub) (G : Ground) :
    (theLotInstKeepCode cells weights get set :
      HLot (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X).halves Z G =
      (rowLotKeep (fastFillKeep (codeRows Z) (fastWit cells weights (reqAt Z) Z)) get
        set).halves Z G :=
  rfl

/-- The halves of `theLotKeepTab` at Z are those of `rowLotKeep` at its letters at Z. -/
theorem theLotKeepTab_halves (cells : Tr → Cells) (weights : W₀ → Weights)
    (req : Xi → OnBytes.Model.Head.Covered × Array Nat) (get : X → RowOwn) (set : X → RowOwn → X)
    (Z : Pub) (G : Ground) :
    (theLotKeepTab cells weights req get set :
      HLot (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X).halves Z G =
      (rowLotKeep (fastFillKeep (codeRows Z) (tabWit cells weights req Z)) get set).halves Z G :=
  rfl

/-- The halves of `theLotInstKeepTab` at Z are those of `rowLotKeep` at its letters at Z. -/
theorem theLotInstKeepTab_halves (cells : Tr → Cells) (weights : W₀ → Weights) (get : X → RowOwn)
    (set : X → RowOwn → X) (Z : Pub) (G : Ground) :
    (theLotInstKeepTab cells weights get set :
      HLot (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X).halves Z G =
      (rowLotKeep (fastFillKeep (codeRows Z) (tabWit cells weights (reqAt Z) Z)) get
        set).halves Z G :=
  rfl

/-- The halves of `theLotKeepTabG` at Z are those of `rowLotKeep` at its letters at Z. -/
theorem theLotKeepTabG_halves (cells : Tr → Cells) (weights : W₀ → Weights)
    (req : Xi → OnBytes.Model.Head.Covered × Array Nat) (get : X → RowOwn) (set : X → RowOwn → X)
    (Z : Pub) (G : Ground) :
    (theLotKeepTabG cells weights req get set :
      HLot (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X).halves Z G =
      (rowLotKeep (fastFillKeep (codeRows Z) (tabWitG cells weights req Z)) get set).halves Z G :=
  rfl

/-- The halves of `theLotInstKeepTabG` at Z are those of `rowLotKeep` at its letters at Z. -/
theorem theLotInstKeepTabG_halves (cells : Tr → Cells) (weights : W₀ → Weights) (get : X → RowOwn)
    (set : X → RowOwn → X) (Z : Pub) (G : Ground) :
    (theLotInstKeepTabG cells weights get set :
      HLot (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X).halves Z G =
      (rowLotKeep (fastFillKeep (codeRows Z) (tabWitG cells weights (reqAt Z) Z)) get
        set).halves Z G :=
  rfl

/-- The halves of `theLotFast` at Z are those of `rowLot` at its letters at Z. -/
theorem theLotFast_halves (cells : Tr → Cells) (weights : W₀ → Weights)
    (req : Xi → OnBytes.Model.Head.Covered × Array Nat) (Z : Pub) (G : Ground) :
    (theLotFast cells weights req : HLot (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X).halves Z G =
      (rowLot (fastFillAsk cells weights req Z)).halves Z G :=
  rfl

/-- The halves of `theLotInstFast` at Z are those of `rowLot` at its letters at Z. -/
theorem theLotInstFast_halves (cells : Tr → Cells) (weights : W₀ → Weights) (Z : Pub) (G : Ground) :
    (theLotInstFast cells weights : HLot (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X).halves Z G =
      (rowLot (fastFillAsk cells weights (reqAt Z) Z)).halves Z G :=
  rfl

/-- The halves of `theLotKeepRun` at Z are those of `rowLotKeep` at its letters at Z. -/
theorem theLotKeepRun_halves (runAsk : Site → Ask) (get : X → RowOwn) (set : X → RowOwn → X)
    (Z : Pub) (G : Ground) :
    (theLotKeepRun runAsk get set : HLot V W X).halves Z G =
      (rowLotKeep (fastFillKeep (codeRows Z) fun s _ => runAsk s) get set).halves Z G :=
  rfl

/-- The halves of `theLotKeepBound` at Z are those of `rowLotKeep` at its letters at Z. -/
theorem theLotKeepBound_halves (cells : Tr → Cells) (weights : W₀ → Weights)
    (req : Xi → OnBytes.Model.Head.Covered × Array Nat) (get : X → RowOwn) (set : X → RowOwn → X)
    (Z : Pub) (G : Ground) :
    (theLotKeepBound cells weights req get set :
      HLot (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X).halves Z G =
      (rowLotKeep (fastFillKeep (codeRows Z) (boundWit cells weights req Z)) get set).halves Z G :=
  rfl

/-- The halves of `theLotInstKeepBound` at Z are those of `rowLotKeep` at its letters at Z. -/
theorem theLotInstKeepBound_halves (cells : Tr → Cells) (weights : W₀ → Weights) (get : X → RowOwn)
    (set : X → RowOwn → X) (Z : Pub) (G : Ground) :
    (theLotInstKeepBound cells weights get set :
      HLot (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X).halves Z G =
      (rowLotKeep (fastFillKeep (codeRows Z) (boundWit cells weights (reqAt Z) Z)) get
        set).halves Z G :=
  rfl

end ProofFile.Honest.K3.Law

#print axioms ProofFile.Honest.K3.Law.rowLotAt_halves
#print axioms ProofFile.Honest.K3.Law.theLot_halves
#print axioms ProofFile.Honest.K3.Law.theLotSpec_halves
#print axioms ProofFile.Honest.K3.Law.theLotKeepHot_halves
#print axioms ProofFile.Honest.K3.Law.theLotInstKeepHot_halves
#print axioms ProofFile.Honest.K3.Law.theLotKeep_halves_rowLotKeep
#print axioms ProofFile.Honest.K3.Law.theLotInstKeep_halves
#print axioms ProofFile.Honest.K3.Law.theLotInst_halves
#print axioms ProofFile.Honest.K3.Law.theLotInstSpec_halves
#print axioms ProofFile.Honest.K3.Law.theLotKeepTabAll2_halves
#print axioms ProofFile.Honest.K3.Law.theLotInstKeepTabAll2_halves
#print axioms ProofFile.Honest.K3.Law.theLotKeepHotTabAll2_halves
#print axioms ProofFile.Honest.K3.Law.theLotInstKeepHotTabAll2_halves
#print axioms ProofFile.Honest.K3.Law.theLotKeepTabAll_halves
#print axioms ProofFile.Honest.K3.Law.theLotInstKeepTabAll_halves
#print axioms ProofFile.Honest.K3.Law.theLotKeepCode_halves
#print axioms ProofFile.Honest.K3.Law.theLotInstKeepCode_halves
#print axioms ProofFile.Honest.K3.Law.theLotKeepTab_halves
#print axioms ProofFile.Honest.K3.Law.theLotInstKeepTab_halves
#print axioms ProofFile.Honest.K3.Law.theLotKeepTabG_halves
#print axioms ProofFile.Honest.K3.Law.theLotInstKeepTabG_halves
#print axioms ProofFile.Honest.K3.Law.theLotFast_halves
#print axioms ProofFile.Honest.K3.Law.theLotInstFast_halves
#print axioms ProofFile.Honest.K3.Law.theLotKeepRun_halves
#print axioms ProofFile.Honest.K3.Law.theLotKeepBound_halves
#print axioms ProofFile.Honest.K3.Law.theLotInstKeepBound_halves
