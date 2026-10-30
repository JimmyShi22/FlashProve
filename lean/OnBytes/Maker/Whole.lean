-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/Whole.lean: from the rounds' data of the three chains of a file, and a run on their
three views, to one interactive oracle reduction to the trivial statement, over the shape of a file
with three joined chains (Compile/Joined/Types.lean, `Chains`). Definitions alone.

A key file and a proof file each hold three chains. Here they are one protocol:
  the front round | chain 1 | the joining round | chain 2 | the seam | chain 3.
The front round, the joining round and the seam send a plain part alone and have one verifier
message (`plainRound`). The verifier reads
  (a) one stored table, a string of length 2 ^ a over `SgX` (Run/PlanQX.lean): the implicit
      instance;
  (b) the trees of the three chains: the prover's oracles. A round may send several
      (OnBytes/Maker/Trees.lean): here they are ONE oracle of that round, whose positions say which
      tree; that they are several trees with a root each is the wire record's matter
      (OnBytes/Maker/Wire.lean). A tree may be read at several rounds, and a later chain may read a
      tree of an earlier one.

A tree is named by one number over the whole file: the trees of the first chain in the order of
sending, then the second's, then the third's.

What the file contains.
  `WholeD`: the data. `ds₁` is the first chain WITHOUT its last round, the seal: in the shape that
    round is the joining round. `key₁`, `key₂`, `key₃`: under which key a tree's columns stand in a
    chain's view, as a function of the tree's number over the whole file.
  `Want`, `wantsOf`: what the drawn positions of a chain ask for, in the file's order: round by
    round, first the stored table's parts, then the trees, position by position (Run/PlanQX.lean,
    `wantedXL`).
  `fullOf`: no part of a round's draws is shortened in silence (Run/PlanQX.lean, `everyOpeningHasItsDraws`).
  `chainsOf`: the rounds of the file. `decApp`, `decWhole`: equality of its positions is decidable.
  `extPosOf`, `ownPosOf`: a want as a position of the stored table, or of the prover's oracles.
  `colOf`, `carriesOf`, `viewOf`: the column at a want; every symbol read of the stored table
    carries the position at which it was read (Run/PlanQX.lean, `symbolsCarryTheirPositions`); a chain's view.
  `reductionOfWholeFile`: the reduction. `annOf`: the annotation of its shape (`Chains.ann`).

To be minded by whoever lays `run`. The first view has one round fewer than the program's block of
the first chain closes: the seal is the joining round, which has one verifier message, so no digest
is drawn there. `run` must put that round back before it hands the view to the block. What the three
silent rounds send is handed to `silent`, with the instance, and not to `run`: whatever of it must
agree with the instance (a record's answers) is to be tested there.

The proofs of work stand inside the shape, whatever the kit `C` is (Trees.lean, `roundT`), and the
verifier tests them: no work is to be laid on this reduction afterwards.

Owed by the caller. `D` is a free letter: nothing here says that it comes from a dry run of any
block, or that it passes any test. By type a chain may open a tree that a later chain sends.
OnBytes/Maker/Files.lean lays `D` from the program's own blocks, under tests that fail closed.

What is not claimed. No law is stated here. That the data are those of a file's chains. A want that
names no position gives no column, and the view is then shorter than the run on it expects. The
field `tie` is the empty set and the field `blinded` is constant; nothing is said here of what these
two fields are read for.


-/
import OnBytes.Maker.Trees
import Compile.Joined.Types
import Ior.Ior

set_option autoImplicit false

namespace OnBytes.Maker

open Iop _root_.Run _root_.Run.PQ Compile.Joined

/-- The data of the three chains of a file. -/
structure WholeD where
  /-- the stored table's depth -/
  a : ℕ
  /-- the first chain's rounds without the last, the seal -/
  ds₁ : List RDT
  ds₂ : List RDT
  ds₃ : List RDT
  key₁ : ℕ → ℕ
  key₂ : ℕ → ℕ
  key₃ : ℕ → ℕ

/-- What a drawn position asks for. -/
inductive Want where
  /-- the stored table under the statement's item, at position x -/
  | table (item x : ℕ)
  /-- the tree with the number j over the whole file, at leaf x -/
  | tree (j x : ℕ)

namespace WholeD
variable (D : WholeD)

/-- The numbers of trees that the first and the second chain send. -/
def t₁ : ℕ := (D.ds₁.map (·.trees.length)).sum
def t₂ : ℕ := (D.ds₂.map (·.trees.length)).sum

/-- The depth of the tree with the number j over the whole file. -/
def depth (j : ℕ) : Option ℕ :=
  if j < D.t₁ then (treeShT D.ds₁ j).map (·.a)
  else if j - D.t₁ < D.t₂ then (treeShT D.ds₂ (j - D.t₁)).map (·.a)
  else (treeShT D.ds₃ (j - D.t₁ - D.t₂)).map (·.a)

end WholeD

/-- What the drawn positions of a chain ask for. a: the stored table's depth. dep: the trees'
depths. -/
def wantsOf (a : ℕ) (dep : ℕ → Option ℕ) : List RDT → List Fmt.Drawn → List Want
  | d :: ds, R :: Rs =>
    (d.stored.flatMap fun s =>
      (Fmt.listOf ((Fmt.partOf s R.poss).map (· % 2 ^ a))).map fun x => Want.table s.item x) ++
    (d.opens.flatMap fun j =>
      match dep j with
      | none => []
      | some b => (Fmt.listOf (R.poss.map (· % 2 ^ b))).map fun x => Want.tree j x) ++
    wantsOf a dep ds Rs
  | _, _ => []

/-- Every stored table's part of a round's draws has as many draws as it says. -/
def fullOf : List RDT → List Fmt.Drawn → Bool
  | d :: ds, R :: Rs =>
    (d.stored.all fun s => (Fmt.partOf s R.poss).length == s.count) && fullOf ds Rs
  | _, _ => true

/-- Equality of positions of two shapes laid behind each other. -/
def decApp (s t : Shape) [DecidableEq (OPos s)] [DecidableEq (OPos t)] :
    DecidableEq (OPos (s ++ t)) :=
  fun p q => decidable_of_iff (OPos.split (s := s) p = OPos.split (s := s) q)
    ⟨fun h => by rw [← OPos.elim_split (s := s) p, h, OPos.elim_split], fun h => congrArg _ h⟩

section
variable (C : CK) (D : WholeD) {TF TJ T3 : Type} (tF : TF) (tJ : TJ) (t3 : T3)

/-- **The rounds of the file.** TF, TJ, T3: what the front round, the joining round and the seam
send; tF, tJ, t3: the fixed message that each of these rounds has to name. The joining round is
shared. -/
@[reducible] def chainsOf : Chains :=
  ⟨plainRound TF tF, uLT C D.ds₁, plainRound TJ tJ, uLT C D.ds₂, plainRound T3 t3, uLT C D.ds₃,
    RAnn.ofShared .sh _⟩

instance decWhole : DecidableEq (OPos (chainsOf C D tF tJ t3).sh) :=
  haveI : DecidableEq (OPos (plainRound T3 t3 :: uLT C D.ds₃)) :=
    inferInstanceAs (DecidableEq (Empty ⊕ OPos (uLT C D.ds₃)))
  haveI : DecidableEq (OPos (uLT C D.ds₂ ++ plainRound T3 t3 :: uLT C D.ds₃)) := decApp _ _
  haveI : DecidableEq
      (OPos (plainRound TJ tJ :: (uLT C D.ds₂ ++ plainRound T3 t3 :: uLT C D.ds₃))) :=
    inferInstanceAs (DecidableEq (Empty ⊕ OPos (uLT C D.ds₂ ++ plainRound T3 t3 :: uLT C D.ds₃)))
  haveI : DecidableEq (OPos (uLT C D.ds₁ ++
      plainRound TJ tJ :: (uLT C D.ds₂ ++ plainRound T3 t3 :: uLT C D.ds₃))) := decApp _ _
  inferInstanceAs (DecidableEq (Empty ⊕ OPos (uLT C D.ds₁ ++
    plainRound TJ tJ :: (uLT C D.ds₂ ++ plainRound T3 t3 :: uLT C D.ds₃))))

/-- A want as a position of the stored table. -/
def extPosOf : Want → Option (oneExternalString (2 ^ D.a) SgX).Pos
  | .table _ x => if h : x < 2 ^ D.a then some ⟨x, h⟩ else none
  | .tree _ _ => none

/-- A want as a position of the prover's oracles. -/
def ownPosOf : Want → Option (OPos (chainsOf C D tF tJ t3).sh)
  | .table _ _ => none
  | .tree j x =>
    if j < D.t₁ then (posAtST C D.ds₁ j x).map (chainsOf C D tF tJ t3).i₁
    else if j - D.t₁ < D.t₂ then (posAtST C D.ds₂ (j - D.t₁) x).map (chainsOf C D tF tJ t3).i₂
    else (posAtST C D.ds₃ (j - D.t₁ - D.t₂) x).map (chainsOf C D tF tJ t3).i₃

/-- The wants of the three chains, from the verifier's messages. -/
def wants₁ (ρ : Rho (chainsOf C D tF tJ t3).sh) : List Want :=
  wantsOf D.a D.depth D.ds₁ (drawnT C D.ds₁ ((chainsOf C D tF tJ t3).rho₁ ρ))

def wants₂ (ρ : Rho (chainsOf C D tF tJ t3).sh) : List Want :=
  wantsOf D.a D.depth D.ds₂ (drawnT C D.ds₂ ((chainsOf C D tF tJ t3).rho₂ ρ))

def wants₃ (ρ : Rho (chainsOf C D tF tJ t3).sh) : List Want :=
  wantsOf D.a D.depth D.ds₃ (drawnT C D.ds₃ ((chainsOf C D tF tJ t3).rho₃ ρ))

/-- The column at a want. τ₁, τ₂, τ₃: the three chains' parts of a transcript. -/
def colOf (y : (oneExternalString (2 ^ D.a) SgX).Str) (τ₁ : Iop.Tr (uLT C D.ds₁)) (τ₂ : Iop.Tr (uLT C D.ds₂))
    (τ₃ : Iop.Tr (uLT C D.ds₃)) : Want → Option (List UInt64)
  | .table _ x => if h : x < 2 ^ D.a then some (y ⟨x, h⟩).2 else none
  | .tree j x =>
    if j < D.t₁ then colAtST C D.ds₁ τ₁ j x
    else if j - D.t₁ < D.t₂ then colAtST C D.ds₂ τ₂ (j - D.t₁) x
    else colAtST C D.ds₃ τ₃ (j - D.t₁ - D.t₂) x

/-- Every symbol read of the stored table carries the position at which it was read. -/
def carriesOf (y : (oneExternalString (2 ^ D.a) SgX).Str) (ws : List Want) : Bool :=
  ws.all fun w => match w with
    | .table _ x => if h : x < 2 ^ D.a then (y ⟨x, h⟩).1 == x else false
    | .tree _ _ => true

/-- A chain's view. rs: its rounds. key: the trees' keys. ws: its wants. -/
def viewOf (y : (oneExternalString (2 ^ D.a) SgX).Str) (τ₁ : Iop.Tr (uLT C D.ds₁)) (τ₂ : Iop.Tr (uLT C D.ds₂))
    (τ₃ : Iop.Tr (uLT C D.ds₃)) (rs : List RV) (key : ℕ → ℕ) (ws : List Want) : View where
  rounds := rs
  opened := ws.filterMap fun w => (colOf C D y τ₁ τ₂ τ₃ w).map fun c =>
    match w with
    | .table item x => (Fmt.storedKey item, x, c)
    | .tree j x => (key j, x, c)

/-- **The reduction of a whole file.** silent: a test of what the front round, the joining round and
the seam send, against the explicit instance. run: from the explicit instance and the three views to
the verdict. -/
@[reducible] def reductionOfWholeFile {Xi : Type} (silent : Xi → TF → TJ → T3 → Bool)
    (run : Xi → View → View → View → Bool) :
    IOR Xi (oneExternalString (2 ^ D.a) SgX) Unit extNone where
  shape := (chainsOf C D tF tJ t3).sh
  blinded := fun _ => true
  extReads := fun ρ =>
    ((wants₁ C D tF tJ t3 ρ ++ (wants₂ C D tF tJ t3 ρ ++ wants₃ C D tF tJ t3 ρ)).filterMap
      (extPosOf D)).toFinset
  reads := fun ρ =>
    ((wants₁ C D tF tJ t3 ρ ++ (wants₂ C D tF tJ t3 ρ ++ wants₃ C D tF tJ t3 ρ)).filterMap
      (ownPosOf C D tF tJ t3)).toFinset
  out := fun x y τ =>
    let τ₁ := (chainsOf C D tF tJ t3).tr₁ τ
    let τ₂ := (chainsOf C D tF tJ t3).tr₂ τ
    let τ₃ := (chainsOf C D tF tJ t3).tr₃ τ
    let R₁ := drawnT C D.ds₁ (rhoT C D.ds₁ τ₁)
    let R₂ := drawnT C D.ds₂ (rhoT C D.ds₂ τ₂)
    let R₃ := drawnT C D.ds₃ (rhoT C D.ds₃ τ₃)
    let w₁ := wantsOf D.a D.depth D.ds₁ R₁
    let w₂ := wantsOf D.a D.depth D.ds₂ R₂
    let w₃ := wantsOf D.a D.depth D.ds₃ R₃
    if passT C D.ds₁ (rhoT C D.ds₁ τ₁) && passT C D.ds₂ (rhoT C D.ds₂ τ₂) &&
        passT C D.ds₃ (rhoT C D.ds₃ τ₃) &&
        fullOf D.ds₁ R₁ && fullOf D.ds₂ R₂ && fullOf D.ds₃ R₃ && carriesOf D y (w₁ ++ (w₂ ++ w₃)) &&
        silent x ((chainsOf C D tF tJ t3).msgF τ).2 ((chainsOf C D tF tJ t3).msgJ τ).2
          ((chainsOf C D tF tJ t3).msg3 τ).2 &&
        run x (viewOf C D y τ₁ τ₂ τ₃ (rvT C D.ds₁ τ₁) D.key₁ w₁)
          (viewOf C D y τ₁ τ₂ τ₃ (rvT C D.ds₂ τ₂) D.key₂ w₂)
          (viewOf C D y τ₁ τ₂ τ₃ (rvT C D.ds₃ τ₃) D.key₃ w₃) then some () else none
  imp := fun _ _ => ()
  srcE := fun _ _ => ∅
  srcO := fun _ _ => ∅
  tie := fun _ _ => ∅

/-- The annotation of the reduction's shape: the front and chain 1 local, the joining round and
chain 2 shared, the seam and chain 3 local. -/
def annOf {Xi : Type} (silent : Xi → TF → TJ → T3 → Bool) (run : Xi → View → View → View → Bool) :
    RoundSplits (reductionOfWholeFile C D tF tJ t3 silent run).shape :=
  (chainsOf C D tF tJ t3).ann

end

end OnBytes.Maker
