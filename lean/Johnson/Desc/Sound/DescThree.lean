-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/DescThree.lean: the rule of composition across a file's three chains
(Johnson/Desc/Sound/FileRule.lean, FileBatch.lean) AT A FILE'S DESCRIPTION (`FileDescription`,
Johnson/Desc/Block.lean): which of its premises are facts about the fold, for every description. A
SHEET OF STATEMENTS: definitions, and propositions written as `def … : Prop`. NOTHING IS PROVED IN
THIS FILE.

The setting. FileRule.lean speaks of a value `Three`: three rows of pieces (a block with its
stretch of the written rounds) and six functions that make the chains' first records and pack what
a chain hands on; `Three.ofStarts` is the filling that is meant. Johnson/Desc/Sound/DescRuns.lean
writes a description's own three runs.

What is said. `OfDesc F T`: the pieces of T hold the description's own three flat lists of blocks
(each block with the test below the prime, lifted to the pair of what was handed to the chain and
the chain's own record), at the numbers that `FileDescription.runEnd` hands its three folds, with the
sealing round put back behind the first chain and nothing behind the others. `atDesc F T`: the
filling that is meant, at the description's own `pub`, `start₁`, `start₂`, `start₃`.
`RunsAtDesc`: its three runs ARE the description's three runs: equations of functions.
`RunGivesRowAt`: so the decision's yes gives the yes of the three runs of which the rule of
composition speaks. `LiftedAtDesc`: three binders of `FileKnowsJOfGood` (the shared chain's blocks
are lifted; the two laws on get and set) hold. `FirstKeyAtDesc`: the first key IS `start₂` of the
instance's public part, with the stored table: so the law on the first key holds JUST WHERE THE
SHARED CHAIN'S FIRST RECORD IS THE SAME AT ALL INSTANCES at which the first chain's reduction puts
out at some transcript.

Limits. (1) GENERAL IN THE DESCRIPTION: no block, plan or size is named; nothing on soundness.
(2) `OfDesc` IS A PREMISE HERE. It asks nothing of a stretch's data, base, extractor or errors: it
is owed, by unfolding, by whoever makes the pieces from a description and the data of its written
rounds; `OfDescHasMembers` says that it can be met at every description whose three lists are not
empty. (3) THE LAW ON THE FIRST KEY IS NOT FREE. That `start₂ (pub x)` is one value at all
instances x FAILS at a type of instances in which the key file's record varies, if the shared
chain's first record holds that record's key. It is meant record by record, as the top theorem asks
the list: OWED: `start₂ (pub (x, rec))` is a function of rec alone. NOTHING IN `FileDescription` FORBIDS A
`start₂` THAT READS THE REQUEST: at such a description that fails too, and the slots of a batch have
no common key. (4) `start₁` is total: where a
description lays a blank record for a request that it cannot read, the first relation is read at
that blank record; only `okStart`, which is not in the row, tells the two apart.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.DescRuns
import Johnson.Desc.Sound.FileBatch

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Flat KObj
open TypedOracleCompiler.Joined (LinkJ Links)
open _root_.Run.PQ (CK SgX)
open _root_.Iop (Reduction Err Shape IOR ExtSpec oneExternalString)

/-- Three rows of pieces at the records of the filling that is meant, for the description F. -/
abbrev ThreeAt (C : CK) (D : WholeD) (all : List LeftT) {Xi : Type} (F : FileDescription Xi)
    (X₁ X₂ W : Type) : Type :=
  Three C D all Xi (F.XiPub × F.S₁) ((F.XiPub × F.S₁) × F.S₂) ((F.XiPub × F.S₁ × F.S₂) × F.S₃) X₁
    X₂ F.Cl W

/-- The conditions and relations at the boundaries, at the same records. -/
abbrev PlacesAt (D : WholeD) (all : List LeftT) {Xi : Type} (F : FileDescription Xi) (W : Type) : Type :=
  Places D all (F.XiPub × F.S₁) ((F.XiPub × F.S₁) × F.S₂) ((F.XiPub × F.S₁ × F.S₂) × F.S₃) W

variable {C : CK} {D : WholeD} {all : List LeftT} {Xi X₁ X₂ W : Type}

/-- **The filling that is meant, at a description**: `Three.ofStarts` at the description's own
four functions; a refusal of `start₃` loses its words. -/
def atDesc (F : FileDescription Xi) (T : ThreeAt C D all F X₁ X₂ W) :
    ThreeAt C D all F (F.XiPub × F.S₁) (F.XiPub × F.S₁ × F.S₂) W :=
  Three.ofStarts F.pub F.start₁ F.start₂ (fun p a b => (F.start₃ p a b).toOption) T

/-- **The pieces hold the description's own blocks.** -/
structure OfDesc (F : FileDescription Xi) (T : ThreeAt C D all F X₁ X₂ W) : Prop where
  ft₁ : T.ft₁ = 0
  ft₂ : T.ft₂ = 0
  ft₃ : T.ft₃ = F.lastChainFirstTreeNumber
  b₁ : (T.p₁ :: T.l₁).map (·.b) =
    (F.first.blocksInOrder.map below).map (Block.lift Prod.snd fun t s => (t.1, s))
  b₂ : (T.p₂ :: T.l₂).map (·.b) =
    (F.shared.blocksInOrder.map below).map (Block.lift Prod.snd fun t s => (t.1, s))
  b₃ : (T.p₃ :: T.l₃).map (·.b) =
    (F.second.blocksInOrder.map below).map (Block.lift Prod.snd fun t s => (t.1, s))
  back₁ : rowBack T.p₁ T.l₁ = [sealRound]
  back₂ : rowBack T.p₂ T.l₂ = []
  back₃ : rowBack T.p₃ T.l₃ = []

/-- **The three runs of the rule of composition are the description's own three runs.** The chains'
names in T are not asked: a run drops a refusal's words. -/
def RunsAtDesc : Prop :=
  ∀ (C : CK) (D : WholeD) (all : List LeftT) (Xi X₁ X₂ W : Type) (F : FileDescription Xi)
    (T : ThreeAt C D all F X₁ X₂ W), OfDesc F T →
    (atDesc F T).run₁ = descRun₁ F ∧ (atDesc F T).run₂ = descRun₂ F ∧
      (atDesc F T).run₃ = descRun₃ F

/-- **The decision's yes gives the yes of the three runs of which the rule of composition speaks.**
-/
def RunGivesRowAt : Prop :=
  ∀ (C : CK) (D : WholeD) (all : List LeftT) (Xi X₁ X₂ W : Type) (F : FileDescription Xi)
    (T : ThreeAt C D all F X₁ X₂ W), OfDesc F T →
    ∀ (x : Xi) (v₁ v₂ v₃ : Fmt.View), F.run x v₁ v₂ v₃ = true →
      runRow (atDesc F T).run₁ (atDesc F T).run₂ (atDesc F T).run₃ x v₁ v₂ v₃ = true

/-- **Three binders of `FileKnowsJOfGood`**, at get := the second part, set := laying it. -/
def LiftedAtDesc : Prop :=
  ∀ (C : CK) (D : WholeD) (all : List LeftT) (Xi X₁ X₂ W : Type) (F : FileDescription Xi)
    (T : ThreeAt C D all F X₁ X₂ W), OfDesc F T →
    (∀ (t : (F.XiPub × F.S₁) × F.S₂) (s : F.S₂), Prod.snd (t.1, s) = s) ∧
    (∀ (t : (F.XiPub × F.S₁) × F.S₂) (s s' : F.S₂), ((t.1, s).1, s') = (t.1, s')) ∧
    ∀ q ∈ (atDesc F T).p₂ :: (atDesc F T).l₂, ∃ b₀ : Block F.S₂ F.Cl,
      q.b = b₀.lift Prod.snd fun t s => (t.1, s)

/-- **What the first key is.** The key of `FileKnowsJOfGood` (the shared chain's own first record,
with the stored table), read at what the first chain's reduction hands on at the instance a.1 and
the stored table a.2, IS (`start₂` of the instance's public part, that stored table). So the law on
the first key (a binder of `FileKnowsJOfGood`: that key is a function of the stored table alone)
holds JUST AS FAR AS `start₂ (pub x)` does not hang on x. -/
def FirstKeyAtDesc : Prop :=
  ∀ (C : CK) (D : WholeD) (all : List LeftT) (Xi X₁ X₂ W TF TJ T3 : Type) (tF : TF) (tJ : TJ)
    (t3 : T3) (F : FileDescription Xi) (T : ThreeAt C D all F X₁ X₂ W) (Q : PlacesAt D all F W)
    (okF : Xi → TF → Bool) (okJ : F.XiPub × F.S₁ → TJ → Bool)
    (ok3 : F.XiPub × F.S₁ × F.S₂ → T3 → Bool)
    (h₁ : (rowIOR (atDesc F T).p₁ (atDesc F T).l₁).shape = uLT C D.ds₁)
    (h₂ : (rowIOR (atDesc F T).p₂ (atDesc F T).l₂).shape = uLT C D.ds₂)
    (h₃ : (rowIOR (atDesc F T).p₃ (atDesc F T).l₃).shape = uLT C D.ds₃),
    OfDesc F T →
    ∀ a τ b, (((atDesc F T).row tF tJ t3 okF okJ ok3).links
      ((atDesc F T).snd tF tJ t3 Q okF okJ ok3 h₁ h₂ h₃)).K₁.out a τ = some b →
      (Prod.snd ((atDesc F T).in₂ b.1), b.2.1) = (F.start₂ (F.pub a.1), a.2)

/-- **`OfDesc` can be met**: at every description whose three flat lists of blocks are not empty
there are three rows of pieces with it. (The stretches of these members hold no written round: they
show that the record of equations is not empty, and nothing else: they need not have `Three.Fits`. A
member of both: Johnson/Desc/Sound/DescToy.lean.) -/
def OfDescHasMembers : Prop :=
  ∀ (C : CK) (D : WholeD) (all : List LeftT) (Xi W : Type) (F : FileDescription Xi) (d : W),
    F.first.blocksInOrder ≠ [] → F.shared.blocksInOrder ≠ [] → F.second.blocksInOrder ≠ [] →
    ∃ T : ThreeAt C D all F (F.XiPub × F.S₁) (F.XiPub × F.S₁ × F.S₂) W, OfDesc F T


end VerifiableInference.Desc.Sound
