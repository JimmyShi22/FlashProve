-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/SharedJointCountRowB.lean: THE ROW `shared_joint_count`, STATED, SECOND FORM: in
the plain form's letters, at the terms of the table of joints at the shared chain as they rest,
WITH THE EXTRACTORS NAMED. Definitions, ONE STATEMENT, one example that it joins upward. NOTHING IS
PROVED IN THIS FILE.

It parts from the first form (SharedJointCountRow.lean, not in this library) in two things. (1) That
form's step ("there is a world" on both sides of a border's whole
relation: TOO WIDE): a kind that brings in nothing new has its law AT ONE WORLD; a place that newly
commits a part of the witness has "a new part, the old part kept", with its extractor NAMED on the
row. (2) The table's terms are `relQ₂ N Mg split p l`, `onQ₂ N Pm Oc
split p l`.

The row, in words. At the written description of the proof file, each block of the shared chain has
the plain law for a batch in two parts, at ITS OWN ERRORS, AND THESE ARE THE PLAN's PRICES OF ITS
ROUNDS: what hangs on the slots' common key is paid once, what hangs on a slot's own statement N
times. What the law leads to: the condition behind the block holds; and FOR EVERY WORLD w: if every
item that is open behind the block holds of w, every item that is open in front of it holds of `ext
k a w`: the same world, but for the components that the table says the block at place k lays.

Whose each term is.
  `EachLawsBN`, `keyAt` (Johnson/Desc/Sound/KeysByMake.lean): for each block `LeadsBN`
    (Johnson/Desc/Plain/Both.lean) at its own errors, at the
    key "the acting part", and the hand-over of the condition. THE LAWS OF KEYS ARE NOT ASKED: they
    come by make.
  `onQ₂`, `relQ₂` (Johnson/Desc/Sound/BordersSharedQ.lean), `laysOfS`, `sharedPlaces`, `Comp`
    (Johnson/Desc/Shared/BordersShared.lean), `EachPriced` (Johnson/Desc/Sound/PricesSharedQ.lean):
    the table of joints at the shared chain.
New here. `laysAt split k`: the components that the block number k lays, by the table: the cells at
1; the folded row's message at 9; the split's mask row's at 10; else none. `ExtNamed`: the named
extractor is the identity where the table lays nothing, and everywhere keeps each component that the
table does not lay there. `stepAt`: what a block's law leads to.

THE STATEMENT IS A FORM WITH LETTERS: IT IS NOT A CLOSED ROW. `SharedJointCountRow` takes as
  arguments: F, T, D, all, C: THE DESCRIPTION, its pieces and data: to be set to the one written
    description at the release's plan, the pieces by make.
    That term is not laid in here.
  Ns, Mg, Pm, Oc, Wt: the table's letters: left to the table's and the kinds' files.
  ext: THE EXTRACTORS: at place 1 "the cells that the stored table decodes to with the record" (the
    key file's decoder); at 9 and 10 "the message that the committed word decodes to with its
    sample".
  same: "two worlds agree at a component": A LETTER THAT THE TABLE HAS NOT YET: its `Comp` and
    `reads` are names by hand: nothing ties them to Wt or to the meanings.
  cnt: a price as a count of a written round's challenges. Pn, N, split: off the plan.
UNDER "for all" OVER THESE LETTERS THE ROW WOULD BE FALSE; UNDER "there is" EMPTY (meanings that
always hold; cnt := all of a round's challenges; same := "true"). Each has to become a named term.

What one may try against it. Yes to all; no to all (meets it for nothing); cnt too large; meanings
that always hold; same := "true" (then "the old part kept" says nothing); an ext that reads what no
oracle of the statement fixes; N = 0; whether `Ns.lo = D.t₁` is the only tie that the numbers want.

Every "there is", walked. In `LeadsBN`: the split of a block's errors; the two games. None of its
own. Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.DescBByMake
import Johnson.Desc.Sound.BordersSharedQ
import Johnson.Desc.Sound.PricesSharedQ

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Flat KObj OnBytes.Params
open _root_.Run.PQ (CK SgX)
open _root_.Iop (Reduction Err Shape IOR ExtSpec oneExternalString Round)
open VerifiableInference.Desc.Shared

/-- The components of the witness that block number k lays, by the table. -/
def laysAt (split : Bool) (k : ℕ) : List Comp :=
  ((sharedPlaces split)[k]?.map (laysOfS split)).getD []

/-- **The named extractor lays what the table says, and nothing else.** A: the statements. -/
def ExtNamed {A Wt : Type} (split : Bool) (ext : ℕ → A → Wt → Wt)
    (same : Comp → Wt → Wt → Prop) : Prop :=
  (∀ k, laysAt split k = [] → ∀ a w, ext k a w = w) ∧
    ∀ k a w c, c ∉ laysAt split k → same c (ext k a w) w

section
variable {P₁ S₂ Cl Wt : Type} {C : CK} {Fr : Frame} (Ns : NumbersS) (Mg : MeaningS S₂ P₁ Wt)
  (Pm : PromMeaning S₂) (Oc : P₁ → Strs → Prop) (split : Bool)
  (p : Piece C Fr (P₁ × S₂) Cl Wt) (l : List (Piece C Fr (P₁ × S₂) Cl Wt))
  (ext : ℕ → (P₁ × S₂) × Fr.E.Str → Wt → Wt)

/-- **What block number k's law leads to.** -/
def stepAt (k : ℕ) (a b : (P₁ × S₂) × Fr.E.Str) : Prop :=
  onQ₂ Ns Pm Oc split p l (k + 1) b ∧
    ∀ w, relQ₂ Ns Mg split p l (k + 1) b w → relQ₂ Ns Mg split p l k a (ext k a w)

end

/-- **THE ROW `shared_joint_count`, AS A FORM: SECOND FORM.** -/
def SharedJointCountRow (C : CK) (D : WholeD) (all : List LeftT) (X Rec X₁ X₂ Wt : Type)
    (F : FileDescription (X × Rec)) (T : ThreeAt C D all F X₁ X₂ Wt) (Ns : NumbersS)
    (Mg : MeaningS F.S₂ (F.XiPub × F.S₁) Wt) (Pm : PromMeaning F.S₂)
    (Oc : F.XiPub × F.S₁ → Strs → Prop) (split : Bool) (N : ℕ) (cnt : Round → Binary → ℕ → ℕ)
    (Pn : Planned)
    (ext : ℕ → ((F.XiPub × F.S₁) × F.S₂) × (EAll D all).Str → Wt → Wt)
    (same : Comp → Wt → Wt → Prop) : Prop :=
  Ns.lo = D.t₁ ∧
  EachPriced cnt F.shared.blocksInOrder Pn 0 ((atDesc F T).p₂ :: (atDesc F T).l₂) ∧
  ExtNamed split ext same ∧
  EachLawsBN (keyAt Prod.snd D.t₁ (atDesc F T).p₂ (atDesc F T).l₂)
    (onQ₂ Ns Pm Oc split (atDesc F T).p₂ (atDesc F T).l₂)
    (stepAt Ns Mg Pm Oc split (atDesc F T).p₂ (atDesc F T).l₂ ext) N 0
    ((atDesc F T).p₂ :: (atDesc F T).l₂)

#check @SharedJointCountRow

-- WHAT THE TABLE LAYS, EVALUATED: with a split: the cells at 1, o_u's message at 9, o_sp's at 10
example : (List.range 12).map (laysAt true) =
    [[], [.cells], [], [], [], [], [], [], [], [.msg .oU], [.msg .oSp], []] := by decide

-- IT JOINS UPWARD: the row's fourth clause is, as it stands, the premise e₂ of
-- `proofSound_at_descB_byMake` (Johnson/Desc/Sound/DescBByMake.lean), at the places whose second
-- chain's fields are the table's
example (C : CK) (D : WholeD) (all : List LeftT) (X Rec X₁ X₂ Wt : Type) (F : FileDescription (X × Rec))
    (T : ThreeAt C D all F X₁ X₂ Wt) (Ns : NumbersS) (Mg : MeaningS F.S₂ (F.XiPub × F.S₁) Wt)
    (Pm : PromMeaning F.S₂) (Oc : F.XiPub × F.S₁ → Strs → Prop) (split : Bool) (N : ℕ)
    (cnt : Round → Binary → ℕ → ℕ) (Pn : Planned)
    (ext : ℕ → ((F.XiPub × F.S₁) × F.S₂) × (EAll D all).Str → Wt → Wt)
    (same : Comp → Wt → Wt → Prop)
    (Pl : Plain.PPlaces D all (F.XiPub × F.S₁) ((F.XiPub × F.S₁) × F.S₂)
      ((F.XiPub × F.S₁ × F.S₂) × F.S₃))
    (h : SharedJointCountRow C D all X Rec X₁ X₂ Wt F T Ns Mg Pm Oc split N cnt Pn ext same) :
    EachLawsBN (keyAt Prod.snd D.t₁ (atDesc F T).p₂ (atDesc F T).l₂)
      ({ Pl with
          on₂ := onQ₂ Ns Pm Oc split (atDesc F T).p₂ (atDesc F T).l₂
          Q₂ := stepAt Ns Mg Pm Oc split (atDesc F T).p₂ (atDesc F T).l₂ ext } :
        Plain.PPlaces D all _ _ _).on₂
      ({ Pl with
          on₂ := onQ₂ Ns Pm Oc split (atDesc F T).p₂ (atDesc F T).l₂
          Q₂ := stepAt Ns Mg Pm Oc split (atDesc F T).p₂ (atDesc F T).l₂ ext } :
        Plain.PPlaces D all _ _ _).Q₂
      N 0 ((atDesc F T).p₂ :: (atDesc F T).l₂) :=
  h.2.2.2

end VerifiableInference.Desc.Sound
