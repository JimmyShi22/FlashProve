-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/BordersQ.lean: the table of joints (Johnson/Desc/First/Borders.lean) as the
conditions and relations of the rule of composition at the first chain. Definitions, four statements
written as `def … : Prop` (`JointsJoin`, `JointsJoinPlain`, `OwnAtTable`, `OwnAtTableWide`), and
their proofs (of the first two: a call of `spineRule`, a call of `spinePlain`).

What is said. `onQ`, `relQ`: the condition and the relation at boundary k of the first chain: the
table's promise there; "every item that is open at boundary k holds". `JointsJoin`: if every block
of the chain has its own law between the items that its row closes and opens (`Piece.Own`) and the
items that ride past it are kept (`Piece.Frames`), the chain has `EachGoodIn` at `onQ` and `relQ`:
what `ChainRule` and `FileKnowsJOfGood` ask of it. `JointsJoinPlain`: THE TABLE's
SHADOW: under the same premises the chain has the plain law (`EachPlain`,
Johnson/Desc/Sound/SpinePlain.lean) at "there is a witness of which every open item holds": AT AN
EARLY BOUNDARY THAT MEANS: THE OPEN ITEMS CAN STILL ALL BE MET.

`Item.unmarked` STANDS IN EVERY BLOCK's ROW (`insQ`, `outsQ`): a block that marks and goes on says
yes at every challenge: without it such a block's own law would be false; with it each block owes
"no mark behind, so none in front": a mark stays.

Limits. (1) The items' meaning (`Meaning`) and the plan's numbers (`Numbers`) are letters. (2) The
rows are unchecked. (3) The open set of the relation is the rule's (`openAfter`); the promise reads
the list that Borders.lean computes (`openSets`). That the two have the same members is not shown
here: `openL_iff_openSets` (Johnson/Desc/Sound/SpineList.lean) has it where `readsOpen` and
`rowsApart` say yes, "no mark" is in the start set and k ≤ the places' length (`openIsList` joins
`openAfter`). (4) That each piece's extractor is the table's one extractor is asked nowhere here.

Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.First.Borders
import Johnson.Desc.Sound.SpinePlain
import Johnson.Desc.Sound.MsgAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open VerifiableInference.Desc.First (ModelPart Item BlockRow Meaning Numbers rowOf start onAt openSets
  pubSets)

/-- The row of block number k. A number behind the last block: the empty row. -/
def rowQ (links : List ModelPart) (ps : List Place) (k : ℕ) : BlockRow :=
  (ps[k]?.map (rowOf links)).getD {}

/-- What block number k closes, with what it reads, and "no mark". -/
def insQ (links : List ModelPart) (ps : List Place) (k : ℕ) (i : Item) : Prop :=
  i ∈ (rowQ links ps k).ins ++ (rowQ links ps k).ctx ++ [.unmarked]

/-- What it opens, with what it reads, and "no mark". -/
def outsQ (links : List ModelPart) (ps : List Place) (k : ℕ) (i : Item) : Prop :=
  i ∈ (rowQ links ps k).outs ++ (rowQ links ps k).ctx ++ [.unmarked]

section
variable {A P W : Type} {Fr : Frame} (N : Numbers) (Mg : Meaning P W) (links : List ModelPart)
  (ps : List Place) (get : A → P × First.S)

/-- **The condition at boundary k.** get: what was handed to the chain, and the first chain's state,
in the chain's record. BEHIND THE LAST BLOCK: THE PROMISE AT WHAT IS OPEN THERE, with the
book-keeping of the chain's end: the next chain's first promise is to be got from it. -/
def onQ (k : ℕ) (a : A × Fr.E.Str) : Prop :=
  onAt N Mg links ps[k]? ((openSets links ps (start links))[k]?.getD [])
    ((pubSets Mg.more links ps)[k]?.getD []) (get a.1) (strsOf Fr a.2)

/-- What an item says of a statement of the chain. -/
def meansQ (i : Item) (a : A × Fr.E.Str) (w : W) : Prop :=
  i.holds N Mg (get a.1) (strsOf Fr a.2) w

/-- **The relation at boundary k: every open item holds.** -/
def relQ (k : ℕ) : A × Fr.E.Str → W → Prop :=
  relAt (meansQ (Fr := Fr) N Mg get)
    (openAfter (insQ links ps) (outsQ links ps) (· ∈ start links) k)

end

/-- **The joints join.** -/
def JointsJoin : Prop :=
  ∀ (A Cl P W : Type) (C : CK) (Fr : Frame) (N : Numbers) (Mg : Meaning P W) (links : List ModelPart)
    (ps : List Place) (get : A → P × First.S) (l : List (Piece C Fr A Cl W)),
    EachOwn (onQ N Mg links ps get) (meansQ N Mg get) (insQ links ps) (outsQ links ps)
      (· ∈ start links) 0 l →
    EachGoodIn (onQ N Mg links ps get) (relQ N Mg links ps get) 0 l

/-- **The table's shadow.** -/
def JointsJoinPlain : Prop :=
  ∀ (A Cl P W : Type) (C : CK) (Fr : Frame) (N : Numbers) (Mg : Meaning P W) (links : List ModelPart)
    (ps : List Place) (get : A → P × First.S) (l : List (Piece C Fr A Cl W)),
    EachOwn (onQ N Mg links ps get) (meansQ N Mg get) (insQ links ps) (outsQ links ps)
      (· ∈ start links) 0 l →
    EachPlain (onQ N Mg links ps get) (fun k => shadow (relQ N Mg links ps get k)) 0 l

theorem jointsJoin : JointsJoin := by
  intro A Cl P W C Fr N Mg links ps get l h
  exact spineRule A Cl W Item C Fr _ _ _ _ _ l 0 h

theorem jointsJoinPlain : JointsJoinPlain := by
  intro A Cl P W C Fr N Mg links ps get l h
  exact spinePlain A Cl W Item C Fr _ _ _ _ _ l 0 h

/-- **THE DOOR AT THE TABLE: what a kind brings for block number k.** o, o', R, R': the kind's own
conditions and relations, with its law between them. It brings four implications, each asked AT
UNMARKED STATEMENTS ALONE where it starts from the table's promise; and two facts on its block's
text: a mark stays; "the stored table decodes with the record" rides. What is the same at every row
is paid here, once: at a marked statement the promise behind holds (the mark, and "decodes"), and
what the row opens holds of no witness ("no mark" stands among it). -/
def OwnAtTable : Prop :=
  ∀ (A Cl P W : Type) (C : CK) (Fr : Frame) (N : Numbers) (Mg : Meaning P W) (links : List ModelPart)
    (ps : List Place) (get : A → P × First.S) (k : ℕ) (q : Piece C Fr A Cl W)
    (o o' : A × Fr.E.Str → Prop) (R R' : A × Fr.E.Str → W → Prop),
    q.GoodIn o o' R R' →
    (∀ a, onQ N Mg links ps get k a → ¬ (get a.1).2.failed ≠ none → o a) →
    (∀ a τ b, onQ N Mg links ps get k a → ¬ (get a.1).2.failed ≠ none →
      q.ior.red.out a τ = some b → o' b → onQ N Mg links ps get (k + 1) b) →
    (∀ b w, relAt (meansQ N Mg get) (outsQ links ps k) b w → R' b w) →
    (∀ a w, onQ N Mg links ps get k a → ¬ (get a.1).2.failed ≠ none → R a w →
      relAt (meansQ N Mg get) (insQ links ps k) a w) →
    (∀ a τ b, q.ior.red.out a τ = some b → (get a.1).2.failed ≠ none →
      (get b.1).2.failed ≠ none) →
    (∀ a τ b, q.ior.red.out a τ = some b → Mg.decodes (get a.1) (strsOf Fr a.2) →
      Mg.decodes (get b.1) (strsOf Fr b.2)) →
    q.Own (onQ N Mg links ps get k) (onQ N Mg links ps get (k + 1)) (meansQ N Mg get)
      (insQ links ps k) (outsQ links ps k)

theorem ownAtTable : OwnAtTable := by
  intro A Cl P W C Fr N Mg links ps get k q o o' R R' h ho ho' hR' hR hMark hDec
  refine ownOfGoodInBut A Cl W Item C Fr q _ _ _ _ _ (fun a => (get a.1).2.failed ≠ none) o o' R R'
    h ho ho' hR' hR ?_
  intro a τ b ha hm hb
  refine ⟨⟨hDec a τ b hb ha.1, Or.inl (hMark a τ b hb hm)⟩, fun w hw => ?_⟩
  have hu : meansQ (Fr := Fr) N Mg get .unmarked b w :=
    hw .unmarked (List.mem_append_right _ (List.mem_singleton.2 rfl))
  exact hMark a τ b hb hm hu

/-- **The same door, wider** (`OwnOfGoodInWide`): the third and fourth implication are asked at an
unmarked statement inside the promise, at a yes of the block, with the kind's condition behind in
hand; the fourth also with what the row opens at (b, w), at the extractor's value alone. -/
def OwnAtTableWide : Prop :=
  ∀ (A Cl P W : Type) (C : CK) (Fr : Frame) (N : Numbers) (Mg : Meaning P W) (links : List ModelPart)
    (ps : List Place) (get : A → P × First.S) (k : ℕ) (q : Piece C Fr A Cl W)
    (o o' : A × Fr.E.Str → Prop) (R R' : A × Fr.E.Str → W → Prop),
    q.GoodIn o o' R R' →
    (∀ a, onQ N Mg links ps get k a → ¬ (get a.1).2.failed ≠ none → o a) →
    (∀ a τ b, onQ N Mg links ps get k a → ¬ (get a.1).2.failed ≠ none →
      q.ior.red.out a τ = some b → o' b → onQ N Mg links ps get (k + 1) b) →
    (∀ a τ b w, onQ N Mg links ps get k a → ¬ (get a.1).2.failed ≠ none →
      q.ior.red.out a τ = some b → o' b → relAt (meansQ N Mg get) (outsQ links ps k) b w →
      R' b w) →
    (∀ a τ b w, onQ N Mg links ps get k a → ¬ (get a.1).2.failed ≠ none →
      q.ior.red.out a τ = some b → o' b → relAt (meansQ N Mg get) (outsQ links ps k) b w →
      R a (q.ext a τ w) → relAt (meansQ N Mg get) (insQ links ps k) a (q.ext a τ w)) →
    (∀ a τ b, q.ior.red.out a τ = some b → (get a.1).2.failed ≠ none →
      (get b.1).2.failed ≠ none) →
    (∀ a τ b, q.ior.red.out a τ = some b → Mg.decodes (get a.1) (strsOf Fr a.2) →
      Mg.decodes (get b.1) (strsOf Fr b.2)) →
    q.Own (onQ N Mg links ps get k) (onQ N Mg links ps get (k + 1)) (meansQ N Mg get)
      (insQ links ps k) (outsQ links ps k)

theorem ownAtTableWide : OwnAtTableWide := by
  intro A Cl P W C Fr N Mg links ps get k q o o' R R' h ho ho' hR' hR hMark hDec
  refine ownOfGoodInWide A Cl W Item C Fr q _ _ _ _ _ (fun a => (get a.1).2.failed ≠ none) o o' R
    R' h ho ho' hR' hR ?_
  intro a τ b ha hm hb
  refine ⟨⟨hDec a τ b hb ha.1, Or.inl (hMark a τ b hb hm)⟩, fun w hw => ?_⟩
  have hu : meansQ (Fr := Fr) N Mg get .unmarked b w :=
    hw .unmarked (List.mem_append_right _ (List.mem_singleton.2 rfl))
  exact hMark a τ b hb hm hu

end VerifiableInference.Desc.Sound
