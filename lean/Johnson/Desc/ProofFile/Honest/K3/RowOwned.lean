-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/RowOwned.lean: the lookup's row of parts (Honest/K3/Row.lean) with
the owner of each stretch of coins as a letter: whose message's coins a stage's two stretches are.
At a proof file's links all are the segment's mask row's; at the key file's two lookups they are two
messages'. Definitions with code, and theorems by unfolding.

Terms. Honest/K3/GLOSSARY.md ("row", "part, stretch", "book, coins", "mask, mask row", "slot",
"letter, letters").

What is defined and shown.
  `Owners`, `oneOwner`: for a stage: the owner of its first stretch ("sum") and of its second
    ("ends"); the letter at which the row is that of Row.lean.
  `sumNameBy`, `endNameBy`, `partOfOwned`, `lookRowOwned`, `proverSideOfLookup`, `proverSideOfLookupInChain`,
    `lookPairsOwned`: the texts of Row.lean, with the letter put into the two names alone.
  `partOfOwned_one`, `lookRowOwned_one`, `proverSideOfLookup_one`, `proverSideOfLookupInChain_one`,
    `lookPairsOwned_one`: at `oneOwner` each is the definition of Row.lean, by unfolding.
  `partOfOwned_moves`, `lookRowOwned_moves`: the letter changes no part's number of moves.
  `stretchesOwned` (helpers: `nextOf`, `putNext`): the list of stretches, each with its owner,
    counted owner by owner: an owner's entries are dealt in the order of sending, from a first
    number that is given for each owner. It is tied to `stretches` (Row.lean) by no theorem.
  `multRun`, `keyOwners`: the key file's letter: the two end values of each part's last key level
    are the index-mask message's; all else the multiplicities' mask rows'.
  `secondOf`: a letter unrolled slot by slot, in the order of sending: whether the slot's coin is a
    named owner's.

Imported. Honest/ForKinds.lean lies beneath this file.

Limits. Names and numbers alone. The forms of simulators beside the parts read no name: they are
those of Row.lean. That `keyOwners` unrolled is the verifier's own list (`K3.fromKeys`,
Johnson/Desc/First/Look/K3Key.lean) is proved in Honest/K3/RowOwnedLaw.lean (`fromKeys_eq`: at a
face with two planes or more). "the multiplicities' mask rows" is a name that the frame's own list
of owners
(Honest/ForKinds.lean) does not have.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.RowLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3
open VerifiableInference.Desc (Place)

variable {V W Pb V₁ W₁ X₁ : Type}

/-! ## 1 The letter -/

/-- **Whose message's coins a stage's two stretches are**: the first stretch's owner, the second's.
-/
abbrev Owners : Type := Stage → String × String

/-- All of one owner: the segment's mask row. -/
def oneOwner : Owners := fun _ => (maskRowRun, maskRowRun)

/-- The name of the first stretch that the part number i of the row at a place spends. -/
def sumNameBy (o : Owners) (s : Stage) (p : Place) (i : Nat) : String :=
    runName (o s).1 ⟨p, i⟩ "sum"

/-- The name of the second. -/
def endNameBy (o : Owners) (s : Stage) (p : Place) (i : Nat) : String :=
    runName (o s).2 ⟨p, i⟩ "ends"

/-! ## 2 The row -/

/-- **The part of a stage.** Here i is its number in the row. -/
def partOfOwned (o : Owners) (R : Reads) (J : LookJobs W) (a : At) (s : Stage) (i : Nat) :
    Part V W Unit :=
  match s.call a.face with
  | some k => sumPart (sumNameBy o s a.place i) (endNameBy o s a.place i) (jobOf R J a s k)
  | none => quiet

/-- **A lookup's row of parts**, at a letter for the owners. -/
def lookRowOwned (o : Owners) (R : Reads) (J : LookJobs W) (a : At) : List (Part V W Unit) :=
  (stages a.face).zipIdx.map fun x => partOfOwned o R J a x.1 x.2

/-- The half. -/
def proverSideOfLookup (o : Owners) (R : Reads) (J : LookJobs W) (a : At) : Placed V W Unit :=
  ⟨a.place, lookRowOwned o R J a⟩

/-- The half, seated in a chain's letters. -/
def proverSideOfLookupInChain (o : Owners) (R : Reads) (J : LookJobs W) (wit : W₁ → W) (a : At) :
    Placed V₁ W₁ X₁ :=
  ⟨a.place, (lookRowOwned (V := Unit) o R J a).map
    (Part.lift (fun _ => ()) wit (fun _ => ()) fun x _ => x)⟩

/-- The seated row, each part with the form beside it. -/
def lookPairsOwned (o : Owners) (R : Reads) (J : LookJobs W) (wit : W₁ → W) (a : At) :
    List (Part V₁ W₁ X₁ × Sim Pb) :=
  (proverSideOfLookupInChain o R J wit a).parts.zip (lookSims a)

/-! ## 3 At one owner it is the row -/

/-- At one owner a part is that of Honest/K3/Row.lean. -/
theorem partOfOwned_one (R : Reads) (J : LookJobs W) (a : At) (s : Stage) (i : Nat) :
    partOfOwned (V := V) oneOwner R J a s i = partOf R J a s i := rfl

/-- **At one owner the row is that of Honest/K3/Row.lean.** -/
theorem lookRowOwned_one (R : Reads) (J : LookJobs W) (a : At) :
    lookRowOwned (V := V) oneOwner R J a = lookRow R J a := rfl

/-- So is the half. -/
theorem proverSideOfLookup_one (R : Reads) (J : LookJobs W) (a : At) :
    proverSideOfLookup (V := V) oneOwner R J a = proverSideOfLookupAtOneOwner R J a := rfl

/-- So is the seated half. -/
theorem proverSideOfLookupInChain_one (R : Reads) (J : LookJobs W) (wit : W₁ → W) (a : At) :
    proverSideOfLookupInChain (V₁ := V₁) (X₁ := X₁) oneOwner R J wit a = proverSideOfLookupInChainAtOneOwner R J wit a := rfl

/-- So is the seated row with the forms beside it. -/
theorem lookPairsOwned_one (R : Reads) (J : LookJobs W) (wit : W₁ → W) (a : At) :
    lookPairsOwned (V₁ := V₁) (X₁ := X₁) (Pb := Pb) oneOwner R J wit a = lookPairs R J wit a := rfl

/-! ## 4 The letter changes no number of moves -/

/-- A part has as many moves as the part of `partOf` (Honest/K3/Row.lean), at every letter. That
this number is the stage's rounds is `partOf_moves` (Honest/K3/RowLaw.lean). -/
theorem partOfOwned_moves (o : Owners) (R : Reads) (J : LookJobs W) (a : At) (s : Stage) (i : Nat) :
    (partOfOwned (V := V) o R J a s i).moves.length = (partOf (V := V) R J a s i).moves.length := by
  unfold partOfOwned partOf
  cases s.call a.face with
  | none => rfl
  | some k => rw [sumPart_moves, sumPart_moves]

/-- The numbers of moves of the row's parts are those of the row of Honest/K3/Row.lean, at every
letter. -/
theorem lookRowOwned_moves (o : Owners) (R : Reads) (J : LookJobs W) (a : At) :
    (lookRowOwned (V := V) o R J a).map (·.moves.length) =
      (lookRow (V := V) R J a).map (·.moves.length) := by
  unfold lookRowOwned lookRow
  simp only [List.map_map, Function.comp_def, partOfOwned_moves]

/-! ## 5 The stretches, counted owner by owner -/

/-- The next free entry of an owner: what is written for it; else what the letter `firsts` gives. -/
def nextOf (firsts : String → Nat) (l : List (String × Nat)) (w : String) : Nat :=
  (l.lookup w).getD (firsts w)

/-- The list with an owner's next free entry set anew. -/
def putNext (l : List (String × Nat)) (w : String) (n : Nat) : List (String × Nat) :=
  (w, n) :: l.filter fun x => x.1 != w

/-- **The stretches that the row spends**, in the order of sending; each with its owner and the
number, in its owner's own count, of the first entry that it takes. Here firsts gives each owner's
first free entry in front of the lookup. -/
def stretchesOwned (o : Owners) (a : At) (firsts : String → Nat) : List Stretch :=
  ((stages a.face).zipIdx.foldl
    (fun (y : List Stretch × List (String × Nat)) x =>
      let w1 := (o x.1).1
      let n1 := nextOf firsts y.2 w1
      let l1 := if x.1.own a.face == 0 then y.2 else putNext y.2 w1 (n1 + x.1.own a.face)
      let w2 := (o x.1).2
      let n2 := nextOf firsts l1 w2
      let l2 := if x.1.tail a.face == 0 then l1 else putNext l1 w2 (n2 + x.1.tail a.face)
      (y.1 ++
        (if x.1.own a.face == 0 then [] else
          [⟨x.1, x.2, sumNameBy o x.1 a.place x.2, w1, n1, x.1.own a.face⟩]) ++
        (if x.1.tail a.face == 0 then [] else
          [⟨x.1, x.2, endNameBy o x.1 a.place x.2, w2, n2, x.1.tail a.face⟩]), l2))
    ([], [])).1

/-! ## 6 The key file's letter -/

/-- The lookups' own message at the key file: the multiplicities with their mask rows. -/
def multRun : String := "the multiplicities' mask rows"

/-- **The key file's letter**: the two end values of each part's last key level are the index-mask
message's; every other stretch is the lookups' own message's. -/
def keyOwners (f : LFace) : Owners
  | .key i m => (multRun, if m + 1 == f.parts.getD i 0 then indexMaskRun else multRun)
  | _ => (multRun, multRun)

/-- **A letter unrolled**, slot by slot in the order of sending: whether the slot's coin is that of
w. -/
def secondOf (o : Owners) (f : LFace) (w : String) : List Bool :=
  (stages f).flatMap fun s =>
    List.replicate (s.own f) ((o s).1 == w) ++ List.replicate (s.tail f) ((o s).2 == w)

#print axioms ProofFile.Honest.K3.partOfOwned_one
#print axioms ProofFile.Honest.K3.lookRowOwned_one
#print axioms ProofFile.Honest.K3.proverSideOfLookup_one
#print axioms ProofFile.Honest.K3.proverSideOfLookupInChain_one
#print axioms ProofFile.Honest.K3.lookPairsOwned_one
#print axioms ProofFile.Honest.K3.partOfOwned_moves
#print axioms ProofFile.Honest.K3.lookRowOwned_moves

end ProofFile.Honest.K3
