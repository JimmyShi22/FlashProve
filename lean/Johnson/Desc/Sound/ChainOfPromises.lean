-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/ChainOfPromises.lean: THE CHAIN OF PROMISES AT THE FIRST CHAIN's TABLE: from each
block's law IN ITS KIND's OWN WORDS, with its five ties to the table, to what the rule of
composition asks of the whole chain by way of laws. Two definitions, three theorems. A RULE OVER
LETTERS.

Why. "Block k's promise out is block k + 1's promise in." At the table of joints
(Johnson/Desc/First/Borders.lean) that holds by the make: ONE term, `onQ (k + 1)`, stands behind
block k and in front of block k + 1 (Johnson/Desc/Sound/BordersQ.lean). But a kind's law comes with
a condition in front and a condition behind of its own. What ties these to the table's term is owed
block by block. This file says what is owed, as one proposition a block, and that nothing else is.

What is said. `TiedAt k q`: there are conditions o, o' and relations R, R' (the kind's own) with
  law  the piece's law between them (`Piece.GoodIn`);
  t1   the table's promise in front, at a record without a mark, gives o;
  t2   that, a yes of the block and o' behind give THE TABLE's PROMISE BEHIND;
  t3   with these in hand, what the row opens (with its context) at (b, w) gives R' b w;
  t4   with these and what the row opens in hand, R at the extractor's value gives what the row
       closes (with its context) there;
  t5   every open item that the row does not close rides from (b, w) to the extractor's value:
       ASKED, AS t1 TO t4, AT A RECORD WITHOUT A MARK, with the yes, the table's promise behind and
       ALL THAT IS OPEN BEHIND at (b, w) in hand (`Piece.Frames` asks it at marked records too,
       where the promise gives nothing that a rider's lemma could spend);
and two facts on the block's text: a mark stays; "the stored table decodes with the record" rides.
`EachTied`: so at every block of a list, from number k on. `goodIn_of_tied` (over the rule's one
step with the riders asked only where its proof spends them: Johnson/Desc/Sound/SpineWide.lean): a
tied block's law between the table's promises and relations at its two borders. `chainOfPromises`:
so `EachGoodIn` at the table's promises and relations: WHAT THE RULE FOR A FILE ASKS OF THE FIRST
CHAIN's PIECES BY WAY OF LAWS. `tiedAt_of_own`: THE WAY BACK: a block's own law at the table, with
what rides and the two facts, is a tie (the kind's words := the table's): so NOTHING ELSE IS OWED.
(A tie asks LESS than that law with what rides: t5 is fenced to records without a mark.)

Limits. (1) A RULE OVER LETTERS: N, Mg, links, ps, get and the pieces are letters (at `Mg.decodes`
:= never every promise is empty, every tie but "a mark stays" is free, and the conclusion says
nothing; at `ps` := [] every row is empty); `TiedAt` is shown at no block of any description; NO
FILLING OF THE TABLE's LETTERS IS KNOWN AT WHICH IT HOLDS AT EVERY BLOCK OF A REAL CHAIN. (2) o' of
block k and o of block k + 1 never meet: each is tied to the table's term alone: so a kind need not
know its neighbour's words; the price is t1 and t2 at every block. (3) A kind whose condition
between two of its own blocks is "came out of the block in front" has no predicate to lay for o: it
must name one. (4) The extractor is the piece's own (`q.ext`): that it is the table's one extractor
is asked elsewhere (Johnson/Desc/Sound/BordersFill.lean's `EachExtQ`). (5) Nothing here ties the
list of pieces to `ps`: at a longer list the rows beyond are empty and the promise reads its
defaults, in silence. (6) The rule for a file asks more than laws: that the pieces are the
description's, the tie at the start and the joint to the shared chain, the errors under the cap.

Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.Sound.BordersQ
import Johnson.Desc.Sound.SpineWide

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound

open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open VerifiableInference.Desc.First (ModelPart Item Meaning Numbers start)

section
variable {A Cl P W : Type} {C : CK} {Fr : Frame} (N : Numbers) (Mg : Meaning P W)
  (links : List ModelPart) (ps : List Place) (get : A → P × First.S)

/-- **What is owed at block number k**: the kind's law in its own words, and its five ties to the
table. -/
def TiedAt (k : ℕ) (q : Piece C Fr A Cl W) : Prop :=
  ∃ (o o' : A × Fr.E.Str → Prop) (R R' : A × Fr.E.Str → W → Prop),
    q.GoodIn o o' R R' ∧
    (∀ a, onQ N Mg links ps get k a → ¬ (get a.1).2.failed ≠ none → o a) ∧
    (∀ a τ b, onQ N Mg links ps get k a → ¬ (get a.1).2.failed ≠ none →
      q.ior.red.out a τ = some b → o' b → onQ N Mg links ps get (k + 1) b) ∧
    (∀ a τ b w, onQ N Mg links ps get k a → ¬ (get a.1).2.failed ≠ none →
      q.ior.red.out a τ = some b → o' b → relAt (meansQ N Mg get) (outsQ links ps k) b w →
      R' b w) ∧
    (∀ a τ b w, onQ N Mg links ps get k a → ¬ (get a.1).2.failed ≠ none →
      q.ior.red.out a τ = some b → o' b → relAt (meansQ N Mg get) (outsQ links ps k) b w →
      R a (q.ext a τ w) → relAt (meansQ N Mg get) (insQ links ps k) a (q.ext a τ w)) ∧
    (∀ a τ b w i, onQ N Mg links ps get k a → ¬ (get a.1).2.failed ≠ none →
      q.ior.red.out a τ = some b → onQ N Mg links ps get (k + 1) b →
      relQ N Mg links ps get (k + 1) b w →
      openAfter (insQ links ps) (outsQ links ps) (· ∈ start links) k i → ¬ insQ links ps k i →
      meansQ N Mg get i a (q.ext a τ w)) ∧
    (∀ a τ b, q.ior.red.out a τ = some b → (get a.1).2.failed ≠ none →
      (get b.1).2.failed ≠ none) ∧
    (∀ a τ b, q.ior.red.out a τ = some b → Mg.decodes (get a.1) (strsOf Fr a.2) →
      Mg.decodes (get b.1) (strsOf Fr b.2))

/-- So at every block of a list; the first has the number k. -/
def EachTied : ℕ → List (Piece C Fr A Cl W) → Prop
  | _, [] => True
  | k, q :: l => TiedAt N Mg links ps get k q ∧ EachTied (k + 1) l

/-- A tied block's law between the table's promises and relations at its two borders. -/
theorem goodIn_of_tied (k : ℕ) (q : Piece C Fr A Cl W) (h : TiedAt N Mg links ps get k q) :
    q.GoodIn (onQ N Mg links ps get k) (onQ N Mg links ps get (k + 1)) (relQ N Mg links ps get k)
      (relQ N Mg links ps get (k + 1)) := by
  obtain ⟨o, o', R, R', hl, t1, t2, t3, t4, t5, hMark, hDec⟩ := h
  refine spineStepIn q _ _ (meansQ N Mg get) _ (insQ links ps k) (outsQ links ps k)
    (ownAtTableWide A Cl P W C Fr N Mg links ps get k q o o' R R' hl t1 t2 t3 t4 hMark hDec) ?_
  intro a τ b w i ha hb hon hall hi hin
  refine t5 a τ b w i ha ?_ hb hon hall hi hin
  intro hm
  have hu : meansQ (Fr := Fr) N Mg get .unmarked b w :=
    hall .unmarked (Or.inr (List.mem_append_right _ (List.mem_singleton.2 rfl)))
  exact hMark a τ b hb hm hu

/-- **THE CHAIN OF PROMISES**: the ties at every block give what the rule for a file asks of the
first chain's pieces by way of laws, at the table's promises and relations. -/
theorem chainOfPromises (l : List (Piece C Fr A Cl W)) :
    ∀ k, EachTied N Mg links ps get k l →
      EachGoodIn (onQ N Mg links ps get) (relQ N Mg links ps get) k l := by
  induction l with
  | nil => intro _ _; trivial
  | cons q l ih =>
    intro k h
    exact ⟨goodIn_of_tied N Mg links ps get k q h.1, ih (k + 1) h.2⟩

/-- **THE WAY BACK**: a block's own law at the table, what rides, and the two facts on its text are
a tie: the kind's words := the table's. -/
theorem tiedAt_of_own (k : ℕ) (q : Piece C Fr A Cl W)
    (ho : q.Own (onQ N Mg links ps get k) (onQ N Mg links ps get (k + 1)) (meansQ N Mg get)
      (insQ links ps k) (outsQ links ps k))
    (hf : q.Frames (onQ N Mg links ps get k) (onQ N Mg links ps get (k + 1)) (meansQ N Mg get)
      (openAfter (insQ links ps) (outsQ links ps) (· ∈ start links) k) (insQ links ps k))
    (hMark : ∀ a τ b, q.ior.red.out a τ = some b → (get a.1).2.failed ≠ none →
      (get b.1).2.failed ≠ none)
    (hDec : ∀ a τ b, q.ior.red.out a τ = some b → Mg.decodes (get a.1) (strsOf Fr a.2) →
      Mg.decodes (get b.1) (strsOf Fr b.2)) :
    TiedAt N Mg links ps get k q :=
  ⟨_, _, _, _, ho, fun _ ha _ => ha, fun _ _ _ _ _ _ hb => hb, fun _ _ _ _ _ _ _ _ hO => hO,
    fun _ _ _ _ _ _ _ _ _ hR => hR,
    fun a τ b w i ha _ hb hon hall hi hin =>
      hf a τ b w i ha hb hon hi hin (hall i (Or.inl ⟨hi, hin⟩)),
    hMark, hDec⟩

end

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.goodIn_of_tied
#print axioms VerifiableInference.Desc.Sound.tiedAt_of_own
#print axioms VerifiableInference.Desc.Sound.chainOfPromises
