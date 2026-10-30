-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/SpineOnce.lean: "EVERY OPEN ITEM HOLDS" AT THE BORDERS OF THE SHARED CHAIN, WITH THE
ITEMS SORTED: SHARED, OR A SLOT's OWN: a stretch in which no own item is opened or closed is paid once
for all N slots. Definitions, and one statement written as `def … : Prop`. NOTHING IS PROVED IN THIS
FILE.

The setting. Johnson/Desc/Sound/Spine.lean makes the relation at every border of a chain by a function:
an ITEM is a named claim; block number k closes the items `In k` and opens the items `Out k`; the
relation at border k is "every item that is open there holds" (`openAfter`, `relAt`). At the shared
chain of a proof file that relation has to bear a count for a batch
(Johnson/Desc/Sound/SharedRule.lean, SharedOnce.lean): a round is paid once only where the relations
read a statement through the acting part alone (the chain's own record, the stored table, the chain's
own trees), and what a slot has of its own is only carried.

What is said. THE ITEMS OF THIS FILE ARE THE SHARED ONES. The meaning of a shared item is WRITTEN AS A
FUNCTION OF THE ACTING PART's VALUE at the border at which it is read (`μ i k`): so it cannot read what
was handed to the chain, nor a tree of an earlier chain. All that the slots have of their own is ONE
relation Rc for the whole stretch.
  `relSh`: every item of a set holds, at border k.
  `EachOwnSh`: WHAT A KIND's FILES OWE, for ONE statement: `GoodIn` from the items that the block
    closes to those that it opens (`Piece.Own` of Spine.lean, at such meanings).
  `EachFramesSh`: what is owed for the shared items that ride past a block.
  `SpineOnce`: with these, extractors that read through the acting part (`EachExtBy`) and keep Rc
    (`EachKeeps`), lifted blocks and the test on the data: EVERY BLOCK OF THE STRETCH PAYS FOR EVERY N AT
    ITS OWN ERRORS (`EachPaysN`), between the relations "every open shared item holds, and Rc".

Limits. (1) A rule: μ, In, Out, Rc and the conditions are letters. (2) Those of SharedOnce.lean. (3) A
block that opens or closes an own item (the shared point) is not in such a stretch: it stands in front
of it, with a law of its own; In, Out and O₀ are of SHARED items alone, and `openAfter` runs over the
blocks in front of the stretch too: so that block's row is cut in two: its shared ins and outs stand
here, its own ones in its own law. (4) An item's meaning at border k and at border k + 1 are two functions:
the acting part behind a block shows the trees that the block has sent; `EachFramesSh` ties the two.
(5) `EachExtBy`: an extractor that decodes reads the members' words (the chain's own trees) and their
samples, the table and its record: AT THIS CHAIN THE LETTERS THAT READ SAMPLES AND RECORD OFF THE CARRIED
RECORD MUST READ THE CHAIN's OWN PART ALONE. (6) An own item may read a shared component of the witness
(the slot's row on Omega): `EachKeeps` then asks that no extractor of the stretch lays that component.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.SharedOnce
import Johnson.Desc.Sound.Spine

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open _root_.Iop (Reduction Err Shape IOR ExtSpec oneExternalString BTr Doomed)

variable {S Cl W ι : Type} {C : CK} {F : Frame}

/-- Every shared item of a set holds, at border k: read through the acting part there. -/
def relSh (act : ℕ → BKey F S) (μ : ι → ∀ k, (act k).1 → W → Prop) (O : ι → Prop) (k : ℕ) :
    S × F.E.Str → W → Prop :=
  fun a w => ∀ i, O i → μ i k ((act k).2 a) w

/-- **What a kind's files owe, for one statement**: from the shared items that the block closes to
those that it opens. -/
def EachOwnSh (on : ℕ → S × F.E.Str → Prop) (act : ℕ → BKey F S)
    (μ : ι → ∀ k, (act k).1 → W → Prop) (In Out : ℕ → ι → Prop) :
    ℕ → List (Piece C F S Cl W) → Prop
  | _, [] => True
  | k, p :: l =>
    p.GoodIn (on k) (on (k + 1)) (relSh act μ (In k) k) (relSh act μ (Out k) (k + 1)) ∧
      EachOwnSh on act μ In Out (k + 1) l

/-- What is owed for the shared items that ride past a block. Op k: the items open at border k. -/
def EachFramesSh (on : ℕ → S × F.E.Str → Prop) (act : ℕ → BKey F S)
    (μ : ι → ∀ k, (act k).1 → W → Prop) (In Op : ℕ → ι → Prop) :
    ℕ → List (Piece C F S Cl W) → Prop
  | _, [] => True
  | k, p :: l =>
    (∀ a τ b w i, on k a → p.ior.red.out a τ = some b → on (k + 1) b → Op k i → ¬ In k i →
      μ i (k + 1) ((act (k + 1)).2 b) w → μ i k ((act k).2 a) (p.ext a τ w)) ∧
      EachFramesSh on act μ In Op (k + 1) l

/-- **A stretch of the shared chain in which no own item is opened or closed is paid once.** i₀: the
place at which the stretch p :: l stands in the chain; In, Out, O₀: the whole chain's table of shared
items, numbered from the chain's first block. -/
def SpineOnce : Prop :=
  ∀ (S S₀ Cl W ι : Type) (C : CK) (F : Frame) (get : S → S₀) (set : S → S₀ → S) (lo N i₀ : ℕ)
    (act : ℕ → BKey F S) (p : Piece C F S Cl W) (l : List (Piece C F S Cl W))
    (on : ℕ → S × F.E.Str → Prop) (o : ∀ k, (act k).1 → Prop)
    (μ : ι → ∀ k, (act k).1 → W → Prop) (Rc : S × F.E.Str → W → Prop) (In Out : ℕ → ι → Prop)
    (O₀ : ι → Prop),
    (∀ k, act (i₀ + k) = actAt F get lo (hiAt k p l)) → Tiled p l →
    (∀ t s, get (set t s) = s) → (∀ t s s', set (set t s) s' = set t s') →
    (∀ q ∈ p :: l, ∃ b₀ : Block S₀ Cl, q.b = b₀.lift get set) →
    (∀ q ∈ p :: l, ∀ d ∈ q.ds, ∀ j ∈ d.opens, lo ≤ j) →
    (∀ k, i₀ < k → on k = fun a => o k ((act k).2 a)) →
    EachOwnSh on act μ In Out i₀ (p :: l) →
    EachFramesSh on act μ In (openAfter In Out O₀) i₀ (p :: l) →
    EachExtBy act i₀ (p :: l) → EachKeeps on Rc i₀ (p :: l) →
    EachPaysN N on (fun k a w => relSh act μ (openAfter In Out O₀ k) k a w ∧ Rc a w) act i₀
      (p :: l)

#check @SpineOnce

end VerifiableInference.Desc.Sound
