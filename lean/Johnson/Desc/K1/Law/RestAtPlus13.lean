-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/RestAtPlus13.lean: **hrest_plus13**:
the binder hrest of k01_law (Johnson/Desc/K1/Law/K01Law.lean), to the letter, at the wider meaning
`plus13 (d13 Dm) dk (mgAll Dm Mg₀)` over the composed meaning, and N := Dm.N: at an
accept of a later sending's sub-protocol, from inside the promise in front, every public item that
is open in front and behind and is none of the seven of `sevenItem` passes its test behind.
HOW. (a) A fact by evaluation in Lean's kernel, `rest_mw`: at the closed list `mwMore`,
at each of the fifty places, every such item lies in one of five
classes (`restClass`). The classes were read off a print of the evaluator
(in a file that is not in this library), and are held here by the kernel.
(b) One arm a class.
  the eight names of `cA13`   PAID: ClassAtLater.lean (five), DoorThreeAtLater.lean (three)
  `leftOn`                    PAID: its test is `true` (`First.pubAll_leftOn`)
  `hasRow`                    PAID: `pub_hasRow_later` over `KeepsRow` (HasRowAtPubAll.lean,
                              HasRowAtLater.lean, HasRowAtReads.lean)
  `linkFresh`, `lookIn`, `lookOut` of the place's own segment   PAID: `pub_look_later`,
                              UNDER TWO NAMED PREMISES: hh: behind an
                              accept at a link's reads nothing is heard at the digits' seat; hSort:
                              the pieces of the open lookIn | lookOut are the segment's two lookups'
                              by the public parameters (at the reads: lookOut's is the one on the
                              calls): a test on the public parameters alone
  "K5.okAt", "K5.plain" of the place's own segment   A NAMED PREMISE: hK5
TWO FORMS. `hrest_point`: hh and hK5 are asked at this x, x' and q alone, behind the accept and the
promise: the form to call. `hrest_plus13`: the binder to the letter, with both asked at every state
inside this meaning's promise: not shown meetable so.
THE OTHER PREMISES, BY NAME. hM: the base meaning's list of extra public tests is empty. hfB: the
test `Sound.bookFitsB` says `Book.BookFits`. hft: ONE equation: the number from which
"K12.bookInOrder" counts is the first tree of `gpOf Z` (all fifty places have that one: `parL_gp`).
hp, hs, hx: at each of the fifty, from the counts at the place on, dk's lists of seats, of trees'
shapes and of messages' shapes go on with what the place lays.
CAN THEY BE MET TOGETHER? NOT SHOWN HERE. hp, hs, hx ask ONE dk at all fifty places. The member that
is meant: dk.L, dk.M := the lists that the list of rounds' own sendings give, laid one behind the
other (`K12.Door.laidOfChain`); that such a list goes on at each sending is `laidOf_goes_on`
(K12/Coin/BookRides.lean). No example at the release's own values lies here.
  `restTests_fail`  [kernel] the test on the classes can fail: without the class of the eight names;
                    and at another segment's number
None of the five names that have left for good ("pile.room", "frame.liveIs", the approximate range
proof's three) is named as open, made, asked or dropped.
The recursion limit is raised in this file (maxRecDepth 1000000):
for the elaboration of the kernel's evaluations alone.
What is not claimed. hh, hSort, hK5, and the four equations, at any list of rounds. Nothing on
`pubP`.
Nothing on soundness.

-/
import Johnson.Desc.K1.Law.FillsAtPlus13
import Johnson.Desc.K1.Law.DoorAtPlus13
import Johnson.Desc.K1.Law.ClassAtLater
import Johnson.Desc.K1.Law.DoorThreeAtLater
import Johnson.Desc.K1.Law.LookAtLater
import Johnson.Desc.K1.Law.PubAtLaterCall
import Johnson.Desc.K1.Law.HasRowAtPubAll
import Johnson.Desc.K1.Law.HasRowAtReads

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model
open Cb Johnson.Pack
open VerifiableInference.Desc.First (S ModelPart Item Pub Meaning Numbers More flatPlacesOf)
open VerifiableInference.Desc.Sound (linksFull MsgT MgData CellsQ mgAll d13)
open VerifiableInference.Desc.Book (BookFits)
open VerifiableInference.Desc.K13.Law (openAt plus13 cA13)
open VerifiableInference.Desc.K12.Door (K12Data toTree)
open OnBytes.Model.Stages (LinkH)
open IM (k1Ix)

/-! ## 1 The classes, and the kernel's fact -/

/-- The lookups' three sorts of item, of segment l. -/
def lookAt (l : ℕ) : Pub → Bool
  | .linkFresh m => m == l
  | .lookIn m _ => m == l
  | .lookOut m _ => m == l
  | _ => false

def leftOnItem : Pub → Bool
  | .leftOn _ => true
  | _ => false

def hasRowItem : Pub → Bool
  | .hasRow _ => true
  | _ => false

/-- Attention's two names, of segment l. -/
def k5At (l : ℕ) : Pub → Bool
  | .more (some m) n => m == l && (n == "K5.okAt" || n == "K5.plain")
  | _ => false

/-- **The five classes.** -/
def restClass (l : ℕ) (q : Pub) : Bool :=
  cA13 q || lookAt l q || leftOnItem q || hasRowItem q || k5At l q

/-- Every item that is open in front of sub-protocol k and behind it, and is none of the seven,
passes c. -/
def restB (M : More) (links : List ModelPart) (ps : List Place) (k : ℕ) (c : Pub → Bool) : Bool :=
  ((First.pubSets M links ps)[k]?.getD [] ++ First.pubOfItems (openAt links ps k)).all fun q =>
    !openB M links ps (k + 1) q || sevenItem q || c q

theorem rest_of {M : More} {links : List ModelPart} {ps : List Place} {k : ℕ} {c : Pub → Bool}
    (h : restB M links ps k c = true) {q : Pub}
    (hq : q ∈ (First.pubSets M links ps)[k]?.getD [] ++ First.pubOfItems (openAt links ps k))
    (hq' : q ∈ (First.pubSets M links ps)[k + 1]?.getD [] ++
      First.pubOfItems (openAt links ps (k + 1))) (h7 : sevenItem q = false) : c q = true := by
  have h1 := List.all_eq_true.1 h q hq
  have h2 : openB M links ps (k + 1) q = true := List.contains_iff_mem.2 hq'
  rw [h2, h7] at h1
  exact h1

theorem rest_mw : ((List.range 25).all fun l => [false, true].all fun d =>
    restB mwMore linksFull (flatPlacesOf linksFull true) (14 * l + k1Ix l d + 2)
      (restClass l)) = true := by
  decide +kernel

/-- **The test can fail**: without the class of the eight names; and at another segment's number. -/
theorem restTests_fail :
    restB mwMore linksFull (flatPlacesOf linksFull true) (14 * 3 + k1Ix 3 true + 2)
      (fun q => lookAt 3 q || leftOnItem q || hasRowItem q || k5At 3 q) = false ∧
    restB mwMore linksFull (flatPlacesOf linksFull true) (14 * 3 + k1Ix 3 true + 2)
      (restClass 4) = false := by
  decide +kernel

/-! ## 2 Small steps -/

theorem keepsRow_blkL (Z : ProofFile.Pub) (G : ProofFile.Ground) (l : ℕ) (d : Bool) (X : LinkH)
    (arrs : Option (List ℕ)) : KeepsRow (blkL Z G l d X arrs) := by
  cases d with
  | true => exact keepsRow_laterAt _ _ _ _ _ _
  | false => exact keepsRow_k1Reads _ _ _ _ _ _

/-- All fifty places have one set of the chain's numbers. -/
theorem parL_gp (Z : ProofFile.Pub) (G : ProofFile.Ground) (l : ℕ) (d : Bool) :
    (parL Z G l d).gp = gpOf Z := by
  cases d <;> rfl

/-- The promise in front holds its own clause on the book. -/
theorem inAt_bookHeld {Pp W : Type} {N : Numbers} {Mg : Meaning Pp W} {links : List ModelPart}
    {ps : List Place} {k : ℕ} {x : Pp × S} {y : Strs} (h : InAt N Mg links ps k x y) :
    First.bookAt N ps[k]? x.2 = true := by
  obtain ⟨⟨_, hr⟩, hm⟩ := h
  rcases hr with hx | ⟨h1, _, _, _⟩
  · exact absurd hm hx
  · simp only [Bool.and_eq_true] at h1
    exact h1.2

/-! ## 3 The binder -/

section
variable {Xi Tok : Type} {rows cols nR : ℕ} {XV : OnBytes.Model.Verify.Public}
  (Dm : MgData Xi ProofFile.InstPub Tok rows cols nR XV) (dk : K12Data)
  (Mg₀ : Meaning ProofFile.InstPub (Wit (CellsQ rows cols) Tok MsgT))

/-- **THE BINDER hrest OF k01_law AT THE WIDER MEANING, POINTWISE**: what has no lemma yet is asked
at this x, x' and q alone, behind the accept and the promise. -/
theorem hrest_point (hM : Mg₀.more = {}) (Z : ProofFile.Pub) (Bs : ProofFile.PureBase)
    (hfB : ∀ B, Sound.bookFitsB B = true ↔ BookFits B)
    (hft : dk.ft = (gpOf Z).firstTree)
    (hp : ∀ l, l < 25 → ∀ d : Bool,
      ((toTree dk.L).places.drop (Dm.N.msgsAt (flatPlacesOf linksFull true)[noL l d]?)).take
          (parL Z Bs.G₀ l d).sent.size =
        K12.Coin.placesOf (Dm.N.treesAt (flatPlacesOf linksFull true)[noL l d]?)
          (parL Z Bs.G₀ l d).sent.size (layOf (parL Z Bs.G₀ l d)))
    (hs : ∀ l, l < 25 → ∀ d : Bool,
      ((toTree dk.L).shapes.drop (Dm.N.treesAt (flatPlacesOf linksFull true)[noL l d]?)).take
          (layOf (parL Z Bs.G₀ l d)).shapes.size = (layOf (parL Z Bs.G₀ l d)).shapes.toList)
    (hx : ∀ l, l < 25 → ∀ d : Bool,
      (dk.M.drop (Dm.N.msgsAt (flatPlacesOf linksFull true)[noL l d]?)).take
          (shapesOf (parL Z Bs.G₀ l d)).length = shapesOf (parL Z Bs.G₀ l d))
    (hSort : ∀ l, l < 25 → ∀ d : Bool, ∀ q, lookAt l q = true →
      q ∈ (First.pubSets mwMore linksFull (flatPlacesOf linksFull true))[noL l d]?.getD [] ++
        First.pubOfItems (openAt linksFull (flatPlacesOf linksFull true) (noL l d)) →
      lookPaid Dm.pubD (dgsL d) q = true) :
    ∀ l, l < 25 → ∀ d : Bool, ∀ X arrs, Bs.G₀.built[l]? = some X → ∀ x x' y q,
      YesOf (blkL Z Bs.G₀ l d X arrs) x x' →
      InAt Dm.N (plus13 (d13 Dm) dk (mgAll Dm Mg₀)) linksFull (flatPlacesOf linksFull true)
        (noL l d) x y →
      hhL d x'.2 →
      (k5At l q = true → (plus13 (d13 Dm) dk (mgAll Dm Mg₀)).pub q x = true →
        (plus13 (d13 Dm) dk (mgAll Dm Mg₀)).pub q x' = true) →
      q ∈ (First.pubSets (plus13 (d13 Dm) dk (mgAll Dm Mg₀)).more linksFull
          (flatPlacesOf linksFull true))[noL l d]?.getD [] ++
        First.pubOfItems (openAt linksFull (flatPlacesOf linksFull true) (noL l d)) →
      q ∈ (First.pubSets (plus13 (d13 Dm) dk (mgAll Dm Mg₀)).more linksFull
          (flatPlacesOf linksFull true))[noL l d + 1]?.getD [] ++
        First.pubOfItems (openAt linksFull (flatPlacesOf linksFull true) (noL l d + 1)) →
      sevenItem q = false → (plus13 (d13 Dm) dk (mgAll Dm Mg₀)).pub q x' = true := by
  intro l hl d X arrs _ x x' y q hy hIn hH hK5 hq hq' h7
  have h0 := inAt_pub hIn q hq
  rw [plus13_more_closed Dm dk Mg₀ hM] at hq hq'
  have hc : restClass l q = true :=
    rest_of (List.all_eq_true.1 (List.all_eq_true.1 rest_mw l (List.mem_range.2 hl)) d
      (by cases d <;> simp)) hq hq' h7
  have hy' := hy
  obtain ⟨_, rs, gs, hfit, hd⟩ := hy'
  have hlen : (rs.map noDigest).length = 2 := by
    rw [List.length_map, Keeps.fit_length _ _ hfit, rounds_blkL]
  have hB := laterSeated_blkL Z Bs.G₀ l d X arrs
  have hbk := inAt_bookHeld hIn
  unfold restClass at hc
  simp only [Bool.or_eq_true] at hc
  rcases hc with (((hc | hc) | hc) | hc) | hc
  · rcases class_names q hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact masks_later _ dk _ hy h0
    · exact within_later _ dk _ hy h0
    · exact oneRow_later _ dk _ hy
    · exact weights_later _ dk _ hy h0
    · exact book_later _ dk _ hB x x' _ gs hlen hd (by rw [parL_gp]; exact hft) h0
    · exact seats_later _ dk _ hB x x' _ gs hlen hd Dm.N _ hbk (hp l hl d) (hs l hl d) h0
    · exact shapes_later _ dk _ hB x x' _ gs hlen hd Dm.N _ hbk (hx l hl d) h0
    · exact fits_later _ dk _ hfB hy h0
  · rw [pub_plus13] at h0 ⊢
    exact pub_look_later (laterLook_blkL Z Bs.G₀ l d X arrs) Dm.pubD _ x x' _ gs hlen hd hH q
      (hSort l hl d q hc hq) h0
  · cases q with
    | leftOn m =>
      rw [pub_plus13]
      rfl
    | _ => cases hc
  · cases q with
    | hasRow m =>
      rw [pub_plus13] at h0 ⊢
      exact pub_hasRow_later (keepsRow_blkL Z Bs.G₀ l d X arrs) _ _ m x x' _ gs hd h0
    | _ => cases hc
  · exact hK5 hc h0

/-- **THE BINDER hrest OF k01_law, TO THE LETTER, AT THE WIDER MEANING**: `hrest_point`, with its
two pointwise premises asked at every state inside the promise. NOT SHOWN MEETABLE IN THIS FORM:
that promise may not hold what pays hh and hK5. -/
theorem hrest_plus13 (hM : Mg₀.more = {}) (Z : ProofFile.Pub) (Bs : ProofFile.PureBase)
    (hfB : ∀ B, Sound.bookFitsB B = true ↔ BookFits B)
    (hft : dk.ft = (gpOf Z).firstTree)
    (hp : ∀ l, l < 25 → ∀ d : Bool,
      ((toTree dk.L).places.drop (Dm.N.msgsAt (flatPlacesOf linksFull true)[noL l d]?)).take
          (parL Z Bs.G₀ l d).sent.size =
        K12.Coin.placesOf (Dm.N.treesAt (flatPlacesOf linksFull true)[noL l d]?)
          (parL Z Bs.G₀ l d).sent.size (layOf (parL Z Bs.G₀ l d)))
    (hs : ∀ l, l < 25 → ∀ d : Bool,
      ((toTree dk.L).shapes.drop (Dm.N.treesAt (flatPlacesOf linksFull true)[noL l d]?)).take
          (layOf (parL Z Bs.G₀ l d)).shapes.size = (layOf (parL Z Bs.G₀ l d)).shapes.toList)
    (hx : ∀ l, l < 25 → ∀ d : Bool,
      (dk.M.drop (Dm.N.msgsAt (flatPlacesOf linksFull true)[noL l d]?)).take
          (shapesOf (parL Z Bs.G₀ l d)).length = shapesOf (parL Z Bs.G₀ l d))
    (hSort : ∀ l, l < 25 → ∀ d : Bool, ∀ q, lookAt l q = true →
      q ∈ (First.pubSets mwMore linksFull (flatPlacesOf linksFull true))[noL l d]?.getD [] ++
        First.pubOfItems (openAt linksFull (flatPlacesOf linksFull true) (noL l d)) →
      lookPaid Dm.pubD (dgsL d) q = true)
    (hh : ∀ l, l < 25 → ∀ X arrs, Bs.G₀.built[l]? = some X → ∀ x x' y,
      YesOf (blkL Z Bs.G₀ l false X arrs) x x' →
      InAt Dm.N (plus13 (d13 Dm) dk (mgAll Dm Mg₀)) linksFull (flatPlacesOf linksFull true)
        (noL l false) x y → HeardNone x'.2)
    (hK5 : ∀ l, l < 25 → ∀ d : Bool, ∀ X arrs, Bs.G₀.built[l]? = some X → ∀ x x' y q,
      YesOf (blkL Z Bs.G₀ l d X arrs) x x' →
      InAt Dm.N (plus13 (d13 Dm) dk (mgAll Dm Mg₀)) linksFull (flatPlacesOf linksFull true)
        (noL l d) x y → k5At l q = true →
      (plus13 (d13 Dm) dk (mgAll Dm Mg₀)).pub q x = true →
      (plus13 (d13 Dm) dk (mgAll Dm Mg₀)).pub q x' = true) :
    ∀ l, l < 25 → ∀ d : Bool, ∀ X arrs, Bs.G₀.built[l]? = some X → ∀ x x' y q,
      YesOf (blkL Z Bs.G₀ l d X arrs) x x' →
      InAt Dm.N (plus13 (d13 Dm) dk (mgAll Dm Mg₀)) linksFull (flatPlacesOf linksFull true)
        (noL l d) x y →
      q ∈ (First.pubSets (plus13 (d13 Dm) dk (mgAll Dm Mg₀)).more linksFull
          (flatPlacesOf linksFull true))[noL l d]?.getD [] ++
        First.pubOfItems (openAt linksFull (flatPlacesOf linksFull true) (noL l d)) →
      q ∈ (First.pubSets (plus13 (d13 Dm) dk (mgAll Dm Mg₀)).more linksFull
          (flatPlacesOf linksFull true))[noL l d + 1]?.getD [] ++
        First.pubOfItems (openAt linksFull (flatPlacesOf linksFull true) (noL l d + 1)) →
      sevenItem q = false → (plus13 (d13 Dm) dk (mgAll Dm Mg₀)).pub q x' = true := by
  intro l hl d X arrs hX x x' y q hy hIn
  refine hrest_point Dm dk Mg₀ hM Z Bs hfB hft hp hs hx hSort l hl d X arrs hX x x' y q hy hIn ?_
    (hK5 l hl d X arrs hX x x' y q hy hIn)
  cases d with
  | true => trivial
  | false => exact hh l hl X arrs hX x x' y hy hIn

end

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.rest_mw
#print axioms VerifiableInference.Desc.K1.restTests_fail
#print axioms VerifiableInference.Desc.K1.hrest_point
#print axioms VerifiableInference.Desc.K1.hrest_plus13
