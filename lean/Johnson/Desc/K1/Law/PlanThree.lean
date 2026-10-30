-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/PlanThree.lean: what the proximity
test's data `dk : K12Data` must be for hrest_plus13 (Johnson/Desc/K1/Law/RestAtPlus13.lean), and its premises
hp, hs, hx as ONE TEST WITH CODE on the list of rounds.
  `dkOfChain ft c`, `dkOf Z`   **the member that is meant**: ft := the first tree of `gpOf Z`; L :=
                   the first chain's own sendings laid one behind the other
                   (`K12.Door.laidOfChain`); M := their messages' shapes in turn
                   (`K12.Door.msgsOfChain`); both off `Z.made.proof.1`, the list of sendings that
                   the planner's structure holds for the first chain. `none` where a sending's
                   trees cannot be laid
  `dkOf_ft`        so hft holds of it, by its make
  `goesOnB dk N p P`   at ONE place: from the counts `N.msgsAt p`, `N.treesAt p` on, dk's three
                   lists go on with what a sending of P lays. `goesOn_of`: what its accept says:
                   hp, hs, hx
  `planThreeB dk N Z G`   that test at all fifty later places; `goesOn_at`
  `hrest_plus13_plan`   **hrest_plus13 with the three equations replaced by the one test**
  `goesOn_fails`   the test can fail: at an empty list M it refuses every P that sends a message
WHAT THIS DOES AND DOES NOT DO FOR "ONE dk AT ALL FIFTY". It brings the question down to the value
of one closed test at the release's own public files: `planThreeB dk N Z G` has code and reads
nothing but dk, the table's numbers N, the public part Z and G.first. IT IS EVALUATED NOWHERE HERE:
that it says true at `dkOf Z` and the release's N is not shown. No theorem in scope says so either.

(Where this and lean/THEOREM.md differ, the page holds.)
What is not claimed. Nothing on soundness.

-/
import Johnson.Desc.K1.Law.RestAtPlus13

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model
open Cb Johnson.Pack
open VerifiableInference.Desc.First (S ModelPart Item Pub Meaning Numbers More flatPlacesOf)
open VerifiableInference.Desc.Sound (linksFull MsgT MgData CellsQ mgAll d13)
open VerifiableInference.Desc.Book (BookFits)
open VerifiableInference.Desc.K13.Law (openAt plus13)
open VerifiableInference.Desc.K12.Door (K12Data toTree laidOfChain msgsOfChain)
open OnBytes.Model.Stages (LinkH)

/-! ## 1 The member that is meant -/

/-- The proximity test's data off a chain's list of sendings. -/
def dkOfChain (ft : ℕ) (c : Johnson.G.ChainSends) : Option K12Data :=
  (laidOfChain c).map fun L => ⟨ft, L, msgsOfChain c⟩

/-- **The member that is meant**: off the public part's own list of the first chain's sendings. -/
def dkOf (Z : ProofFile.Pub) : Option K12Data := dkOfChain (gpOf Z).firstTree Z.made.proof.1

theorem dkOf_ft {Z : ProofFile.Pub} {dk : K12Data} (h : dkOf Z = some dk) :
    dk.ft = (gpOf Z).firstTree := by
  unfold dkOf dkOfChain at h
  obtain ⟨L, _, rfl⟩ := Option.map_eq_some_iff.1 h
  rfl

/-! ## 2 The test -/

/-- At one place: dk's three lists go on with what a sending of P lays. -/
def goesOnB (dk : K12Data) (N : Numbers) (p : Option Place) (P : Par) : Bool :=
  ((toTree dk.L).places.drop (N.msgsAt p)).take P.sent.size ==
      K12.Coin.placesOf (N.treesAt p) P.sent.size (layOf P) &&
    ((toTree dk.L).shapes.drop (N.treesAt p)).take (layOf P).shapes.size ==
      (layOf P).shapes.toList &&
    (dk.M.drop (N.msgsAt p)).take (shapesOf P).length == shapesOf P

theorem goesOn_of {dk : K12Data} {N : Numbers} {p : Option Place} {P : Par}
    (h : goesOnB dk N p P = true) :
    ((toTree dk.L).places.drop (N.msgsAt p)).take P.sent.size =
        K12.Coin.placesOf (N.treesAt p) P.sent.size (layOf P) ∧
      ((toTree dk.L).shapes.drop (N.treesAt p)).take (layOf P).shapes.size =
        (layOf P).shapes.toList ∧
      (dk.M.drop (N.msgsAt p)).take (shapesOf P).length = shapesOf P := by
  unfold goesOnB at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

/-- **The test can fail**: at an empty list of messages' shapes it refuses every P that sends. -/
theorem goesOn_fails (ft : ℕ) (L : K12.Door.Laid) (N : Numbers) (p : Option Place) (P : Par)
    (hP : shapesOf P ≠ []) : goesOnB ⟨ft, L, []⟩ N p P = false := by
  cases h : goesOnB ⟨ft, L, []⟩ N p P with
  | false => rfl
  | true =>
    have e := (goesOn_of h).2.2
    rw [List.drop_nil, List.take_nil] at e
    exact absurd e.symm hP

/-- The test at all fifty later places. -/
def planThreeB (dk : K12Data) (N : Numbers) (Z : ProofFile.Pub) (G : ProofFile.Ground) : Bool :=
  (List.range 25).all fun l => [false, true].all fun d =>
    goesOnB dk N (flatPlacesOf linksFull true)[noL l d]? (parL Z G l d)

theorem goesOn_at {dk : K12Data} {N : Numbers} {Z : ProofFile.Pub} {G : ProofFile.Ground}
    (h : planThreeB dk N Z G = true) (l : ℕ) (hl : l < 25) (d : Bool) :
    goesOnB dk N (flatPlacesOf linksFull true)[noL l d]? (parL Z G l d) = true :=
  List.all_eq_true.1 (List.all_eq_true.1 h l (List.mem_range.2 hl)) d (by cases d <;> simp)

/-! ## 3 The binder, under the one test -/

section
variable {Xi Tok : Type} {rows cols nR : ℕ} {XV : OnBytes.Model.Verify.Public}
  (Dm : MgData Xi ProofFile.InstPub Tok rows cols nR XV) (dk : K12Data)
  (Mg₀ : Meaning ProofFile.InstPub (Wit (CellsQ rows cols) Tok MsgT))

/-- **hrest_plus13 with hp, hs, hx replaced by the one test.** -/
theorem hrest_plus13_plan (hM : Mg₀.more = {}) (Z : ProofFile.Pub) (Bs : ProofFile.PureBase)
    (hfB : ∀ B, Sound.bookFitsB B = true ↔ BookFits B)
    (hft : dk.ft = (gpOf Z).firstTree) (hPlan : planThreeB dk Dm.N Z Bs.G₀ = true)
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
      sevenItem q = false → (plus13 (d13 Dm) dk (mgAll Dm Mg₀)).pub q x' = true :=
  hrest_plus13 Dm dk Mg₀ hM Z Bs hfB hft
    (fun l hl d => (goesOn_of (goesOn_at hPlan l hl d)).1)
    (fun l hl d => (goesOn_of (goesOn_at hPlan l hl d)).2.1)
    (fun l hl d => (goesOn_of (goesOn_at hPlan l hl d)).2.2) hSort hh hK5

end

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.dkOf_ft
#print axioms VerifiableInference.Desc.K1.goesOn_of
#print axioms VerifiableInference.Desc.K1.goesOn_fails
#print axioms VerifiableInference.Desc.K1.hrest_plus13_plan
