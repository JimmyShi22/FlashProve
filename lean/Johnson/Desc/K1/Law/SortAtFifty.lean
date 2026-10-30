-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/SortAtFifty.lean: the premise hSort of
hrest_plus13, brought down to ONE TEST WITH CODE on the public
parameters, by a fact on the closed list `mwMore` that Lean's kernel evaluates.
  `pC l`, `pD l`   the pieces at which the table has a segment's lookup on the calls and its lookup
                   on the digits: 2 and 7; at the head's segment (24) 3 and 8. Read off the print
                   of a file that is not in this library
  `lookIsB`, `lookPiecesB`, `lookPieces_mw`   [kernel] in front of each of the fifty places, every
                   open `lookOut` of the place's segment is at `pC l`, every open `lookIn` at `pD l`
  `sortB X`        THE TEST: by the public parameters X, at each of the 25 segments, `k3SortAt` says
                   "the lookup on the calls" at `pC l`, and names a lookup at `pD l`
  `hSort_of`       **hSort, to hrest_plus13's letter, from `sortB XV = true`**
  `sortTests_fail`   [kernel] `lookPiecesB` can fail: at another segment's pieces (the head's)
WHAT IS LEFT. `sortB XV = true`: a closed test once XV is written. It is evaluated nowhere here.
That `sortB` can refuse is not shown here: it reads `Desc.K3.pieceAt X`, a text not weighed here.
The recursion limit is raised in this file (maxRecDepth 1000000):
for the elaboration of the kernel's evaluations alone.
What is not claimed. Nothing on soundness.

-/
import Johnson.Desc.K1.Law.RestAtPlus13

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace VerifiableInference.Desc.K1
open Cb Johnson.Pack
open VerifiableInference.Desc.First (S ModelPart Item Pub Meaning Numbers More flatPlacesOf)
open VerifiableInference.Desc.First.Look (k3SortAt)
open VerifiableInference.Desc.Sound (linksFull MsgT MgData CellsQ)
open VerifiableInference.Desc.K13.Law (openAt)
open IM (k1Ix)

/-- The piece of a segment's lookup on the calls, by the table. -/
def pC (l : ℕ) : ℕ := if l == 24 then 3 else 2

/-- The piece of a segment's lookup on the digits, by the table. -/
def pD (l : ℕ) : ℕ := if l == 24 then 8 else 7

/-- A `lookOut` is at `pC l`, a `lookIn` at `pD l`. -/
def lookIsB (l : ℕ) : Pub → Bool
  | .lookOut _ pc => pc == pC l
  | .lookIn _ pc => pc == pD l
  | _ => true

/-- Every item of the lookups' three sorts, of segment l, that is open in front of sub-protocol k
passes c. -/
def lookPiecesB (M : More) (links : List ModelPart) (ps : List Place) (k l : ℕ) (c : Pub → Bool) :
    Bool :=
  ((First.pubSets M links ps)[k]?.getD [] ++ First.pubOfItems (openAt links ps k)).all fun q =>
    !lookAt l q || c q

theorem lookPieces_mw : ((List.range 25).all fun l => [false, true].all fun d =>
    lookPiecesB mwMore linksFull (flatPlacesOf linksFull true) (14 * l + k1Ix l d + 2) l
      (lookIsB l)) = true := by
  decide +kernel

/-- **The test can fail**: segment 3's open items are not at the head's pieces. -/
theorem sortTests_fail :
    lookPiecesB mwMore linksFull (flatPlacesOf linksFull true) (14 * 3 + k1Ix 3 true + 2) 3
      (lookIsB 24) = false := by
  decide +kernel

/-- **THE TEST on the public parameters.** -/
def sortB (X : OnBytes.Model.Verify.Public) : Bool :=
  (List.range 25).all fun l =>
    k3SortAt X l (pC l) == some false && (k3SortAt X l (pD l)).isSome

section
variable {Xi P Tok : Type} {rows cols nR : ℕ} {XV : OnBytes.Model.Verify.Public}
  (Dm : MgData Xi P Tok rows cols nR XV)

/-- **hSort, to hrest_plus13's letter.** -/
theorem hSort_of (hX : sortB XV = true) : ∀ l, l < 25 → ∀ d : Bool, ∀ q, lookAt l q = true →
    q ∈ (First.pubSets mwMore linksFull (flatPlacesOf linksFull true))[noL l d]?.getD [] ++
      First.pubOfItems (openAt linksFull (flatPlacesOf linksFull true) (noL l d)) →
    lookPaid Dm.pubD (dgsL d) q = true := by
  intro l hl d q hq hmem
  have h1 := List.all_eq_true.1 (List.all_eq_true.1 (List.all_eq_true.1 lookPieces_mw l
    (List.mem_range.2 hl)) d (by cases d <;> simp)) q hmem
  rw [hq] at h1
  have h2 : lookIsB l q = true := h1
  have h3 := List.all_eq_true.1 hX l (List.mem_range.2 hl)
  rw [Bool.and_eq_true, beq_iff_eq] at h3
  cases q with
  | linkFresh m => rfl
  | lookIn m pc =>
    have hq' : (m == l) = true := hq
    have h2' : (pc == pD l) = true := h2
    rw [eq_of_beq hq', eq_of_beq h2']
    exact h3.2
  | lookOut m pc =>
    have hq' : (m == l) = true := hq
    have h2' : (pc == pC l) = true := h2
    rw [eq_of_beq hq', eq_of_beq h2']
    show (k3SortAt XV l (pC l)).any (dgsL d) = true
    rw [h3.1]
    cases d <;> rfl
  | _ => cases hq

end

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.lookPieces_mw
#print axioms VerifiableInference.Desc.K1.sortTests_fail
#print axioms VerifiableInference.Desc.K1.hSort_of
