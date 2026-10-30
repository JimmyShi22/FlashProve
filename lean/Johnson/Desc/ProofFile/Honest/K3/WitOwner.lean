-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/WitOwner.lean: the honest side of the kind "lookup" (K3): the
filling of the letters `Sources` (Honest/K3/Wit.lean) that reads a borrowed matrix under its owner's
segment and name, at any number of groups. Definitions with code, and small theorems.

Terms. Honest/K3/GLOSSARY.md: see there owner and borrowed matrix, sources, seated filling, cells,
mark (of a borrowed entry) and link. In this file: a link's list of matrices holds matrices to which
an earlier link has committed: the stream that comes into a group of layers from the second group
on; attention's qa; the head's stream. The verifier's own plan says who owns a matrix: an entry of
the list (`TMat`, OnBytes/Model/Frame.lean) with kind = 1 is borrowed, and its field aId is 256
times the owning sub-proof's number plus the matrix's index in the owner's list. Every owner is a
group of layers, and the sub-proof of group g has the number 1 + g (`tailsOf`,
OnBytes/Model/LayerPlan.lean).

What is defined and shown.
  `ownerOf`, `atOwn`, `ownG`, `ownA`, `ownH`: who owns an entry of a link's list; the readings.
  `matsOwn`, `zzOwn`: the list of where the matrices of a link's smallness test are read; ZZ.
  `ownSources`, `tiedOwnSources`: the filling; the same with the head's shape and layout tied to the
    public part (`headPub`, Honest/K3/WitHead.lean).
  `ownerOf_own`, `atOwn_own`, `matsOwn_own`: where a link's list borrows nothing this is the reading
    of Honest/K3/WitPlan.lean and the list of Honest/K3/WitDigits.lean.
  `matsOwn_length`: the list is as long as the plan's list.
`ownerOf` and `matsOwn` have a second text in another file: `ownerKey`
(Honest/BorrowedOne.lean), over the library's
`First.Look.tlAt`. The two agree at a borrowed entry; at an own entry `ownerKey` has the first
column 0, this file `ttOff`. The ties: `ownerKey_seg`, `ownerKey_name`, and, where the entry is
borrowed or begins at column 0, `ownerKey_col` and `ownerKey_is`; of the list, where every entry is
so, `matsOwn_is` (all in Honest/K3/Law/OwnerKeyIs.lean).

Hypotheses that remain.
  `h`: (in the three theorems on what is not borrowed) the entry, or every entry of the list, has
    kind ≠ 1; in `atOwn_own` and `matsOwn_own` it also begins at column 0.

Imported. Beneath this file lie Honest/ForKinds.lean
(`Cells`), Honest/Frame.lean, Honest/Side.lean,
Honest/Sum.lean,
Honest/K8/Digits.lean (`zzOf`), Honest/K8/Part.lean and Johnson/HonestTrace/DigitsAtTrace.lean.

Users. Among the files that import this one: Honest/K3/LotFilled.lean, Honest/K3/WitFits.lean,
Honest/K3/Law/KeysAreKvG.lean and Honest/K3/Law/OwnerKeyIs.lean.

Limits. The reader of cells (`Cells`) is asked for a borrowed matrix under its owner's segment
and name: that is a rule of use; the Lean text of `Cells` does not say so, and it is not stated
as a theorem in this file. The filling of WitPlan.lean reads every matrix at the link itself.
That a plan's aId names the owner as said is read off the makers of the plans' lists; it is not
shown of what `Verify.publicOf` returns. Evaluated in part: Honest/K3/Law/WitOwnerMember.lean [not
in this library; so here read: not tested in this library]: `ownersOk`, a test with code for the
public hypothesis `PlanOwners`
(Honest/K3/Law/WitOwnerFull.lean), accepts at one synthetic public part at the full size's numbers.
What stays open: that public part is not what `Verify.publicOf` returns. An aId below 256 is taken
for that of group 0, and a mark beyond its owner's list yields the name "": the test `marksFitB`
(WitFits.lean) rejects such a list. A matrix number beyond the link's list reads 0:
the tests `namesFitB` and `featuresFitB` (WitFits.lean) reject the shapes at which a key or a bit
asks for one. The first column ttOff is added at an own matrix too: `marksFitB` asks that it be
0. No theorem on keys and bits is stated here at this filling: the theorems of
Honest/K3/WitFill.lean stand at readings under the borrower's segment and label, at a reader that
answers there too. Shown in part: Honest/K3/Law/WitOwnerFull.lean states them at this filling.
What stays open, by that file's own limits: they are conditional, and at the full size alone.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.WitHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3
open OnBytes.HonestTrace (fsAt)
open OnBytes.Road (Hd.shapeA)
open ProofFile.Honest.K8 (zzOf)

/-! ## 1 The owner, and the readings -/

/-- **Under which segment and name an entry of a link's list is read**: a borrowed one (kind = 1)
under its owner's: the link of the group of layers with the sub-proof's number aId / 256, and the
name of entry aId mod 256 of that link's list ("" beyond it); every other one at the link itself
under its own name. -/
def ownerOf (X : OnBytes.Model.Verify.Public) (link : ℕ) (M : OnBytes.Model.TMat) : ℕ × String :=
  if M.kind == 1 then
    (linkG X (M.aId / 256 - 1),
      (nameAt (tlOf X (linkG X (M.aId / 256 - 1))).mats (M.aId % 256)).getD "")
  else (link, M.name)

/-- The cell (r, c) of matrix number a of the link's list, in the extension field; 0 beyond the
list. A borrowed matrix begins at column ttOff of its owner's. -/
def atOwn (X : OnBytes.Model.Verify.Public) (cell : ℕ → String → ℕ → ℕ → Cb.Gl.F)
    (link a r c : ℕ) : Cb.Gl.E :=
  match (tlOf X link).mats[a]? with
  | some M =>
    algebraMap Cb.Gl.F Cb.Gl.E (cell (ownerOf X link M).1 (ownerOf X link M).2 r (M.ttOff + c))
  | none => 0

def ownG (X : OnBytes.Model.Verify.Public) (cell : ℕ → String → ℕ → ℕ → Cb.Gl.F)
    (entry : ℕ → ℕ → Cb.Gl.F) (link : ℕ) : OnBytes.Ends.G.NameG → Cb.Gl.E
  | .cell a r c => atOwn X cell link a r c
  | .w r c => algebraMap Cb.Gl.F Cb.Gl.E (entry r c)

def ownA (X : OnBytes.Model.Verify.Public) (cell : ℕ → String → ℕ → ℕ → Cb.Gl.F) (link : ℕ) :
    OnBytes.Ends.NameA → Cb.Gl.E := fun n => atOwn X cell link n.M n.r n.c

def ownH (X : OnBytes.Model.Verify.Public) (cell : ℕ → String → ℕ → ℕ → Cb.Gl.F)
    (entry : ℕ → ℕ → Cb.Gl.F) (link : ℕ) : OnBytes.Ends.H.NameH → Cb.Gl.E
  | .cell a r c => atOwn X cell link a r c
  | .w r c => algebraMap Cb.Gl.F Cb.Gl.E (entry r c)

/-! ## 2 The digits' list -/

/-- Where the matrices of a link's list are read: owner's segment, name there, first column there.
-/
def matsOwn (X : OnBytes.Model.Verify.Public) (link : ℕ) : List (ℕ × String × ℕ) :=
  (tlOf X link).mats.toList.map fun M => ((ownerOf X link M).1, (ownerOf X link M).2, M.ttOff)

/-- ZZ of the link's smallness test. -/
def zzOwn (X : OnBytes.Model.Verify.Public) (link : ℕ) (C : Cells) (ts : List Int) :
    ℕ → ℕ → Cb.Gl.F := zzOf (tlOf X link) (matsOwn X link) C ts

/-! ## 3 The filling -/

/-- **The filling: a borrowed matrix under its owner's segment and name.** -/
def ownSources {W₀ Xi Tr' : Type} (X : OnBytes.Model.Verify.Public) (cells : Tr' → Cells)
    (weights : W₀ → Weights) (pubH : Xi → OnBytes.Ends.H.PubH) : Sources W₀ Xi Tr' :=
  { cells := cells
    weights := weights
    layers := fun g C W =>
      ⟨fun theta n => OnBytes.Ends.G.keyG X.layers g (ownG X C.cell W.entry (linkG X g)) theta n,
       fun u j => OnBytes.Ends.G.bitsG X.y (ownG X C.cell W.entry (linkG X g)) (u * 32 + j)⟩
    attention := fun g C =>
      ⟨fun theta n =>
        OnBytes.Ends.A.keyA (Hd.shapeA X g) (fsAt X g) (ownA X C.cell (linkA X g)) theta n,
       fun u j =>
        OnBytes.Ends.A.bitsA (Hd.shapeA X g) (fsAt X g) (ownA X C.cell (linkA X g)) (u * 32 + j)⟩
    head := fun x C W =>
      ⟨fun theta n => OnBytes.Ends.H.keyH (pubH x) (ownH X C.cell W.entry (linkH X)) theta n,
       fun u j =>
        OnBytes.Ends.H.bitsH (pubH x).h (pubH x).L.fs (ownH X C.cell W.entry (linkH X))
          (u * 32 + j)⟩
    digits := fun link C ts => lookZ (tlOf X link) (zzOwn X link C ts) }

/-- **The same, the head tied.** Here req gives, of the instance, the covered positions and the
token that is checked at each. -/
def tiedOwnSources {W₀ Xi Tr' : Type} (X : OnBytes.Model.Verify.Public) (cells : Tr' → Cells)
    (weights : W₀ → Weights) (req : Xi → OnBytes.Model.Head.Covered × Array ℕ) :
    Sources W₀ Xi Tr' :=
  ownSources X cells weights fun x => headPub X (req x).1 (req x).2

/-! ## 4 Where nothing is borrowed -/

/-- An entry that is not borrowed is read at the link itself under its own name. -/
theorem ownerOf_own (X : OnBytes.Model.Verify.Public) (link : ℕ) (M : OnBytes.Model.TMat)
    (h : M.kind ≠ 1) : ownerOf X link M = (link, M.name) := by
  unfold ownerOf
  rw [if_neg (by simpa using h)]

/-- At an entry that is not borrowed and begins at column 0 the reading is that of
Honest/K3/WitPlan.lean. -/
theorem atOwn_own (X : OnBytes.Model.Verify.Public) (cell : ℕ → String → ℕ → ℕ → Cb.Gl.F)
    (link a r c : ℕ)
    (h : ∀ M, (tlOf X link).mats[a]? = some M → M.kind ≠ 1 ∧ M.ttOff = 0) :
    atOwn X cell link a r c = atMats (tlOf X link).mats cell link a r c := by
  unfold atOwn atMats nameAt
  cases hM : (tlOf X link).mats[a]? with
  | none => rfl
  | some M =>
    obtain ⟨h1, h2⟩ := h M hM
    show algebraMap Cb.Gl.F Cb.Gl.E (cell (ownerOf X link M).1 (ownerOf X link M).2 r (M.ttOff + c))
      =
      algebraMap Cb.Gl.F Cb.Gl.E (cell link M.name r c)
    rw [ownerOf_own X link M h1, h2, Nat.zero_add]

/-- Where a link's list borrows nothing, and each entry begins at column 0, the digits' list is that
of Honest/K3/WitDigits.lean. -/
theorem matsOwn_own (X : OnBytes.Model.Verify.Public) (link : ℕ)
    (h : ∀ M ∈ (tlOf X link).mats.toList, M.kind ≠ 1 ∧ M.ttOff = 0) :
    matsOwn X link = matsAt X link := by
  unfold matsOwn matsAt
  refine List.map_congr_left fun M hM => ?_
  obtain ⟨h1, h2⟩ := h M hM
  rw [ownerOf_own X link M h1, h2]

/-- The digits' list is as long as the plan's list. -/
theorem matsOwn_length (X : OnBytes.Model.Verify.Public) (link : ℕ) :
    (matsOwn X link).length = (tlOf X link).mats.size := by
  unfold matsOwn
  rw [List.length_map, Array.length_toList]

end ProofFile.Honest.K3

#print axioms ProofFile.Honest.K3.ownerOf_own
#print axioms ProofFile.Honest.K3.atOwn_own
#print axioms ProofFile.Honest.K3.matsOwn_own
#print axioms ProofFile.Honest.K3.matsOwn_length
