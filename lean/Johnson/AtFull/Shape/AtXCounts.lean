-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Shape/AtXCounts.lean: A TEST AT THE WHOLE PUBLIC RECORD OF THE STORED FULL-SIZE FILES
(`atXL`, `atXH`, AtX.lean) WITH THE LAYERS' LAYOUT's COUNTS OF PADDING KEYS LAID IN NUMERALS:
`atXLC`, `atXHC`; AND THAT AN ACCEPT STILL SPEAKS OF WHAT publicOfO RETURNS. Two definitions of
tests, one of a record, four laws; nothing is evaluated here.

What it is for. Under atXL the layout's field fo.pub stands as a closed term that folds over all
placed calls (`pubOf`, Johnson/AtFull/Public/Owners.lean: "a closed term that no fact here opens").
A test that compares these counts makes whoever evaluates it run that fold. The library has the
counts in numerals by a law (`counts_yFull`, Johnson/AtFull/K3X/CountsAtFull.lean: yFull.fo.pub =
pubW 0 false). Here the numerals are laid into the record in front of the test, and the law carries
the accept back.

Main names.
* `withCounts X`: X with layers.y.fo.pub := pubW 0 false (sixteen numerals,
  Johnson/AtFull/Desc/Lots/K3Written.lean). **`withCounts_eq`**: X.layers.y = yFull ⊢ withCounts X =
  X.
* `y_at_zFull`: what publicOfO returns at VerifierAndGoals.storedPublicFiles's files has the layout yFull (out of the
  library's join, `publicOfO_zFull_of_rest`).
* **`atXLC t`** := atXL fun X => t (withCounts X); **`atXHC t`** likewise over atXH.
  **`atXLC_zFull`**, **`atXHC_zFull`**: an accept ⊢ ∃ X₀, publicOfO … = .ok X₀ ∧ t X₀ = true: at X₀
  itself, not at withCounts X₀.

Limits. UNDER hsz, the stored layout file's size, as in AtX.lean. No test is shown to accept.
withCounts_eq's premise (the whole layout is the written one) is stronger than its conclusion needs:
X.layers.y.fo.pub = pubW 0 false is enough. Whether a given test is light under these two is not
said here. One field is laid in numerals; every other field of the record stands as in AtX.lean. The
full size alone. At the format's second hash function. Nothing on soundness, completeness or hiding.
-/
import Johnson.AtFull.Shape.AtX
import Johnson.AtFull.K3X.CountsAtFull

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape
open OnBytes OnBytes.Model OnBytes.Model.Verify
open OnBytes.Road.K4.Trial.Values (yFull)
open VerifiableInference.PlanWritten (publicOfO)
open Johnson.AtFull.Lots.K3 (pubW)

/-- The public record with the layers' layout's counts of padding keys in numerals. -/
def withCounts (X : Verify.Public) : Verify.Public :=
  { X with layers := { X.layers with y := { X.layers.y with
      fo := { X.layers.y.fo with pub := pubW 0 false } } } }

/-- **At the layout that stands by name nothing turns.** -/
theorem withCounts_eq {X : Verify.Public} (hy : X.layers.y = yFull) : withCounts X = X := by
  have hp : X.layers.y.fo.pub = pubW 0 false := by
    rw [hy]
    exact Johnson.AtFull.K3X.counts_yFull
  unfold withCounts
  rw [← hp]

/-- **What publicOfO returns at the stored full-size files has that layout.** -/
theorem y_at_zFull (hsz : VerifierAndGoals.storedPublicFiles.lay.size = 224975) {X₀ : Verify.Public}
    (h : publicOfO OnBytes.secondHashFunction VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.KL (some VerifierAndGoals.storedPublicFiles.lay) =
      .ok X₀) :
    X₀.layers.y = yFull := by
  obtain ⟨sc, wsLay, HLy, l, ps, layers, G, seenA, owner, e1, e2, ⟨e3, -, -⟩, e4, ⟨e5, -⟩, e6, e7,
    e8, -, ⟨e9, -⟩, hX⟩ := _root_.AtFull.Public.publicOfO_zFull_of_rest hsz
  obtain rfl := Except.ok.inj (h.symm.trans hX)
  exact OnBytes.Road.Hd.pubOf_y e6

/-- **A test at the whole public record, the counts of padding keys in numerals**; of the head's
layout and of the owner nothing is asked; the attention's lines are asked once, by atMakers itself.
-/
def atXLC (t : Verify.Public → Bool) : Bool := atXL fun X => t (withCounts X)

/-- The same with the head's layout bound by the library's withLaid. -/
def atXHC (t : Verify.Public → Bool) : Bool := atXH fun X => t (withCounts X)

/-- **An accept speaks of what publicOfO returns at the stored full-size files.** -/
theorem atXLC_zFull (hsz : VerifierAndGoals.storedPublicFiles.lay.size = 224975) {t : Verify.Public → Bool}
    (h : atXLC t = true) :
    ∃ X₀ : Verify.Public,
      publicOfO OnBytes.secondHashFunction VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.KL (some VerifierAndGoals.storedPublicFiles.lay) = .ok X₀ ∧
      t X₀ = true := by
  obtain ⟨X₀, hX, ht⟩ := atXL_zFull hsz h
  rw [withCounts_eq (y_at_zFull hsz hX)] at ht
  exact ⟨X₀, hX, ht⟩

/-- **The same from a line under atXHC.** -/
theorem atXHC_zFull (hsz : VerifierAndGoals.storedPublicFiles.lay.size = 224975) {t : Verify.Public → Bool}
    (h : atXHC t = true) :
    ∃ X₀ : Verify.Public,
      publicOfO OnBytes.secondHashFunction VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.KL (some VerifierAndGoals.storedPublicFiles.lay) = .ok X₀ ∧
      t X₀ = true := by
  obtain ⟨X₀, hX, ht⟩ := atXH_zFull hsz h
  rw [withCounts_eq (y_at_zFull hsz hX)] at ht
  exact ⟨X₀, hX, ht⟩

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.withCounts_eq
#print axioms Johnson.AtFull.Shape.y_at_zFull
#print axioms Johnson.AtFull.Shape.atXLC_zFull
#print axioms Johnson.AtFull.Shape.atXHC_zFull
#print axioms Johnson.AtFull.Shape.withCounts
#print axioms Johnson.AtFull.Shape.atXLC
#print axioms Johnson.AtFull.Shape.atXHC
