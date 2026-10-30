-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/Sound/KeyAtFK.lean: It stands on the key file's description
Johnson/Desc/Key/Desc.lean.
THE KEY FILE'S OWN DESCRIPTION
AT THE RECORDS, AND ITS FIRST ROW.

The setting. The key file's own description `Key.descriptionFromSource X N P` has the table's key as its instance
(`Key.Xi`). The library's frame wants a description at the records (`RecFull`).

What is said.
  `keyInstanceOfOutOfDomainSample`: a record's instance: the program's key written of it (`keyOf`,
    OnBytes/Slice/KeyOfRec.lean). `instK_injective`: two records with one instance are one
    (`keyOf_injective`).
  `FK X N P`: THE KEY FILE'S OWN DESCRIPTION AT THE RECORDS: `(Key.descriptionFromSource X N P).pull keyInstanceOfOutOfDomainSample`.
  `firstRow`: THE FIRST ROW, FILLED: the joint "no collision at the record's seed; decodes with the
    record", the instance read out of the carried record's first part, the guard `onImage` as its
    invariant. `first_on`, `first_rel`: THE FIRST ROW'S TWO FACTS ARE THEOREMS AT `FK`.

Limits. NO SEAT IS FILLED HERE. X, N, P are letters: that they are made of a plan is not asked.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Key.Link
import Johnson.Desc.Key.Chain1
import Johnson.Desc.Key.FileOk
import Johnson.Desc.Key.Slot
import Johnson.Desc.Sound.KeyRowsAnyDepth
import Johnson.Desc.Sound.KeyAtSizes
import OnBytes.Slice.KeyOfRecInj
import Johnson.Desc.Sound.KeyRowsOfPieces
import Johnson.Desc.Sound.PaidAtDesc

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped ENNReal

noncomputable section

namespace Johnson.RunOne.Sound
open VerifiableInference.Desc VerifiableInference.Desc.Sound
open VerifiableInference.OnPublicFiles OnBytes.Flat OnBytes.Slice OnBytes.RunA OnBytes.Maker
open VerifiableInference.Desc.Key (Xi)
open VerifiableInference.Desc.Key (descriptionFromSource Source keyInstanceOfOutOfDomainSample)
open _root_.Run (ckP)
open KObj (jWf)

theorem instK_injective : Function.Injective keyInstanceOfOutOfDomainSample := fun r r' h =>
  keyOf_injective (fun β : NZ => β.val) Subtype.val_injective (congrArg Key.Xi.key h)

/-- **The key file's own description at the records.** -/
def FK (X : Key.Source) (N : H2U.PlaceNums) (P : Key.LaterPlaces) : FileDescription RecFull :=
  (Key.descriptionFromSource X N P).pull keyInstanceOfOutOfDomainSample

variable {Xr : Type} {A : (frS.toDecR frZ 402653181).Claims Xr} {E : Coding A}
  (X : Key.Source) (N : H2U.PlaceNums) (P : Key.LaterPlaces)

theorem FK_pub_injective : Function.Injective (FK X N P).pub := instK_injective

local notation "Kc" => lettersAt A (relationsAndEncodingOfClaims A E)

/-- **The first row, filled.** -/
def firstRow (A : (frS.toDecR frZ 402653181).Claims Xr) (E : Coding A) (DK : WholeD)
    (all : List LeftT) (ft : ℕ) (rec₀ : RecFull) :
    JointRow ((FK X N P).XiPub × (FK X N P).S₁)
      (frameAt (DK.at frS.P.T.a) all (DK.at frS.P.T.a).key₁ ft) :=
  JointRow.first (lettersAt A (relationsAndEncodingOfClaims A E)) (FK X N P).pub rec₀ (onImage (FK X N P).pub)

theorem first_on (DK : WholeD) (all : List LeftT) (ft : ℕ) (rec₀ rec : RecFull)
    (y : (Kc).conf.E0.Str) (hc : ¬ (Kc).conf.coll y rec.1) :
    (firstRow X N P A E DK all ft rec₀).on
      (((FK X N P).pub rec, (FK X N P).start₁ ((FK X N P).pub rec)), (y, fun _ => [])) := by
  refine ⟨?_, onImage_first _ rec _ _⟩
  show (jWf (Kc).conf).on ((firstRow X N P A E DK all ft rec₀).rd _)
  rw [show (firstRow X N P A E DK all ft rec₀).rd
      (((FK X N P).pub rec, (FK X N P).start₁ ((FK X N P).pub rec)), (y, fun _ => [])) =
      (rec, y) from first_reads (Kc) _ (FK_pub_injective X N P) rec₀ _ rec _ _]
  exact hc

theorem first_rel (DK : WholeD) (all : List LeftT) (ft : ℕ) (rec₀ rec : RecFull)
    (y : (Kc).conf.E0.Str)
    (hr : (firstRow X N P A E DK all ft rec₀).rel
      (((FK X N P).pub rec, (FK X N P).start₁ ((FK X N P).pub rec)), (y, fun _ => []))) :
    (Kc).conf.D y rec ≠ none := by
  obtain ⟨w, hw⟩ := hr
  have hw' : (jWf (Kc).conf).relR ((firstRow X N P A E DK all ft rec₀).rd
      (((FK X N P).pub rec, (FK X N P).start₁ ((FK X N P).pub rec)), (y, fun _ => []))) w :=
    hw
  rw [show (firstRow X N P A E DK all ft rec₀).rd
      (((FK X N P).pub rec, (FK X N P).start₁ ((FK X N P).pub rec)), (y, fun _ => [])) =
      (rec, y) from first_reads (Kc) _ (FK_pub_injective X N P) rec₀ _ rec _ _] at hw'
  exact Option.isSome_iff_ne_none.1 hw'

end Johnson.RunOne.Sound

#print axioms Johnson.RunOne.Sound.instK_injective
#print axioms Johnson.RunOne.Sound.first_on
#print axioms Johnson.RunOne.Sound.first_rel
#print axioms Johnson.RunOne.Sound.FK_pub_injective
