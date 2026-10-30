-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Flat/BigIns.lean: concrete input data (`FilesParameters`, OnBytes/Flat/FilesAt.lean) for the definitions
of the key-file and proof-file protocols, built from a planner's result, and facts that connect this
data to a call that the Lean verifier program accepts.

`bigIns pl Pz hV rec₀ r₁` is `bigAt` (OnBytes/Flat/BigAt.lean) with three fields filled in: the
first chain's block is `(pubOf pl Pz hV).block`; the fixed instance used for dry runs is
`firstInstance Pz hV`; the early part of an instance is the instance with its reply set to 0. The
two sample records rec₀ and r₁ remain parameters.
  `atPlan_bigIns`: where `planOf Z = .ok pl`, this data is at Z's plan (`AtPlan Z`). `early_full`,
    `early_small`: the early part of the three files' own object at this data is `withoutReply hV`,
    by unfolding.
  `block_formed`: at an instance with r < e (and y = 0 if e is before the window's end), where
    0 < Pz.V, `sizesAt pol = .ok Pz` and the planner returns pl, the block
    `(pubOf pl Pz hV).block` is `blockAt pl links₀ so₀.y` for some so₀, cov₀, links₀ at which the
    program's second and third computations return. That so₀ is what the first computation returns
    is not in the statement.
  `hblk_bigIns`: for an accepted call whose statement satisfies Sv, the block of this data at the
    call's instance (`insOf Pz`) is `blockAt` at whatever the program's plan and its three
    computations return.
  `hitm_full`, `hitm_small`: there `(holdsIns hV Z.pol Z.lay Z.KL).reqX`, at the early part of that
    instance, is the item that the program forms (`Proof.requestItem`).
    Sv is any predicate which
    implies that the call's three public files are Z's. `hblk_bigIns`, `hitm_full` and `hitm_small`
    are premises of no statement of the library in this form, and no file calls them.



Assumes: `0 < Pz.V`; for the facts about a call, `sizesAt Z.pol = .ok Pz` and `planOf Z = .ok pl`.

Limits: nothing where `sizesAt` refuses the parameter file: the exit code 0 can occur there.
The other clauses of a test in "served" are not touched. One direction only. Nothing on
soundness.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Maker.Page.CallInstAt
import OnBytes.Flat.BigAt
import OnBytes.TypedOracleCompiler.Joined.DryInst
import OnBytes.Flat.LinksFreeAll
import Johnson.Thin.Link.PlanV
import Johnson.Flat.CoveredAt
import Johnson.Flat.FirstRange

set_option autoImplicit false

namespace Johnson.Session
open OnBytes OnBytes.Maker OnBytes.Flat Inst.Model OnBytes.Model OnBytes.Model.Verify
open Cb Cb.Ood OnBytes.Slice

variable (pl : Planned) (Pz : Params) (hV : 0 < Pz.V)

section Value
variable {R : Type} (rec₀ r₁ : R)

/-- **The value.** -/
def bigIns : FilesParameters (Instance' Pz) R :=
  bigAt pl (pubOf pl Pz hV).block rec₀ (firstInstance Pz hV, r₁) (withoutReply hV)

/-- It is at the plan. -/
theorem atPlan_bigIns {Z : K.Pub} (h : planOf Z = .ok pl) :
    AtPlan Z (bigIns pl Pz hV rec₀ r₁) := atPlan_bigAt h _ _ _ _

end Value

/-- The early part of the three files' own object, at the full size. -/
theorem early_full (rec₀ r₁ : RecFull) (A : (frS.toDecR frZ 402653181).Claims (Instance' Pz))
    (E : Coding A) (P : (threeProtocolsFromDryRunAtFullSize A (relationsAndEncodingOfClaims A E) (bigIns pl Pz hV rec₀ r₁)).Provers) :
    ((threeProtocolsFromDryRunAtFullSize A (relationsAndEncodingOfClaims A E) (bigIns pl Pz hV rec₀ r₁)).withProvers P).early = withoutReply hV := rfl

/-- The same at the small size. -/
theorem early_small (rec₀ r₁ : RecSmall) (A : (srS.toDecR srZ 524285).Claims (Instance' Pz))
    (E : Coding A) (P : (threeProtocolsFromDryRunAtSmallSize A (relationsAndEncodingOfClaims A E) (bigIns pl Pz hV rec₀ r₁)).Provers) :
    ((threeProtocolsFromDryRunAtSmallSize A (relationsAndEncodingOfClaims A E) (bigIns pl Pz hV rec₀ r₁)).withProvers P).early = withoutReply hV := rfl

/-- **The flat description's block at an instance with r < e (and y = 0 if e is before the window's
end)**, under hV, hP and hpl. That the first two computations return there is `covered_wordsOf`
(Johnson/Flat/CoveredAt.lean); that the third does is `linksOf_returns`
(Johnson/Flat/FirstRange.lean). -/
theorem block_formed {pol lay KL : ByteArray} (hP : sizesAt pol = .ok Pz)
    (hpl : planned pol KL (some lay) = .ok pl) (x₀ : Instance' Pz) (hre : x₀.r < x₀.e)
    (hy : x₀.e < Pz.T → x₀.y.val = 0) :
    ∃ (so₀ : Head.StOwn) (cov₀ : Head.Covered) (links₀ : Array Stages.LinkH),
      Head.coveredOf so₀ pl.X.T pl.X.P.h.V = .ok cov₀ ∧ linksOf pl.X cov₀ = .ok links₀ ∧
      (pubOf pl Pz hV).block x₀ = blockAt pl links₀ so₀.y := by
  obtain ⟨hPT, hPV, hT, hV'⟩ := sizesAt_planned hP hpl
  obtain ⟨so₀, cov₀, hs₀, hc₀⟩ := covered_wordsOf x₀ hT hV' hre hy
  rw [hPT] at hs₀
  rw [hPT, hPV] at hc₀
  obtain ⟨links₀, hl₀⟩ := linksOf_returns hpl cov₀
  exact ⟨so₀, cov₀, links₀, hc₀, hl₀,
    (pubOf_block_at pl Pz hV x₀ hPT hT hV' hre hy ⟨hs₀, hc₀, hl₀⟩).trans
      (blockAt_eq pl links₀ so₀.y).symm⟩

section Served
variable {Z : K.Pub} (hP : sizesAt Z.pol = .ok Pz) (hpl : planOf Z = .ok pl)
  (Sv : K.UserStm → Prop) (hSv : ∀ x, Sv x → x.pol = Z.pol ∧ x.lay = Z.lay ∧ x.KL = Z.KL)

include hP hpl hSv in
/-- **The block at the instance of an accepted call whose statement meets Sv (its three public files
are Z's) is the program's block**; under hV, hP and hpl. -/
theorem hblk_bigIns {R : Type} (rec₀ r₁ : R) :
    ∀ (F : K.Files) (o : Options) (id : String) (table further : OnBytes.Params.TableName)
      (i : Instance' Pz) (pl' : Planned) (so : Head.StOwn) (cov : Head.Covered)
      (links : Array Stages.LinkH),
      K.PortYesAt F id table further → Sv (K.stmOf F o) → insOf Pz (K.stmOf F o) = some i →
      planned F.pol F.KL (some F.lay) = .ok pl' →
      Head.stFromCall (words32 F.request) (words32 F.y) pl'.X.T = .ok so →
      Head.coveredOf so pl'.X.T pl'.X.P.h.V = .ok cov → linksOf pl'.X cov = .ok links →
      (bigIns pl Pz hV rec₀ r₁).block i = blockAt pl' links so.y :=
  block_of_ins hV Z.pol Z.lay Z.KL hP hpl Sv hSv _ rfl

include hP hpl hSv in
/-- **The item read off the early part of the instance of such a call is the program's item**: the
full size; under hV, hP and hpl. -/
theorem hitm_full (rec₀ r₁ : RecFull) (A : (frS.toDecR frZ 402653181).Claims (Instance' Pz))
    (E : Coding A) (P : (threeProtocolsFromDryRunAtFullSize A (relationsAndEncodingOfClaims A E) (bigIns pl Pz hV rec₀ r₁)).Provers) :
    ∀ (F : K.Files) (o : Options) (id : String) (table further : OnBytes.Params.TableName)
      (i : Instance' Pz) (item : ByteArray),
      K.PortYesAt F id table further → Sv (K.stmOf F o) → insOf Pz (K.stmOf F o) = some i →
      Proof.requestItem F.pol F.KL F.request = some item →
      (holdsIns hV Z.pol Z.lay Z.KL).reqX
        (((threeProtocolsFromDryRunAtFullSize A (relationsAndEncodingOfClaims A E) (bigIns pl Pz hV rec₀ r₁)).withProvers P).early i) = item :=
  item_of_ins hV Z.pol Z.lay Z.KL hP hpl Sv hSv _ rfl _ (early_full pl Pz hV rec₀ r₁ A E P)

include hP hpl hSv in
/-- The same at the small size. -/
theorem hitm_small (rec₀ r₁ : RecSmall) (A : (srS.toDecR srZ 524285).Claims (Instance' Pz))
    (E : Coding A) (P : (threeProtocolsFromDryRunAtSmallSize A (relationsAndEncodingOfClaims A E) (bigIns pl Pz hV rec₀ r₁)).Provers) :
    ∀ (F : K.Files) (o : Options) (id : String) (table further : OnBytes.Params.TableName)
      (i : Instance' Pz) (item : ByteArray),
      K.PortYesAt F id table further → Sv (K.stmOf F o) → insOf Pz (K.stmOf F o) = some i →
      Proof.requestItem F.pol F.KL F.request = some item →
      (holdsIns hV Z.pol Z.lay Z.KL).reqX
        (((threeProtocolsFromDryRunAtSmallSize A (relationsAndEncodingOfClaims A E) (bigIns pl Pz hV rec₀ r₁)).withProvers P).early i) = item :=
  item_of_ins hV Z.pol Z.lay Z.KL hP hpl Sv hSv _ rfl _ (early_small pl Pz hV rec₀ r₁ A E P)

end Served

end Johnson.Session
