-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Keep/SideKeep.lean: the kind "lookup" (K3): the seated row that
passes its tables on (`proverSideOfLookupInChainKeepingTablesAtOneOwner`, Honest/K3/RowKeep.lean), each part beside the simulator of the
row that passes nothing on; and the sides over it. The sisters of `rowPairs` and `rowSides`
(Honest/K3/LotRow.lean). Two definitions; theorems.

Never to be retold as "the row that passes its tables on is simulated". By construction: the row's
writer sets the simulators: that a simulator stands beside a part says nothing of the two.

Terms. Honest/K3/GLOSSARY.md. `FillKeep`, `rowLotKeep`: Honest/K3/LotKeep.lean. `lookSims`:
Honest/K3/Row.lean. `Side`, `Side.seated`: Honest/Side.lean.

What is defined.
  `rowPairsKeep A get set s`: the parts of the seated row at the site s, each beside the member of
    `lookSims s.at_` at its number. Against `rowPairs`: `FillKeep` for `OnlineProverParts`; the letters' jobs
    with a kept state for the jobs; get and set come; `proverSideOfLookupInChainKeepingTablesAtOneOwner` for `proverSideOfLookupInChainAtOneOwner`.
    `lookSims s.at_` is the very term that stands in `rowPairs`: it reads the place and the stages'
    calls alone. No new simulator is defined. No coin is named. The input is read by `A.wit` alone.
  `rowSidesKeep`: `rowSides` with `rowPairsKeep` for `rowPairs`.

What is shown.
  `map_snd_zip_eq`: a fact on lists, beside `map_fst_zip_eq` (Honest/K3/RowAt.lean).
  `proverSideOfLookupInChainKeepingTablesAtOneOwner_length`: the seated row has a part for each stage.
  `rowPairsKeep_parts`, `rowPairsKeep_sims`: the pairs' first components are the seated row's parts;
    their second are `lookSims s.at_`. No premise.
  `halves_rowLotKeep`: **the halves of `rowLotKeep` are the sites, each mapped to its place and the
    pairs' first components.** An equation; no premise: so no half of the lot is left without its
    row. `half_of_lotKeep`: the membership, as its corollary.
  `block_of_seated`, `seated_of_find`: what `Side.seated` lays, free of any kind.
  `row_of_seatedKeep`: **a side seated over `rowPairsKeep` has the row that `k3_exact_kept`
    (Honest/K3/Law/Keep/ExactKept.lean) asks as hrow.** By unfolding.
That `rowLotKeep` is a `lotBy`: `rowLotKeep_is` (Honest/K3/Law/CoverageLots.lean
[not in this library]).

Limits. hrow is paid at a definition of this file, by unfolding. That a filling of the honest side's
frame lays this side is typed by nobody: "`exact` at the filling" is not had. The sisters of
`k3Lettered` (Honest/K3/Law/Good/K3Lettered.lean) and of the lot of rows with simulators are not
written. Where no site is made nothing is said. A lot over these rows bears the one lot's name: it
is meant in the original lot's place, not beside it: a caution; nothing here shows or tests it.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.LotKeep
import Johnson.Desc.ProofFile.Honest.K3.RowLaw
import Johnson.Desc.ProofFile.Honest.K3.RowAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3
open VerifiableInference.Desc (Block Place)

variable {S Cl V W X Pb : Type}

/-! ## 1 The two definitions -/

/-- BY CONSTRUCTION: the row's writer sets the simulators. **The seated row that passes its tables
on, at a site, each part with the form of a simulator beside it**: the forms are those of the row
that passes nothing on. -/
def rowPairsKeep (A : FillKeep W) (get : X → RowOwn) (set : X → RowOwn → X) (s : Site) :
    List (Part V W X × Sim Pb) :=
  (proverSideOfLookupInChainKeepingTablesAtOneOwner (A.keeps s) (A.wit s) get set s.at_).parts.zip (lookSims s.at_)

/-- BY CONSTRUCTION: the row's writer sets the simulators. **The sides**: at each site the row
beside the member of bs that stands at the place; nothing where none does. Here bs is the
description's first chain as a flat list. -/
def rowSidesKeep (A : FillKeep W) (get : X → RowOwn) (set : X → RowOwn → X)
    (bs : List (Block S Cl)) (sites : List Site) : List (Site × Option (Side S Cl V W X Pb)) :=
  sites.map fun s => (s, Side.seated bs s.at_.place (rowPairsKeep A get set s))

/-! ## 2 The pairs' two components -/

theorem map_snd_zip_eq {α β : Type} (l₁ : List α) (l₂ : List β) (h : l₁.length = l₂.length) :
    (l₁.zip l₂).map (·.2) = l₂ := by
  induction l₁ generalizing l₂ with
  | nil =>
    cases l₂ with
    | nil => rfl
    | cons b l₂ => simp at h
  | cons a l ih =>
    cases l₂ with
    | nil => simp at h
    | cons b l₂ => simp [ih l₂ (by simpa using h)]

/-- The seated row has a part for each stage. -/
theorem proverSideOfLookupInChainKeepingTablesAtOneOwner_length (Kp : Keeps) (wit : W → Ask) (get : X → RowOwn)
    (set : X → RowOwn → X) (a : At) :
    (proverSideOfLookupInChainKeepingTablesAtOneOwner (V₁ := V) Kp wit get set a).parts.length = (stages a.face).length := by
  simp [proverSideOfLookupInChainKeepingTablesAtOneOwner, lookRowKeep]

/-- The pairs' first components are the seated row's parts. No premise. -/
theorem rowPairsKeep_parts (A : FillKeep W) (get : X → RowOwn) (set : X → RowOwn → X) (s : Site) :
    (rowPairsKeep (V := V) (Pb := Pb) A get set s).map (·.1) =
      (proverSideOfLookupInChainKeepingTablesAtOneOwner (A.keeps s) (A.wit s) get set s.at_).parts := by
  unfold rowPairsKeep
  apply map_fst_zip_eq
  rw [proverSideOfLookupInChainKeepingTablesAtOneOwner_length, lookSims_length]

/-- Their second components are the forms of the row that passes nothing on. No premise. -/
theorem rowPairsKeep_sims (A : FillKeep W) (get : X → RowOwn) (set : X → RowOwn → X) (s : Site) :
    (rowPairsKeep (V := V) (Pb := Pb) A get set s).map (·.2) = lookSims s.at_ := by
  unfold rowPairsKeep
  apply map_snd_zip_eq
  rw [proverSideOfLookupInChainKeepingTablesAtOneOwner_length, lookSims_length]

/-! ## 3 The lot's halves -/

/-- **The lot's halves are the sites, each mapped to its place and the pairs' first components.** No
premise. Here Pb, the type of what a simulator is handed, stands on the right alone. -/
theorem halves_rowLotKeep (Pb : Type) (A : FillKeep W) (get : X → RowOwn) (set : X → RowOwn → X)
    (Z : Pub) (G : Ground) :
    (rowLotKeep A get set : HLot V W X).halves Z G =
      (lookSites Z).map fun s =>
        ⟨s.at_.place, (rowPairsKeep (Pb := Pb) A get set s).map (·.1)⟩ := by
  show (lookSites Z).map (fun s => (⟨s.at_.place,
    (proverSideOfLookupInChainKeepingTablesAtOneOwner (A.keeps s) (A.wit s) get set s.at_).parts⟩ : Placed V W X)) = _
  exact List.map_congr_left fun s _ => by rw [rowPairsKeep_parts]

/-- The side's half is the lot's half. Conditional on the site. -/
theorem half_of_lotKeep (Pb : Type) (A : FillKeep W) (get : X → RowOwn) (set : X → RowOwn → X)
    (Z : Pub) (G : Ground) (s : Site) (hs : s ∈ lookSites Z) :
    (⟨s.at_.place, (rowPairsKeep (Pb := Pb) A get set s).map (·.1)⟩ : Placed V W X) ∈
      (rowLotKeep A get set : HLot V W X).halves Z G := by
  rw [halves_rowLotKeep Pb]
  exact List.mem_map.2 ⟨s, hs, rfl⟩

/-! ## 4 The seated side -/

/-- What `Side.seated` lays. -/
theorem block_of_seated (row : List (Part V W X × Sim Pb)) (bs : List (Block S Cl)) (a : Place)
    (fs : List (Fall S)) (σ : Side S Cl V W X Pb) (h : Side.seated bs a row fs = some σ) :
    bs.find? (fun b => b.place == a) = some σ.block ∧ σ.row = row ∧ σ.fall = fallOf fs a := by
  unfold Side.seated at h
  obtain ⟨m, hm, rfl⟩ := Option.map_eq_some_iff.1 h
  exact ⟨hm, rfl, rfl⟩

/-- Where a member is found at the place, the side is there. -/
theorem seated_of_find (row : List (Part V W X × Sim Pb)) (bs : List (Block S Cl)) (a : Place)
    (fs : List (Fall S)) (b : Block S Cl) (h : bs.find? (fun b => b.place == a) = some b) :
    Side.seated bs a row fs = some ⟨b, row, fallOf fs a⟩ := by
  unfold Side.seated
  rw [h]
  rfl

/-- **A side seated over `rowPairsKeep` has that row.** By unfolding. Conditional on the side being
there. -/
theorem row_of_seatedKeep (A : FillKeep W) (get : X → RowOwn) (set : X → RowOwn → X) (s : Site)
    (bs : List (Block S Cl)) (fs : List (Fall S)) (σ' : Side S Cl V W X Pb)
    (h : Side.seated bs s.at_.place (rowPairsKeep A get set s) fs = some σ') :
    σ'.row = (proverSideOfLookupInChainKeepingTablesAtOneOwner (A.keeps s) (A.wit s) get set s.at_).parts.zip (lookSims s.at_) :=
  (block_of_seated _ bs s.at_.place fs σ' h).2.1

end ProofFile.Honest.K3

#print axioms ProofFile.Honest.K3.map_snd_zip_eq
#print axioms ProofFile.Honest.K3.proverSideOfLookupInChainKeepingTablesAtOneOwner_length
#print axioms ProofFile.Honest.K3.rowPairsKeep_parts
#print axioms ProofFile.Honest.K3.rowPairsKeep_sims
#print axioms ProofFile.Honest.K3.halves_rowLotKeep
#print axioms ProofFile.Honest.K3.half_of_lotKeep
#print axioms ProofFile.Honest.K3.block_of_seated
#print axioms ProofFile.Honest.K3.seated_of_find
#print axioms ProofFile.Honest.K3.row_of_seatedKeep
