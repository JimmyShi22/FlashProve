-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/K4PlanLab.lean: THE 24 CLOSED TESTS OF Johnson/Road/K4/K4PlanFast.lean WITHOUT THE
BUILT LINKS. The twelve tests `firstFastB Z g` read, through `symTieB`, the built links' lists of
arrays (Z.p.built) and the matrices' trees (gtTree). Under the names' tie, which another file has as
a theorem in the goals' scope (`names_tie`), each is `firstLabCoreB`, which asks at the owner and
the name that the public parameters' label names (Johnson/Road/K4/SymsByLabel.lean) and reads
neither. Four definitions (two of them conditions) and three theorems. Glue; no draw, no count.

  `NamesAt D X g`, `NamesTied Z`: the names' tie at one group, with D and X as letters; at the
    twelve feed-forward links, at Z: meant to be the end of that theorem by unfolding
    (Z.p := Z.made.p): `namesTied_of_scope` (Johnson/Road/K4/K4PlanNames.lean) is that call, in the
    goals' scope, where the files read, at an opening.
  `firstLabCoreB`: `firstCoreB` with `symLabB` in `symTieB`'s place.
  `firstLab_eq`: under the tie at g the two are one: AN EQUATION.
  `allLabB Z`: all 24 in one, every letter laid once, without the built links.
  `allLab_eq`: under `NamesTied Z`, `allLabB Z = allFastB Z`.
  `parts_of_allLab`: so one yes of `allLabB` gives each of the 24.

Limits. K04_law IS NOT PROVED BY THIS. `NamesTied Z` IS A PREMISE: this file does not import its
proof. `sentAt Z` still holds the built links' lists as a field; `allLabB` reads of it codes, shape
and layout alone (by its text; no theorem says "reads"). OF THE PUBLIC PARAMETERS X IT STILL READS:
the labels (aId), the matrices' sizes (m, k, NM), and what `nmFit` and `pairFit` read.
-/
import Johnson.Road.K4.K4PlanFast
import Johnson.Road.K4.SymsByLabel

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open OnBytes
open OnBytes.Model.Verify (Public)
open VerifiableInference.Desc.First (Numbers)
open VerifiableInference.Desc.First.Look (Sent sigListCalls)
open VerifiableInference.Desc.Sound (Mem msOf)
open Meaning (labAt ownerK ownerA nameOf)

/-- The names' tie at group g, with D and X as letters. -/
def NamesAt (D : Sent) (X : Public) (g : ℕ) : Prop :=
  ∀ μ, μ < (Meaning.sizesOf X (2 * g)).NM →
    (D.arrayOf.getD (2 * g) #[])[(Meaning.tlAt X (2 * g)).gtTree.getD μ 0]? =
      some (ownerK (labAt X (2 * g) μ), nameOf (ownerA (labAt X (2 * g) μ)))

/-- **The names' tie at the twelve feed-forward links.** -/
def NamesTied (Z : ProofFile.Pub) : Prop := ∀ g, g < 12 → NamesAt (sentAt Z) Z.p.X g

/-- `firstCoreB` with the test at the label's owner and name. -/
def firstLabCoreB (D : Sent) (ps : List P5T.PSeat) (N : Numbers) (ms : List Mem) (X : Public)
    (g : ℕ) (num arr : ℕ → ℕ → ℕ) : Bool :=
  sitsInB (sigListCalls D (fun _ => 0) (2 * g)) (pinsCore D ps (2 * g)).seatT ms N (2 * g) &&
    (List.range (Meaning.sizesOf X (2 * g)).NM).all fun μ =>
      symLabB (pinsCore D ps (2 * g)) num arr N (2 * g) X (Meaning.sizesOf X) μ

/-- **Under the names' tie at g the two tests are one.** -/
theorem firstLab_eq {D : Sent} {X : Public} {g : ℕ} (h : NamesAt D X g) (ps : List P5T.PSeat)
    (N : Numbers) (ms : List Mem) (num arr : ℕ → ℕ → ℕ) :
    firstCoreB D ps N ms X g num arr = firstLabCoreB D ps N ms X g num arr := by
  unfold firstCoreB firstLabCoreB
  congr 1
  exact P5T.all_congr_mem _ _ _ fun μ hμ =>
    symTie_eq_lab (pinsCore D ps (2 * g)) num arr N (2 * g) (Meaning.tlAt X (2 * g)) X
      (Meaning.sizesOf X) μ (h μ (List.mem_range.1 hμ))

/-- **ALL 24 IN ONE, EVERY LETTER LAID ONCE, WITHOUT THE BUILT LINKS.** -/
def allLabB (Z : ProofFile.Pub) : Bool :=
  let D := sentAt Z
  let ps := seatsAt Z
  let N := numbersAt Z
  let L := lists0At Z
  let ms := msOf L
  let X := Z.p.X
  let keys := seatKeys (allSeatsAt Z)
  let tab := arrTab keys (allSeatsAt Z)
  let tbl := (List.range 25).map fun k => N.group k
  let num : ℕ → ℕ → ℕ := fun l k => keys.idxOf (0, l, k)
  let arr : ℕ → ℕ → ℕ := fun j t => (tab.lookup (j, t)).getD keys.length
  commonCoreB D N L X (lastAt Z) num arr (fun k => tbl.getD k []) &&
    ((List.range 12).all fun g => firstLabCoreB D ps N ms X g num arr) &&
    (List.range 11).all fun i => seamCoreB D N X (i + 1) num arr

/-- **Under the names' tie it is `allFastB`.** -/
theorem allLab_eq (Z : ProofFile.Pub) (h : NamesTied Z) : allLabB Z = allFastB Z := by
  unfold allLabB allFastB
  simp only []
  congr 2
  exact P5T.all_congr_mem _ _ _ fun g hg =>
    (firstLab_eq (h g (List.mem_range.1 hg)) _ _ _ _ _).symm

/-- **One yes gives each of the 24.** -/
theorem parts_of_allLab (Z : ProofFile.Pub) (h : NamesTied Z) (hB : allLabB Z = true) :
    commonFastB Z = true ∧ (∀ g, g < 12 → firstFastB Z g = true) ∧
      ∀ g, 0 < g → g < 12 → seamFastB Z g = true :=
  parts_of_all Z ((allLab_eq Z h).symm.trans hB)

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.firstLab_eq
#print axioms OnBytes.Road.K4.allLab_eq
#print axioms OnBytes.Road.K4.parts_of_allLab
