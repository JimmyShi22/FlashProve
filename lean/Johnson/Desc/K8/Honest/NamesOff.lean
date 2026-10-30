-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/NamesOff.lean: THE SMALLNESS TEST: A CLAIM THAT NAMES NO ENTRY AND NO RUN OF
A VIRTUAL ROW BEARS NOTHING ON THAT ROW's ENTRIES; AND THE FIRST FOUR CLAIMS OF THE LIST
"K8.equations" NAME NOTHING OF A VIRTUAL ROW THAT LIES NEITHER IN THE PLANES' ARRAY NOR AMONG THE
PIECES' ROWS OF THE DIGITS' ARRAY. Definitions and lemmas; none of the library's goals. On claims
and plain data: no ledger, no block, no prover; nothing on completeness, soundness or hiding.

  `NamesNot t cl`, `NamesNotAt t r cl`, `namesNot_at`   the claim names no entry and no run of array
      t; of virtual row r of array t; the first gives the second at every r
  `runsE_none`, **`coefOn_off`**   runs on other virtual rows bear nothing at the place; so the
      claim's coefficient on each entry of the row (`coefOn`, Johnson/Desc/K8/Honest/FallCount.lean)
      is 0
  `pair_row`   under `piecesLaid` (Johnson/Desc/K8/Honest/PiecesLaid.lean): the two calls' pieces
      lie in the digits' array, in virtual rows below twice the number of blocks
  **`four8_off`**   the sentence on the four (K9L.four8, Johnson/Desc/First/Batch/Law/K8Four.lean),
      where the two forms among them that the digits' lookup has heard name no entry
By: `coefOn_eq` (Johnson/Desc/K8/Honest/CoefCode.lean) · `entsE_none` (PlanesLiveOf.lean) ·
`addMul_ents`, `joinRuns_eq`, `pair_lt` (DigitsLiveOf.lean) · `rowForm_ents`, `no_ent` (GoodOf.lean)
· `pair_mem` (PublicOfPieces.lean).
Limits. `NamesNot` at the digits' array is FALSE of the first of the four: its runs lie there, on
the pieces' rows. That what the lookup has heard names no entry, and `piecesLaid`, are premises.
Nothing on any other claim.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.K8.Honest.GoodOf
import Johnson.Desc.K8.Honest.PublicOfPieces

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open VerifiableInference.Desc

/-- The claim names no entry and no run of array t. -/
def NamesNot (t : Nat) (cl : Claim) : Prop :=
  (∀ x ∈ cl.form.ents, x.tree ≠ t) ∧ ∀ u ∈ cl.runs, u.tree ≠ t

/-- The claim names no entry and no run of virtual row r of array t. -/
def NamesNotAt (t r : Nat) (cl : Claim) : Prop :=
  (∀ x ∈ cl.form.ents.toList, ¬ (x.tree = t ∧ x.row = r)) ∧
    ∀ u ∈ cl.runs.toList, ¬ (u.tree = t ∧ u.row = r)

theorem namesNot_at {t : Nat} {cl : Claim} (h : NamesNot t cl) (r : Nat) : NamesNotAt t r cl :=
  ⟨fun x hx hc => h.1 x (Array.mem_toList_iff.1 hx) hc.1,
    fun u hu hc => h.2 u (Array.mem_toList_iff.1 hu) hc.1⟩

/-- Runs on other virtual rows bear nothing at the place. -/
theorem runsE_none : ∀ (l : List Run2) (t r i : Nat),
    (∀ R ∈ l, ¬ (R.tree = t ∧ R.row = r)) → runsE l t r i = zeroE
  | [], _, _, _, _ => rfl
  | R :: l, t, r, i, h => by
    have ih := runsE_none l t r i fun R' hR' => h R' (List.mem_cons_of_mem _ hR')
    unfold runsE at ih ⊢
    rw [List.foldr_cons, if_neg fun hc => h R List.mem_cons_self ⟨hc.1, hc.2.1⟩]
    exact ih

/-- **A claim that names nothing of the virtual row bears nothing on its entries.** -/
theorem coefOn_off {t r : Nat} {cl : Claim} (h : NamesNotAt t r cl) (i : Nat) :
    coefOn cl t r i = 0 := by
  rw [coefOn_eq]
  unfold coefE
  rw [entsE_none _ _ _ _ fun x hx hc => h.1 x hx ⟨hc.1, hc.2.1⟩, runsE_none _ _ _ _ h.2,
    Reading.gl.add, Reading.gl.zero, add_zero]

/-- Where the two calls' pieces lie as the plan lays them: in the digits' array, in front of the
reads' row. -/
theorem pair_row (tl : HTailF2) (hL : piecesLaid tl = true) (x : Nat × OnBytes.Model.Piece)
    (hx : x ∈ joinPairs tl) : x.2.tree = tl.ix.ZZ ∧ x.2.row < 2 * tl.zzBlocks := by
  unfold piecesLaid at hL
  rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at hL
  have hq := pair_lt tl x hx
  have hp := pair_mem tl x hx
  have h01 : x.1 = 0 ∨ x.1 = 1 := by omega
  rcases h01 with e | e
  · rw [e] at hp
    have hm : pieceKey x.2 ∈ tl.z1.pieces.toList.map pieceKey := List.mem_map_of_mem hp
    rw [hL.1] at hm
    obtain ⟨j, hj, ej⟩ := List.mem_map.1 hm
    unfold pieceKey at ej
    simp only [Prod.mk.injEq] at ej
    have k := List.mem_range.1 hj
    exact ⟨ej.1.symm, by omega⟩
  · rw [e] at hp
    have hm : pieceKey x.2 ∈ tl.z2.pieces.toList.map pieceKey := List.mem_map_of_mem hp
    rw [hL.2] at hm
    obtain ⟨j, hj, ej⟩ := List.mem_map.1 hm
    unfold pieceKey at ej
    simp only [Prod.mk.injEq] at ej
    have k := List.mem_range.1 hj
    exact ⟨ej.1.symm, by omega⟩

/-- **THE FIRST FOUR CLAIMS OF THE SMALLNESS TEST's OWN LIST NAME NOTHING OF A VIRTUAL ROW (t, r)
THAT IS NOT IN THE PLANES' ARRAY AND IS NONE OF THE PIECES' ROWS OF THE DIGITS' ARRAY**: where the
two forms that the digits' lookup has heard name no entry. -/
theorem four8_off (tl : HTailF2) (g : Forest.Heard) (hc : g.cEnd.ents.isEmpty = true)
    (hl : g.leaves.start.ents.isEmpty = true) (hL : piecesLaid tl = true) (t r : Nat)
    (hB : tl.ix.BZ ≠ t) (hZ : ¬ (tl.ix.ZZ = t ∧ r < 2 * tl.zzBlocks)) :
    ∀ cl ∈ K9L.four8 tl g, NamesNotAt t r cl := by
  have bz : ∀ (row : Nat) (c : E) (w : Array E), ∀ u ∈ (#[Fo.bzRun tl row c w] : Array Run2).toList,
      ¬ (u.tree = t ∧ u.row = r) := by
    intro row c w u hu hcu
    obtain rfl : u = Fo.bzRun tl row c w := List.mem_singleton.1 hu
    exact hB hcu.1
  intro cl hcl
  simp only [K9L.four8, List.mem_cons, List.not_mem_nil, or_false] at hcl
  rcases hcl with rfl | rfl | rfl | rfl
  · refine ⟨fun x hx _ => ?_, fun u hu hcu => ?_⟩
    · rcases addMul_ents _ _ _ x hx with h1 | ⟨y, hy, -, -, -⟩
      · simp [Aff.ofConst] at h1
      · exact absurd hy (no_ent _ hc y)
    · have hu' : u ∈ Fo.joinRuns tl g := by simpa using hu
      rw [joinRuns_eq] at hu'
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hu'
      obtain ⟨e1, e2⟩ := pair_row tl hL x hx
      have c1 : x.2.tree = t := hcu.1
      have c2 : x.2.row = r := hcu.2
      exact hZ ⟨e1.symm.trans c1, c2 ▸ e2⟩
  · refine ⟨fun x hx _ => ?_, bz _ _ _⟩
    obtain ⟨y, hy, -, -, -⟩ := rowForm_ents _ _ x hx
    exact absurd hy (no_ent _ hl y)
  · exact ⟨fun x hx _ => by simp [Aff.slot] at hx, bz _ _ _⟩
  · exact ⟨fun x hx _ => by simp [Aff.ofConst] at hx, bz _ _ _⟩

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.namesNot_at
#print axioms VerifiableInference.Desc.First.K8.Honest.runsE_none
#print axioms VerifiableInference.Desc.First.K8.Honest.coefOn_off
#print axioms VerifiableInference.Desc.First.K8.Honest.pair_row
#print axioms VerifiableInference.Desc.First.K8.Honest.four8_off
