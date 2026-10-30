-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Caller/KeptSeatsOrc.lean: code switching: THE NAMED TEST keptSeatsB
(K2Caller/KeptSeatsB.lean) READS OF THE DESCRIPTION ONE THING: THE ORACLE MESSAGE AT THE TENANT's
TREE. The test's own text with a letter in that reading's place, and the way back. General: no size,
no scope. NO SUB-PROTOCOL IMPORTS THIS FILE.
WHY. To have the test's accept at closed values by Lean's kernel one would need a closed
description. With a letter orc for «the oracle message at tree j» the rest of the test is a Bool on
plain lists.
  keptSeatOrc · keptSeatsOrc   the two texts, with orc. HELPERS: no new condition: nothing is to be
                    asked under these names
  keptSeatB_is      the test at one kept member is keptSeatOrc at the description's own reading: by
                    definition
  keptSeatOrc_below  an accept has the tenant's tree below «trees»
  keptSeatB_of · keptSeatsB_of   THE WAY BACK: where the description's reading is orc's at every
                    tree below «trees», an accept with orc is an accept of the named test
LIMITS. Nothing is evaluated here. No soundness is claimed.
-/
import Johnson.Top.H0.K2Caller.KeptSeatsB

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Caller
open OnBytes OnBytes.Slice Johnson.Pack
open VerifiableInference.Desc (FileDescription Oracle)
open VerifiableInference.Desc.K12.Door (Laid)

section
variable (cs : Codes) (L : Laid) (seats : List (ℕ × ℕ)) (trees : ℕ)

/-- keptSeatB's text, with orc for the description's oracle message at the tenant's tree. -/
def keptSeatOrc (orc : Option Oracle) (sh : OracleShape) (seat : ℕ × ℕ) (old : ℕ) : Bool :=
  (match L.places[old]? with
    | some q => q.2 == seat.2 && q.1 == seat.1 && decide (q.1 < trees) &&
      (match L.shapes[q.1]? with
        | some sh0 => decide ((cMain cs sh).a ≤ sh0.logN) &&
          (match orc with
            | some o => (sh0.mainSymbols.extract 0 seat.2).foldl (· + ·) 0 == o.mainSkip seat.2
            | none => true)
        | none => false)
    | none => false) && seats.contains seat && seats.idxOf seat == old

theorem keptSeatB_is {Xi : Type} (G : FileDescription Xi) (sh : OracleShape) (seat : ℕ × ℕ) (old : ℕ) :
    keptSeatB G cs L seats trees sh seat old =
      keptSeatOrc cs L seats trees (G.oracleAt seat.1) sh seat old := rfl

theorem keptSeatOrc_below {orc : Option Oracle} {sh : OracleShape} {seat : ℕ × ℕ} {old : ℕ}
    (h : keptSeatOrc cs L seats trees orc sh seat old = true) : seat.1 < trees := by
  unfold keptSeatOrc at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨h1, -⟩, -⟩ := h
  cases hp : L.places[old]? with
  | none => simp [hp] at h1
  | some q =>
    rw [hp] at h1
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h1
    rw [← h1.1.1.2]
    exact h1.1.2

theorem keptSeatB_of {Xi : Type} {G : FileDescription Xi} {orc : ℕ → Option Oracle}
    (hG : ∀ j, j < trees → G.oracleAt j = orc j) {sh : OracleShape} {seat : ℕ × ℕ} {old : ℕ}
    (h : keptSeatOrc cs L seats trees (orc seat.1) sh seat old = true) :
    keptSeatB G cs L seats trees sh seat old = true := by
  rw [keptSeatB_is, hG _ (keptSeatOrc_below cs L seats trees h)]
  exact h

variable (lo : List (OracleShape × ℕ)) (seat : Fin lo.length → ℕ × ℕ)

/-- keptSeatsB's text, with orc. -/
def keptSeatsOrc (orc : ℕ → Option Oracle) (kept olds : List ℕ) : Bool :=
  (List.range kept.length).all fun n =>
    match kept[n]?, olds[n]? with
    | some i, some old =>
      if h : i < lo.length then
        keptSeatOrc cs L seats trees (orc (seat ⟨i, h⟩).1) (lo.get ⟨i, h⟩).1 (seat ⟨i, h⟩) old
      else false
    | _, _ => false

/-- **The way back.** -/
theorem keptSeatsB_of {Xi : Type} {G : FileDescription Xi} {orc : ℕ → Option Oracle}
    (hG : ∀ j, j < trees → G.oracleAt j = orc j) {kept olds : List ℕ}
    (h : keptSeatsOrc cs L seats trees lo seat orc kept olds = true) :
    keptSeatsB G cs L seats trees lo seat kept olds = true := by
  unfold keptSeatsOrc at h
  unfold keptSeatsB
  refine List.all_eq_true.2 fun n hn => ?_
  have e := List.all_eq_true.1 h n hn
  split at e
  · rename_i i old hk ho
    simp only [hk, ho]
    split at e
    · rename_i hlt
      rw [dif_pos hlt]
      exact keptSeatB_of cs L seats trees hG e
    · cases e
  · cases e

end

end VerifiableInference.Desc.First.K2Caller

#print axioms VerifiableInference.Desc.First.K2Caller.keptSeatB_is
#print axioms VerifiableInference.Desc.First.K2Caller.keptSeatOrc_below
#print axioms VerifiableInference.Desc.First.K2Caller.keptSeatB_of
#print axioms VerifiableInference.Desc.First.K2Caller.keptSeatsB_of
