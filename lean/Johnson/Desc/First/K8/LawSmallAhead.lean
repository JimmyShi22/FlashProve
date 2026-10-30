-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/K8/LawSmallAhead.lean: THE SMALLNESS TEST AT THE TABLE OF JOINTS: TWO OF THE
LAW'S THREE SENTENCES AGAINST THE TABLE'S, AT THE LAW'S ONE TABLE OF CELLS `cellsAhead`
(Johnson/Desc/First/K8/CellsAhead.lean).

  `tieOf_congr`: the tie reads early cells alone: two tables that agree at every early cell give one
    tie, where there are as many numbers of symbol arrays as matrices and a third vector of reads.
  `tieAt_ahead_iff`: **at a state at which the test `Named.namedB` says yes: the tie at `cellsAhead`
    is the tie at `cellsAt`**, the table of the item "tie": every early array's message is found by
    the state (`msgNow_of_named`), and there the two tables are one
    (`cellsAhead_sent`).
  `smallAt_of_formsQA`: **the item "forms" of the run "small" gives the law's `SmallAt` at
    `cellsAhead`**: where the reader of that run is the reader of the single equations
    (`K9.smallReader`, Johnson/Desc/First/Batch/SmallReader.lean) and the caller's list of tables is
    the structure's own: the forms' own world is, by the make, the world of the cells `cellsAhead`;
    and the forms are worth 0 just where every single equation holds at these cells
    (`rowsAff_zero_iff`, Johnson/Desc/First/TailClaims/SingleFormsLaw.lean).
Statements and proofs.
Limits. That the caller's list is the structure's own is a premise. Nothing on the digits. Nothing
on soundness.

-/
import Johnson.Desc.First.K8.CellsAhead
import Johnson.Desc.First.K8.LawEarlyCells
import Johnson.Desc.First.K8.LawItems
import OnBytes.Tie.Pv.Tail.EndsAtPort
import Johnson.Desc.First.Batch.SmallReader
import Johnson.Desc.First.TailClaims.SingleFormsLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8

open OnBytes OnBytes.Model OnBytes.Tie.Pv.Tail OnBytes.Tie.Pv.Tail.Port VerifiableInference.Desc
  VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First.TailClaims (rowsAff)
open VerifiableInference.Desc.First.TailClaims.Law (ownWorld rowsAff_zero_iff)

/-- The tie reads early cells alone. -/
theorem tieOf_congr {tl : HTailF2} {A A' : ℕ → ℕ → ℕ → Cb.Gl.E} (hgt : tl.NM ≤ tl.gtTree.size)
    (hu : ∃ t, tl.ix.U[2]? = some (some t))
    (h : ∀ t r c, early tl (.cell t r c) = true → A t r c = A' t r c) (H : TieOf tl A) :
    TieOf tl A' := by
  obtain ⟨a, h1, h2, h3⟩ := H
  refine ⟨a, h1, fun μ hμ c hc i' hi' => ?_, fun n Fn hn c sg pos hp => ?_⟩
  · rw [← h _ _ _ (early_sym (Nat.lt_of_lt_of_le hμ hgt) i' c)]
    exact h2 μ hμ c hc i' hi'
  · rw [← h _ _ _ (early_u3 hu 0 pos)]
    exact h3 n Fn hn c sg pos hp

variable {P Cells Tok : Type}

/-- **The tie at the law's table is the tie at the item's.** -/
theorem tieAt_ahead_iff (cs : OnBytes.Codes) (arr : ℕ → ℕ → ℕ) (ms : List Mem) (N : Numbers)
    (m : ℕ) (z : P) (s : S) {p : Par} {L : LinkCtx} {F : Fork} {tl : HTailF2}
    (hL : s.link? = some L) (hF : s.fork? = some F) (ht : s.tl? = some tl)
    (hN : Named.namedB p s.st s.book tl L = true) (hgt : tl.NM ≤ tl.gtTree.size)
    (hu : ∃ t, tl.ix.U[2]? = some (some t)) (w : Wit Cells Tok MsgT) :
    TieAt (cellsAhead cs arr ms N m (z, s)) s w ↔ TieAt (cellsAt cs arr ms N m (z, s)) s w := by
  have e : ∀ t r c, early tl (.cell t r c) = true →
      cellsAhead cs arr ms N m (z, s) w t r c = cellsAt cs arr ms N m (z, s) w t r c := by
    intro t r c he
    obtain ⟨o, ho⟩ := msgNow_of_named hN he
    exact cellsAhead_sent cs arr ms N m z s w hL hF ht ho r c
  constructor
  · rintro ⟨tl', ht', H⟩
    obtain rfl := Option.some.inj (ht.symm.trans ht')
    exact ⟨tl, ht, tieOf_congr hgt hu e H⟩
  · rintro ⟨tl', ht', H⟩
    obtain rfl := Option.some.inj (ht.symm.trans ht')
    exact ⟨tl, ht, tieOf_congr hgt hu (fun t r c he => (e t r c he).symm) H⟩

/-- **From the table's sentence on the run "small" to the law's.** -/
theorem smallAt_of_formsQA (cs : OnBytes.Codes) (arr : ℕ → ℕ → ℕ) (ms : List Mem) (N : Numbers)
    (m : ℕ) (z : P) (s : S) (Rd : K9.Readers) (piece : ℕ) (run : String) {tl : HTailF2}
    (ht : s.tl? = some tl) (hf : s.funs? = some tl.funs)
    (hR : Rd.forms piece run s = K9.smallReader s) (w : Wit Cells Tok MsgT)
    (h : formsQA (N.sent m) (N.group m) Rd piece run s (seatTab cs arr ms w)) :
    SmallAt (cellsAhead cs arr ms N m (z, s)) s w := by
  obtain ⟨a, R, ha, hs, _, hv⟩ := h
  rw [hR] at hs
  unfold K9.smallReader at hs
  rw [ht, hf] at hs
  obtain rfl : ({ forms := rowsAff tl tl.funs, late := [] } : K9.Read) = R := Option.some.inj hs
  refine ⟨tl, ht, ?_⟩
  have e : cellsAhead cs arr ms N m (z, s) w =
      (worldOwn a [] (dataQA (N.sent m) (N.group m) a (seatTab cs arr ms w))).entry := by
    funext t r c
    show (match K9.segAt? s with
      | some p =>
        (worldOwn p [] (dataQA (N.sent m) (N.group m) p (seatTab cs arr ms w))).entry t r c
      | none => 0) = _
    rw [ha]
  rw [e]
  exact (rowsAff_zero_iff Reading.gl _
    (worldOwn a [] (dataQA (N.sent m) (N.group m) a (seatTab cs arr ms w))).slot tl tl.funs 0).1
    fun f hm => (hv f hm).2

end VerifiableInference.Desc.First.K8

#print axioms VerifiableInference.Desc.First.K8.tieOf_congr
#print axioms VerifiableInference.Desc.First.K8.tieAt_ahead_iff
#print axioms VerifiableInference.Desc.First.K8.smallAt_of_formsQA
