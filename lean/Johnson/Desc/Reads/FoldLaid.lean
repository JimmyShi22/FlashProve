-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Reads/FoldLaid.lean: where a list of tables is made by adding tables line after line,
as the verifier's routine for the output head's tables does, the read that a line declares has its
tables laid part by part, its parts fit the record, and its number of entries is its room.

All of this file is a tool: it holds for all records, lists of lines and maps, and names no
description of the protocol.

Why. The road to "joined" that is open at an honest list is `PartsLaid` with `PartsFit` and `Whole`
(Reads/Join.lean). The library has what adding tables does to a list (`fold_spec`,
Johnson/Road/HeadReads.lean): for each line, and each part q of its matrix, the record `recOf` of
that part lies in the list. That record is, field for field, the table to which a declaration
unfolds at part q (`ReadDecl.tabs`, Reads/Decl.lean), with its array of weights.

What is here.
  `declOfAsk a make tb m k w`: the declaration that a line a makes: its name, first part, number of
    parts and run are the line's; its first entry is tb; its number of entries is parts * (k * (m /
    run)); the make and the weights are letters.
  `laid_of_fold`: where the fold over the lines returns t, the line a is among them, all its parts
    have m rows and k columns and lie in the record: there is a first entry tb with the line's row
    (name, tb, length) in t's table of tables, such that for every make and all weights w which the
    line's array reads as, below the run's length: `PartsLaid`, `PartsFit`, and count = room, at the
    row's sizes and weights of t's list.

Of OnBytes/Model/ this file names the records `HTailF2`, `HFun` and `Head.Tables`, and through
Johnson/Road/HeadReads.lean the routine `Head.addFun`.

Limits. That a description's list is such a fold, that the parts have one size, and that the arrays
read as declared weights are premises. The make's own condition (`Make.Fits`) and "the run is not
empty" are not shown here. Nothing on soundness.


-/
import Johnson.Desc.Reads.HeadLaid
import Johnson.Road.HeadReads

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Reads

open Cb.Pv.Tail
open OnBytes (E zeroE)
open OnBytes.Model (HTailF2 HFun)
open OnBytes.Model.Head (Tables)
open OnBytes.Road.Hd (Ask addAsk recOf Uni fold_spec wfT_empty)

/-- The declaration that a line of the list makes. -/
def declOfAsk (a : Ask) (make : Make) (tb m k : ℕ) (w : ℕ → E) : ReadDecl E :=
  { name := a.2.2.2.2, mat := a.1, parts := a.2.1, make := make, len := a.2.2.1,
    count := a.2.1 * (k * (m / a.2.2.1)), start := tb, w := w }

/-- **The read that a line declares is laid part by part.** -/
theorem laid_of_fold {K : Type} (tl : HTailF2) (val : E → K) {asks : List Ask} {t : Tables}
    (hU : ∀ a ∈ asks, ∃ m k, Uni tl.mats a m k)
    (hf : asks.foldlM (addAsk tl.mats) {} = some t) {a : Ask} (ha : a ∈ asks) {m k : ℕ}
    (hUa : Uni tl.mats a m k) (hp : 0 < a.2.1) (hNM : a.1 + a.2.1 ≤ tl.NM) :
    ∃ tb, (a.2.2.2.2, tb, a.2.1 * (k * (m / a.2.2.1))) ∈ t.tab ∧
      ∀ (make : Make) (w : ℕ → E),
        (∀ j, j < a.2.2.1 → val (a.2.2.2.1.getD j zeroE) = val (w j)) →
        PartsLaid (sizeU3 tl t.funs) (phiU3 val t.funs) val (declOfAsk a make tb m k w) ∧
        PartsFit (sizeU3 tl t.funs) (declOfAsk a make tb m k w) ∧
        (declOfAsk a make tb m k w).count =
          (declOfAsk a make tb m k w).room ((sizeU3 tl t.funs).m a.1)
            ((sizeU3 tl t.funs).k a.1) := by
  obtain ⟨-, -, -, -, hall⟩ := fold_spec tl.mats asks {} t hU wfT_empty hf
  obtain ⟨tb, hmem, hrec⟩ := hall a ha m k hUa
  have hm0 : (sizeU3 tl t.funs).m a.1 = m := by
    have h := (hUa 0 hp).1
    rw [Nat.add_zero] at h
    exact h
  have hk0 : (sizeU3 tl t.funs).k a.1 = k := by
    have h := (hUa 0 hp).2
    rw [Nat.add_zero] at h
    exact h
  refine ⟨tb, hmem, fun make w hw => ⟨?_, ⟨hNM, fun q hq => ?_⟩, ?_⟩⟩
  · refine laid_of_mem tl t.funs val _ fun q hq =>
      ⟨recOf a tb (k * (m / a.2.2.1)) q, by simpa using hrec q hq, rfl, rfl, rfl, ?_, hw⟩
    show tb + q * (k * (m / a.2.2.1)) =
      tb + q * ((sizeU3 tl t.funs).k a.1 * ((sizeU3 tl t.funs).m a.1 / a.2.2.1))
    rw [hm0, hk0]
  · show (tl.mats.getD (a.1 + q) {}).m = (sizeU3 tl t.funs).m a.1 ∧
      (tl.mats.getD (a.1 + q) {}).k = (sizeU3 tl t.funs).k a.1
    rw [hm0, hk0]
    exact hUa q hq
  · show a.2.1 * (k * (m / a.2.2.1)) =
      a.2.1 * ((sizeU3 tl t.funs).k a.1 * ((sizeU3 tl t.funs).m a.1 / a.2.2.1))
    rw [hm0, hk0]

end VerifiableInference.Reads

#print axioms VerifiableInference.Reads.laid_of_fold
