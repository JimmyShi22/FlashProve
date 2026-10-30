-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/Keep/PlanesRowsIn.lean: The kind "lookup" (K3): A CLAIM OF THE RUN "planes" NAMES NO
ENTRY OF AN ARRAY BUT WHAT THE CALLER's FORMS ON THE COLUMNS (bit, pin) AND THE START FORM OF THE
LEAVES' SUMCHECK NAME. General in the property Q of (array, row). Statements and proofs.

OBJECT: K3.planesRun (Johnson/Desc/First/Look/K3Runs.lean) at any seat whose claims' forms are read
  by form.
Used by Johnson/Desc/First/Att/K05PlanesEnts.lean.
LETTERS: Q, seat, form, lm, readers, n, s free.
Compiled with the whole library.

Main names:
  rowsIn_got: what a reader's column hands in has Q where each of its forms has.
  rowsIn_planesAff, rowsIn_countAff: the two sums.
  planes_rowsIn: THE END.
  planes_rowsIn_bare: the same where the leaves' start form is bare (behind the block's yes:
    PadNames.start, Johnson/Top/H/Keep/PadNamed.lean).

Limits. On the entries alone: nothing on the slots. The premise on g.leaves.start is the lookup's
own (paid by PadNames.start); those on the readers' forms are the caller's.

Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Top.H.K3RunsLaw
import Johnson.Top.H.Keep.K3Inv
import OnBytes.Tie.Pv.Led.LedRowsPsc
import OnBytes.Tie.Pv.Led.LedRowsLook

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open OnBytes OnBytes.Model OnBytes.Model.Forest OnBytes.K.Kc
open OnBytes.Road.Rows (RowsIn Bare rowsIn_empty rowsIn_ofConst rowsIn_slot rowsIn_addMul
  rowsIn_scale rowsIn_add rowsIn_sub rowsIn_foldl rowsIn_rowForm)
open Cb.Fo.PlaneClaims (planesAff countAff)
open VerifiableInference.Desc.K3 (Seat Readers planesRun)
open _root_.Fo.Tp (got)

variable {Q : ℕ → ℕ → Prop}

/-- What a reader's column hands in. -/
theorem rowsIn_got (o : Option Aff) (h : ∀ f, o = some f → RowsIn Q f) (F : Fork) (c : Tape) :
    RowsIn Q (got (Fl.need o) F c) := by
  cases o with
  | none => exact rowsIn_empty
  | some f => exact h f rfl

theorem rowsIn_planesAff (g : Heard) (lm e : ℕ) (B : ℕ → Aff) (h : ∀ col, RowsIn Q (B col)) :
    RowsIn Q (planesAff g lm e B) := by
  unfold planesAff
  exact rowsIn_foldl _ (fun f col hf => rowsIn_addMul _ hf (h col)) _ _ (rowsIn_ofConst _)

theorem rowsIn_countAff (g : Heard) (lm : ℕ) (P : ℕ → Aff) (h : ∀ col, RowsIn Q (P col)) :
    RowsIn Q (countAff g lm P) := by
  unfold countAff
  exact rowsIn_foldl _ (fun f col hf => rowsIn_add hf (h col)) _ _ (rowsIn_ofConst _)

/-- **THE END.** -/
theorem planes_rowsIn {S Cl : Type} (seat : Seat S Cl) (form : Cl → Aff)
    (hform : ∀ a, form (seat.claim a) = a) (lm : ℕ) (readers : Readers S) {n : ℕ} {s s' : S}
    {cl : List Cl} {g : Heard} (hg : seat.heard s = some g)
    (hrun : planesRun seat lm readers n s = .ok (cl, s')) (hs : RowsIn Q g.leaves.start)
    (hb : ∀ r, readers s = some r → ∀ e col f, r.1 e col = some f → RowsIn Q f)
    (hp : ∀ r, readers s = some r → ∀ col f, r.2 col = some f → RowsIn Q f) :
    ∀ c ∈ cl, RowsIn Q (form c) := by
  obtain ⟨F, g1, e1, e2⟩ := planes_heard seat lm readers hrun
  obtain rfl : g = g1 := Option.some.inj (hg.symm.trans e2)
  obtain ⟨r, rows, G, u, hr, h1, rfl, _⟩ := planesRun_cut seat lm readers e1 e2 hrun
  obtain ⟨_, row, p', h2, rfl⟩ := _root_.Fo.Tp.planeClaims_run g lm _ _ (fun _ _ => quiet_need _)
    (fun _ => quiet_need _) F G [] u rows h1
  obtain ⟨-, -, -, -, -, -, rfl, -⟩ := _root_.Fo.Tp.pscRow_ok _ _ _ _ _ _ _ _ _ h2
  have b0 : ∀ e, RowsIn Q (planesAff g lm e fun col => got (Fl.need (r.1 e col)) F []) :=
    fun e => rowsIn_planesAff g lm e _ fun col => rowsIn_got _ (hb r hr e col) F []
  have c0 : RowsIn Q (countAff g lm fun col => got (Fl.need (r.2 col)) F []) :=
    rowsIn_countAff g lm _ fun col => rowsIn_got _ (hp r hr col) F []
  intro c hc
  obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hc
  rw [hform]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl
  · exact rowsIn_rowForm _ _ hs (rowsIn_scale _ (b0 0))
  · exact rowsIn_sub (rowsIn_slot _) (b0 1)
  · exact c0

/-- The same where the leaves' start form is bare. -/
theorem planes_rowsIn_bare {S Cl : Type} (seat : Seat S Cl) (form : Cl → Aff)
    (hform : ∀ a, form (seat.claim a) = a) (lm : ℕ) (readers : Readers S) {n : ℕ} {s s' : S}
    {cl : List Cl} {g : Heard} (hg : seat.heard s = some g)
    (hrun : planesRun seat lm readers n s = .ok (cl, s')) (hs : Bare g.leaves.start)
    (hb : ∀ r, readers s = some r → ∀ e col f, r.1 e col = some f → RowsIn Q f)
    (hp : ∀ r, readers s = some r → ∀ col f, r.2 col = some f → RowsIn Q f) :
    ∀ c ∈ cl, RowsIn Q (form c) :=
  planes_rowsIn seat form hform lm readers hg hrun (hs Q) hb hp

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.planes_rowsIn
#print axioms VerifiableInference.OnPublicFiles.planes_rowsIn_bare
