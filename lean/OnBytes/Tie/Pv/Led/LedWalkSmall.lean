-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Led/LedWalkSmall.lean: the small routines by which the sub-proofs of the shipped Lean
verifier add claims, each with the list that it adds.

Statements in the form Walks r P ol (LedWalk.lean): whenever the routine returns, its value has the
property P, the list ol is there, and the new state comes from the old one by adding just that list.

Main names.
  walks_ask, walks_must, walks_paid: reading the state, a condition, and marking an owed claim as
    added add nothing.
  walks_forM_lin: adding the claims of an array adds its entries.
  walks_pscRow: the routine that makes the claim of a sumcheck returns Psc.rowForm and adds nothing.
  walks_objects: the lookup's own claims (Forest.objects) are the rows that were kept while its
    messages were read.
  walks_joinAdded, walks_planesAdded: these add nothing.
  walks_wsForkLin: the merge's claim is the row form of its sumcheck at the value that was shown.
  walks_coefficientsF: the routine that sets the virtual rows' weights adds nothing.

What this file does not claim. What a form says. Nothing where a routine does not return.


-/
import OnBytes.Model.Merge
import OnBytes.Tie.Pv.Lookup.Port.LookLins
import OnBytes.Tie.Pv.Led.LedWalk

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.Rows

/-- Reading the state adds nothing. -/
theorem walks_ask {α : Type} (f : Model.Fork → Option α) :
    Walks (Model.SubM.ask f) (fun _ => True) (some []) :=
  walks_still fun F G c c' a hr => by
    obtain ⟨a', _, e⟩ := (PscRun.ask_ok f F c _).1 hr
    simp only [Prod.mk.injEq] at e
    exact ⟨e.1.2, trivial⟩

/-- A condition adds nothing. -/
theorem walks_must (b : Bool) : Walks (Model.SubM.must b) (fun _ => True) (some []) :=
  walks_still fun F G c c' a hr => by
    obtain ⟨_, e⟩ := (PscRun.must_ok b F c _).1 hr
    simp only [Prod.mk.injEq] at e
    exact ⟨e.1.2, trivial⟩

/-- Marking an owed claim as added adds nothing. -/
theorem walks_paid (i : Nat) : Walks (Model.SubM.paid i) (fun _ => True) (some []) :=
  walks_keep fun F G c c' a hr => by
    have e := (LookRun.paid_ok i F c _).1 hr
    simp only [Prod.mk.injEq] at e
    obtain ⟨⟨_, rfl⟩, _⟩ := e
    exact ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, trivial⟩

/-- Adding the claims of an array adds its entries. -/
theorem walks_forM_lin (rows : Array Model.Aff) :
    Walks (rows.forM Model.SubM.lin : Model.SubM PUnit) (fun _ => True) (some rows.toList) :=
  fun F G c c' _ hr =>
    ⟨trivial, _, rfl, adds_lins _ _ _ ((LookRun.forM_lin rows F G c c').1 hr).1⟩

/-- The routine that makes the claim of a sumcheck returns Psc.rowForm and adds nothing: it puts the
coefficients of the hiding polynomial under their slots. -/
theorem walks_pscRow (p : Model.Psc) (S0 : E) (kept : Model.Aff) :
    Walks (Model.pscRow p S0 kept) (fun x => x.1 = p.rowForm S0 kept) (some []) :=
  walks_keep fun F G c c' a hr => by
    obtain ⟨row, p'⟩ := a
    obtain ⟨_, _, _, _, _, hG, hrow, _⟩ := PscRun.pscRow_ok p S0 kept F G c c' row p' hr
    exact ⟨hideRun_keeps hG, hrow⟩

/-- The lookup's own claims. -/
theorem walks_objects (g : Model.Forest.Heard) :
    Walks (Model.Forest.objects g) (fun _ => True) (some g.rows.toList) := by
  unfold Model.Forest.objects
  exact walks_before (walks_forM_lin g.rows) fun _ _ => walks_paid _

theorem walks_joinAdded (g : Model.Forest.Heard) :
    Walks (Model.Forest.joinAdded g) (fun _ => True) (some []) := walks_paid _

theorem walks_planesAdded (g : Model.Forest.Heard) :
    Walks (Model.Forest.planesAdded g) (fun _ => True) (some []) := walks_paid _

/-- The merge's claim. -/
theorem walks_wsForkLin (o : Model.WsMerged) :
    Walks (Model.wsForkLin o) (fun _ => True) (some [o.p.rowForm o.fvp {}]) := by
  unfold Model.wsForkLin
  refine walks_after (walks_pscRow o.p o.fvp {}) fun x hx => ?_
  obtain ⟨row, p'⟩ := x
  obtain rfl : row = o.p.rowForm o.fvp {} := hx
  exact walks_lin _

/-- The routine that sets the virtual rows' weights adds nothing. -/
theorem walks_coefficientsF (tl : Model.HTailF2) :
    Walks tl.coefficientsF (fun _ => True) (some []) :=
  walks_keep fun F G c c' _ hr => ⟨coefficientsF_keeps tl F G c c' hr, trivial⟩

end OnBytes.Road.Rows

#print axioms OnBytes.Road.Rows.walks_objects
#print axioms OnBytes.Road.Rows.walks_wsForkLin
#print axioms OnBytes.Road.Rows.walks_coefficientsF
