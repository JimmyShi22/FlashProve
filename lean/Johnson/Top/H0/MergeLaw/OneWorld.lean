-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/MergeLaw/OneWorld.lean: the form that the merge's sumcheck leaves has one value in
all
worlds that fit the entries. Theorems with their proofs.

`ClosedSays` (Johnson/Top/H0/MergeLaw/Closed.lean) asks for SOME world with `Fits2`
(Johnson/Top/H0/K11Caller/AtSlots.lean: each of the sumcheck's own slots holds its mask entry; the
slot of the claim's value holds "shown - factor * mask entry") in which the form is worth 0. Here:
which such world is taken does not matter. So "the form is worth 0 in a world that fits" is one
statement on the record behind the merge and the entries, though the own slots are filled only
later, by the kind's run of claims.

Main names:
  `sumFrom_congr`: a sum over a stretch of slots hangs on these slots alone.
  `rowForm_same`: for a sumcheck's record p whose first own slot is N.first, whose hiding polynomial
    has 2 lk + 2 coefficients and whose start form is `wsForkStart` at the claims' slots:
    `Psc.rowForm`
    with nothing kept has the same value in any two worlds with `Fits2`. By the library's
    `Psc.rowForm_value` (OnBytes/Model/HideLaws.lean) and `K11Caller.start_value`.
  `closed_same`: the same of what the merge has left in the record, behind `FrontIs` and
    `ClosedSays`.

Limits. That a world with `Fits2` exists is not shown here (ClosedRun.lean gives one from a later
ledger). An identity: no random step. Nothing on soundness or on hiding.

-/
import Johnson.Top.H0.MergeLaw.Closed

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.MergeLaw
open OnBytes (E zeroE)
open OnBytes.Flat OnBytes.Maker OnBytes.Slice
open OnBytes.Model (Reading World wsForkStart Psc sumFrom)
open Johnson.Desc.First.ForkMerge (HeadMergeP)
open K11Caller (MergeIn GS Fits2 maskOf start_value)

/-- A sum over a stretch of slots hangs on these slots alone. -/
theorem sumFrom_congr {K α : Type} [CommRing K] (g g' : ℕ → α → K) : ∀ (l : List α) (s : ℕ),
    (∀ j x, s ≤ j → j < s + l.length → g j x = g' j x) → sumFrom g s l = sumFrom g' s l
  | [], _, _ => rfl
  | x :: l, s, h => by
    simp only [sumFrom]
    rw [h s x (Nat.le_refl _) (by simp), sumFrom_congr g g' l (s + 1) fun j y h1 h2 =>
      h j y (by omega) (by simp only [List.length_cons]; omega)]

variable {Pl : K11Caller.Place} (N : K11Caller.Nums Pl)

/-- **The form that a sumcheck at the merge's slots leaves has one value in all worlds that fit the
entries.** -/
theorem rowForm_same {st : MergeIn Pl.n} {m : Pl.Cell ⊕ (Fin N.ns ⊕ Fin N.ni) → GE} {W W' : World
    GE}
    (F : Fits2 Reading.gl N st m W) (F' : Fits2 Reading.gl N st m W') (p : Psc) (rho : Array E)
    (hfirst : p.first = N.first) (hlen : p.walk.1.length = 2 * Pl.lay.lk + 2)
    (hstart : p.start = wsForkStart N.svA rho) (S0 : E) :
    (p.rowForm S0 {}).value Reading.gl W = (p.rowForm S0 {}).value Reading.gl W' := by
  rw [Psc.rowForm_value, Psc.rowForm_value, hstart, start_value, start_value, hfirst]
  have e1 : sumFrom (fun j x => Reading.gl.val x * W.slot j) N.first p.walk.1 =
      sumFrom (fun j x => Reading.gl.val x * W'.slot j) N.first p.walk.1 :=
    sumFrom_congr _ _ _ _ fun j x h1 h2 => by
      rw [F.w1 j h1 (by omega), F'.w1 j h1 (by omega)]
  have e2 : ∑ a : Fin Pl.n, Reading.gl.val (rho.getD a.val zeroE) * W.slot (N.sv a) =
      ∑ a : Fin Pl.n, Reading.gl.val (rho.getD a.val zeroE) * W'.slot (N.sv a) :=
    Finset.sum_congr rfl fun a _ => by rw [F.w2 a, F'.w2 a]
  rw [e1, e2, OnBytes.Model.Aff.value_empty, OnBytes.Model.Aff.value_empty]

variable (Rd : MergeIn Pl.n → (Pl.Cell ⊕ (Fin N.ns ⊕ Fin N.ni) → GE) → Prop)

/-- **Behind the merge's yes the form that it leaves has one value in all worlds that fit the
entries**: so "there is a world that fits in which it is worth 0" and "it is worth 0 in every world
that fits" part only where no world fits. -/
theorem closed_same (P : HeadMergeP) (hlk : Pl.lay.lk = P.lay.lk) {m : Pl.Cell ⊕ (Fin N.ns ⊕ Fin
    N.ni) → GE}
    {st : MergeIn Pl.n} {s s' : S} (hfr : FrontIs N st s) (hC : ClosedSays N Rd P m st s s')
    (a' : HeadOwn) (wo : OnBytes.Model.WsForkOut) (ha' : s'.here = .head a') (hwo : a'.wo = some wo)
    {W W' : World GE} (F : Fits2 Reading.gl N st m W) (F' : Fits2 Reading.gl N st m W') (S0 : E) :
    (wo.p.rowForm S0 {}).value Reading.gl W = (wo.p.rowForm S0 {}).value Reading.gl W' := by
  obtain ⟨a, b', claim, x0, wo', x, _, _, _, _, _, _, _, e1, e2, e3, e4, e5, _, _, _, hfirst,
      hstart, hlen, _⟩ := hC
  obtain ⟨_, _, fsv, ffirst⟩ := hfr a claim x0 e1 e3 e4
  have eb : b' = a' := by
    rw [ha'] at e2
    exact (Here.head.inj e2).symm
  subst eb
  have ew : wo' = wo := by
    rw [hwo] at e5
    exact (Option.some.inj e5).symm
  subst ew
  exact rowForm_same N F F' wo'.p (OnBytes.Model.powers x 1) (by rw [hfirst, ffirst]) (by rw [hlen,
      hlk])
    (by rw [hstart, fsv]) S0

end VerifiableInference.Desc.First.MergeLaw

#print axioms VerifiableInference.Desc.First.MergeLaw.closed_same
#print axioms VerifiableInference.Desc.First.MergeLaw.rowForm_same
