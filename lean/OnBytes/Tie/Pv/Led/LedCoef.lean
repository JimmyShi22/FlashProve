-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Led/LedCoef.lean: the routine of the shipped Lean verifier that sets the virtual
rows' weights adds nothing to the gathered equation.

coefficientsF (OnBytes/Model/Tail.lean) runs behind the last claim of a sub-proof and before the one
equation is written. It changes virtual rows in five loops and three single steps, each by onRow
with a function that sets the row's weights on the rows of its array and the row's product form.

Main names.
  Keeps.refl, Keeps.trans (Keeps: LedAdds.lean).
  forIn_inv, forIn_inv_array: a property that each pass of a loop keeps holds behind the loop.
  keeps_onRow: onRow with a function that leaves L and L0 keeps.
  coefficientsF_keeps: where the routine returns, the new state has the weights L, the coefficients
    LS, the constant, the count of claims, theta and the number of slots of the old one. So it is a
    step of a walk that adds nothing (Adds.keep).

What this file does not claim. Nothing on which weights the routine sets.


-/
import OnBytes.Model.Tail
import OnBytes.Tie.Pv.Psc.PscRun
import OnBytes.Tie.Pv.Led.LedAdds

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.Rows

theorem Keeps.refl (F : Model.Fork) : Keeps F F := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem Keeps.trans {F G H : Model.Fork} (a : Keeps F G) (b : Keeps G H) : Keeps F H :=
  ⟨b.keys.trans a.keys, b.LS.trans a.LS, b.c0.trans a.c0, b.nClaim.trans a.nClaim,
    b.theta.trans a.theta, b.ns.trans a.ns⟩

/-- A property that each pass of a loop over a list keeps holds behind the loop. -/
theorem forIn_inv {α β : Type} (P : β → Prop) (f : α → β → Id (ForInStep β))
    (hf : ∀ a b, P b → P (f a b).run.value) :
    ∀ (l : List α) (b : β), P b → P (forIn l b f : Id β).run
  | [], b, hb => by
    rw [List.forIn_nil]
    exact hb
  | a :: as, b, hb => by
    rw [List.forIn_cons]
    have key : ∀ x : ForInStep β, P x.value →
        P (Id.run (match x with
          | ForInStep.done b => pure b
          | ForInStep.yield b => forIn as b f)) := by
      intro x hx
      cases x with
      | done b' => exact hx
      | yield b' => exact forIn_inv P f hf as b' hx
    exact key (f a b).run (hf a b hb)

/-- The same for a loop over an array. -/
theorem forIn_inv_array {α β : Type} (P : β → Prop) (f : α → β → Id (ForInStep β))
    (hf : ∀ a b, P b → P (f a b).run.value) (xs : Array α) (b : β) (hb : P b) :
    P (forIn xs b f : Id β).run := by
  rw [← Array.forIn_toList]
  exact forIn_inv P f hf xs.toList b hb

/-- What holds of a first part's result and is carried by the rest holds of the whole. -/
theorem run_bind {β γ : Type} (P : β → Prop) (Q : γ → Prop) (x : Id β) (k : β → Id γ)
    (hx : P x.run) (hk : ∀ r, P r → Q (k r).run) : Q (x >>= k).run := hk _ hx

theorem keeps_onRow {F0 F : Model.Fork} (h : Keeps F0 F) (t r : Nat)
    (f : Model.HRow → Model.HRow) (hf : ∀ R, (f R).L = R.L ∧ (f R).L0 = R.L0) :
    Keeps F0 (Model.HTailF2.onRow F t r f) :=
  h.trans (modifyRow_keeps F t r f hf)

theorem modify_ok (f : Model.Fork → Model.Fork) (F G : Model.Fork) (c c' : Ctx)
    (h : (modify f : Model.SubM PUnit) F c = .ok ((PUnit.unit, G), c')) : G = f F :=
  (congrArg (fun r : (PUnit × Model.Fork) × Ctx => r.1.2) (Except.ok.inj h)).symm

/-- The routine that sets the virtual rows' weights adds nothing. -/
theorem coefficientsF_keeps (tl : Model.HTailF2) (F G : Model.Fork) (c c' : Ctx)
    (h : tl.coefficientsF F c = .ok (((), G), c')) : Keeps F G := by
  unfold Model.HTailF2.coefficientsF at h
  obtain ⟨g, F1, c1, h1, h2⟩ := (PscRun.bind_ok _ _ _ _ _).1 h
  obtain ⟨_, _, e⟩ := (PscRun.get_ok _ _ _ _).1 h1
  simp only [Prod.mk.injEq] at e
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := e
  rw [modify_ok _ _ _ _ _ h2]
  dsimp only
  refine run_bind (Keeps F1) (Keeps F1) _ _ ?_ fun r1 k1 => ?_
  · refine forIn_inv (Keeps F1) _ (fun n r hr => ?_) _ _ (Keeps.refl F1)
    dsimp only
    split
    · split
      · exact keeps_onRow hr _ _ _ fun _ => ⟨rfl, rfl⟩
      · exact hr
    · exact hr
  refine run_bind (Keeps F1) (Keeps F1) _ _ ?_ fun r2 k2 => ?_
  · refine forIn_inv (Keeps F1) _ (fun q r hr => ?_) _ _ k1
    dsimp only
    refine run_bind (Keeps F1) (fun x : ForInStep Model.Fork => Keeps F1 x.value) _ _ ?_
      fun r' k' => k'
    refine forIn_inv_array (Keeps F1) _ (fun p r'' hr'' => ?_) _ _ hr
    exact keeps_onRow hr'' _ _ _ fun _ => ⟨rfl, rfl⟩
  refine run_bind (Keeps F1) (Keeps F1) _ _ ?_ fun r3 k3 => ?_
  · refine forIn_inv (Keeps F1) _ (fun e r hr => ?_) _ _ ?_
    · exact keeps_onRow hr _ _ _ fun _ => ⟨rfl, rfl⟩
    · apply keeps_onRow
      · apply keeps_onRow
        · exact k2
        · exact fun _ => ⟨rfl, rfl⟩
      · exact fun _ => ⟨rfl, rfl⟩
  refine run_bind (Keeps F1) (Keeps F1) _ _ ?_ fun r4 k4 => k4
  refine forIn_inv (Keeps F1) _ (fun mu r hr => ?_) _ _ ?_
  · exact keeps_onRow hr _ _ _ fun _ => ⟨rfl, rfl⟩
  · apply keeps_onRow
    · exact k3
    · exact fun _ => ⟨rfl, rfl⟩

end OnBytes.Road.Rows

#print axioms OnBytes.Road.Rows.coefficientsF_keeps
