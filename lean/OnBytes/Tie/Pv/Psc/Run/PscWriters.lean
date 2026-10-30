-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Tie/Pv/Psc/Run/PscWriters.lean: routines of OnBytes/Model/Trees.lean and
OnBytes/Model/Tail.lean that write the sub-proof's state directly keep the filled slots.

Main names:
  `SameSlots F G`: G has the four fields on slots of F. `SameSlots.kept`.
  `begun_slots`: behind Fork.slots n the arrays are sized and every slot is free.
  `ks_t2FillL`, `ks_kapMap`, `ks_doorShut`, `ks_pushRuns`, `ks_t2Lin`: Trees.lean.
  `same_onRow`, `ks_modify`, `ks_coefficientsF`, `ks_coefficients`: Tail.lean.
  `forIn_id_inv`, `forIn_id_inv_arr`, `id_bind_inv`: a loop in Id keeps what each of its steps
    keeps.
Limits: which routines write the state directly was found by a search of the program files for
SubM.change, SubM.take, modify and set; no statement says that the list is whole. Routines that set
the slots up anew are not among them. Nothing is said on hiding.
-/
import OnBytes.Model.Tail
import OnBytes.Tie.Pv.Psc.Run.PscFrame

set_option autoImplicit false

namespace OnBytes.Model.Road

/-- G has the four fields on slots of F. -/
structure SameSlots (F G : Fork) : Prop where
  ns : G.ns = F.ns
  vp : G.vp = F.vp
  mf : G.mf = F.mf
  got : G.gotF = F.gotF

theorem SameSlots.refl (F : Fork) : SameSlots F F := ⟨rfl, rfl, rfl, rfl⟩
theorem SameSlots.trans {F G H : Fork} (a : SameSlots F G) (b : SameSlots G H) : SameSlots F H :=
  ⟨b.ns.trans a.ns, b.vp.trans a.vp, b.mf.trans a.mf, b.got.trans a.got⟩
theorem SameSlots.kept {F G : Fork} (a : SameSlots F G) : SlotsKept F G :=
  SlotsKept.same a.ns a.vp a.mf a.got

/-- Behind the setting up: sized, and every slot free. -/
theorem begun_slots (F : Fork) (n : Nat) :
    Sized (F.slots n) ∧ (F.slots n).ns = n ∧ ∀ j, (F.slots n).gotF.getD j false = false := by
  refine ⟨sized_slots F n, rfl, fun j => ?_⟩
  show (Array.replicate n false).getD j false = false
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_replicate]
  split <;> rfl

/-! ## Trees.lean -/

theorem same_t2FillL (F : Fork) (T : Tail2) : SameSlots F (t2FillL F T) := ⟨rfl, rfl, rfl, rfl⟩

instance ks_t2FillL (T : Tail2) : KeepsSlots (SubM.change fun F => some (t2FillL F T)) :=
  ks_change _ fun F _ h => by cases h; exact (same_t2FillL F T).kept

instance ks_kapMap : KeepsSlots (SubM.change fun F =>
    some { F with kapMapF := Array.replicate F.planClaimsF false }) :=
  ks_change _ fun _ _ h => by cases h; exact SlotsKept.same rfl rfl rfl rfl

instance ks_doorShut : KeepsSlots (SubM.change fun F => some { F with doorShutF := true }) :=
  ks_change _ fun _ _ h => by cases h; exact SlotsKept.same rfl rfl rfl rfl

theorem kept_pushRuns (F G : Fork) (k : E) (runs : Array Run2) (h : F.pushRuns k runs = some G) :
    SlotsKept F G := by
  unfold Fork.pushRuns at h
  simp only [] at h
  cases e : runs.foldlM (pushRun k) F.trees with
  | none => rw [e] at h; cases h
  | some t => rw [e] at h; cases h; exact SlotsKept.same rfl rfl rfl rfl

instance ks_pushRuns (k : E) (runs : Array Run2) : KeepsSlots (SubM.change (·.pushRuns k runs)) :=
  ks_change _ fun F G h => kept_pushRuns F G k runs h

instance ks_t2Lin (a : Aff) (runs : Array Run2) : KeepsSlots (t2Lin a runs) := by unfold t2Lin; ks

/-! ## Tail.lean -/

theorem same_onRow (F : Fork) (t r : Nat) (f : HRow → HRow) : SameSlots F (HTailF2.onRow F t r f) :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- A loop in Id keeps what each of its steps keeps. -/
theorem forIn_id_inv {α β : Type} (Inv : β → Prop) (f : α → β → Id (ForInStep β))
    (hf : ∀ a b, Inv b → Inv (match f a b with | .yield x => x | .done x => x)) :
    ∀ (l : List α) (b : β), Inv b → Inv (forIn l b f : Id β)
  | [], b, h => by simpa using h
  | a :: l, b, h => by
    rw [List.forIn_cons]
    have h1 := hf a b h
    show Inv (match f a b with | .done x => x | .yield x => (forIn l x f : Id β))
    cases e : f a b with
    | done x => rw [e] at h1; exact h1
    | yield x => rw [e] at h1; exact forIn_id_inv Inv f hf l x h1

instance ks_modify (f : Fork → Fork) (hf : ∀ F, SameSlots F (f F)) : KeepsSlots (modify f :
    SubM PUnit) :=
  ⟨fun F c a G c' h => by
    have : G = f F := by
      have h' : (Except.ok ((PUnit.unit, f F), c) : Except Failure _) = .ok ((a, G), c') := h
      simp only [Except.ok.injEq, Prod.mk.injEq] at h'
      exact h'.1.2.symm
    rw [this]; exact (hf F).kept⟩

theorem forIn_id_inv_arr {α β : Type} (Inv : β → Prop) (f : α → β → Id (ForInStep β))
    (hf : ∀ a b, Inv b → Inv (match f a b with | .yield x => x | .done x => x))
    (l : Array α) (b : β) (h : Inv b) : Inv (forIn l b f : Id β) := by
  rw [← Array.forIn_toList]
  exact forIn_id_inv Inv f hf l.toList b h

theorem id_bind_inv {β γ : Type} (P : β → Prop) (Q : γ → Prop) (x : Id β) (f : β → Id γ) (hx : P x)
    (hf : ∀ b, P b → Q (f b)) : Q (x >>= f) := hf x hx

/-- coefficientsF (OnBytes/Model/Tail.lean) writes the weights of the virtual rows on the arrays
alone. -/
instance ks_coefficientsF (tl : HTailF2) : KeepsSlots tl.coefficientsF := by
  unfold HTailF2.coefficientsF
  apply KeepsSlots.bind
  · infer_instance
  intro g
  apply ks_modify
  intro F
  simp only [Id.run]
  refine id_bind_inv (SameSlots F) (SameSlots F) _ _
    (forIn_id_inv (SameSlots F) _ ?_ _ _ (SameSlots.refl F)) (fun r1 h1 => ?_)
  · intro n r hr
    cases tl.ix.U.getD n none with
    | none => exact hr
    | some t =>
      by_cases hk : ((r.trees.getD t {}).kind == HKind.table) = true
      · simp only [hk, if_true]; exact hr.trans (same_onRow _ _ _ _)
      · simp only [hk]; exact hr
  refine id_bind_inv (SameSlots F) (SameSlots F) _ _
    (forIn_id_inv (SameSlots F) _ ?_ _ _ h1) (fun r2 h2 => ?_)
  · intro q r hr
    exact forIn_id_inv_arr (SameSlots F) _ (fun p r' hr' => hr'.trans (same_onRow _ _ _ _)) _ _ hr
  refine id_bind_inv (SameSlots F) (SameSlots F) _ _
    (forIn_id_inv (SameSlots F) _ ?_ _ _ ((h2.trans (same_onRow _ _ _ _)).trans (same_onRow _ _ _
        _)))
    (fun r3 h3 => ?_)
  · intro e r hr
    exact hr.trans (same_onRow _ _ _ _)
  refine id_bind_inv (SameSlots F) (SameSlots F) _ _
    (forIn_id_inv (SameSlots F) _ ?_ _ _ (h3.trans (same_onRow _ _ _ _))) (fun r4 h4 => h4)
  intro mu r hr
  exact hr.trans (same_onRow _ _ _ _)

instance ks_coefficients (tl : HTailF2) : KeepsSlots tl.coefficients := by
  unfold HTailF2.coefficients; infer_instance

#print axioms ks_coefficientsF
#print axioms ks_t2Lin
#print axioms begun_slots

end OnBytes.Model.Road
