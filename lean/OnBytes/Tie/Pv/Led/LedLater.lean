-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Led/LedLater.lean: what is said of a sub-proof's state in the shipped Lean verifier
stays true at every later state.

A routine of a sub-proof's check gives its facts at the state at which it ends. The claims are
added, and the one equation is written, at the last state. This file carries a fact from the one
to the other.

The relation is PscRun.Later (OnBytes/Tie/Pv/Psc/PscLater.lean): every slot that is filled in F is
filled in H, with the same shown scalar and the same factor. That file has it for the routines of
the masked sumcheck, for Fork.hideRun, Fork.owe and Fork.paid. Fork.hide refuses a slot that is
filled. Beside it the marks are written only at a sub-proof's start: by Fork.slots, which each kind
of sub-proof calls once, and, in the head's check, by the new state that it makes before that call
(Head.lean, runForkHidH2: a state made anew has no marks). This is by a search for "gotF :=" and
": Fork)" in OnBytes/Model (tests aside) and OnBytes/Iop, not by a theorem. That each step behind
the call of Fork.slots leads to a later state is proved here only for the steps named below.

Main theorems.
  later_of_same (a step that leaves the marks, what was shown and the factors alone).
  hide_later, push_later, kap_later, lin_later, lins_later, batchBy_later, rootTaken_later: further
    steps of OnBytes/Model/Hide.lean.
  push_rowWeight, lin_rowWeight: adding a claim changes no virtual row's weights on the rows of its
    array.
  portWorld_slot_eq, portWorld_slot_later: under a slot that is filled in F, the world of the
    committed entries holds the same value at F and at H. The first asks only for the two
    equations on what the states hold for the slot, so it serves any relation that gives them.
  LaterRows: the virtual rows have the same weights in the two states.
  value_later: a form whose slots are all filled in F, and whose virtual rows have the same weights
    in F and H, is worth the same in the two worlds.

When a virtual row's weights are set. The field HRow.coef is set by one routine alone,
coefficientsF (OnBytes/Model/Tail.lean). The three kinds of sub-proof call it behind their last
claim and before the one equation is written (Layer.lean, runForkHidG2; Attention.lean, Seam.finish;
Head.lean, selfTests). This is by a search for "coef :=" in OnBytes/Model (tests aside), Proof, Key
and Params, and by reading the three places, not by a theorem. So a fact on an entry of a virtual
row is to be stated at a state behind that call: before it the weights are those of the plan's
state.

What this file does not claim. That the last state is later than a routine's end state is A
HYPOTHESIS of the theorems on portWorld here. It is proved for single steps: not for a claim with
runs of entries (Fork.pushRuns), not for the routine that sets the virtual rows' weights, and for no
whole routine beside those of the masked sumcheck. It does not follow from a walk (LedAdds.lean),
which says nothing of what lies under the slots.


-/
import OnBytes.Tie.Pv.Psc.PscLater
import OnBytes.Tie.Pv.Led.LedPort

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.Rows
open TWhole

/-- A step that leaves the number of slots, the marks, what was shown and the factors alone, and
takes no slot back, leads to a later state. -/
theorem later_of_same {F H : Model.Fork} (h0 : F.next ≤ H.next) (hn : H.ns = F.ns)
    (h1 : H.gotF = F.gotF) (h2 : H.vp = F.vp) (h3 : H.mf = F.mf) : PscRun.Later F H :=
  ⟨h0, hn, fun s => by
    unfold PscRun.Sized at *
    rw [h1, h2, h3, hn]
    exact s, fun j hj => ⟨by
    unfold PscRun.Filled at *
    rw [h1]
    exact hj, by rw [h2], by rw [h3]⟩⟩

theorem getD_irrel {α : Type} (a : Array α) (i : Nat) (d d' : α) (h : i < a.size) :
    a.getD i d = a.getD i d' := by
  simp [Array.getD_eq_getD_getElem?, h]

theorem hide_later {F G : Model.Fork} {j : Nat} {y f : E} (h : F.hide j y f = some G) :
    PscRun.Later F G := by
  have hs : PscRun.Sized F → PscRun.Sized G := fun s => PscRun.hide_sized s h
  obtain ⟨rfl, hn, hg, hfree⟩ := hide_spec h
  have ne : ∀ i, F.gotF.getD i false = true → i ≠ j := by
    intro i hi e
    rw [e, getD_irrel F.gotF j false true (hg ▸ hn), hfree] at hi
    cases hi
  exact ⟨Nat.le_refl _, rfl, hs, fun i hi => ⟨(getD_set_ne _ _ _ _ _ (ne i hi)).trans hi,
    getD_set_ne _ _ _ _ _ (ne i hi), getD_set_ne _ _ _ _ _ (ne i hi)⟩⟩

/-- Of the state, Fork.push changes only the arrays, the coefficients LS and the constant. -/
theorem push_same {F G : Model.Fork} {w : E} {a : Model.Aff} (h : F.push w a = some G) :
    G.next = F.next ∧ G.ns = F.ns ∧ G.gotF = F.gotF ∧ G.vp = F.vp ∧ G.mf = F.mf := by
  unfold Model.Fork.push at h
  split at h
  · simp at h
  · dsimp only at h
    split at h
    · obtain rfl := Option.some.inj h
      exact ⟨rfl, rfl, rfl, rfl, rfl⟩
    · simp at h

theorem push_later {F G : Model.Fork} {w : E} {a : Model.Aff} (h : F.push w a = some G) :
    PscRun.Later F G := by
  obtain ⟨a0, a1, a2, a3, a4⟩ := push_same h
  exact later_of_same (Nat.le_of_eq a0.symm) a1 a2 a3 a4

/-- What Fork.lin is made of: the weight is handed out, then the form is pushed. -/
theorem lin_split {F G : Model.Fork} {f : Model.Aff} (h : F.lin f = some G) :
    ∃ k F1, F.kap = some (k, F1) ∧ F1.push k f = some G := by
  unfold Model.Fork.lin at h
  cases hk : F.kap with
  | none => simp [hk] at h
  | some x => exact ⟨x.1, x.2, rfl, by simpa [hk] using h⟩

theorem kap_later {F F1 : Model.Fork} {k : E} (hk : F.kap = some (k, F1)) :
    PscRun.Later F F1 := by
  obtain ⟨_, hF1, _, _⟩ := Model.Fork.kap_spec F F1 k hk
  exact later_of_same (Nat.le_of_eq (by rw [hF1])) (by rw [hF1]) (by rw [hF1]) (by rw [hF1])
    (by rw [hF1])

theorem lin_later {F G : Model.Fork} {f : Model.Aff} (h : F.lin f = some G) :
    PscRun.Later F G := by
  obtain ⟨k, F1, hk, hp⟩ := lin_split h
  exact (kap_later hk).trans (push_later hp)

theorem lins_later : ∀ (l : List Model.Aff) (F G : Model.Fork), F.lins l = some G →
    PscRun.Later F G
  | [], F, G, h => by
    have e : F = G := by simpa [Model.Fork.lins] using h
    subst e
    exact PscRun.Later.refl _
  | f :: l, F, G, h => by
    unfold Model.Fork.lins at h
    rw [List.foldlM_cons] at h
    cases hq : F.lin f with
    | none => simp [hq] at h
    | some F1 =>
      have h2 : F1.lins l = some G := by simpa [Model.Fork.lins, hq] using h
      exact (lin_later hq).trans (lins_later l F1 G h2)

theorem batchBy_later {F G : Model.Fork} {x : E} (h : F.batchBy x = some G) :
    PscRun.Later F G := by
  unfold Model.Fork.batchBy at h
  split_ifs at h
  obtain rfl := Option.some.inj h
  exact later_of_same (Nat.le_refl _) rfl rfl rfl rfl

theorem rootTaken_later (F : Model.Fork) (t w : Nat) : PscRun.Later F (F.rootTaken t w) :=
  later_of_same (Nat.le_refl _) rfl rfl rfl rfl

/-! ## The virtual rows' weights -/

theorem getD_map {α β : Type} (g : α → β) (a : Array α) (i : Nat) (d : α) :
    (a.map g).getD i (g d) = g (a.getD i d) := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_map]
  cases a[i]? <;> rfl

variable {K : Type} [Field K] (ρ : Model.Reading K)

/-- Arrays that differ only in the values of the weights L have the same virtual rows' weights on
their rows. -/
theorem rowWeight_of_frame (a b : Array Model.HTree)
    (h : Model.treesFrame a = Model.treesFrame b) (t r : Nat) :
    rowWeight ρ a t r = rowWeight ρ b t r := by
  have h1 : Model.HTree.frame (a.getD t default) = Model.HTree.frame (b.getD t default) := by
    rw [← getD_map Model.HTree.frame a t default, ← getD_map Model.HTree.frame b t default]
    exact congrArg (fun c => c.getD t (Model.HTree.frame default)) h
  have h2 : (a.getD t default).rows.map Model.HRow.frame =
      (b.getD t default).rows.map Model.HRow.frame := congrArg Prod.snd h1
  have h3 : Model.HRow.frame ((a.getD t default).rows.getD r default) =
      Model.HRow.frame ((b.getD t default).rows.getD r default) := by
    rw [← getD_map Model.HRow.frame (a.getD t default).rows r default,
      ← getD_map Model.HRow.frame (b.getD t default).rows r default]
    exact congrArg (fun c => c.getD r (Model.HRow.frame default)) h2
  have h4 : ((a.getD t default).rows.getD r default).coef =
      ((b.getD t default).rows.getD r default).coef :=
    congrArg (fun p : Model.HRow × Nat => p.1.coef) h3
  funext i
  simp only [rowWeight, h4]

theorem push_rowWeight {F G : Model.Fork} {w : E} {a : Model.Aff} (hs : F.LS.size = F.ns)
    (h : F.push w a = some G) (t r : Nat) :
    rowWeight ρ G.trees t r = rowWeight ρ F.trees t r :=
  rowWeight_of_frame ρ _ _
    (Model.Fork.push_total ρ ⟨fun _ => 0, fun _ _ _ => 0⟩ F G w a hs h).2.2.2 t r

theorem lin_rowWeight {F G : Model.Fork} {f : Model.Aff} (hs : F.LS.size = F.ns)
    (h : F.lin f = some G) (t r : Nat) :
    rowWeight ρ G.trees t r = rowWeight ρ F.trees t r :=
  rowWeight_of_frame ρ _ _
    (Model.Fork.lin_total ρ ⟨fun _ => 0, fun _ _ _ => 0⟩ F G f hs h).2.2.2.2.2 t r

/-! ## The use -/

variable {J : Type} [Fintype J] (Y : Lay J)

/-- The virtual rows have the same weights on the rows of their arrays in the two states. This fails
from a state before the routine that sets the weights to a state behind it, for every row that the
routine sets: so a fact on an entry is to be stated at a state behind it. -/
def LaterRows (F H : Model.Fork) : Prop :=
  ∀ t r, rowWeight ρ H.trees t r = rowWeight ρ F.trees t r

/-- Where two states hold the same shown scalar and factor for a slot, the worlds of the committed
entries hold the same value under it. -/
theorem portWorld_slot_eq (F H : Model.Fork) (m : J → K) (j : Nat)
    (hv : H.vp.getD j zeroE = F.vp.getD j zeroE) (hm : H.mf.getD j zeroE = F.mf.getD j zeroE) :
    (portWorld ρ Y H m).slot j = (portWorld ρ Y F m).slot j := by
  rw [portWorld_slot, portWorld_slot, hv, hm]

/-- Under a slot that is filled in F the world of the committed entries holds the same value at
every later state. -/
theorem portWorld_slot_later {F H : Model.Fork} (L : PscRun.Later F H) (m : J → K) (j : Nat)
    (hj : PscRun.Filled F j) :
    (portWorld ρ Y H m).slot j = (portWorld ρ Y F m).slot j :=
  portWorld_slot_eq ρ Y F H m j (L.keep j hj).2.1 (L.keep j hj).2.2

/-- An entry of a virtual row with the same weights in two states has the same value. -/
theorem portWorld_entry_same (F H : Model.Fork) (m : J → K) (t r idx : Nat)
    (hw : rowWeight ρ H.trees t r = rowWeight ρ F.trees t r) :
    (portWorld ρ Y H m).entry t r idx = (portWorld ρ Y F m).entry t r idx := by
  rw [portWorld_entry, portWorld_entry, hw]

omit [Fintype J] in
/-- A form whose slots are all filled in F, and whose virtual rows have the same weights in F and
H, has the same reading at the two states. -/
theorem ofAff_later {F H : Model.Fork} (L : PscRun.Later F H) (a : Model.Aff)
    (hs : ∀ x ∈ a.slots.toList, PscRun.Filled F x.1)
    (he : ∀ x ∈ a.ents.toList,
      rowWeight ρ H.trees x.tree x.row = rowWeight ρ F.trees x.tree x.row) :
    ofAff ρ Y H a = ofAff ρ Y F a := by
  have e1 : affSum (entTerm ρ Y H.trees) a.ents.toList =
      affSum (entTerm ρ Y F.trees) a.ents.toList :=
    affSum_congr _ _ _ fun x hx => by simp only [entTerm, he x hx]
  have e2 : affSum (slotTerm ρ Y H) a.slots.toList = affSum (slotTerm ρ Y F) a.slots.toList :=
    affSum_congr _ _ _ fun x hx => by
      simp only [slotTerm,
        slotAff_congr ρ Y F H x.1 (L.keep x.1 (hs x hx)).2.1 (L.keep x.1 (hs x hx)).2.2]
  simp only [ofAff, e1, e2]

/-- Such a form is worth the same in the worlds of the two states. -/
theorem value_later {F H : Model.Fork} (L : PscRun.Later F H) (a : Model.Aff) (m : J → K)
    (hs : ∀ x ∈ a.slots.toList, PscRun.Filled F x.1)
    (he : ∀ x ∈ a.ents.toList,
      rowWeight ρ H.trees x.tree x.row = rowWeight ρ F.trees x.tree x.row) :
    a.value ρ (portWorld ρ Y H m) = a.value ρ (portWorld ρ Y F m) := by
  rw [← ofAff_val, ← ofAff_val, ofAff_later ρ Y L a hs he]

end OnBytes.Road.Rows

#print axioms OnBytes.Road.Rows.hide_later
#print axioms OnBytes.Road.Rows.lins_later
#print axioms OnBytes.Road.Rows.lin_rowWeight
#print axioms OnBytes.Road.Rows.portWorld_slot_later
#print axioms OnBytes.Road.Rows.value_later
