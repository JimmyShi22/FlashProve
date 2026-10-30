-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Led/LedPort.lean: the state of a sub-proof in the shipped Lean verifier, as a joint.

OnBytes/Model/Hide.lean keeps the claims of a sub-proof as forms (Model.Aff) that name a hidden
value by its slot and an entry of a virtual row by three numbers, and gathers them in one equation
(Model.Fork). This file reads such a form, through a reading of the program's field elements in a
field K and a lay Y of the committed entries J, as an affine form on the entries (TWhole.Aff), and
says how the steps of Model.Fork act on that reading.

Main definitions: rowWeight, portWorld, slotAff, ofAff, jointOf, claimsOf, Packed.
portWorld is the one place where the committed entries m : J → K become a world of
OnBytes/Model/HideLaws.lean: under slot j lies vp[j] - mf[j] * (entry j of the mask row), and an
entry of a virtual row is the row's combination of the array's cells.
Main theorems: ofAff_val (the value of the form that was read is Model.Aff.value in portWorld);
ofAff_hide (a form keeps its reading when another slot is filled); jointOf_hide (Fork.hide is
Joint.fill); lins_batch and one_equation (the equation that Fork.settle writes has, as its left
side, the gap of the one form batchAt of the claims that were added, numbered as the state
numbers them); batchAt_numbered (for claims numbered from 0, batchAt and Ledger.batch have the same
gap).

What this file does not claim. Nothing is said about probabilities or about hiding. The theorems
have the form "if the step returns a state, then". The lay is a free letter: an entry that a form
names and J does not have counts as 0, and no theorem here says that J has the entries of the
state's arrays. That the left side of the one equation is 0 is the chain's business.
one_equation speaks of claims that are added by Fork.lin alone, in one fold, with nothing between
the last claim and Fork.settle. The verifier's run also adds claims that hold runs of entries, and
fills slots between claims, so one_equation does not apply to a whole run as it stands;
LedAdds.lean (settle_batch_iff) has the form on totals that does.


-/
import OnBytes.Model.HideLaws
import OnBytes.Model.FormF
import OnBytes.Tie.Pv.Led.LedJoint
import Mathlib.Algebra.BigOperators.Fin

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.Rows
open TWhole

variable {K J : Type} [Field K] [Fintype J] (ρ : Model.Reading K) (Y : Lay J)

/-! ## Reading a form -/

/-- The weight of virtual row r of array t on the array's row i. -/
def rowWeight (trees : Array Model.HTree) (t r i : Nat) : K :=
  ρ.val (((trees.getD t default).rows.getD r default).coef.getD i zeroE)

/-- The world of OnBytes/Model/HideLaws.lean that the committed entries m give at a state F. -/
def portWorld (F : Model.Fork) (m : J → K) : Model.World K :=
  F.worldOf ρ (Y.maskAt m) fun t r idx => Y.entryAt m t (rowWeight ρ F.trees t r) idx

theorem portWorld_slot (F : Model.Fork) (m : J → K) (j : Nat) :
    (portWorld ρ Y F m).slot j =
      ρ.val (F.vp.getD j zeroE) - ρ.val (F.mf.getD j zeroE) * Y.maskAt m j := rfl

theorem portWorld_entry (F : Model.Fork) (m : J → K) (t r idx : Nat) :
    (portWorld ρ Y F m).entry t r idx = Y.entryAt m t (rowWeight ρ F.trees t r) idx := rfl

/-- The cells M of the matrices are packed in the symbol arrays of m: three cells of a column, from
the rows 3 i, 3 i + 1 and 3 i + 2, make the symbol cell 0 + B * cell 1 + B^2 * cell 2 in row i, with
the radix B of OnBytes/Model/FormF.lean. sym: the number of the symbol array of a matrix. -/
def Packed (sym : Nat → Nat) (m : J → K) (M : Nat → Nat → Nat → K) : Prop :=
  ∀ mat i c, Y.cellAt m (sym mat) i c =
    M mat (3 * i) c + (Model.radb : K) * M mat (3 * i + 1) c +
      (Model.radb : K) ^ 2 * M mat (3 * i + 2) c

/-- The hidden value under slot j at a state F, as a form on the entries. -/
def slotAff (F : Model.Fork) (j : Nat) : Aff K J :=
  Y.hid (fun s => ρ.val (F.vp.getD s zeroE)) (fun s => ρ.val (F.mf.getD s zeroE)) j

/-- One entry of a virtual row with its coefficient, as a form on the entries. -/
def entTerm (trees : Array Model.HTree) (x : Model.Ent) : Aff K J :=
  affAddMul (affConst 0) (Y.ent x.tree (rowWeight ρ trees x.tree x.row) x.idx) (ρ.val x.coef)

/-- One slot with its coefficient, as a form on the entries. -/
def slotTerm (F : Model.Fork) (x : Nat × E) : Aff K J :=
  affAddMul (affConst 0) (slotAff ρ Y F x.1) (ρ.val x.2)

/-- A form of the program, read at a state F as a form on the entries. -/
def ofAff (F : Model.Fork) (a : Model.Aff) : Aff K J :=
  affAddMul
    (affAddMul (affSum (entTerm ρ Y F.trees) a.ents.toList)
      (affSum (slotTerm ρ Y F) a.slots.toList) 1)
    (affConst (ρ.val a.const)) 1

theorem slotAff_val (F : Model.Fork) (j : Nat) (m : J → K) :
    (slotAff ρ Y F j).val m = (portWorld ρ Y F m).slot j := by
  rw [slotAff, Lay.hid_val, portWorld_slot]

/-- The form that was read has, on the entries m, the value that OnBytes/Model/HideLaws.lean gives
the program's form in the world of m. -/
theorem ofAff_val (F : Model.Fork) (a : Model.Aff) (m : J → K) :
    (ofAff ρ Y F a).val m = a.value ρ (portWorld ρ Y F m) := by
  have e1 : ∀ x, (entTerm ρ Y F.trees x).val m =
      Model.Ent.value ρ (portWorld ρ Y F m) x := by
    intro x
    simp only [entTerm, affAddMul_val, affConst_val, Lay.ent_val, Model.Ent.value,
      portWorld_entry]
    ring
  have e2 : ∀ x, (slotTerm ρ Y F x).val m = Model.slotValue ρ (portWorld ρ Y F m) x := by
    intro x
    simp only [slotTerm, affAddMul_val, affConst_val, slotAff_val, Model.slotValue]
    ring
  simp only [ofAff, affAddMul_val, affSum_val, affConst_val, e1, e2, Model.Aff.value]
  ring

/-! ## Filling a slot -/

theorem getD_set_ne {α : Type} (a : Array α) (j i : Nat) (v d : α) (h : i ≠ j) :
    (a.set! j v).getD i d = a.getD i d := by
  simp [Array.getD_eq_getD_getElem?, Ne.symm h]

theorem getD_set_eq {α : Type} (a : Array α) (j : Nat) (v d : α) (h : j < a.size) :
    (a.set! j v).getD j d = v := by
  simp [Array.getD_eq_getD_getElem?, h]

theorem update_getD {α β : Type} (a : Array α) (j : Nat) (v d : α) (g : α → β)
    (hs : j < a.size) :
    (fun i : Nat => g ((a.set! j v).getD i d)) =
      Function.update (fun i : Nat => g (a.getD i d)) j (g v) := by
  funext i
  by_cases e : i = j
  · subst e
    rw [Function.update_self]
    exact congrArg g (getD_set_eq a i v d hs)
  · rw [Function.update_of_ne e, getD_set_ne a j i v d e]

/-- What Fork.hide does where it returns a state: the slot is inside the number of slots and was
free, and only the slot's mark, what was shown and the factor change. -/
theorem hide_spec {F G : Model.Fork} {j : Nat} {y f : E} (h : F.hide j y f = some G) :
    G = { F with gotF := F.gotF.set! j true, vp := F.vp.set! j y, mf := F.mf.set! j f } ∧
      j < F.ns ∧ F.gotF.size = F.ns ∧ F.gotF.getD j true = false := by
  unfold Model.Fork.hide at h
  split_ifs at h with hc
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Bool.not_eq_true'] at hc
  exact ⟨(Option.some.inj h).symm, hc.1.1, hc.1.2, hc.2⟩

omit [Fintype J] in
theorem affSum_congr {α : Type} (g h : α → Aff K J) (l : List α) (H : ∀ x ∈ l, g x = h x) :
    affSum g l = affSum h l := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    simp only [affSum]
    rw [H x (List.mem_cons_self ..), ih fun y hy => H y (List.mem_cons_of_mem _ hy)]

omit [Fintype J] in
/-- The reading of the hidden value under slot i hangs on what the state holds for slot i alone. -/
theorem slotAff_congr (F G : Model.Fork) (i : Nat) (hv : G.vp.getD i zeroE = F.vp.getD i zeroE)
    (hm : G.mf.getD i zeroE = F.mf.getD i zeroE) : slotAff ρ Y G i = slotAff ρ Y F i := by
  simp only [slotAff, Lay.hid, hv, hm]

omit [Fintype J] in
/-- The hidden value under another slot keeps its reading when slot j is filled. -/
theorem slotAff_hide {F G : Model.Fork} {j : Nat} {y f : E} (h : F.hide j y f = some G) (i : Nat)
    (hi : i ≠ j) : slotAff ρ Y G i = slotAff ρ Y F i := by
  obtain ⟨rfl, _, _, _⟩ := hide_spec h
  exact slotAff_congr ρ Y _ _ i (getD_set_ne _ _ _ _ _ hi) (getD_set_ne _ _ _ _ _ hi)

omit [Fintype J] in
/-- A form that does not name slot j keeps its reading when slot j is filled. Fork.hide refuses a
slot that is filled, so a form whose slots were all filled when it was made keeps the reading of its
slots under every later Fork.hide. The reading of its entries of virtual rows still changes when the
rows' weights are set. -/
theorem ofAff_hide {F G : Model.Fork} {j : Nat} {y f : E} (h : F.hide j y f = some G)
    (a : Model.Aff) (ha : ∀ x ∈ a.slots.toList, x.1 ≠ j) : ofAff ρ Y G a = ofAff ρ Y F a := by
  have ht : G.trees = F.trees := by
    obtain ⟨rfl, _⟩ := hide_spec h
    rfl
  have e : affSum (slotTerm ρ Y G) a.slots.toList = affSum (slotTerm ρ Y F) a.slots.toList :=
    affSum_congr _ _ _ fun x hx => by simp only [slotTerm, slotAff_hide ρ Y h x.1 (ha x hx)]
  simp only [ofAff, ht, e]

/-! ## The state as a joint -/

/-- The joint that a state of the program gives. The state keeps no list of forms (it keeps the
weighted sum of its claims), so the list owed is an argument: the program's forms, read at F. pub
and opens are the caller's. -/
def jointOf {P : Type} (p : P) (F : Model.Fork) (owed : List Model.Aff)
    (opens : List (Open K J)) : Joint P K J where
  pub := p
  com := fun t => ((F.trees.getD t default).root).isSome
  next := F.next
  got := fun j => F.gotF.getD j false
  vp := fun j => ρ.val (F.vp.getD j zeroE)
  mf := fun j => ρ.val (F.mf.getD j zeroE)
  owed := owed.map fun a => (ofAff ρ Y F a).claim
  opens := opens

omit [Fintype J] in
/-- The hidden value of the joint is the reading of the program's slot. -/
theorem jointOf_hid {P : Type} (p : P) (F : Model.Fork) (owed : List Model.Aff)
    (opens : List (Open K J)) (j : Nat) :
    (jointOf ρ Y p F owed opens).hid Y j = slotAff ρ Y F j := rfl

omit [Fintype J] in
/-- Fork.hide is Joint.fill, for a state whose lists vp and mf have one element for each slot and
for owed claims that do not name the slot. -/
theorem jointOf_hide {P : Type} (p : P) {F G : Model.Fork} {j : Nat} {y f : E}
    (h : F.hide j y f = some G) (hv : F.vp.size = F.ns) (hm : F.mf.size = F.ns)
    (owed : List Model.Aff) (opens : List (Open K J))
    (ho : ∀ a ∈ owed, ∀ x ∈ a.slots.toList, x.1 ≠ j) :
    jointOf ρ Y p G owed opens = (jointOf ρ Y p F owed opens).fill j (ρ.val y) (ρ.val f) := by
  have c2 : (owed.map fun a => (ofAff ρ Y G a).claim) =
      owed.map fun a => (ofAff ρ Y F a).claim :=
    List.map_congr_left fun a ha => by rw [ofAff_hide ρ Y h a (ho a ha)]
  obtain ⟨hG, hn, hg, _⟩ := hide_spec h
  subst hG
  exact Joint.ext rfl rfl rfl
    (update_getD F.gotF j true false id (hg ▸ hn))
    (update_getD F.vp j y zeroE ρ.val (hv ▸ hn))
    (update_getD F.mf j f zeroE ρ.val (hm ▸ hn)) c2 rfl

/-! ## The one equation -/

omit [Fintype J] in
theorem sumFrom_pow {α : Type} (x : K) (g : α → K) : ∀ (l : List α) (s : Nat),
    Model.sumFrom (fun i f => x ^ i * g f) s l =
      ∑ c : Fin l.length, x ^ (s + (c : ℕ)) * g (l.get c)
  | [], _ => (Fin.sum_univ_zero _).symm
  | f :: l, s => by
    show x ^ s * g f + Model.sumFrom (fun i f => x ^ i * g f) (s + 1) l =
      ∑ c : Fin (l.length + 1), x ^ (s + (c : ℕ)) * g ((f :: l).get c)
    rw [Fin.sum_univ_succ, sumFrom_pow x g l (s + 1)]
    refine congrArg₂ (· + ·) (by simp) (Finset.sum_congr rfl fun c _ => ?_)
    have e : s + 1 + (c : ℕ) = s + ((c.succ : Fin (l.length + 1)) : ℕ) := by
      rw [Fin.val_succ]
      omega
    have e2 : (f :: l).get c.succ = l.get c := rfl
    rw [e, e2]

omit [Fintype J] in
theorem sumFrom_map {α β : Type} (g : Nat → β → K) (h : α → β) : ∀ (l : List α) (s : Nat),
    Model.sumFrom g s (l.map h) = Model.sumFrom (fun i x => g i (h x)) s l
  | [], _ => rfl
  | x :: l, s => by simp only [List.map_cons, Model.sumFrom, sumFrom_map g h l (s + 1)]

/-- The gap of the one form of a ledger under the exponents c, c + 1 and so on. -/
theorem batchAt_range_gap (x : K) (m : J → K) : ∀ (l : TWhole.Ledger K J) (c : Nat),
    (batchAt x ((List.range' c l.length).zip l)).gap m =
      Model.sumFrom (fun i f => x ^ i * f.gap m) c l
  | [], c => by simp [batchAt_gap, Model.sumFrom]
  | f :: l, c => by
    have ih := batchAt_range_gap x m l (c + 1)
    rw [batchAt_gap] at ih ⊢
    simp only [List.length_cons, List.range'_succ, List.zip_cons_cons, List.map_cons,
      List.sum_cons, Model.sumFrom, ih]

/-- Under the exponents 0, 1 and so on, the one form of this file and Ledger.batch have the same
gap. -/
theorem batchAt_numbered (x : K) (m : J → K) (l : TWhole.Ledger K J) :
    (batchAt x ((List.range' 0 l.length).zip l)).gap m = (TWhole.Ledger.batch l x).gap m := by
  have e := sumFrom_pow x (fun f : TWhole.Form K J => f.gap m) l 0
  simp only [Nat.zero_add] at e
  rw [batchAt_range_gap, TWhole.Ledger.batch_gap, e]

/-- The ledger of a list of the program's forms, read at a state H. -/
def claimsOf (H : Model.Fork) (l : List Model.Aff) : TWhole.Ledger K J :=
  l.map fun a => (ofAff ρ Y H a).claim

/-- The gap of the one form of a list of claims, read at a state H, under the exponents c, c + 1
and so on, is the weighted sum of the values of the program's forms (Model.claimsValue). -/
theorem batch_claimsValue (H : Model.Fork) (l : List Model.Aff) (c : Nat) (x : K) (m : J → K) :
    (batchAt x ((List.range' c l.length).zip (claimsOf ρ Y H l))).gap m =
      Model.claimsValue ρ (portWorld ρ Y H m) x c l := by
  have e := batchAt_range_gap x m (claimsOf ρ Y H l) c
  rw [claimsOf, List.length_map] at e
  rw [claimsOf, e, sumFrom_map]
  simp only [claim_gap, ofAff_val, Model.claimsValue]

/-- Adding a list of claims adds to the gathered total the gap of the one form of these claims,
under the state's theta and the exponents from the state's count of claims on. H is the state at
which the forms are read; in use it is the last one. -/
theorem lins_batch (H F G : Model.Fork) (l : List Model.Aff) (hs : F.LS.size = F.ns)
    (h : F.lins l = some G) (m : J → K) :
    G.total ρ (portWorld ρ Y H m) = F.total ρ (portWorld ρ Y H m) +
      (batchAt (ρ.val F.theta)
        ((List.range' F.nClaim l.length).zip (claimsOf ρ Y H l))).gap m := by
  rw [batch_claimsValue, (Model.Fork.lins_total ρ (portWorld ρ Y H m) l F G hs h).1]

/-- The one equation, for a run that adds its claims by Fork.lin alone, one behind the other. The
sub-proofs of the model also add claims with runs of entries and take other steps between two
claims: for these see settle_batch (LedAdds.lean). Let a state F have the total 0, let the claims l
be added, which gives G, and
let Fork.settle at a later state H return the coefficients mc on the mask row and the constant c.
Between G and H the gathered total must not have changed (hk): the program sets the weights of
some virtual rows on their arrays' rows only there, which changes no weight L. Then the left side
of the equation that goes to the chain (the weights L on the virtual rows, mc on the mask row, and
c) is the gap of the one form of the claims l, read at H. -/
theorem one_equation (F G H : Model.Fork) (l : List Model.Aff) (used : Nat) (mc : Array E) (c : E)
    (m : J → K) (hs : F.LS.size = F.ns) (ht : F.total ρ (portWorld ρ Y H m) = 0)
    (h : F.lins l = some G)
    (hk : H.total ρ (portWorld ρ Y H m) = G.total ρ (portWorld ρ Y H m))
    (hset : H.settle used = some (mc, c)) :
    Model.treesValue ρ (portWorld ρ Y H m) H.trees + Model.maskValue ρ (Y.maskAt m) mc + ρ.val c =
      (batchAt (ρ.val F.theta)
        ((List.range' F.nClaim l.length).zip (claimsOf ρ Y H l))).gap m := by
  have e := Model.Fork.settle_whole ρ H used mc c (Y.maskAt m)
    (fun t r idx => Y.entryAt m t (rowWeight ρ H.trees t r) idx) hset
  have e2 := lins_batch ρ Y H F G l hs h m
  rw [ht, zero_add] at e2
  rw [← e2, ← hk]
  exact e

end OnBytes.Road.Rows

#print axioms OnBytes.Road.Rows.ofAff_val
#print axioms OnBytes.Road.Rows.ofAff_hide
#print axioms OnBytes.Road.Rows.jointOf_hide
#print axioms OnBytes.Road.Rows.batchAt_numbered
#print axioms OnBytes.Road.Rows.lins_batch
#print axioms OnBytes.Road.Rows.one_equation
