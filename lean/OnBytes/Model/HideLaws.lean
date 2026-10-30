-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Model/HideLaws.lean: theorems on what Fork.push and Fork.lin add to the one equation.

OnBytes/Model/Hide.lean gathers the claims of a sub-proof in one equation. This file says what
Fork.push and Fork.lin add to that equation, and how Fork.settle rewrites it on the mask row. The
program does not import this file. Of its theorems on Fork, SubM and the sumcheck only
Model/TreesLaws.lean uses any, and no file imports that one, so no theorem on the program's decision
rests on them. Other files use Reading and Reading.gl.

Main definitions: Reading, Reading.gl, World, Aff.value, Fork.total, Fork.worldOf, Fork.lins. The
setting and the words are explained at Reading. Main theorems: Reading.pow, dot, polyAt;
Aff.value_addMul; Fork.total_start, push_total, kap_spec, lin_total, lins_total, settle_total,
settle_whole; Psc.rowForm_value; complete_sum.

What this file does not claim. Nothing is said about probabilities, about what a verifier's
acceptance shows, about hiding, or about the chain. Where a theorem equates values in K, the
equation is between readings, not between the program's elements of E: a reading need not be
one-to-one. Many theorems have the form "if the step returns a state, then": they say nothing where
a step refuses. That the steps do return states is not proved. A test (OnBytes/Model/TestPsc.lean)
runs them on small values set by hand, and on two small sumchecks with the messages of a prover that
is written in the test itself.

The measures (Aff.value, Fork.total and the others) are this file's own definitions: a theorem says
no more than they do, and none reaches the equation that is passed to the chain (see Fork.total). No
theorem but Fork.total_start says that a total is 0. Of the sumcheck only single steps are read in
K; what Psc.walk computes and how the routines follow each other is not stated. No theorem says that
Fork.hide, Fork.batchBy and others leave the weights alone. The sums with powers of theta are
identities at one element, not statements about a polynomial in theta (see Fork.lins_total). A
routine that changes the weights L by its own steps needs its own theorem (see Fork.push_total).
-/
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import OnBytes.Model.Tsc
import OnBytes.Field.ExtEq
import OnBytes.Slice.Field

namespace OnBytes.Model

/-! ## Readings and worlds -/

/-- A reading: a map from E to a commutative ring K that takes the program's 0, 1, sum, difference
and product to those of K. Every theorem here holds for every reading.

Words. Sub-proof, hidden value, slot, mask row, form (Aff), claim, virtual row, array, state (Fork),
theta, the chain, and the fields L, LS, c0, vp and mf are explained in OnBytes/Model/Hide.lean, at
Fork, Aff, Fork.lin and SubM. The sumcheck and its hiding polynomial are explained in
OnBytes/Model/Psc.lean, at Psc, and at the head of OnBytes/Iop/Psc.lean. In the section on the
sumcheck, w is a weight (OnBytes.Psc.Weight): it says how a polynomial in one variable is summed,
and w.moment holds the sums of 1, X, X^2 and so on. In the theorems on Fork.push, w is an element of
E, the factor of the form that is added.

The setting. In this file "the program" is not the C++ verifier but verify-on-bytes, the Lean
verifier in OnBytes/; this repository builds no stand-alone program from it. It computes on elements
of E, each three machine words. A world (World K) gives every hidden value a value in K: one for
each slot, and one for each entry of each virtual row. Below, weights or coefficients applied to
values means the sum of weight times value. -/
structure Reading (K : Type) [CommRing K] where
  /-- the map -/
  val : E → K
  /-- it takes 0 to 0 -/
  zero : val zeroE = 0
  /-- it takes 1 to 1 -/
  one : val oneE = 1
  /-- it takes sums to sums -/
  add : ∀ a b, val (addE a b) = val a + val b
  /-- it takes differences to differences -/
  sub : ∀ a b, val (subE a b) = val a - val b
  /-- it takes products to products -/
  mul : ∀ a b, val (mulE a b) = val a * val b

/-- The reading in the library's extension field Cb.Gl.E. A word that is not below the prime counts
as its residue. -/
def Reading.gl : Reading Cb.Gl.E where
  val := fun x => Slice.toE x.triple
  zero := by simp only [zeroE_triple]; exact Slice.toE_zeroE
  one := by simp only [oneE_triple]; exact Slice.toE_oneE
  add := fun a b => by simp only [addE_triple]; exact Slice.toE_addE a.triple b.triple
  sub := fun a b => by simp only [subE_triple]; exact Slice.toE_subE a.triple b.triple
  mul := fun a b => by simp only [mulE_triple]; exact Slice.toE_mulE a.triple b.triple

/-- A value for every hidden value. -/
structure World (K : Type) where
  /-- the hidden value under a slot -/
  slot : Nat → K
  /-- the entry of a virtual row: array, virtual row, index -/
  entry : Nat → Nat → Nat → K

variable {K : Type} [CommRing K] (ρ : Reading K) (W : World K)

/-- The loop that computes a power returns, read in K, r times x^e, if it is given at least e
steps. -/
theorem Reading.powLoop : ∀ (k : Nat) (x : E) (e : Nat) (r : E), e ≤ k →
    ρ.val (powLoopE k x e r) = ρ.val r * ρ.val x ^ e
  | 0, x, e, r, h => by
    have h0 : e = 0 := by omega
    subst h0
    rw [powLoopE_zero]; simp
  | k + 1, x, e, r, h => by
    by_cases he : e = 0
    · subst he
      rw [powLoopE_zero]; simp
    · rw [powLoopE_step k x e r he, Reading.powLoop k (mulE x x) (e / 2) _ (by omega), ρ.mul]
      have hsplit : e = 2 * (e / 2) + e % 2 := by omega
      by_cases ho : e % 2 = 1
      · rw [if_pos ho, ρ.mul]
        conv_rhs => rw [hsplit, ho]
        ring
      · have h0 : e % 2 = 0 := by omega
        rw [if_neg ho]
        conv_rhs => rw [hsplit, h0]
        ring

/-- The reading of powE x e is the reading of x to the power e. -/
theorem Reading.pow (x : E) (e : Nat) : ρ.val (powE x e) = ρ.val x ^ e := by
  unfold powE
  rw [ρ.powLoop e x e oneE (Nat.le_refl e), ρ.one, one_mul]

/-! ## Sums over lists -/

/-- The sum of g i x over the elements x of a list, i counting from a start. -/
def sumFrom {α : Type} (g : Nat → α → K) : Nat → List α → K
  | _, [] => 0
  | i, x :: l => g i x + sumFrom g (i + 1) l

/-- Changing one element of a list changes the sum by the difference at that element. -/
theorem sumFrom_modify {α : Type} (g : Nat → α → K) (f : α → α) :
    ∀ (l : List α) (s k : Nat) (x : α), l[k]? = some x →
      sumFrom g s (l.modify k f) = sumFrom g s l + (g (s + k) (f x) - g (s + k) x)
  | [], _, _, _, h => by simp at h
  | y :: l, s, 0, x, h => by
    have hy : y = x := by simpa using h
    subst hy
    rw [List.modify_zero_cons]
    simp only [sumFrom, Nat.add_zero]
    ring
  | y :: l, s, k + 1, x, h => by
    have h' : l[k]? = some x := by simpa using h
    rw [List.modify_succ_cons]
    simp only [sumFrom]
    rw [sumFrom_modify g f l (s + 1) k x h']
    have hi : s + 1 + k = s + (k + 1) := by omega
    rw [hi]
    ring

/-- Replacing one element of a list changes the sum by the difference at that element. -/
theorem sumFrom_set {α : Type} (g : Nat → α → K) (y : α) :
    ∀ (l : List α) (s k : Nat) (x : α), l[k]? = some x →
      sumFrom g s (l.set k y) = sumFrom g s l + (g (s + k) y - g (s + k) x)
  | [], _, _, _, h => by simp at h
  | z :: l, s, 0, x, h => by
    have hz : z = x := by simpa using h
    subst hz
    simp only [List.set_cons_zero, sumFrom, Nat.add_zero]
    ring
  | z :: l, s, k + 1, x, h => by
    have h' : l[k]? = some x := by simpa using h
    simp only [List.set_cons_succ, sumFrom]
    rw [sumFrom_set g y l (s + 1) k x h']
    have hi : s + 1 + k = s + (k + 1) := by omega
    rw [hi]
    ring

/-- If g i x is 0 for every element x of the list and every i, the sum is 0. -/
theorem sumFrom_eq_zero {α : Type} (g : Nat → α → K) :
    ∀ (l : List α) (s : Nat), (∀ i x, x ∈ l → g i x = 0) → sumFrom g s l = 0
  | [], _, _ => rfl
  | x :: l, s, H => by
    simp only [sumFrom]
    rw [H s x (by simp), sumFrom_eq_zero g l (s + 1) (fun i y hy => H i y (by simp [hy])), add_zero]

/-- A sum of multiples is the multiple of the sum. -/
theorem sum_map_scale {α : Type} (g h : α → K) (c : K) (H : ∀ x, h x = c * g x) (l : List α) :
    (l.map h).sum = c * (l.map g).sum := by
  induction l with
  | nil => simp
  | cons x l ih => simp [H, ih, mul_add]

/-- A fold of steps that may refuse. If each step keeps a condition and adds g a to a value, the
whole fold keeps the condition and adds the sum. -/
theorem foldlM_adds {α σ : Type} (f : σ → α → Option σ) (inv : σ → Prop) (val : σ → K) (g : α → K)
    (H : ∀ s a s', inv s → f s a = some s' → inv s' ∧ val s' = val s + g a) :
    ∀ (l : List α) (s s' : σ), inv s → l.foldlM f s = some s' →
      inv s' ∧ val s' = val s + (l.map g).sum
  | [], s, s', hi, h => by
    have hs : s = s' := by simpa using h
    subst hs
    simp [hi]
  | a :: l, s, s', hi, h => by
    rw [List.foldlM_cons] at h
    cases hq : f s a with
    | none => simp [hq] at h
    | some t =>
      rw [hq] at h
      have h2 : l.foldlM f t = some s' := by simpa using h
      obtain ⟨hit, hvt⟩ := H s a t hi hq
      obtain ⟨his, hvs⟩ := foldlM_adds f inv val g H l t s' hit h2
      refine ⟨his, ?_⟩
      rw [hvs, hvt, List.map_cons, List.sum_cons]
      ring

/-- Pushing f x onto a, for each x of b in order, gives the list of a followed by the image of b
under f. -/
theorem foldl_push_toList {α β : Type} (f : α → β) (b : Array α) (a : Array β) :
    (b.foldl (fun l x => l.push (f x)) a).toList = a.toList ++ b.toList.map f := by
  rw [← Array.foldl_toList]
  generalize b.toList = l
  induction l generalizing a with
  | nil => simp
  | cons x l _ => simp

/-! ## The value of a form -/

/-- The value of one entry with its coefficient. -/
def Ent.value (x : Ent) : K := ρ.val x.coef * W.entry x.tree x.row x.idx

/-- The value of one slot with its coefficient. -/
def slotValue (x : Nat × E) : K := ρ.val x.2 * W.slot x.1

/-- The value of a form in a world. -/
def Aff.value (a : Aff) : K :=
  (a.ents.toList.map (Ent.value ρ W)).sum + (a.slots.toList.map (slotValue ρ W)).sum +
    ρ.val a.const

/-- The value of a constant form is the constant. -/
theorem Aff.value_ofConst (v : E) : (Aff.ofConst v).value ρ W = ρ.val v := by
  simp [Aff.value, Aff.ofConst]

/-- The value of the form Aff.slot j is the hidden value under slot j. -/
theorem Aff.value_slot (j : Nat) : (Aff.slot j).value ρ W = W.slot j := by
  simp [Aff.value, Aff.slot, slotValue, ρ.one, ρ.zero]

/-- The value of the form Aff.ent t r i is entry i of virtual row r of array t. -/
theorem Aff.value_ent (t r i : Nat) : (Aff.ent t r i).value ρ W = W.entry t r i := by
  simp [Aff.value, Aff.ent, Ent.value, ρ.one, ρ.zero]

/-- The value of the empty form is 0. -/
theorem Aff.value_empty : ({} : Aff).value ρ W = 0 := by
  simp [Aff.value, ρ.zero]

/-- The value of a + k b is the value of a plus k times the value of b. -/
theorem Aff.value_addMul (a b : Aff) (k : E) :
    (Aff.addMul a b k).value ρ W = a.value ρ W + ρ.val k * b.value ρ W := by
  have he : (b.ents.toList.map
      (fun x => Ent.value ρ W { x with coef := mulE x.coef k })).sum =
      ρ.val k * (b.ents.toList.map (Ent.value ρ W)).sum :=
    sum_map_scale _ _ _ (fun x => by simp only [Ent.value, ρ.mul]; ring) _
  have hs : (b.slots.toList.map (fun x => slotValue ρ W (x.1, mulE x.2 k))).sum =
      ρ.val k * (b.slots.toList.map (slotValue ρ W)).sum :=
    sum_map_scale _ _ _ (fun x => by simp only [slotValue, ρ.mul]; ring) _
  simp only [Aff.value, Aff.addMul, foldl_push_toList, List.map_append, List.sum_append,
    List.map_map, Function.comp_def, ρ.add, ρ.mul]
  rw [he, hs]
  ring

/-- The value of k a is k times the value of a. -/
theorem Aff.value_scale (a : Aff) (k : E) :
    (Aff.scale a k).value ρ W = ρ.val k * a.value ρ W := by
  rw [Aff.scale, Aff.value_addMul, Aff.value_empty, zero_add]

/-- The value of a sum is the sum of the values. -/
theorem Aff.value_add (a b : Aff) : (a + b).value ρ W = a.value ρ W + b.value ρ W := by
  show (Aff.addMul a b oneE).value ρ W = _
  rw [Aff.value_addMul, ρ.one, one_mul]

/-- The value of a difference is the difference of the values. -/
theorem Aff.value_sub (a b : Aff) : (a - b).value ρ W = a.value ρ W - b.value ρ W := by
  show (Aff.addMul a b (subE zeroE oneE)).value ρ W = _
  rw [Aff.value_addMul, ρ.sub, ρ.zero, ρ.one]
  ring

/-! ## The value of the gathered equation -/

/-- The sum over i of L[i] times entry L0 + i of the virtual row: the row's weights L, applied to
the row's entries in the world W. t, r: the numbers of the array and of the row. -/
def HRow.value (t r : Nat) (R : HRow) : K :=
  sumFrom (fun i v => ρ.val v * W.entry t r i) R.L0 R.L.toList

/-- The sum of HRow.value over the virtual rows of an array. -/
def HTree.value (t : Nat) (X : HTree) : K :=
  sumFrom (fun r R => HRow.value ρ W t r R) 0 X.rows.toList

/-- The sum of HTree.value over the arrays. -/
def treesValue (trees : Array HTree) : K :=
  sumFrom (fun t X => HTree.value ρ W t X) 0 trees.toList

/-- The sum over the slots j of LS[j] times the hidden value under slot j. -/
def slotsValue (LS : Array E) : K := sumFrom (fun j v => ρ.val v * W.slot j) 0 LS.toList

/-- The value in a world of the left side of the equation "... = 0" that a state has gathered:
treesValue of its arrays, plus slotsValue of LS, plus c0.

The measures (Aff.value, Fork.total, treesValue, slotsValue and the others) and Fork.lins are
definitions of this file, not of the program: a theorem says no more than they do. The entries of
virtual rows are arbitrary values of a world here, and so are the values under the slots. In
Fork.settle_total and Fork.settle_whole the mask row is any function: no theorem ties it to a
committed row, and none but Fork.total_start (a fresh state) says that a total is 0. No theorem here
says that an entry of a virtual row is the combination coef of the rows of a committed array, so the
theorems do not reach the equation that is passed to the chain. -/
def Fork.total (F : Fork) : K := treesValue ρ W F.trees + slotsValue ρ W F.LS + ρ.val F.c0

/-- A virtual row with its weights L removed, and the number of those weights. -/
def HRow.frame (R : HRow) : HRow × Nat := ({ R with L := #[] }, R.L.size)

/-- An array with its virtual rows removed, and HRow.frame of each of those rows. -/
def HTree.frame (X : HTree) : HTree × Array (HRow × Nat) :=
  ({ X with rows := #[] }, X.rows.map HRow.frame)

/-- Everything that the arrays hold except the values of the weights L. How many weights each
virtual row has is kept. -/
def treesFrame (trees : Array HTree) : Array (HTree × Array (HRow × Nat)) := trees.map HTree.frame

/-- If g (f x) = g x for every x, modifying one element by f leaves the array's image under g
unchanged. -/
theorem map_modify_same {α β : Type} (g : α → β) (f : α → α) (H : ∀ x, g (f x) = g x)
    (a : Array α) (i : Nat) : (a.modify i f).map g = a.map g := by
  have hl : ∀ (l : List α) (i : Nat), (l.modify i f).map g = l.map g := by
    intro l
    induction l with
    | nil => intro i; simp
    | cons x l ih =>
      intro i
      cases i with
      | zero => simp [H]
      | succ i => simp [ih]
  apply Array.toList_inj.mp
  simp only [Array.toList_map, Array.toList_modify, hl]

/-- What Fork.hasEnt finds: the array, the virtual row and the weight that an entry names. -/
theorem hasEnt_spec {trees : Array HTree} {x : Ent} (h : Fork.hasEnt trees x = true) :
    ∃ X R v, trees.toList[x.tree]? = some X ∧ X.rows.toList[x.row]? = some R ∧ R.L0 ≤ x.idx ∧
      R.L.toList[x.idx - R.L0]? = some v := by
  unfold Fork.hasEnt at h
  split at h
  · simp at h
  · rename_i X hX
    split at h
    · simp at h
    · rename_i R hR
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨h1, h2⟩ := h
      refine ⟨X, R, R.L[x.idx - R.L0], ?_, ?_, h1, ?_⟩
      · simpa using hX
      · simpa using hR
      · simp [h2]

/-- One step of Fork.push on an entry changes nothing in the arrays except values of weights L. -/
theorem pushEnt_frame (w : E) (trees trees' : Array HTree) (x : Ent)
    (h : Fork.pushEnt w trees x = some trees') : treesFrame trees' = treesFrame trees := by
  unfold Fork.pushEnt at h
  split at h
  · have ht := Option.some.inj h
    subst ht
    unfold treesFrame
    apply map_modify_same
    intro X
    simp only [HTree.frame, Prod.mk.injEq, true_and]
    apply map_modify_same
    intro R
    simp [HRow.frame]
  · simp at h

/-- One step of Fork.push on an entry adds w times the entry's value (Ent.value, which includes the
coefficient) to treesValue. -/
theorem pushEnt_value (w : E) (trees trees' : Array HTree) (x : Ent)
    (h : Fork.pushEnt w trees x = some trees') :
    treesValue ρ W trees' = treesValue ρ W trees + ρ.val w * Ent.value ρ W x := by
  unfold Fork.pushEnt at h
  split at h
  · rename_i hh
    obtain ⟨X, R, v, hX, hR, hle, hv⟩ := hasEnt_spec hh
    have ht := Option.some.inj h
    subst ht
    have hi : R.L0 + (x.idx - R.L0) = x.idx := by omega
    simp only [treesValue, Array.toList_modify]
    rw [sumFrom_modify _ _ _ 0 x.tree X hX]
    simp only [HTree.value, Array.toList_modify]
    rw [sumFrom_modify _ _ _ 0 x.row R hR]
    simp only [HRow.value, Array.toList_modify]
    rw [sumFrom_modify _ _ _ R.L0 (x.idx - R.L0) v hv, hi]
    simp only [ρ.add, ρ.mul, Ent.value, Nat.zero_add]
    ring
  · simp at h

/-- One step of Fork.push on a slot adds w times the slot's value (slotValue, which includes the
coefficient) to slotsValue, and LS keeps its ns elements. -/
theorem pushSlot_value (w : E) (ns : Nat) (LS LS' : Array E) (x : Nat × E) (hs : LS.size = ns)
    (h : Fork.pushSlot w ns LS x = some LS') :
    LS'.size = ns ∧ slotsValue ρ W LS' = slotsValue ρ W LS + ρ.val w * slotValue ρ W x := by
  unfold Fork.pushSlot at h
  split at h
  · rename_i hlt
    have ht := Option.some.inj h
    subst ht
    have hv : LS.toList[x.1]? = some LS[x.1] := by simp [hs, hlt]
    refine ⟨by simp [hs], ?_⟩
    simp only [slotsValue, Array.toList_modify]
    rw [sumFrom_modify _ _ _ 0 x.1 _ hv]
    simp only [ρ.add, ρ.mul, slotValue, Nat.zero_add]
    ring
  · simp at h

/-- A state that was just set up (fillL, then slots) and whose constant c0 is 0 has the total 0. -/
theorem Fork.total_start (F : Fork) (n : Nat) (hc : F.c0 = zeroE) :
    (F.fillL.slots n).total ρ W = 0 := by
  have h1 : treesValue ρ W (F.fillL.slots n).trees = 0 := by
    unfold treesValue
    apply sumFrom_eq_zero
    intro t X hX
    simp only [Fork.slots, Fork.fillL, Array.toList_map, List.mem_map] at hX
    obtain ⟨X0, _, rfl⟩ := hX
    unfold HTree.value
    apply sumFrom_eq_zero
    intro r R hR
    simp only [Array.toList_map, List.mem_map] at hR
    obtain ⟨R0, _, rfl⟩ := hR
    unfold HRow.value
    apply sumFrom_eq_zero
    intro i v hv
    simp only [Array.toList_replicate, List.mem_replicate] at hv
    rw [hv.2, ρ.zero, zero_mul]
  have h2 : slotsValue ρ W (F.fillL.slots n).LS = 0 := by
    unfold slotsValue
    apply sumFrom_eq_zero
    intro i v hv
    simp only [Fork.slots, Array.toList_replicate, List.mem_replicate] at hv
    rw [hv.2, ρ.zero, zero_mul]
  have h3 : (F.fillL.slots n).c0 = zeroE := hc
  rw [Fork.total, h1, h2, h3, ρ.zero]
  simp

/-- After Fork.slots there is one coefficient in LS for each slot, as the theorems below require. -/
theorem Fork.slots_sized (F : Fork) (n : Nat) : (F.slots n).LS.size = (F.slots n).ns := by
  simp [Fork.slots]

/-- Adding w times a form to the equation adds w times the form's value to Fork.total, if LS has one
coefficient for each slot (F.LS.size = F.ns, as after Fork.slots). Of the state only the arrays, the
coefficients LS and the constant c0 change; of the arrays only the values of the weights L, not how
many there are; and there is still one coefficient in LS for each slot.

A routine that takes a weight by Fork.kap and then changes the weights L by steps of its own needs a
theorem of its own in the place of Fork.push_total. OnBytes/Model/TreesLaws.lean has it for the
claims on long runs of entries. -/
theorem Fork.push_total (F G : Fork) (w : E) (a : Aff) (hs : F.LS.size = F.ns)
    (h : F.push w a = some G) :
    G.total ρ W = F.total ρ W + ρ.val w * a.value ρ W ∧
      G = { F with trees := G.trees, LS := G.LS, c0 := G.c0 } ∧ G.LS.size = G.ns ∧
      treesFrame G.trees = treesFrame F.trees := by
  unfold Fork.push at h
  split at h
  · simp at h
  · dsimp only at h
    split at h
    · rename_i trees' LS' h1 h2
      have hG := Option.some.inj h
      subst hG
      rw [← Array.foldlM_toList] at h1 h2
      have e1 := foldlM_adds (Fork.pushEnt w) (fun s => treesFrame s = treesFrame F.trees)
        (treesValue ρ W) (fun x => ρ.val w * Ent.value ρ W x)
        (fun s x s' hi hx => ⟨(pushEnt_frame w s s' x hx).trans hi, pushEnt_value ρ W w s s' x hx⟩)
        _ _ _ rfl h1
      have e2 := foldlM_adds (Fork.pushSlot w F.ns) (fun s => s.size = F.ns) (slotsValue ρ W)
        (fun x => ρ.val w * slotValue ρ W x)
        (fun s x s' hi hx => pushSlot_value ρ W w F.ns s s' x hi hx) _ _ _ hs h2
      refine ⟨?_, rfl, e2.1, e1.1⟩
      simp only [Fork.total, Aff.value, ρ.add, ρ.mul]
      rw [e1.2, e2.2, List.sum_map_mul_left, List.sum_map_mul_left]
      ring
    · simp at h

/-- The weight of the next claim is theta to the power nClaim. Of the state only nClaim and the
marks kapMapF change. A weight is handed out only while the mark thetaDrawnF is set and the mark
doorShutF is not. The theorem speaks of the two marks, not of who sets them (Fork.batchBy the first,
doorH in OnBytes/Model/Trees.lean the second). -/
theorem Fork.kap_spec (F G : Fork) (k : E) (h : F.kap = some (k, G)) :
    k = powE F.theta F.nClaim ∧
      G = { F with nClaim := F.nClaim + 1, kapMapF := G.kapMapF } ∧
      F.thetaDrawnF = true ∧ F.doorShutF = false := by
  simp only [Fork.kap, Fork.kapTake, Fork.kapAt] at h
  split_ifs at h with h1 h2 h3 h4 h5 <;> simp at h
  all_goals
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨rfl, rfl, by assumption, by simpa using h1⟩

/-- Adding the claim that a form is 0 adds theta^c times the form's value, where c is nClaim before
the step, if LS has one coefficient for each slot. The form's value may itself depend on theta. -/
theorem Fork.lin_total (F G : Fork) (f : Aff) (hs : F.LS.size = F.ns) (h : F.lin f = some G) :
    G.total ρ W = F.total ρ W + ρ.val F.theta ^ F.nClaim * f.value ρ W ∧
      G.nClaim = F.nClaim + 1 ∧ G.theta = F.theta ∧ G.ns = F.ns ∧ G.LS.size = G.ns ∧
      treesFrame G.trees = treesFrame F.trees := by
  unfold Fork.lin at h
  cases hk : F.kap with
  | none => simp [hk] at h
  | some x =>
    obtain ⟨k, F1⟩ := x
    rw [hk] at h
    have h2 : F1.push k f = some G := by simpa using h
    obtain ⟨hk1, hF1, _, _⟩ := Fork.kap_spec F F1 k hk
    have hs1 : F1.LS.size = F1.ns := by rw [hF1]; exact hs
    obtain ⟨ht, hG, hsG, hfr⟩ := Fork.push_total ρ W F1 G k f hs1 h2
    have htot : F1.total ρ W = F.total ρ W := by rw [hF1]; rfl
    have htr : F1.trees = F.trees := by rw [hF1]
    refine ⟨?_, ?_, ?_, ?_, hsG, ?_⟩
    · rw [ht, htot, hk1, ρ.pow]
    · rw [hG, hF1]
    · rw [hG, hF1]
    · rw [hG, hF1]
    · rw [hfr, htr]

/-- The claims of a list, added one after the other. The program has no such function: it adds its
claims one by one. -/
def Fork.lins (F : Fork) (l : List Aff) : Option Fork := l.foldlM Fork.lin F

/-- The sum over the forms of a list of x^c times the form's value, c counting from a start. -/
def claimsValue (x : K) (c : Nat) (l : List Aff) : K :=
  sumFrom (fun i f => x ^ i * Aff.value ρ W f) c l

/-- After a list of claims the total has grown by the sum of theta^(c + i) times the value of form
number i, where c is nClaim before the list, if LS has one coefficient for each slot.

The sums with powers of theta are identities at the one element theta of the state. They are not
statements about a polynomial in theta: the forms, and the values that a world gives to the entries
of virtual rows, may themselves depend on theta. In the smallness test (OnBytes/Model/Tail.lean)
they do. -/
theorem Fork.lins_total : ∀ (l : List Aff) (F G : Fork), F.LS.size = F.ns → F.lins l = some G →
    G.total ρ W = F.total ρ W + claimsValue ρ W (ρ.val F.theta) F.nClaim l ∧
      G.nClaim = F.nClaim + l.length ∧ G.theta = F.theta ∧ G.ns = F.ns ∧ G.LS.size = G.ns
  | [], F, G, hs, h => by
    have hF : F = G := by simpa [Fork.lins] using h
    subst hF
    simp [claimsValue, sumFrom, hs]
  | f :: l, F, G, hs, h => by
    unfold Fork.lins at h
    rw [List.foldlM_cons] at h
    cases hq : F.lin f with
    | none => simp [hq] at h
    | some F1 =>
      rw [hq] at h
      have h2 : F1.lins l = some G := by simpa [Fork.lins] using h
      obtain ⟨ht, hn, hth, hns, hs1, _⟩ := Fork.lin_total ρ W F F1 f hs hq
      obtain ⟨t2, n2, th2, ns2, s2⟩ := Fork.lins_total l F1 G hs1 h2
      refine ⟨?_, ?_, ?_, ?_, s2⟩
      · rw [t2, ht, hn, hth]
        simp only [claimsValue, sumFrom]
        ring
      · rw [n2, hn, List.length_cons]
        omega
      · rw [th2, hth]
      · rw [ns2, hns]

/-! ## The equation on the mask row -/

/-- The sum over j of m[j] times mask[j]: the coefficients m, applied to a mask row. -/
def maskValue (mask : Nat → K) (m : Array E) : K :=
  sumFrom (fun j v => ρ.val v * mask j) 0 m.toList

/-- The program's test for 0 is true only of the element whose three words are 0. -/
theorem isZeroE_eq {a : E} (h : isZeroE a = true) : a = zeroE := by
  simp only [isZeroE, Bool.and_eq_true, beq_iff_eq] at h
  exact E.ext3 h.1.1 h.1.2 h.2

/-- Coefficients that are all 0 give the value 0 on every mask row. -/
theorem sumFrom_zeros (mask : Nat → K) : ∀ (n s : Nat),
    sumFrom (fun j v => ρ.val v * mask j) s (List.replicate n zeroE) = 0
  | 0, _ => rfl
  | n + 1, s => by
    simp only [List.replicate_succ, sumFrom, ρ.zero, zero_mul, zero_add]
    exact sumFrom_zeros mask n (s + 1)

/-- Run the steps of Fork.settle over the coefficients l of the slots j, j + 1 and so on. If they
return a result, the value on the mask row plus the constant has grown by the sum over i of l[i]
times the hidden value under slot j + i, that is vp - mf * mask at j + i (0 for a vp or mf that is
not there). Hypothesis: the coefficients of these slots' mask entries are still 0. -/
theorem settleSteps (F : Fork) (mask : Nat → K) :
    ∀ (l : List E) (j : Nat) (m : Array E) (c : E) (x : Nat × Array E × E),
      l.foldlM (Fork.settleStep F) (j, m, c) = some x →
      (∀ i, j ≤ i → i < j + l.length → m.toList[i]? = some zeroE) →
      maskValue ρ mask x.2.1 + ρ.val x.2.2 = maskValue ρ mask m + ρ.val c +
        sumFrom (fun i v => ρ.val v *
          (ρ.val (F.vp.getD i zeroE) - ρ.val (F.mf.getD i zeroE) * mask i)) j l
  | [], j, m, c, x, h, _ => by
    have hx : (j, m, c) = x := by simpa using h
    subst hx
    simp [sumFrom]
  | v :: l, j, m, c, x, h, hz => by
    rw [List.foldlM_cons] at h
    cases hq : Fork.settleStep F (j, m, c) v with
    | none => simp [hq] at h
    | some y =>
      rw [hq] at h
      have h2 : l.foldlM (Fork.settleStep F) y = some x := by simpa using h
      simp only [Fork.settleStep] at hq
      split_ifs at hq with hzero hgot
      · have hy := Option.some.inj hq
        subst hy
        rw [settleSteps F mask l (j + 1) m c x h2
          (fun i h1 h3 => hz i (by omega) (by simp only [List.length_cons]; omega))]
        simp only [sumFrom, isZeroE_eq hzero, ρ.zero]
        ring
      · have hy := Option.some.inj hq
        subst hy
        have hj : m.toList[j]? = some zeroE :=
          hz j (Nat.le_refl j) (by simp only [List.length_cons]; omega)
        rw [settleSteps F mask l (j + 1) _ _ x h2 (fun i h1 h3 => by
          rw [Array.set!_eq_setIfInBounds, Array.toList_setIfInBounds,
            List.getElem?_set_ne (by omega)]
          exact hz i (by omega) (by simp only [List.length_cons]; omega))]
        simp only [maskValue, Array.set!_eq_setIfInBounds, Array.toList_setIfInBounds]
        rw [sumFrom_set _ _ _ 0 j zeroE hj]
        simp only [sumFrom, ρ.add, ρ.sub, ρ.mul, ρ.zero, Nat.zero_add]
        ring

/-- The world in which the hidden value under slot j is vp[j] - mf[j] * mask[j]. The entries of the
virtual rows are those that the caller gives. -/
def Fork.worldOf (F : Fork) (mask : Nat → K) (entry : Nat → Nat → Nat → K) : World K where
  slot := fun j => ρ.val (F.vp.getD j zeroE) - ρ.val (F.mf.getD j zeroE) * mask j
  entry := entry

/-- The equation that Fork.settle writes on the mask row. Let Fork.settle return (m, c). For every
mask row, sum_j m[j] mask[j] + c = sum_j LS[j] (vp[j] - mf[j] mask[j]) + c0. The right side is the
part of Fork.total on the slots, plus c0, with vp[j] - mf[j] * mask[j] as the hidden value under
slot j. -/
theorem Fork.settle_total (F : Fork) (used : Nat) (m : Array E) (c : E) (mask : Nat → K)
    (entry : Nat → Nat → Nat → K) (h : F.settle used = some (m, c)) :
    maskValue ρ mask m + ρ.val c =
      slotsValue ρ (F.worldOf ρ mask entry) F.LS + ρ.val F.c0 := by
  unfold Fork.settle at h
  split_ifs at h with hc
  simp only [Bool.and_eq_true, beq_iff_eq] at hc
  have hLS : F.LS.size = F.ns := hc.1.1.1.1.2
  split at h
  · rename_i x hx
    have hm := Option.some.inj h
    rw [← Array.foldlM_toList] at hx
    have e := settleSteps ρ F mask F.LS.toList 0 _ _ x hx (fun i _ h3 => by
      have : i < F.ns := by simpa [hLS] using h3
      simp [this])
    rw [hm] at e
    rw [e]
    simp only [maskValue, Array.toList_replicate, sumFrom_zeros, slotsValue, Fork.worldOf]
    ring
  · simp at h

/-- The whole gathered equation, written on the virtual rows and the mask row. Let Fork.settle
return (m, c). Then treesValue of the arrays, plus sum_j m[j] mask[j], plus c is Fork.total, both in
the world of Fork.worldOf. -/
theorem Fork.settle_whole (F : Fork) (used : Nat) (m : Array E) (c : E) (mask : Nat → K)
    (entry : Nat → Nat → Nat → K) (h : F.settle used = some (m, c)) :
    treesValue ρ (F.worldOf ρ mask entry) F.trees + maskValue ρ mask m + ρ.val c =
      F.total ρ (F.worldOf ρ mask entry) := by
  rw [Fork.total, add_assoc, Fork.settle_total ρ F used m c mask entry h, add_assoc]

/-- The routine SubM.lin, run from a state F and a context c of Blk (Ctx, OnBytes/Iop/Ground.lean),
succeeds exactly where the step Fork.lin returns a state. It then goes on with that state and leaves
the context as it was. -/
theorem SubM.lin_run (f : Aff) (F G : Fork) (c c' : Ctx) :
    SubM.lin f F c = .ok (((), G), c') ↔ F.lin f = some G ∧ c' = c := by
  simp only [SubM.lin, SubM.change]
  cases F.lin f with
  | none => simp [liftOption_none]
  | some H => simp [liftOption_some, eq_comm]

/-- The routine SubM.settle succeeds exactly where the function Fork.settle returns a value. It then
gives that value and changes neither the state nor the context. -/
theorem SubM.settle_run (used : Nat) (F G : Fork) (c c' : Ctx) (x : Array E × E) :
    SubM.settle used F c = .ok ((x, G), c') ↔ F.settle used = some x ∧ G = F ∧ c' = c := by
  simp only [SubM.settle, SubM.ask]
  cases F.settle used with
  | none => simp [liftOption_none]
  | some y => simp [liftOption_some, eq_comm, and_assoc]

/-! ## The sumcheck -/

/-- addSlots a first form adds to the value of a the sum over i of form[i] times the hidden value
under slot first + i. -/
theorem addSlots_value (a : Aff) (first : Nat) (form : Array E) :
    (addSlots a first form).value ρ W =
      a.value ρ W + sumFrom (fun j x => ρ.val x * W.slot j) first form.toList := by
  unfold addSlots
  rw [← Array.foldl_toList]
  generalize form.toList = l
  induction l generalizing a first with
  | nil => simp [sumFrom]
  | cons x l ih =>
    simp only [List.foldl_cons, addSlot, sumFrom]
    rw [ih, Aff.value_addMul, Aff.value_slot]
    ring

/-- The form that a sumcheck leaves, read in K term by term. Psc.walk is not unfolded: the statement
has p.walk.1 and p.walk.2 as they are. Not stated, because it is the work of pscRow and pscBegin:
that the slots from p.first on hold the coefficients of the hiding polynomial, and that p.target is
the public part of p.start. -/
theorem Psc.rowForm_value (p : Psc) (S0 : E) (kept : Aff) :
    (p.rowForm S0 kept).value ρ W =
      sumFrom (fun j x => ρ.val x * W.slot j) p.first p.walk.1 +
        ρ.val p.eps * ρ.val p.walk.2 * (ρ.val p.target - p.start.value ρ W) +
        ρ.val p.eps * kept.value ρ W - (ρ.val p.claim - ρ.val p.eps * ρ.val S0) := by
  simp only [Psc.rowForm, Aff.value_addMul, addSlots_value, Aff.value_sub, Aff.value_ofConst,
    ρ.sub, ρ.mul, ρ.zero]
  ring

/-- The sum of the terms c_i x^(s + i) of a polynomial is x^s times the value that the program
computes (OnBytes.Psc.polyAt). At s = 0 the program's value is the sum of the terms. -/
theorem Reading.polyAt (x : E) : ∀ (g : List E) (s : Nat),
    sumFrom (fun i c => ρ.val c * ρ.val x ^ i) s g = ρ.val x ^ s * ρ.val (OnBytes.Psc.polyAt g x)
  | [], s => by simp [sumFrom, OnBytes.Psc.polyAt, ρ.zero]
  | c :: g, s => by
    have hp : OnBytes.Psc.polyAt (c :: g) x = addE (mulE (OnBytes.Psc.polyAt g x) x) c := rfl
    simp only [sumFrom]
    rw [Reading.polyAt x g (s + 1), hp, ρ.add, ρ.mul]
    ring

/-- The sum of the products of the elements of two lists, in K, as far as the shorter list goes. -/
def dotValue (a b : List E) : K := ((a.zip b).map fun p => ρ.val p.1 * ρ.val p.2).sum

/-- A fold of steps that never refuse. If each step adds g p to a value, the whole fold adds the
sum. -/
theorem foldl_adds {α β : Type} (val : β → K) (f : β → α → β) (g : α → K)
    (h : ∀ r p, val (f r p) = val r + g p) :
    ∀ (l : List α) (r : β), val (l.foldl f r) = val r + (l.map g).sum
  | [], r => by rw [List.foldl_nil, List.map_nil, List.sum_nil, add_zero]
  | p :: l, r => by
    rw [List.foldl_cons, List.map_cons, List.sum_cons, foldl_adds val f g h l, h, add_assoc]

/-- The step of the loop in OnBytes.Psc.dot, under a name, so that Reading.dot can apply foldl_adds
without unfolding addE and mulE. -/
def pairStep (r : E) (p : E × E) : E := addE r (mulE p.1 p.2)

/-- What pairStep adds, read in K: the product of the pair's readings. -/
def pairTerm (p : E × E) : K := ρ.val p.1 * ρ.val p.2

/-- The reading of pairStep r p is the reading of r plus pairTerm p. -/
theorem pairStep_adds (r : E) (p : E × E) : ρ.val (pairStep r p) = ρ.val r + pairTerm ρ p := by
  rw [pairStep, pairTerm, ρ.add, ρ.mul]

/-- The reading of OnBytes.Psc.dot a b is dotValue a b. -/
theorem Reading.dot (a b : List E) : ρ.val (OnBytes.Psc.dot a b) = dotValue ρ a b := by
  have h := foldl_adds ρ.val pairStep (pairTerm ρ) (pairStep_adds ρ) (a.zip b) zeroE
  rw [ρ.zero, zero_add] at h
  exact h

/-- Writing y for 0 at one place of the second list adds y times the first list's element at that
place (0 if the first list has no element there). -/
theorem dotValue_at (y : E) (high : List E) : ∀ (low m : List E),
    dotValue ρ m (low ++ y :: high) =
      dotValue ρ m (low ++ zeroE :: high) + ρ.val (m.getD low.length zeroE) * ρ.val y
  | [], [] => by simp [dotValue, ρ.zero]
  | [], a :: m => by simp [dotValue, ρ.zero]; ring
  | b :: low, [] => by simp [dotValue, ρ.zero]
  | b :: low, a :: m => by
    have ih := dotValue_at y high low m
    simp only [dotValue, List.cons_append, List.zip_cons_cons, List.map_cons, List.sum_cons,
      List.length_cons, List.getD_cons_succ] at ih ⊢
    rw [ih]
    ring

/-- The sum of products of n copies of c with a list of at most n elements is c times the list's
plain sum. -/
theorem dotValue_replicate (c : E) : ∀ (n : Nat) (l : List E), l.length ≤ n →
    dotValue ρ (List.replicate n c) l = ρ.val c * (l.map ρ.val).sum
  | _, [], _ => by simp [dotValue]
  | 0, _ :: _, h => by simp at h
  | n + 1, x :: l, h => by
    have ih := dotValue_replicate c n l (by simpa using h)
    simp only [dotValue, List.replicate_succ, List.zip_cons_cons, List.map_cons, List.sum_cons]
      at ih ⊢
    rw [ih]
    ring

/-- The value of a polynomial at 1 is the sum of its coefficients. -/
theorem Reading.polyAt_one (g : List E) :
    ρ.val (OnBytes.Psc.polyAt g oneE) = (g.map ρ.val).sum := by
  have gen : ∀ (l : List E) (s : Nat),
      sumFrom (fun i c => ρ.val c * ρ.val oneE ^ i) s l = (l.map ρ.val).sum := by
    intro l
    induction l with
    | nil => intro s; rfl
    | cons c l ih =>
      intro s
      simp only [sumFrom, List.map_cons, List.sum_cons]
      rw [ih, ρ.one, one_pow, mul_one]
  have h := ρ.polyAt oneE g 0
  rw [gen, pow_zero, one_mul] at h
  exact h.symm

/-- The value of a polynomial at 0 is its constant coefficient. -/
theorem Reading.polyAt_zero (c : E) (g : List E) :
    ρ.val (OnBytes.Psc.polyAt (c :: g) zeroE) = ρ.val c := by
  have hp : OnBytes.Psc.polyAt (c :: g) zeroE =
      addE (mulE (OnBytes.Psc.polyAt g zeroE) zeroE) c := rfl
  rw [hp, ρ.add, ρ.mul, ρ.zero, mul_zero, zero_add]

/-- For a polynomial q of at most d coefficients, the sum of (Weight.plain d).moment[i] * q[i] is
q(0) + q(1). A longer q is not covered: the sum ends with the shorter list. -/
theorem plain_moment (d : Nat) (q : List E) (h : q.length ≤ d) :
    dotValue ρ (OnBytes.Psc.Weight.plain d).moment q =
      ρ.val (OnBytes.Psc.polyAt q zeroE) + ρ.val (OnBytes.Psc.polyAt q oneE) := by
  cases q with
  | nil => simp [dotValue, OnBytes.Psc.polyAt, ρ.zero]
  | cons c g =>
    have hg : g.length ≤ d - 1 := by
      simp only [List.length_cons] at h
      omega
    have hr := dotValue_replicate ρ oneE (d - 1) g hg
    rw [ρ.polyAt_zero, ρ.polyAt_one]
    simp only [dotValue, OnBytes.Psc.Weight.plain, List.zip_cons_cons, List.map_cons,
      List.sum_cons, ρ.add, ρ.one] at hr ⊢
    rw [hr]
    ring

/-- For a polynomial q of at most d coefficients, the sum of (Weight.equality z d).moment[i] * q[i]
is (1 - z) q(0) + z q(1). A longer q is not covered: the sum ends with the shorter list. -/
theorem equality_moment (z : E) (d : Nat) (q : List E) (h : q.length ≤ d) :
    dotValue ρ (OnBytes.Psc.Weight.equality z d).moment q =
      (1 - ρ.val z) * ρ.val (OnBytes.Psc.polyAt q zeroE) +
        ρ.val z * ρ.val (OnBytes.Psc.polyAt q oneE) := by
  cases q with
  | nil => simp [dotValue, OnBytes.Psc.polyAt, ρ.zero]
  | cons c g =>
    have hg : g.length ≤ d - 1 := by
      simp only [List.length_cons] at h
      omega
    have hr := dotValue_replicate ρ z (d - 1) g hg
    rw [ρ.polyAt_zero, ρ.polyAt_one]
    simp only [dotValue, OnBytes.Psc.Weight.equality, List.zip_cons_cons, List.map_cons,
      List.sum_cons, ρ.one] at hr ⊢
    rw [hr]
    ring

/-- Why a round tests no equation: pscRound (OnBytes/Model/Psc.lean) fills in the coefficient that
is not sent, so that the equation holds. Statement: the program's sum of products (OnBytes.Psc.dot)
of w.moment with w.complete sent claim has the same reading as claim. It has two hypotheses: at
least w.fixed coefficients were sent, and w.moment[w.fixed] times w.fixedInv is the program's 1.
pscRound tests both before it completes a polynomial (Weight.fits, weightHeld, the number of
elements received). No theorem here derives the hypotheses from those tests. plain_moment and
equality_moment say what w.moment is for the two kinds of weight. -/
theorem complete_sum (w : OnBytes.Psc.Weight) (sent : List E) (claim : E)
    (hfix : w.fixed ≤ sent.length)
    (hinv : mulE (w.moment.getD w.fixed zeroE) w.fixedInv = oneE) :
    ρ.val (OnBytes.Psc.dot w.moment (w.complete sent claim)) = ρ.val claim := by
  have hlen : (sent.take w.fixed).length = w.fixed := by simp [hfix]
  have h1 : ρ.val (w.moment.getD w.fixed zeroE) * ρ.val w.fixedInv = 1 := by
    rw [← ρ.mul, hinv, ρ.one]
  unfold OnBytes.Psc.Weight.complete
  simp only []
  rw [ρ.dot, dotValue_at, hlen, ρ.mul, ρ.sub, ρ.dot]
  linear_combination (ρ.val claim -
    dotValue ρ w.moment (List.take w.fixed sent ++ zeroE :: List.drop w.fixed sent)) * h1

end OnBytes.Model

-- Each line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms OnBytes.Model.Reading.gl
#print axioms OnBytes.Model.Reading.polyAt
#print axioms OnBytes.Model.Fork.settle_whole
#print axioms OnBytes.Model.SubM.lin_run
#print axioms OnBytes.Model.SubM.settle_run
#print axioms OnBytes.Model.Fork.total_start
#print axioms OnBytes.Model.Psc.rowForm_value
#print axioms OnBytes.Model.complete_sum
#print axioms OnBytes.Model.plain_moment
#print axioms OnBytes.Model.equality_moment
#print axioms OnBytes.Model.Aff.value_addMul
#print axioms OnBytes.Model.Fork.push_total
#print axioms OnBytes.Model.Fork.lins_total
#print axioms OnBytes.Model.Fork.settle_total
