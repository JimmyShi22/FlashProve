-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K5/Honest/Law/Live.lean: with which coefficient a linear form names a slot, and when
the row that a masked sumcheck leaves names a slot with a coefficient that does not read 0.
Definitions with code, definitions of propositions, and statements with their proofs ON THE
VERIFIER'S OWN DATA: no prover is in this file.

What for. Behind the rounds of a segment the verifier adds all claims under the powers of one drawn
element and then asks of every slot that the sum's coefficient on it is not 0. At an honest run that
test can fail. It fails at every value of the drawn element where every claim that names the slot
names it with the coefficient 0. For the slots of an attention segment's own rounds this file and
its fellows say on which elements drawn in these rounds that hangs.

Main names:
  unitW, noughtW, slotCo   the coefficient, read; slotCo_value: it is the form's value in the world
                  that has 1 under the slot, less its value in the world 0
  slotCo_addMul .. slotCo_empty   the rules
  slotCo_onSlots, slotCo_formOf   the hiding polynomial's weights on its coefficients' slots; the
                  row
  slotCo_batched, slotCo_batched_at, slotCo_batched_off   a batch of slots under weights
  nzE, nzE_val    a test with code on an element: what passes it does not read 0
  powersFrom_ne, hidingAt_ne   where no challenge reads 0, no weight of the hiding polynomial does
  row_own_live, row_start_live   **the row's coefficient on a slot of the sumcheck's own; on a slot
                  that the claimed sum names**
  sumLive, heardLive   **the test with code on the elements drawn in the segment's own rounds**
  k5End           the next slot behind these rounds' slots, by the plan

row_own_live and row_start_live are CONDITIONAL: on challenges, and for the second on the element
eps, that do not read 0. heardLive is the test for that; whoever counts the drawn elements at which
it fails pays for them.
Limits. slotCo is typed on a form; on a claim it is meant at the claim's form. Nothing says how an
element is drawn. No property is claimed by a definition.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.Claims.SayAt
import Johnson.Desc.First.Att.Claims.SlotsBehind
import Johnson.Desc.First.Att.K05Numbers
import Johnson.Desc.Kinds.Law.Decode
import OnBytes.Slice.ProgField
import OnBytes.Slice.SimBase

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K5.Honest
open OnBytes (E addE subE mulE zeroE oneE okE isZeroE)
open OnBytes.Model (Reading World Aff Fork slotValue)
open VerifiableInference.Desc.Part (MaskedSum.Heard)
open VerifiableInference.Desc.Part.MaskedSum (Var hidingAt onSlots ownSlots)
open VerifiableInference.Desc.First.Att.P (Geo geoOf Heard Left Pts hear pointsOf LeftIs GeoFits
  formOf kB kV kH own3)
open VerifiableInference.Desc.First.Att.P.Runs (In JoinsP firstRun secondRun)

/-! ## 1 The coefficient with which a form names a slot -/

section Ring
variable {K : Type} [CommRing K] (ρ : Reading K)

/-- The world in which the value under slot j is 1 and all else is 0. -/
def unitW (K : Type) [CommRing K] (j : ℕ) : World K :=
  ⟨fun i => if i = j then 1 else 0, fun _ _ _ => 0⟩

/-- The world in which all is 0. -/
def noughtW (K : Type) [CommRing K] : World K := ⟨fun _ => 0, fun _ _ _ => 0⟩

/-- **The coefficient with which a form names slot j**, read: the sum over its pairs that name j. -/
def slotCo (f : Aff) (j : ℕ) : K := (f.slots.toList.map (slotValue ρ (unitW K j))).sum

end Ring

/-! ## 2 The test on what was heard -/

/-- All three words are below the prime, and not all are 0. -/
def nzE (w : E) : Bool := okE w && !isZeroE w

/-- A sumcheck's challenges, that of the further variable among them, are not 0; where eps is asked,
neither is the element that scales the claimed sum. -/
def sumLive (eps : Bool) (hh : MaskedSum.Heard) : Bool := hh.r.all nzE && (!eps || nzE hh.eps)

/-- **The test on the elements that were drawn in an attention segment's own rounds.** The element
that scales the claimed sum is asked of the sumchecks whose claimed sum names a slot that no other
form of the two runs names: the softmax-table units', "denominator times output", "the key at the
index". Asked too: the powers that batch the second end values of the score at the index. -/
def heardLive (h : Heard) : Bool :=
  (h.scores.all fun s => sumLive true s.2) && sumLive true h.division && sumLive false h.below &&
    sumLive false h.on && sumLive false h.atIndex && sumLive true h.key &&
    sumLive false h.cells && h.om'.all nzE

/-- The next slot behind the rounds' slots, by the plan, from the slot k on. -/
def k5End (x : OnBytes.Params.AttentionRounds) (k : ℕ) : ℕ := kH x k + own3 x.bits + 2 * x.pairs

section Ring
variable {K : Type} [CommRing K] (ρ : Reading K)

/-- **The coefficient is the form's value in the world that has 1 under the slot, less its value in
the world 0.** So the rules on a form's value compute it. -/
theorem slotCo_value (f : Aff) (j : ℕ) :
    slotCo ρ f j = f.value ρ (unitW K j) - f.value ρ (noughtW K) := by
  have e1 : ∀ W : World K, (∀ a b c, W.entry a b c = 0) →
      (f.ents.toList.map (OnBytes.Model.Ent.value ρ W)).sum = 0 := fun W hW =>
    List.sum_eq_zero fun y hy => by
      obtain ⟨e, _, rfl⟩ := List.mem_map.1 hy
      show ρ.val e.coef * W.entry e.tree e.row e.idx = 0
      rw [hW, mul_zero]
  have e2 : (f.slots.toList.map (slotValue ρ (noughtW K))).sum = 0 :=
    List.sum_eq_zero fun y hy => by
      obtain ⟨e, _, rfl⟩ := List.mem_map.1 hy
      show ρ.val e.2 * (0 : K) = 0
      rw [mul_zero]
  unfold slotCo Aff.value
  rw [e1 _ fun _ _ _ => rfl, e1 _ fun _ _ _ => rfl, e2]
  ring

theorem slotCo_addMul (a b : Aff) (k : E) (j : ℕ) :
    slotCo ρ (Aff.addMul a b k) j = slotCo ρ a j + ρ.val k * slotCo ρ b j := by
  simp only [slotCo_value, Aff.value_addMul]
  ring

theorem slotCo_scale (a : Aff) (k : E) (j : ℕ) :
    slotCo ρ (Aff.scale a k) j = ρ.val k * slotCo ρ a j := by
  simp only [slotCo_value, Aff.value_scale]
  ring

theorem slotCo_add (a b : Aff) (j : ℕ) : slotCo ρ (a + b) j = slotCo ρ a j + slotCo ρ b j := by
  simp only [slotCo_value, Aff.value_add]
  ring

theorem slotCo_sub (a b : Aff) (j : ℕ) : slotCo ρ (a - b) j = slotCo ρ a j - slotCo ρ b j := by
  simp only [slotCo_value, Aff.value_sub]
  ring

theorem slotCo_slot (s j : ℕ) : slotCo ρ (Aff.slot s) j = if s = j then 1 else 0 := by
  rw [slotCo_value, Aff.value_slot, Aff.value_slot]
  show (if s = j then (1 : K) else 0) - 0 = _
  rw [sub_zero]

theorem slotCo_ofConst (v : E) (j : ℕ) : slotCo ρ (Aff.ofConst v) j = 0 := by
  rw [slotCo_value, Aff.value_ofConst, Aff.value_ofConst, sub_self]

theorem slotCo_ent (t r c j : ℕ) : slotCo ρ (Aff.ent t r c) j = 0 := by
  rw [slotCo_value, Aff.value_ent, Aff.value_ent]
  show (0 : K) - 0 = 0
  rw [sub_zero]

theorem slotCo_empty (j : ℕ) : slotCo ρ ({} : Aff) j = 0 := by
  rw [slotCo_value, Aff.value_empty, Aff.value_empty, sub_self]

private theorem slotCo_fold (j : ℕ) : ∀ (u : List E) (s : ℕ) (f : Aff),
    slotCo ρ (u.foldl (fun (s : ℕ × Aff) x => (s.1 + 1, Aff.addMul s.2 (Aff.slot s.1) x))
      (s, f)).2 j = slotCo ρ f j +
        if s ≤ j ∧ j < s + u.length then ρ.val (u.getD (j - s) zeroE) else 0
  | [], s, f => by
    rw [if_neg (by simp only [List.length_nil]; omega), add_zero]
    rfl
  | x :: u, s, f => by
    rw [List.foldl_cons, slotCo_fold j u (s + 1), slotCo_addMul, slotCo_slot, List.length_cons]
    by_cases h0 : s = j
    · subst h0
      rw [if_pos rfl, if_neg (by omega), if_pos (by omega), Nat.sub_self, List.getD_cons_zero]
      ring
    · rw [if_neg h0, mul_zero, add_zero]
      by_cases h1 : s + 1 ≤ j ∧ j < s + 1 + u.length
      · rw [if_pos h1, if_pos (by omega), show j - s = (j - (s + 1)) + 1 by omega,
          List.getD_cons_succ]
      · rw [if_neg h1, if_neg (by omega)]

/-- The hiding polynomial's weights laid on its coefficients' slots. -/
theorem slotCo_onSlots (f : Aff) (first : ℕ) (u : List E) (j : ℕ) :
    slotCo ρ (onSlots f first u) j = slotCo ρ f j +
      if first ≤ j ∧ j < first + u.length then ρ.val (u.getD (j - first) zeroE) else 0 :=
  slotCo_fold ρ j u first f

/-- **The row that a masked sumcheck leaves**: on a slot of its own the hiding polynomial's weight;
on every slot, less eps P times the claimed sum's coefficient. -/
theorem slotCo_formOf (h : MaskedSum.Heard) (S0 : E) (j : ℕ) :
    slotCo ρ (formOf h S0 {}) j =
      (if h.first ≤ j ∧ j < h.first + (hidingAt (h.vars.zip h.r)).1.length then
        ρ.val ((hidingAt (h.vars.zip h.r)).1.getD (j - h.first) zeroE) else 0) -
      ρ.val (mulE h.eps (hidingAt (h.vars.zip h.r)).2) * slotCo ρ h.start j := by
  have e : formOf h S0 {} = Aff.addMul (Aff.addMul
      (onSlots (Aff.ofConst (subE zeroE (subE h.claim (mulE h.eps S0)))) h.first
        (hidingAt (h.vars.zip h.r)).1) (Aff.ofConst h.target - h.start)
      (mulE h.eps (hidingAt (h.vars.zip h.r)).2)) {} h.eps := rfl
  rw [e, slotCo_addMul, slotCo_addMul, slotCo_onSlots, slotCo_sub, slotCo_ofConst, slotCo_ofConst,
    slotCo_empty]
  ring

end Ring


section Batched
variable {K : Type} [CommRing K] (ρ : Reading K)
open VerifiableInference.Desc.First.Att.P (batched)

/-- A batch of slots under weights: the coefficient on slot j. -/
theorem slotCo_batched (w : Array E) (first step off j : ℕ) : ∀ n : ℕ,
    slotCo ρ (batched n w first step off) j = ∑ b ∈ Finset.range n,
      if first + (step * b + off) = j then ρ.val (w.getD b zeroE) else 0
  | 0 => by
    rw [Finset.range_zero, Finset.sum_empty]
    exact slotCo_ofConst ρ zeroE j
  | n + 1 => by
    have e : batched (n + 1) w first step off = Aff.addMul (batched n w first step off)
        (Aff.slot (first + (step * n + off))) (w.getD n zeroE) := by
      unfold batched
      rw [List.range_succ, List.foldl_append]
      rfl
    rw [e, slotCo_addMul, slotCo_batched w first step off j n, slotCo_slot, Finset.sum_range_succ]
    by_cases h : first + (step * n + off) = j
    · rw [if_pos h, if_pos h, mul_one]
    · rw [if_neg h, if_neg h, mul_zero]

/-- At the slot of member b. -/
theorem slotCo_batched_at (w : Array E) (first step off : ℕ) (hs : 0 < step) {n b : ℕ}
    (hb : b < n) : slotCo ρ (batched n w first step off) (first + (step * b + off)) =
      ρ.val (w.getD b zeroE) := by
  rw [slotCo_batched, Finset.sum_eq_single b]
  · rw [if_pos rfl]
  · intro c _ hc
    rw [if_neg]
    intro e
    have : step * c = step * b := by omega
    exact hc (Nat.eq_of_mul_eq_mul_left hs this)
  · intro h
    exact absurd (Finset.mem_range.2 hb) h

/-- At a slot that is no member's. -/
theorem slotCo_batched_off (w : Array E) (first step off j n : ℕ)
    (h : ∀ b < n, first + (step * b + off) ≠ j) :
    slotCo ρ (batched n w first step off) j = 0 := by
  rw [slotCo_batched]
  exact Finset.sum_eq_zero fun b hb => if_neg (h b (Finset.mem_range.1 hb))

end Batched

/-- What passes the test does not read 0. -/
theorem nzE_val {w : E} (h : nzE w = true) : Reading.gl.val w ≠ 0 := by
  unfold nzE at h
  rw [Bool.and_eq_true] at h
  intro h0
  have hz : isZeroE w = true := (OnBytes.Slice.isZeroE_iff w h.1).2 h0
  rw [hz] at h
  exact nomatch h.2

section Field
variable {K : Type} [Field K] (ρ : Reading K)

theorem powersFrom_ne {x : E} (hx : ρ.val x ≠ 0) : ∀ (n : ℕ) (a : E), ρ.val a ≠ 0 →
    ∀ y ∈ VerifiableInference.Desc.Part.MaskedSum.powersFrom x n a, ρ.val y ≠ 0
  | 0, _, _, y, hy => nomatch hy
  | n + 1, a, ha, y, hy => by
    rcases List.mem_cons.1 hy with rfl | hy
    · exact ha
    · exact powersFrom_ne hx n (mulE a x) (by rw [ρ.mul]; exact mul_ne_zero ha hx) y hy

private theorem psiAt_ne (v : Var) {r : E} (hr : ρ.val r ≠ 0) :
    ρ.val (VerifiableInference.Desc.Part.MaskedSum.psiAt v r) ≠ 0 := by
  cases v with
  | plain d => exact hr
  | point z d =>
    show ρ.val oneE ≠ 0
    rw [ρ.one]
    exact one_ne_zero

/-- **Where no challenge reads 0, no weight of the hiding polynomial does, nor does P.** -/
theorem hidingAt_ne : ∀ l : List (Var × E), (∀ p ∈ l, ρ.val p.2 ≠ 0) →
    (∀ y ∈ (hidingAt l).1, ρ.val y ≠ 0) ∧ ρ.val (hidingAt l).2 ≠ 0
  | [], _ => ⟨fun y hy => (nomatch hy), by
      show ρ.val oneE ≠ 0
      rw [ρ.one]
      exact one_ne_zero⟩
  | [(v, r)], h => by
    have hr : ρ.val r ≠ 0 := h (v, r) List.mem_cons_self
    exact ⟨powersFrom_ne ρ hr v.d oneE (by rw [ρ.one]; exact one_ne_zero), psiAt_ne ρ v hr⟩
  | (v, r) :: y :: rest, h => by
    have hr : ρ.val r ≠ 0 := h (v, r) List.mem_cons_self
    obtain ⟨i1, i2⟩ := hidingAt_ne (y :: rest) fun p hp => h p (List.mem_cons_of_mem _ hp)
    refine ⟨fun z hz => ?_, ?_⟩
    · have hz' : z ∈ VerifiableInference.Desc.Part.MaskedSum.powersFrom r (v.d - 1)
          (mulE (hidingAt (y :: rest)).2 r) ++ (hidingAt (y :: rest)).1 := hz
      rcases List.mem_append.1 hz' with hz | hz
      · exact powersFrom_ne ρ hr _ _ (by rw [ρ.mul]; exact mul_ne_zero i2 hr) z hz
      · exact i1 z hz
    · show ρ.val (mulE (hidingAt (y :: rest)).2
        (VerifiableInference.Desc.Part.MaskedSum.psiAt v r)) ≠ 0
      rw [ρ.mul]
      exact mul_ne_zero i2 (psiAt_ne ρ v hr)

/-- **A slot of the sumcheck's own**: the row's coefficient does not read 0, CONDITIONAL on: no
challenge reads 0; there are as many challenges as variables; the claimed sum does not name the
slot. -/
theorem row_own_live (h : MaskedSum.Heard) (S0 : E) (hr : ∀ r ∈ h.r, ρ.val r ≠ 0) {j : ℕ}
    (h1 : h.first ≤ j) (h2 : j < h.first + (hidingAt (h.vars.zip h.r)).1.length)
    (hs : slotCo ρ h.start j = 0) : slotCo ρ (formOf h S0 {}) j ≠ 0 := by
  rw [slotCo_formOf, if_pos ⟨h1, h2⟩, hs, mul_zero, sub_zero,
    List.getD_eq_getElem _ _ (show j - h.first < _ by omega)]
  exact (hidingAt_ne ρ _ fun p hp => hr p.2 (List.of_mem_zip hp).2).1 _ (List.getElem_mem _)

/-- **A slot that the claimed sum names**, in front of the sumcheck's own: the row's coefficient
does not read 0, CONDITIONAL on: no challenge reads 0, nor does eps. -/
theorem row_start_live (h : MaskedSum.Heard) (S0 : E) (hr : ∀ r ∈ h.r, ρ.val r ≠ 0)
    (he : ρ.val h.eps ≠ 0) {j : ℕ} (h1 : j < h.first) (hs : slotCo ρ h.start j ≠ 0) :
    slotCo ρ (formOf h S0 {}) j ≠ 0 := by
  rw [slotCo_formOf, if_neg (by omega), zero_sub, ρ.mul]
  exact neg_ne_zero.2 (mul_ne_zero (mul_ne_zero he
    (hidingAt_ne ρ _ fun p hp => hr p.2 (List.of_mem_zip hp).2).2) hs)

end Field

end H2K5.Honest

#print axioms H2K5.Honest.slotCo_value
#print axioms H2K5.Honest.slotCo_addMul
#print axioms H2K5.Honest.slotCo_scale
#print axioms H2K5.Honest.slotCo_add
#print axioms H2K5.Honest.slotCo_sub
#print axioms H2K5.Honest.slotCo_slot
#print axioms H2K5.Honest.slotCo_ofConst
#print axioms H2K5.Honest.slotCo_ent
#print axioms H2K5.Honest.slotCo_empty
#print axioms H2K5.Honest.slotCo_onSlots
#print axioms H2K5.Honest.slotCo_formOf
#print axioms H2K5.Honest.slotCo_batched
#print axioms H2K5.Honest.slotCo_batched_at
#print axioms H2K5.Honest.slotCo_batched_off
#print axioms H2K5.Honest.nzE_val
#print axioms H2K5.Honest.powersFrom_ne
#print axioms H2K5.Honest.hidingAt_ne
#print axioms H2K5.Honest.row_own_live
#print axioms H2K5.Honest.row_start_live
