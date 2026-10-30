-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/HeadRowForm.lean: every claim that a sumcheck leaves in what the routine hear of the
output head's sub-proof returns can be met by one slot of its own.

The routine hear of the output head's sub-proof runs many masked sumchecks
(OnBytes/Model/Psc.lean): 31 for the tie of the lookup's two sides, one for each level of its two
product trees, one for the leaves, one for the bits, one for the product layer of the squares and
three over the positions. A sumcheck tests no equation. It leaves one claim, a form in hidden
values that must be 0 (Psc.rowForm). This file shows that each such claim has a slot of its own by
which it can be set to 0, and sorts the claims of what hear returns into lists in the order of
their slots. It serves the files that show that the hypotheses of the theorems on the head's link
can be met; the lists are put together there, not here. The sub-proof runs more sumchecks behind
hear: the smallness test has a lookup of its own, and the merge has a sumcheck. They are not
followed here; pad_chain is stated for any lookup, and nothing here applies it to the smallness
test's.

How. The claim has the term "the hiding polynomial at the challenges", a linear form in the
polynomial's coefficients, which are hidden values under slots of the sumcheck's own. The
coefficient of the last variable's constant in that form is 1 (walk_shape). Beside its own slots a
claim reads only the form that the sum must equal, on slots that were taken before the sumcheck
began. So a claim reads no slot at or above the end of its own slots (Tri). If claims are taken in
the order of their slots (RowChain, from a slot lo up to a slot hi), each can be set to 0 by its
own slot without a change to the claims before it: chain_solve meets all claims of such a list by
a change of slots from lo on and below hi; what the slots outside that range hold is kept.
hear_rows gives seven such lists, each with its range: the two slots that the end of the lookup's
key side reads lie between the first two ranges, the end value of the bits behind the third, and
each of the head's four ranges lies behind the slots from which its sumcheck starts and before its
end values. How the head's four ranges lie to each other is not said here: that is hear_slots of
Johnson/Road/HeadSlots.lean.

The sumcheck of the leaves is followed as far as hear goes (PscAt in HeardRows): its claim is made
later, by the routine planeClaims, and pscRow_tri applies to it there.

Main definitions: Below (a form reads low slots alone), Tri (a form with a slot of its own),
RowChain (forms in the order of their slots), PscAt (what is followed of a sumcheck's state),
TieAt, HeardRows.
Main theorems: walk_shape, tri_rowForm, chain_solve; pscBegin_at, pscRound_at, roundIn_at,
pscEnds_at, pscRow_tri; levelIn_tri, level_chain, levels_chain, levels_chain_ne; tieStep_chain,
tie_chain; pad_chain; hearSquares_chain, hearProducts_chain, hearStream_chain, hearLogits_chain;
hear_rows.

What is not claimed. Every theorem on a routine begins "if the routine succeeds": none says that
it does. The values that chain_solve gives to the slots are not those of a prover's messages.
Nothing on what a sumcheck shows, on hiding, or on what a verifier's acceptance shows. The program
does not import this file.
-/
import Johnson.Road.HeadEndForm
import Johnson.Road.HeadLens

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.Hd

open OnBytes.Model (Fork SubM Aff Reading World sumFrom)

section Forms

variable {K : Type} [Field K] (ρ : Reading K)

/-! ## 1. Forms that read low slots alone -/

/-- The value of the form f depends on the entries and on the slots below n alone. -/
def Below (f : Aff) (n : ℕ) : Prop :=
  ∀ (σ σ' : ℕ → K) (ent : ℕ → ℕ → ℕ → K), (∀ k, k < n → σ' k = σ k) →
    f.value ρ ⟨σ', ent⟩ = f.value ρ ⟨σ, ent⟩

/-- A constant reads no slot. -/
theorem below_const (v : E) (n : ℕ) : Below ρ (Aff.ofConst v) n := fun _ _ _ _ => by
  rw [Aff.value_ofConst, Aff.value_ofConst]

/-- The empty form reads no slot. -/
theorem below_empty (n : ℕ) : Below ρ ({} : Aff) n := fun _ _ _ _ => by
  rw [Aff.value_empty, Aff.value_empty]

/-- The form of slot j reads slot j alone. -/
theorem below_slot {j n : ℕ} (h : j < n) : Below ρ (Aff.slot j) n := fun _ _ _ hσ => by
  rw [Aff.value_slot, Aff.value_slot]
  exact hσ j h

/-- The form of an entry reads no slot. -/
theorem below_ent (t r i n : ℕ) : Below ρ (Aff.ent t r i) n := fun _ _ _ _ => by
  simp only [Aff.value_ent]

variable {ρ}

/-- A form that reads slots below n alone reads slots below any larger number alone. -/
theorem Below.mono {f : Aff} {n m : ℕ} (h : Below ρ f n) (hnm : n ≤ m) : Below ρ f m :=
  fun σ σ' ent hσ => h σ σ' ent fun k hk => hσ k (Nat.lt_of_lt_of_le hk hnm)

/-- The form a + k b reads what a and b read. -/
theorem Below.addMul {a b : Aff} {n : ℕ} (ha : Below ρ a n) (hb : Below ρ b n) (k : E) :
    Below ρ (Aff.addMul a b k) n := fun σ σ' ent hσ => by
  rw [Aff.value_addMul, Aff.value_addMul, ha σ σ' ent hσ, hb σ σ' ent hσ]

/-- A multiple of a form reads what the form reads. -/
theorem Below.scale {a : Aff} {n : ℕ} (ha : Below ρ a n) (k : E) : Below ρ (Aff.scale a k) n :=
  fun σ σ' ent hσ => by
    rw [Aff.value_scale, Aff.value_scale, ha σ σ' ent hσ]

/-- A sum of two forms reads what they read. -/
theorem Below.add {a b : Aff} {n : ℕ} (ha : Below ρ a n) (hb : Below ρ b n) : Below ρ (a + b) n :=
  fun σ σ' ent hσ => by
    rw [Aff.value_add, Aff.value_add, ha σ σ' ent hσ, hb σ σ' ent hσ]

/-- A difference of two forms reads what they read. -/
theorem Below.sub {a b : Aff} {n : ℕ} (ha : Below ρ a n) (hb : Below ρ b n) : Below ρ (a - b) n :=
  fun σ σ' ent hσ => by
    rw [Aff.value_sub, Aff.value_sub, ha σ σ' ent hσ, hb σ σ' ent hσ]

/-- A sum of slots under weights, added to a form. -/
theorem below_foldl (sl : ℕ → ℕ) (c : ℕ → E) {n : ℕ} : ∀ (l : List ℕ) (f0 : Aff), Below ρ f0 n →
    (∀ j ∈ l, sl j < n) →
    Below ρ (l.foldl (fun f j => Aff.addMul f (Aff.slot (sl j)) (c j)) f0) n
  | [], f0, h0, _ => h0
  | j :: l, f0, h0, h => by
    rw [List.foldl_cons]
    exact below_foldl sl c l _
      (h0.addMul (below_slot ρ (h j (List.mem_cons.mpr (Or.inl rfl)))) (c j))
      (fun i hi => h i (List.mem_cons.mpr (Or.inr hi)))

/-- What a level of a product tree hands down reads its two end values. -/
theorem below_handed (sL : ℕ) (tau : E) :
    Below ρ (Aff.scale (Aff.slot sL) (subE oneE tau) + Aff.scale (Aff.slot (sL + 1)) tau)
      (sL + 2) :=
  ((below_slot ρ (by omega)).scale _).add ((below_slot ρ (by omega)).scale _)

/-! ## 2. Sums over lists with a running number -/

/-- The sum over two lists, one behind the other. -/
theorem sumFrom_append {α : Type} (g : ℕ → α → K) : ∀ (l1 l2 : List α) (s : ℕ),
    sumFrom g s (l1 ++ l2) = sumFrom g s l1 + sumFrom g (s + l1.length) l2
  | [], l2, s => by simp [sumFrom]
  | x :: l1, l2, s => by
    have e : s + 1 + l1.length = s + (l1.length + 1) := by omega
    rw [List.cons_append]
    simp only [sumFrom, List.length_cons]
    rw [sumFrom_append g l1 l2 (s + 1), e]
    ring

/-- Two sums over one list are equal if their terms are equal at the numbers that the list takes.
-/
theorem sumFrom_congr {α : Type} (g g' : ℕ → α → K) : ∀ (l : List α) (s : ℕ),
    (∀ i x, s ≤ i → i < s + l.length → g i x = g' i x) → sumFrom g s l = sumFrom g' s l
  | [], _, _ => rfl
  | x :: l, s, h => by
    simp only [sumFrom]
    rw [h s x (Nat.le_refl _) (by rw [List.length_cons]; omega),
      sumFrom_congr g g' l (s + 1) fun i y h1 h2 =>
        h i y (by omega) (by rw [List.length_cons]; omega)]

/-- Two sums of slots under the same weights, if the slots hold the same. -/
theorem sumSlots_congr (σ σ' : ℕ → K) (l : List E) (s : ℕ)
    (h : ∀ i, s ≤ i → i < s + l.length → σ' i = σ i) :
    sumFrom (fun i x => ρ.val x * σ' i) s l = sumFrom (fun i x => ρ.val x * σ i) s l :=
  sumFrom_congr _ _ l s fun i x h1 h2 => by
    show ρ.val x * σ' i = ρ.val x * σ i
    rw [h i h1 h2]

/-! ## 3. The linear form of the hiding polynomial -/

/-- The loop of powers puts what it was given, turned round, before what it makes. -/
theorem powersLoop_acc (x : E) : ∀ (n : ℕ) (c : E) (done : List E),
    OnBytes.Psc.powersLoop x n c done = done.reverse ++ OnBytes.Psc.powersLoop x n c []
  | 0, c, done => by simp [OnBytes.Psc.powersLoop]
  | n + 1, c, done => by
    show OnBytes.Psc.powersLoop x n (mulE c x) (c :: done) =
      done.reverse ++ OnBytes.Psc.powersLoop x n (mulE c x) [c]
    rw [powersLoop_acc x n (mulE c x) (c :: done), powersLoop_acc x n (mulE c x) [c]]
    simp

/-- The first of n + 1 powers from c on is c. -/
theorem powers_succ (c x : E) (n : ℕ) :
    OnBytes.Psc.powers c x (n + 1) = c :: OnBytes.Psc.powers (mulE c x) x n := by
  show OnBytes.Psc.powersLoop x n (mulE c x) [c] = c :: OnBytes.Psc.powersLoop x n (mulE c x) []
  rw [powersLoop_acc]
  rfl

/-- The list of n powers has n members. -/
theorem powers_length (x : E) : ∀ (n : ℕ) (c : E), (OnBytes.Psc.powers c x n).length = n
  | 0, _ => rfl
  | n + 1, c => by rw [powers_succ, List.length_cons, powers_length x n]

/-- The linear form of a hiding polynomial in at least one variable: one of its coefficients is 1,
that of the last variable's constant; and it has one coefficient, and one more for each degree from
1 on of each variable. -/
theorem walk_shape : ∀ l : List (OnBytes.Psc.Weight × E), l ≠ [] → (∀ y ∈ l, 1 ≤ y.1.d) →
    ∃ pre post, (OnBytes.Psc.hidingWalk l).1 = pre ++ oneE :: post ∧
      (OnBytes.Psc.hidingWalk l).1.length = 1 + (l.map fun y => y.1.d - 1).sum
  | [], h, _ => absurd rfl h
  | [(w, g)], _, hd => by
    have h1 : 1 ≤ w.d := hd (w, g) (List.mem_cons.mpr (Or.inl rfl))
    obtain ⟨n, hn⟩ : ∃ n, w.d = n + 1 := ⟨w.d - 1, by omega⟩
    have e : (OnBytes.Psc.hidingWalk [(w, g)]).1 = OnBytes.Psc.powers oneE g w.d := rfl
    refine ⟨[], OnBytes.Psc.powers (mulE oneE g) g n, ?_, ?_⟩
    · rw [e, hn, powers_succ]
      rfl
    · rw [e, powers_length, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      show w.d = 1 + (w.d - 1 + 0)
      omega
  | (w, g) :: y :: rest, _, hd => by
    obtain ⟨pre, post, e1, e2⟩ := walk_shape (y :: rest) (List.cons_ne_nil _ _)
      (fun z hz => hd z (List.mem_cons.mpr (Or.inr hz)))
    have e : (OnBytes.Psc.hidingWalk ((w, g) :: y :: rest)).1 =
        OnBytes.Psc.powers (mulE (OnBytes.Psc.hidingWalk (y :: rest)).2 g) g (w.d - 1) ++
          (OnBytes.Psc.hidingWalk (y :: rest)).1 := rfl
    refine ⟨OnBytes.Psc.powers (mulE (OnBytes.Psc.hidingWalk (y :: rest)).2 g) g (w.d - 1) ++ pre,
      post, ?_, ?_⟩
    · rw [e, e1, List.append_assoc]
    · have e3 : (((w, g) :: y :: rest).map fun y => y.1.d - 1).sum =
          (w.d - 1) + ((y :: rest).map fun y => y.1.d - 1).sum := by
        rw [List.map_cons, List.sum_cons]
      rw [e, List.length_append, powers_length, e2, e3]
      omega

/-! ## 4. A claim with a slot of its own -/

/-- A function that is changed at j is unchanged elsewhere. -/
theorem upd_other {A : Type} (σ : ℕ → A) {j k : ℕ} (h : k ≠ j) (v : A) :
    Function.update σ j v k = σ k := by
  simp [Function.update, h]

/-- A function that is changed at j has the new value at j. -/
theorem upd_self {A : Type} (σ : ℕ → A) (j : ℕ) (v : A) : Function.update σ j v j = v := by
  simp [Function.update]

variable (ρ)

/-- The form f reads the slots below hi alone, and its value is what slot j holds plus something
that does not depend on slot j; j is below hi. -/
structure Tri (f : Aff) (j hi : ℕ) : Prop where
  lt : j < hi
  below : Below ρ f hi
  lin : ∀ (σ : ℕ → K) (ent : ℕ → ℕ → ℕ → K) (v : K),
    f.value ρ ⟨Function.update σ j v, ent⟩ = f.value ρ ⟨Function.update σ j 0, ent⟩ + v

/-- The value of the claim that a sumcheck leaves, in a world that is given by its parts. -/
theorem rowForm_at (p : Model.Psc) (S0 : E) (kept : Aff) (σ : ℕ → K) (ent : ℕ → ℕ → ℕ → K) :
    (p.rowForm S0 kept).value ρ ⟨σ, ent⟩ =
      sumFrom (fun i x => ρ.val x * σ i) p.first p.walk.1 +
        ρ.val p.eps * ρ.val p.walk.2 * (ρ.val p.target - p.start.value ρ ⟨σ, ent⟩) +
        ρ.val p.eps * kept.value ρ ⟨σ, ent⟩ - (ρ.val p.claim - ρ.val p.eps * ρ.val S0) :=
  Model.Psc.rowForm_value ρ ⟨σ, ent⟩ p S0 kept

/-- The claim that a sumcheck leaves, if the linear form of its hiding polynomial has the
coefficient 1 behind pre, and if what the sum must equal and the kept terms read slots below the
sumcheck's first slot alone. -/
theorem tri_rowForm (p : Model.Psc) (S0 : E) (kept : Aff) {pre post : List E}
    (hw : p.walk.1 = pre ++ oneE :: post) (hs : Below ρ p.start p.first)
    (hk : Below ρ kept p.first) :
    Tri ρ (p.rowForm S0 kept) (p.first + pre.length) (p.first + p.walk.1.length) where
  lt := by
    rw [hw, List.length_append, List.length_cons]
    omega
  below := fun σ σ' ent hσ => by
    rw [rowForm_at, rowForm_at,
      hs σ σ' ent (fun k hk' => hσ k (by omega)), hk σ σ' ent (fun k hk' => hσ k (by omega)),
      sumSlots_congr σ σ' p.walk.1 p.first (fun i _ h2 => hσ i h2)]
  lin := fun σ ent v => by
    have es : p.start.value ρ ⟨Function.update σ (p.first + pre.length) v, ent⟩ =
        p.start.value ρ ⟨Function.update σ (p.first + pre.length) 0, ent⟩ :=
      hs _ _ ent fun k hk' => by
        have hne : k ≠ p.first + pre.length := by omega
        rw [upd_other σ hne, upd_other σ hne]
    have ek : kept.value ρ ⟨Function.update σ (p.first + pre.length) v, ent⟩ =
        kept.value ρ ⟨Function.update σ (p.first + pre.length) 0, ent⟩ :=
      hk _ _ ent fun k hk' => by
        have hne : k ≠ p.first + pre.length := by omega
        rw [upd_other σ hne, upd_other σ hne]
    have e1 : sumFrom (fun i x => ρ.val x * Function.update σ (p.first + pre.length) v i) p.first
        pre = sumFrom (fun i x => ρ.val x * Function.update σ (p.first + pre.length) 0 i) p.first
        pre :=
      sumSlots_congr _ _ pre p.first fun i _ h2 => by
        have hne : i ≠ p.first + pre.length := by omega
        rw [upd_other σ hne, upd_other σ hne]
    have e2 : sumFrom (fun i x => ρ.val x * Function.update σ (p.first + pre.length) v i)
        (p.first + pre.length + 1) post =
        sumFrom (fun i x => ρ.val x * Function.update σ (p.first + pre.length) 0 i)
        (p.first + pre.length + 1) post :=
      sumSlots_congr _ _ post _ fun i h1 _ => by
        have hne : i ≠ p.first + pre.length := by omega
        rw [upd_other σ hne, upd_other σ hne]
    rw [rowForm_at, rowForm_at, es, ek, hw, sumFrom_append, sumFrom_append]
    simp only [sumFrom]
    rw [e1, e2, upd_self, upd_self, ρ.one]
    ring

/-! ## 5. Claims in the order of their slots -/

/-- The claims of a list have slots of their own that rise: the first claim's slot is at or above
lo; it reads slots below some h alone; the next claim's slot is at or above h; and so on up to
hi. -/
def RowChain : List Aff → ℕ → ℕ → Prop
  | [], lo, hi => lo ≤ hi
  | f :: l, lo, hi => ∃ j h, lo ≤ j ∧ Tri ρ f j h ∧ RowChain l h hi

variable {ρ}

/-- In such a list lo is at most hi. -/
theorem chain_le : ∀ (l : List Aff) (lo hi : ℕ), RowChain ρ l lo hi → lo ≤ hi
  | [], _, _, h => h
  | f :: l, lo, hi, h => by
    simp only [RowChain] at h
    obtain ⟨j, m, h1, T, h2⟩ := h
    have k1 := T.lt
    have k2 := chain_le l m hi h2
    omega

/-- The range of such a list may begin earlier. -/
theorem chain_lower : ∀ (l : List Aff) (lo lo' hi : ℕ), RowChain ρ l lo hi → lo' ≤ lo →
    RowChain ρ l lo' hi
  | [], lo, lo', hi, h, h' => by
    simp only [RowChain] at h ⊢
    omega
  | f :: l, lo, lo', hi, h, h' => by
    simp only [RowChain] at h ⊢
    obtain ⟨j, m, h1, T, h2⟩ := h
    exact ⟨j, m, by omega, T, h2⟩

/-- The range of such a list may end later. -/
theorem chain_raise : ∀ (l : List Aff) (lo hi hi' : ℕ), RowChain ρ l lo hi → hi ≤ hi' →
    RowChain ρ l lo hi'
  | [], lo, hi, hi', h, h' => by
    simp only [RowChain] at h ⊢
    omega
  | f :: l, lo, hi, hi', h, h' => by
    simp only [RowChain] at h ⊢
    obtain ⟨j, m, h1, T, h2⟩ := h
    exact ⟨j, m, h1, T, chain_raise l m hi hi' h2 h'⟩

/-- Two such lists, the second from where the first ends, make one. -/
theorem chain_append : ∀ (l1 l2 : List Aff) (lo mid hi : ℕ), RowChain ρ l1 lo mid →
    RowChain ρ l2 mid hi → RowChain ρ (l1 ++ l2) lo hi
  | [], l2, lo, mid, hi, h1, h2 => by
    simp only [RowChain] at h1
    rw [List.nil_append]
    exact chain_lower l2 mid lo hi h2 h1
  | f :: l1, l2, lo, mid, hi, h1, h2 => by
    simp only [RowChain] at h1
    obtain ⟨j, m, k1, T, k2⟩ := h1
    rw [List.cons_append]
    simp only [RowChain]
    exact ⟨j, m, k1, T, chain_append l1 l2 m mid hi k2 h2⟩

/-- One form with a slot of its own is such a list. -/
theorem chain_one {f : Aff} {lo j h hi : ℕ} (h1 : lo ≤ j) (T : Tri ρ f j h) (h2 : h ≤ hi) :
    RowChain ρ [f] lo hi := by
  simp only [RowChain]
  exact ⟨j, h, h1, T, h2⟩

/-- Every claim of such a list reads slots below hi alone. -/
theorem chain_below : ∀ (l : List Aff) (lo hi : ℕ), RowChain ρ l lo hi → ∀ f ∈ l, Below ρ f hi
  | [], _, _, _, f, hf => by cases hf
  | g :: l, lo, hi, h, f, hf => by
    simp only [RowChain] at h
    obtain ⟨j, m, _, T, h2⟩ := h
    rcases List.mem_cons.mp hf with e | hf'
    · rw [e]
      exact T.below.mono (chain_le l m hi h2)
    · exact chain_below l m hi h2 f hf'

/-- **The claims of such a list can all be met** by a change of slots from lo on and below hi,
whatever the other slots and the entries hold. -/
theorem chain_solve : ∀ (l : List Aff) (lo hi : ℕ), RowChain ρ l lo hi →
    ∀ (σ : ℕ → K) (ent : ℕ → ℕ → ℕ → K), ∃ σ' : ℕ → K,
      (∀ k, k < lo ∨ hi ≤ k → σ' k = σ k) ∧ ∀ f ∈ l, f.value ρ ⟨σ', ent⟩ = 0
  | [], _, _, _, σ, _ => ⟨σ, fun _ _ => rfl, fun f hf => by cases hf⟩
  | f :: l, lo, hi, h, σ, ent => by
    simp only [RowChain] at h
    obtain ⟨j, m, h1, T, h2⟩ := h
    have hjm := T.lt
    have hmh := chain_le l m hi h2
    have z1 : f.value ρ ⟨Function.update σ j (-f.value ρ ⟨Function.update σ j 0, ent⟩), ent⟩ =
        0 := by
      rw [T.lin]
      ring
    obtain ⟨σ', a1, a2⟩ := chain_solve l m hi h2
      (Function.update σ j (-f.value ρ ⟨Function.update σ j 0, ent⟩)) ent
    refine ⟨σ', fun k hk => ?_, fun g hg => ?_⟩
    · rw [a1 k (by omega)]
      exact upd_other σ (by omega) _
    · rcases List.mem_cons.mp hg with e | hg'
      · rw [e, T.below _ σ' ent fun k hk => a1 k (Or.inl hk)]
        exact z1
      · exact a2 g hg'

end Forms

/-! ## 6. The state of a sumcheck -/

/-- What is followed of the state p of a sumcheck: what its sum must equal is C0; its first slot is
f0; every variable so far has a degree bound of at least 1; and the slots of the coefficients of its
hiding polynomial so far end at or before N. -/
structure PscAt (p : Model.Psc) (N : ℕ) (C0 : Aff) (f0 : ℕ) : Prop where
  start : p.start = C0
  first : p.first = f0
  deg : ∀ w ∈ p.vars.toList, 1 ≤ w.d
  room : f0 + 1 + (p.vars.toList.map fun w => w.d - 1).sum ≤ N

/-- The first step of a sumcheck: its first slot is the next free one, it has no variable yet, and
one slot is taken. -/
theorem pscBeginAt_at {t : E} {p : Model.Psc} {F G : Fork} {C D : Ctx}
    (h : Ok (Model.pscBeginAt t) F C p G D) :
    p.first = F.next ∧ p.vars = #[] ∧ G.next = F.next + 1 := by
  unfold Model.pscBeginAt at h
  rw [ok_bind] at h
  obtain ⟨first, F1, C1, h1, h⟩ := h
  obtain ⟨e1, e2⟩ := takeSlots_ok h1
  rw [ok_bind] at h
  obtain ⟨mu, F2, C2, h2, h⟩ := h
  have e3 := congrArg Fork.next (lift_stay h2)
  rw [ok_bind] at h
  obtain ⟨eps, F3, C3, h3, h⟩ := h
  have e4 := congrArg Fork.next (lift_stay h3)
  rw [ok_pure] at h
  obtain ⟨e5, e6, _⟩ := h
  have e7 := congrArg Fork.next e6
  subst e5
  exact ⟨e1, rfl, by omega⟩

/-- The beginning of a sumcheck. -/
theorem pscBegin_at {c : Aff} {p : Model.Psc} {F G : Fork} {C D : Ctx}
    (h : Ok (Model.pscBegin c) F C p G D) : PscAt p G.next c F.next := by
  unfold Model.pscBegin at h
  rw [ok_bind] at h
  obtain ⟨t, F1, C1, h1, h⟩ := h
  have e1 := congrArg Fork.next (ask_stay h1)
  rw [ok_bind] at h
  obtain ⟨p0, F2, C2, h2, h⟩ := h
  obtain ⟨e2, e3, e4⟩ := pscBeginAt_at h2
  rw [ok_pure] at h
  obtain ⟨e5, e6, _⟩ := h
  have e7 := congrArg Fork.next e6
  subst e5
  refine ⟨rfl, e2.trans e1, ?_, ?_⟩
  · show ∀ w ∈ p0.vars.toList, 1 ≤ w.d
    rw [e3]
    intro w hw
    simp at hw
  · show F.next + 1 + (p0.vars.toList.map fun w => w.d - 1).sum ≤ G.next
    rw [e3]
    show F.next + 1 + 0 ≤ G.next
    omega

/-- One round. -/
theorem pscRound_at {p : Model.Psc} {w : OnBytes.Psc.Weight} {draw : Blk E} {x : E × Model.Psc}
    {F G : Fork} {C D : Ctx} (h : Ok (Model.pscRound p w draw) F C x G D) {C0 : Aff} {f0 : ℕ}
    (A : PscAt p F.next C0 f0) : PscAt x.2 G.next C0 f0 := by
  have hn := pscRound_ok h
  unfold Model.pscRound at h
  obtain ⟨hb, h⟩ := subMust_bind h
  rw [ok_bind] at h
  obtain ⟨sent, F2, C2, h2, h⟩ := h
  rw [ok_bind] at h
  obtain ⟨_, F3, C3, h3, h⟩ := h
  try dsimp only at h
  rw [ok_bind] at h
  obtain ⟨r, F4, C4, h4, h⟩ := h
  rw [ok_bind] at h
  obtain ⟨j, F5, C5, h5, h⟩ := h
  try dsimp only at h
  rw [ok_pure] at h
  obtain ⟨e6, _, _⟩ := h
  subst e6
  have hf : w.fits = true := (and_true_split hb).1
  unfold OnBytes.Psc.Weight.fits at hf
  have hd : 2 ≤ w.d :=
    of_decide_eq_true (and_true_split (and_true_split (and_true_split hf).1).1).1
  have el : (p.vars.push w).toList = p.vars.toList ++ [w] := by simp
  refine ⟨A.start, A.first, ?_, ?_⟩
  · show ∀ w' ∈ (p.vars.push w).toList, 1 ≤ w'.d
    rw [el]
    intro w' hw'
    rcases List.mem_append.mp hw' with k | k
    · exact A.deg w' k
    · rw [List.mem_singleton.mp k]
      omega
  · show f0 + 1 + ((p.vars.push w).toList.map fun w => w.d - 1).sum ≤ G.next
    rw [el, List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil]
    have k := A.room
    omega

/-- One round of a given form. -/
theorem roundIn_at {form : Model.RoundForm} {p : Model.Psc} {z : E} {degree : ℕ}
    {x : E × Model.Psc} {F G : Fork} {C D : Ctx}
    (h : Ok (Model.roundIn form p z degree) F C x G D) {C0 : Aff} {f0 : ℕ}
    (A : PscAt p F.next C0 f0) : PscAt x.2 G.next C0 f0 := by
  unfold Model.roundIn at h
  rw [ok_bind] at h
  obtain ⟨_, F1, C1, h1, h⟩ := h
  have e1 := lift_stay h1
  rw [ok_bind] at h
  obtain ⟨w, F2, C2, h2, h⟩ := h
  have e2 := lift_stay h2
  rw [e2, e1] at h
  exact pscRound_at h A

/-- The loop of a token sumcheck keeps what is followed. -/
theorem tscLoop_at {C0 : Aff} {f0 : ℕ} : ∀ (zs : List E) (r : Array E) (p : Model.Psc) (F : Fork)
    (C : Ctx) (x : Array E × Model.Psc) (G : Fork) (D : Ctx),
    Ok (Model.tscLoop zs r p) F C x G D → PscAt p F.next C0 f0 → PscAt x.2 G.next C0 f0
  | [], r, p, F, C, x, G, D, h, A => by
    unfold Model.tscLoop at h
    rw [ok_pure] at h
    obtain ⟨e1, e2, _⟩ := h
    rw [e1, e2]
    exact A
  | z :: zs, r, p, F, C, x, G, D, h, A => by
    unfold Model.tscLoop at h
    rw [ok_bind] at h
    obtain ⟨⟨y, p'⟩, F1, C1, h1, h⟩ := h
    try dsimp only at h
    exact tscLoop_at zs _ _ _ _ _ _ _ h (roundIn_at h1 A)

/-- The rounds over the channels keep what is followed. -/
theorem channelRounds_at {C0 : Aff} {f0 : ℕ} : ∀ (n : ℕ) (r : Array E) (p : Model.Psc) (F : Fork)
    (C : Ctx) (x : Array E × Model.Psc) (G : Fork) (D : Ctx),
    Ok (Model.Head.channelRounds n r p) F C x G D → PscAt p F.next C0 f0 →
    PscAt x.2 G.next C0 f0
  | 0, r, p, F, C, x, G, D, h, A => by
    unfold Model.Head.channelRounds at h
    rw [ok_pure] at h
    obtain ⟨e1, e2, _⟩ := h
    rw [e1, e2]
    exact A
  | n + 1, r, p, F, C, x, G, D, h, A => by
    unfold Model.Head.channelRounds at h
    rw [ok_bind] at h
    obtain ⟨⟨y, p'⟩, F1, C1, h1, h⟩ := h
    try dsimp only at h
    exact channelRounds_at n _ _ _ _ _ _ _ h (roundIn_at h1 A)

/-- The rounds of a level keep what is followed. -/
theorem levelRounds_at {C0 : Aff} {f0 : ℕ} (mu : ℕ) (rho : Array E) : ∀ (order : List ℕ)
    (r : Array E) (p : Model.Psc) (F : Fork) (C : Ctx) (x : Array E × Model.Psc) (G : Fork)
    (D : Ctx), Ok (Model.levelRounds mu rho order r p) F C x G D → PscAt p F.next C0 f0 →
    PscAt x.2 G.next C0 f0
  | [], r, p, F, C, x, G, D, h, A => by
    unfold Model.levelRounds at h
    rw [ok_pure] at h
    obtain ⟨e1, e2, _⟩ := h
    rw [e1, e2]
    exact A
  | v :: order, r, p, F, C, x, G, D, h, A => by
    unfold Model.levelRounds at h
    rw [ok_bind] at h
    obtain ⟨_, F1, C1, h1, h⟩ := h
    have e1 := lift_stay h1
    rw [ok_bind] at h
    obtain ⟨⟨y, p'⟩, F2, C2, h2, h⟩ := h
    rw [e1] at h2
    try dsimp only at h
    exact levelRounds_at mu rho order _ _ _ _ _ _ _ h (roundIn_at h2 A)

/-- The loop of roundsIn keeps what is followed. -/
theorem roundsLoop_at {C0 : Aff} {f0 : ℕ} (form : Model.RoundForm) : ∀ (zs : List (E × ℕ))
    (s : Array E × Model.Psc) (F : Fork) (C : Ctx) (s' : Array E × Model.Psc) (G : Fork) (D : Ctx),
    Ok (zs.foldlM (fun (s : Array E × Model.Psc) z => do
      let (r, q) ← Model.roundIn form s.2 z.1 z.2
      pure (s.1.push r, q)) s) F C s' G D → PscAt s.2 F.next C0 f0 → PscAt s'.2 G.next C0 f0
  | [], s, F, C, s', G, D, h, A => by
    rw [List.foldlM_nil] at h
    obtain ⟨e1, e2, -⟩ := pure_ok h
    rw [e1, e2]
    exact A
  | z :: zs, s, F, C, s', G, D, h, A => by
    rw [List.foldlM_cons] at h
    obtain ⟨s1, F1, C1, h1, h2⟩ := bind_ok h
    obtain ⟨⟨r, q⟩, F2, C2, h3, h4⟩ := bind_ok h1
    have A2 := roundIn_at h3 A
    obtain ⟨e1, e2, -⟩ := pure_ok h4
    refine roundsLoop_at form zs s1 F1 C1 s' G D h2 ?_
    rw [e1, e2]
    exact A2

/-- Rounds of one form keep what is followed. -/
theorem roundsIn_at {form : Model.RoundForm} {p : Model.Psc} {zs : List (E × ℕ)}
    {x : Array E × Model.Psc} {F G : Fork} {C D : Ctx}
    (h : Ok (Model.roundsIn form p zs) F C x G D) {C0 : Aff} {f0 : ℕ}
    (A : PscAt p F.next C0 f0) : PscAt x.2 G.next C0 f0 :=
  roundsLoop_at form zs (#[], p) F C x G D h A

/-- The end of a sumcheck: the slots of the hiding polynomial's coefficients end at or before the
slot of the first end value. -/
theorem pscEnds_at {p : Model.Psc} {dY n : ℕ} {x : ℕ × Model.Psc} {F G : Fork} {C D : Ctx}
    (h : Ok (Model.pscEnds p dY n) F C x G D) {C0 : Aff} {f0 : ℕ} (A : PscAt p F.next C0 f0) :
    PscAt x.2 x.1 C0 f0 := by
  unfold Model.pscEnds at h
  rw [ok_bind] at h
  obtain ⟨_, F1, C1, h1, h⟩ := h
  have e1 := lift_stay h1
  rw [ok_bind] at h
  obtain ⟨⟨beta, p'⟩, F2, C2, h2, h⟩ := h
  rw [e1] at h2
  have A2 := pscRound_at h2 A
  try dsimp only at h
  rw [ok_bind] at h
  obtain ⟨v, F3, C3, h3, h⟩ := h
  have e3 := congrArg Fork.next (lift_stay h3)
  rw [ok_bind] at h
  obtain ⟨_, F4, C4, h4, h⟩ := h
  have e4 := congrArg Fork.next (lift_stay h4)
  rw [ok_bind] at h
  obtain ⟨_, F5, C5, h5, h⟩ := h
  have e5 := congrArg Fork.next (lift_stay h5)
  rw [ok_bind] at h
  obtain ⟨e, F6, C6, h6, h⟩ := h
  obtain ⟨e6, _⟩ := takeSlots_ok h6
  rw [ok_bind] at h
  obtain ⟨_, F7, C7, h7, h⟩ := h
  rw [ok_pure] at h
  obtain ⟨e9, _, _⟩ := h
  subst e9
  have k := A2.room
  exact ⟨A2.start, A2.first, A2.deg, by
    show f0 + 1 + (p'.vars.toList.map fun w => w.d - 1).sum ≤ e
    have k' : f0 + 1 + (p'.vars.toList.map fun w => w.d - 1).sum ≤ F2.next := k
    omega⟩

section Row

variable {K : Type} [Field K] (ρ : Reading K)

/-- **The claim that a sumcheck leaves has a slot of its own**: at or above the sumcheck's first
slot; the claim reads slots below N alone. C0, what the sum must equal, and the kept terms read
slots below the first slot alone. -/
theorem pscRow_tri {p : Model.Psc} {S0 : E} {kept : Aff} {x : Aff × Model.Psc} {F G : Fork}
    {C D : Ctx} (h : Ok (Model.pscRow p S0 kept) F C x G D) {N : ℕ} {C0 : Aff} {f0 : ℕ}
    (A : PscAt p N C0 f0) (hs : Below ρ C0 f0) (hk : Below ρ kept f0) :
    ∃ j hi, f0 ≤ j ∧ hi ≤ N ∧ Tri ρ x.1 j hi := by
  unfold Model.pscRow at h
  obtain ⟨hb, h⟩ := subMust_bind h
  rw [ok_bind] at h
  obtain ⟨_, F2, C2, h2, h⟩ := h
  rw [ok_pure] at h
  obtain ⟨e1, _, _⟩ := h
  subst e1
  obtain ⟨hb1, hsz⟩ := and_true_split hb
  obtain ⟨_, hne⟩ := and_true_split hb1
  have hsz' : p.r.size = p.vars.size := by simpa using hsz
  have hne' : p.vars.toList ≠ [] := by
    intro e0
    have e2 : p.vars.size = 0 := by
      rw [← Array.length_toList, e0]
      rfl
    have e3 : p.vars.isEmpty = true := by
      unfold Array.isEmpty
      rw [e2]
      rfl
    rw [e3] at hne
    simp at hne
  have hlen : p.vars.toList.length ≤ p.r.toList.length := by
    simp only [Array.length_toList]
    omega
  have hfst : (p.vars.toList.zip p.r.toList).map Prod.fst = p.vars.toList :=
    List.map_fst_zip hlen
  have hl : p.vars.toList.zip p.r.toList ≠ [] := by
    intro e0
    rw [e0] at hfst
    exact hne' hfst.symm
  have hdeg : ∀ y ∈ p.vars.toList.zip p.r.toList, 1 ≤ y.1.d := fun y hy =>
    A.deg y.1 (by
      rw [← hfst]
      exact List.mem_map.mpr ⟨y, hy, rfl⟩)
  obtain ⟨pre, post, w1, w2⟩ := walk_shape _ hl hdeg
  have ew : p.walk = OnBytes.Psc.hidingWalk (p.vars.toList.zip p.r.toList) := by
    unfold Model.Psc.walk
    rw [zipT_eq]
  have hsum : ((p.vars.toList.zip p.r.toList).map fun y => y.1.d - 1) =
      p.vars.toList.map fun w => w.d - 1 := by
    have e3 : ((p.vars.toList.zip p.r.toList).map fun y => y.1.d - 1) =
        ((p.vars.toList.zip p.r.toList).map Prod.fst).map fun w => w.d - 1 := by
      rw [List.map_map]
      rfl
    rw [e3, hfst]
  have hs' : Below ρ p.start p.first := by
    rw [A.start, A.first]
    exact hs
  have hk' : Below ρ kept p.first := by
    rw [A.first]
    exact hk
  have T := tri_rowForm ρ p S0 kept (by rw [ew]; exact w1) hs' hk'
  refine ⟨_, _, ?_, ?_, T⟩
  · rw [A.first]
    omega
  · rw [ew, w2, hsum, A.first]
    have k := A.room
    omega

/-! ## 7. A level of a product tree -/

/-- The claim of a level has a slot of its own between the slot that was free before the level and
the slot of the level's left end value. c, what the level starts from, reads taken slots alone. -/
theorem levelIn_tri {mu : ℕ} {rho : Array E} {c : Aff} {order : List ℕ} {o : Model.Level}
    {F G : Fork} {C D : Ctx} (h : Ok (Model.levelIn mu rho c order) F C o G D)
    (hc : Below ρ c F.next) : ∃ j hi, F.next ≤ j ∧ hi ≤ o.sL ∧ Tri ρ o.row j hi := by
  unfold Model.levelIn at h
  rw [ok_bind] at h
  obtain ⟨_, F1, C1, h1, h⟩ := h
  have e1 := lift_stay h1
  rw [ok_bind] at h
  obtain ⟨p, F2, C2, h2, h⟩ := h
  rw [e1] at h2
  have A2 := pscBegin_at h2
  rw [ok_bind] at h
  obtain ⟨⟨r, p1⟩, F3, C3, h3, h⟩ := h
  have A3 := levelRounds_at _ _ _ _ _ _ _ _ _ _ h3 A2
  try dsimp only at h
  rw [ok_bind] at h
  obtain ⟨⟨sL, p2⟩, F4, C4, h4, h⟩ := h
  have A4 := pscEnds_at h4 A3
  try dsimp only at h
  rw [ok_bind] at h
  obtain ⟨tau, F5, C5, h5, h⟩ := h
  rw [ok_bind] at h
  obtain ⟨a, F6, C6, h6, h⟩ := h
  rw [ok_bind] at h
  obtain ⟨b, F7, C7, h7, h⟩ := h
  rw [ok_bind] at h
  obtain ⟨⟨row, p3⟩, F8, C8, h8, h⟩ := h
  try dsimp only at h
  rw [ok_pure] at h
  obtain ⟨e10, _, _⟩ := h
  subst e10
  exact pscRow_tri ρ h8 A4 hc (below_empty ρ _)

/-- One level of the lookup's walk: one claim more, with a slot of its own below the two end values;
the form that is handed down is on these two, the last slots that were taken. -/
theorem level_chain {s s' : Model.Forest.Descent} {mu : ℕ} {order : List ℕ} {F G : Fork}
    {C D : Ctx} (h : Ok (Model.Forest.level s mu order) F C s' G D)
    (hb : Below ρ s.form F.next) :
    ∃ (f : Aff) (sL : ℕ) (tau : E), s'.rows = s.rows.push f ∧
      s'.form = Aff.scale (Aff.slot sL) (subE oneE tau) + Aff.scale (Aff.slot (sL + 1)) tau ∧
      G.next = sL + 2 ∧ RowChain ρ [f] F.next sL := by
  unfold Model.Forest.level at h
  obtain ⟨o, F1, C1, h1, h2⟩ := bind_ok h
  obtain ⟨_, e2, e3⟩ := levelIn_ok h1
  obtain ⟨j, hi, t1, t2, T⟩ := levelIn_tri ρ h1 hb
  have h2' : Ok (pure { rows := s.rows.push o.row, rho := o.handDown.1, form := o.handDown.2 } :
      SubM Model.Forest.Descent) F1 C1 s' G D := h2
  obtain ⟨rfl, rfl, -⟩ := pure_ok h2'
  refine ⟨o.row, o.sL, o.tau, rfl, ?_, e3, chain_one t1 T t2⟩
  show Aff.scale (Aff.slot o.sL) (subE oneE o.tau) + Aff.scale (Aff.slot o.sR) o.tau = _
  rw [e2]

/-- At least one level: the claims that are added, in the order of their slots, all below the last
level's two end values. -/
theorem levels_chain_end (ord : ℕ → List ℕ) (fm : ℕ → ℕ) : ∀ (l : List ℕ) (x : ℕ)
    (s : Model.Forest.Descent) (F : Fork) (C : Ctx) (s' : Model.Forest.Descent) (G : Fork)
    (D : Ctx), Below ρ s.form F.next →
    Ok ((x :: l).foldlM (fun s x => Model.Forest.level s (fm x) (ord x)) s) F C s' G D →
    ∃ (rows : List Aff) (sL : ℕ) (tau : E), s'.rows.toList = s.rows.toList ++ rows ∧
      s'.form = Aff.scale (Aff.slot sL) (subE oneE tau) + Aff.scale (Aff.slot (sL + 1)) tau ∧
      G.next = sL + 2 ∧ RowChain ρ rows F.next sL
  | [], x, s, F, C, s', G, D, hb, h => by
    rw [List.foldlM_cons] at h
    obtain ⟨s1, F1, C1, h1, h2⟩ := bind_ok h
    rw [List.foldlM_nil] at h2
    obtain ⟨rfl, rfl, -⟩ := pure_ok h2
    obtain ⟨f, sL, tau, r1, r2, r3, r4⟩ := level_chain ρ h1 hb
    exact ⟨[f], sL, tau, by rw [r1]; simp, r2, r3, r4⟩
  | y :: l, x, s, F, C, s', G, D, hb, h => by
    rw [List.foldlM_cons] at h
    obtain ⟨s1, F1, C1, h1, h2⟩ := bind_ok h
    obtain ⟨f, sL1, tau1, r1, r2, r3, r4⟩ := level_chain ρ h1 hb
    have hb1 : Below ρ s1.form F1.next := by
      rw [r2, r3]
      exact below_handed sL1 tau1
    obtain ⟨rows, sL, tau, q1, q2, q3, q4⟩ :=
      levels_chain_end ord fm l y s1 F1 C1 s' G D hb1 h2
    refine ⟨f :: rows, sL, tau, ?_, q2, q3, ?_⟩
    · rw [q1, r1]
      simp
    · exact chain_append [f] rows F.next F1.next sL
        (chain_raise [f] F.next sL1 F1.next r4 (by omega)) q4

/-- Any number of levels: the claims that are added, in the order of their slots; the form that is
handed down reads taken slots alone. -/
theorem levels_chain (ord : ℕ → List ℕ) (fm : ℕ → ℕ) (l : List ℕ) {s s' : Model.Forest.Descent}
    {F G : Fork} {C D : Ctx} (hb : Below ρ s.form F.next)
    (h : Ok (l.foldlM (fun s x => Model.Forest.level s (fm x) (ord x)) s) F C s' G D) :
    ∃ rows : List Aff, s'.rows.toList = s.rows.toList ++ rows ∧ RowChain ρ rows F.next G.next ∧
      Below ρ s'.form G.next := by
  cases l with
  | nil =>
    rw [List.foldlM_nil] at h
    obtain ⟨rfl, rfl, -⟩ := pure_ok h
    exact ⟨[], by simp, Nat.le_refl _, hb⟩
  | cons x l =>
    obtain ⟨rows, sL, tau, q1, q2, q3, q4⟩ := levels_chain_end ρ ord fm l x s F C s' G D hb h
    refine ⟨rows, q1, chain_raise rows F.next sL G.next q4 (by omega), ?_⟩
    rw [q2, q3]
    exact below_handed sL tau

/-- The same for a list that is not empty. -/
theorem levels_chain_ne {ord : ℕ → List ℕ} {fm : ℕ → ℕ} {l : List ℕ}
    {s s' : Model.Forest.Descent} {F G : Fork} {C D : Ctx} (hb : Below ρ s.form F.next)
    (h : Ok (l.foldlM (fun s x => Model.Forest.level s (fm x) (ord x)) s) F C s' G D)
    (hl : l ≠ []) :
    ∃ (rows : List Aff) (sL : ℕ) (tau : E), s'.rows.toList = s.rows.toList ++ rows ∧
      s'.form = Aff.scale (Aff.slot sL) (subE oneE tau) + Aff.scale (Aff.slot (sL + 1)) tau ∧
      G.next = sL + 2 ∧ RowChain ρ rows F.next sL := by
  cases l with
  | nil => exact absurd rfl hl
  | cons x l => exact levels_chain_end ρ ord fm l x s F C s' G D hb h

/-! ## 8. The tie of the lookup's two sides -/

/-- The slots that the state of the tie's loop names have been taken. -/
structure TieAt (s : Model.Forest.TieStep) (n : ℕ) : Prop where
  p : s.sP < n
  z : s.sZ < n
  g : ∀ x ∈ s.sG, x < n

/-- An entry of an array of numbers below n, or 0, is below n. -/
theorem getD_lt {a : Array ℕ} {n : ℕ} (h : ∀ x ∈ a, x < n) (h0 : 0 < n) (j : ℕ) :
    a.getD j 0 < n := by
  by_cases hj : j < a.size
  · have e : a.getD j 0 = a[j] := by simp [Array.getD, hj]
    rw [e]
    exact h _ (Array.getElem_mem hj)
  · have e : a.getD j 0 = 0 := by simp [Array.getD, hj]
    rw [e]
    exact h0

/-- One step of the tie: one claim more, with a slot of its own. -/
theorem tieStep_chain {a : E} {s s' : Model.Forest.TieStep} {j : ℕ} {F G : Fork} {C D : Ctx}
    (h : Ok (Model.Forest.tieStep a s j) F C s' G D)
    (hq : j = 0 ∨ (s.sP < F.next ∧ s.sZ < F.next)) (hGs : ∀ x ∈ s.sG, x < F.next) :
    ∃ f, s'.rows = s.rows.push f ∧ RowChain ρ [f] F.next G.next ∧ TieAt s' G.next := by
  unfold Model.Forest.tieStep at h
  rw [ok_bind] at h
  obtain ⟨p, F1, C1, h1, h⟩ := h
  have A1 := pscBegin_at h1
  have g0 := (pscBegin_ok h1).2
  rw [ok_bind] at h
  obtain ⟨⟨first, p1⟩, F2, C2, h2, h⟩ := h
  have A2 := pscEnds_at h2 A1
  obtain ⟨g1, g2⟩ : F1.next ≤ first ∧ F2.next = first + (if j = 0 then 3 else 2) := pscEnds_ok h2
  try dsimp only at h
  rw [ok_bind] at h
  obtain ⟨vP, F3, C3, h3, h⟩ := h
  have e3 := congrArg Fork.next (ask_stay h3)
  rw [ok_bind] at h
  obtain ⟨vG, F4, C4, h4, h⟩ := h
  have e4 := congrArg Fork.next (ask_stay h4)
  try dsimp only at h
  have hcom : ∃ (S0 : E) (x : Aff × Model.Psc) (F5 : Fork) (C5 : Ctx) (F6 : Fork) (C6 : Ctx),
      Ok (Model.pscRow p1 S0) F5 C5 x F6 C6 ∧ F5.next = F4.next ∧ G = F6 ∧
      s' = { rows := s.rows.push x.1, sZ := if j = 0 then first else s.sZ,
             sP := if j = 0 then first + 1 else first,
             sG := s.sG.push ((if j = 0 then first + 1 else first) + 1) } := by
    by_cases hj : j = 0
    · rw [if_pos hj] at h
      rw [ok_bind] at h
      obtain ⟨y0, Fa, Ca, ha, h⟩ := h
      rw [ok_bind] at h
      obtain ⟨y, Fb, Cb, hb, h⟩ := h
      rw [ok_pure] at hb
      rw [ok_bind] at h
      obtain ⟨x, Fc, Cc, hc, h⟩ := h
      rw [ok_pure] at h
      exact ⟨y, x, Fb, Cb, Fc, Cc, hc, by
        rw [hb.2.1]
        exact congrArg Fork.next (ask_stay ha), h.2.1, h.1⟩
    · rw [if_neg hj] at h
      rw [ok_bind] at h
      obtain ⟨y, Fb, Cb, hb, h⟩ := h
      rw [ok_pure] at hb
      rw [ok_bind] at h
      obtain ⟨x, Fc, Cc, hc, h⟩ := h
      rw [ok_pure] at h
      exact ⟨y, x, Fb, Cb, Fc, Cc, hc, by rw [hb.2.1], h.2.1, h.1⟩
  obtain ⟨S0, ⟨row, p2⟩, F5, C5, F6, C6, h6, e5, e8, e7⟩ := hcom
  have e6 := pscRow_ok h6
  have e9 := congrArg Fork.next e8
  subst e7
  have hst : Below ρ (if j = 0 then Aff.ofConst zeroE else Aff.slot s.sP) F.next := by
    by_cases hj : j = 0
    · rw [if_pos hj]
      exact below_const ρ _ _
    · rw [if_neg hj]
      exact below_slot ρ (hq.resolve_left hj).1
  obtain ⟨jj, hi, t1, t2, T⟩ := pscRow_tri ρ h6 A2 hst (below_empty ρ _)
  have hn2 : 2 ≤ (if j = 0 then 3 else 2) := by
    split_ifs <;> omega
  have hG : G.next = first + (if j = 0 then 3 else 2) := by omega
  refine ⟨row, rfl, chain_one t1 T (by omega), ?_, ?_, ?_⟩
  · show (if j = 0 then first + 1 else first) < G.next
    rw [hG]
    split_ifs <;> omega
  · show (if j = 0 then first else s.sZ) < G.next
    by_cases hj : j = 0
    · rw [if_pos hj]
      omega
    · rw [if_neg hj]
      have k := (hq.resolve_left hj).2
      omega
  · show ∀ x ∈ s.sG.push ((if j = 0 then first + 1 else first) + 1), x < G.next
    intro x hx
    rcases Array.mem_push.mp hx with k | k
    · have k' := hGs x k
      omega
    · rw [k, hG]
      split_ifs <;> omega

/-- Steps of the tie, from a state whose slots have been taken: the claims that are added, in the
order of their slots. -/
theorem tieSteps_chain (a : E) : ∀ (l : List ℕ) (s : Model.Forest.TieStep) (F : Fork) (C : Ctx)
    (s' : Model.Forest.TieStep) (G : Fork) (D : Ctx), TieAt s F.next →
    Ok (l.foldlM (Model.Forest.tieStep a) s) F C s' G D →
    ∃ rows : List Aff, s'.rows.toList = s.rows.toList ++ rows ∧ RowChain ρ rows F.next G.next ∧
      TieAt s' G.next
  | [], s, F, C, s', G, D, Q, h => by
    rw [List.foldlM_nil] at h
    obtain ⟨rfl, rfl, -⟩ := pure_ok h
    exact ⟨[], by simp, Nat.le_refl _, Q⟩
  | j :: l, s, F, C, s', G, D, Q, h => by
    rw [List.foldlM_cons] at h
    obtain ⟨s1, F1, C1, h1, h2⟩ := bind_ok h
    obtain ⟨f, r1, r2, r3⟩ := tieStep_chain ρ h1 (Or.inr ⟨Q.p, Q.z⟩) Q.g
    obtain ⟨rows, q1, q2, q3⟩ := tieSteps_chain a l s1 F1 C1 s' G D r3 h2
    refine ⟨f :: rows, ?_, chain_append [f] rows F.next F1.next G.next r2 q2, q3⟩
    rw [q1, r1]
    simp

/-- The tie: its claims in the order of their slots; the slot of the key side's root has been taken,
and the form from which the table side starts reads taken slots alone. -/
theorem tie_chain {a : E} {t : Model.Forest.Tie} {F G : Fork} {C D : Ctx}
    (h : Ok (Model.Forest.tie a) F C t G D) :
    RowChain ρ t.rows.toList F.next G.next ∧ t.sZ < G.next ∧ Below ρ t.cT G.next := by
  unfold Model.Forest.tie at h
  rw [ok_bind] at h
  obtain ⟨s, F1, C1, h1, h⟩ := h
  have e31 : List.range 31 = 0 :: (List.range 30).map (· + 1) := rfl
  rw [e31, List.foldlM_cons] at h1
  obtain ⟨s0, F0, C0, k0, k1⟩ := bind_ok h1
  obtain ⟨f0, r1, r2, r3⟩ := tieStep_chain ρ k0 (Or.inl rfl)
    (fun x hx => absurd hx (Array.not_mem_empty x))
  obtain ⟨rows, q1, q2, q3⟩ := tieSteps_chain ρ a _ s0 F0 C0 s F1 C1 r3 k1
  try dsimp only at h
  rw [ok_bind] at h
  obtain ⟨pt5, F2, C2, h2, h⟩ := h
  have e2 := congrArg Fork.next (lift_stay h2)
  try dsimp only at h
  rw [ok_pure] at h
  obtain ⟨e3, e4, _⟩ := h
  have e5 := congrArg Fork.next e4
  subst e3
  have eG : G.next = F1.next := by omega
  have er : s.rows.toList = f0 :: rows := by
    rw [q1, r1]
    simp
  refine ⟨?_, ?_, ?_⟩
  · show RowChain ρ s.rows.toList F.next G.next
    rw [er, eG]
    exact chain_append [f0] rows F.next F0.next F1.next r2 q2
  · show s.sZ < G.next
    rw [eG]
    exact q3.z
  · show Below ρ ((List.range 32).foldl
      (fun (f : Aff) j => Aff.addMul f (Aff.slot ((s.sG.push s.sP).getD j 0))
        ((Model.eqTab pt5.reverse).getD j zeroE)) (Aff.ofConst zeroE)) G.next
    rw [eG]
    refine below_foldl (fun j => (s.sG.push s.sP).getD j 0) _ _ _ (below_const ρ _ _)
      fun j _ => getD_lt (fun x hx => ?_) (Nat.lt_of_le_of_lt (Nat.zero_le _) q3.p) j
    rcases Array.mem_push.mp hx with k | k
    · exact q3.g x k
    · rw [k]
      exact q3.p

/-! ## 9. The lookup's routine -/

/-- Putting a claim on the list of owed claims takes no slot. -/
theorem owe_next {what : String} {j : ℕ} {F G : Fork} {C D : Ctx}
    (h : Ok (SubM.owe what) F C j G D) : G.next = F.next := by
  have e : SubM.owe what F C = .ok ((F.owed.size, { F with owed := F.owed.push { what } }), C) :=
    rfl
  unfold Ok at h
  rw [e] at h
  cases h
  rfl

/-- The lookup's first draws leave the state. -/
theorem draws_stay {h : Model.Forest.Shape} {x : E × E × E} {F G : Fork} {C D : Ctx}
    (hk : Ok (Model.Forest.draws h) F C x G D) : G = F := by
  unfold Model.Forest.draws at hk
  dsimp only at hk
  by_cases c : h.NC > 1
  · rw [if_pos c] at hk
    rw [ok_bind] at hk
    obtain ⟨theta, F1, C1, h1, hk⟩ := hk
    have e1 := lift_stay h1
    rw [ok_bind] at hk
    obtain ⟨alpha, F2, C2, h2, hk⟩ := hk
    have e2 := lift_stay h2
    rw [ok_pure] at hk
    rw [hk.2.1, e2, e1]
  · rw [if_neg c] at hk
    rw [ok_bind] at hk
    obtain ⟨theta, F1, C1, h1, hk⟩ := hk
    have e1 := (pure_ok h1).2.1
    rw [ok_bind] at hk
    obtain ⟨alpha, F2, C2, h2, hk⟩ := hk
    have e2 := lift_stay h2
    rw [ok_pure] at hk
    rw [hk.2.1, e2, e1]

/-- **The claims of the lookup's routine, in the order of their slots.** l1: the tie's and the key
side's, from the routine's first free slot on and below the two slots cL and cL + 1 that the
hidden value at the end of the key side reads; l2: the table side's, from cL + 2 on and below m1;
the sumcheck of the leaves, whose claim is made later, has its slots from m1 on and below m2, and
starts from a form C0 on taken slots; bRow: the bits', from m2 on and below the slot of the bits'
end value. -/
theorem pad_chain {calls : Array Model.Call} {pub : Array ℕ} {lid : ℕ} {F G : Fork} {C D : Ctx}
    {g : Model.Forest.Heard} (h : Ok (Model.Forest.pad calls pub lid) F C g G D) :
    ∃ (l1 l2 : List Aff) (bRow : Aff) (cL : ℕ) (tau : E) (C0 : Aff) (m1 m2 : ℕ),
      g.rows.toList = l1 ++ l2 ++ [bRow] ∧
      g.cEnd = Aff.scale (Aff.slot cL) (subE oneE tau) + Aff.scale (Aff.slot (cL + 1)) tau ∧
      RowChain ρ l1 F.next cL ∧ RowChain ρ l2 (cL + 2) m1 ∧ PscAt g.leaves m2 C0 m1 ∧
      Below ρ C0 m1 ∧ RowChain ρ [bRow] m2 g.sBit ∧ g.sBit < G.next := by
  unfold Model.Forest.pad at h
  obtain ⟨h0, Fg, _, k, h⟩ := bind_ok h
  obtain ⟨e0, eg, -⟩ := subGet_ok k
  obtain ⟨_, Fq, _, kq, h⟩ := bind_ok h
  have eq := lift_stay kq
  obtain ⟨slot0, Fs, _, ks, h⟩ := bind_ok h
  have es := ask_stay ks
  obtain ⟨o1, Fo1, _, ko1, h⟩ := bind_ok h
  obtain ⟨o2, Fo2, _, ko2, h⟩ := bind_ok h
  obtain ⟨o3, Fo3, _, ko3, h⟩ := bind_ok h
  obtain ⟨⟨theta, alpha, a⟩, Fa, Ca, kd, h⟩ := bind_ok h
  have hlo : Fa.next = F.next := by
    rw [draws_stay kd, owe_next ko3, owe_next ko2, owe_next ko1, es, eq, eg]
  obtain ⟨t, Fb, Cb, kt0, h⟩ := bind_ok h
  obtain ⟨keys, Fk, Ck, kk, h⟩ := bind_ok h
  obtain ⟨table, Ft, Ct, kt, h⟩ := bind_ok h
  obtain ⟨-, h⟩ := must_bind h
  obtain ⟨leaves, F5, C5, k5, h⟩ := bind_ok h
  obtain ⟨⟨zb0, leaves'⟩, F6, C6, k6, h⟩ := bind_ok h
  obtain ⟨r5, F7, C7, k7, h⟩ := bind_ok h
  obtain ⟨bits, F8, C8, k8, h⟩ := bind_ok h
  obtain ⟨⟨zb1, bits'⟩, F9, C9, k9, h⟩ := bind_ok h
  obtain ⟨⟨sBit, bits''⟩, F10, C10, k10, h⟩ := bind_ok h
  obtain ⟨vBit, F11, C11, k11, h⟩ := bind_ok h
  obtain ⟨⟨bitsRow, p'⟩, F12, C12, k12, h⟩ := bind_ok h
  obtain ⟨s, F13, C13, k13, h⟩ := bind_ok h
  obtain ⟨-, h⟩ := must_bind h
  obtain ⟨-, h⟩ := must_bind h
  obtain ⟨-, h⟩ := must_bind h
  obtain ⟨rfl, rfl, -⟩ := pure_ok h
  have hd := shape_depth (ok_of_toOption e0)
  obtain ⟨cT1, cT2, cT3⟩ := tie_chain ρ kt0
  obtain ⟨rows1, cL, tau, q1, q2, q3, q4⟩ := levels_chain_ne ρ
    (s := { rows := t.rows, rho := #[], form := Aff.slot t.sZ }) (below_slot ρ cT2) kk
    (range_ne_nil (by
      show 0 < h0.dT + h0.rK
      omega))
  have hle := chain_le rows1 _ _ q4
  obtain ⟨rows2, u1, u2, u3⟩ := levels_chain ρ _ _ _
    (s := { rows := keys.rows, rho := t.rhoT, form := t.cT }) (cT3.mono (by omega)) kt
  have A6 := roundsIn_at k6 (pscBegin_at k5)
  have g7 := congrArg Fork.next (lift_stay k7)
  have A10 := pscEnds_at k10 (roundsIn_at k9 (pscBegin_at k8))
  obtain ⟨_, g10⟩ : F9.next ≤ sBit ∧ F10.next = sBit + 1 := pscEnds_ok k10
  have g11 := congrArg Fork.next (ask_stay k11)
  have g12 := pscRow_ok k12
  have g13 := congrArg Fork.next (ask_stay k13)
  obtain ⟨jb, hb, b1, b2, Tb⟩ := pscRow_tri ρ k12 A10 (below_const ρ _ _) (below_empty ρ _)
  refine ⟨t.rows.toList ++ rows1, rows2, bitsRow, cL, tau, table.form, Ft.next, F6.next, ?_, q2,
    ?_, ?_, A6, u3, chain_one (by omega) Tb b2, ?_⟩
  · show (table.rows.push bitsRow).toList = _
    have e1 : table.rows.toList = keys.rows.toList ++ rows2 := u1
    have e2 : keys.rows.toList = t.rows.toList ++ rows1 := q1
    have e3 : (table.rows.push bitsRow).toList = table.rows.toList ++ [bitsRow] := by simp
    rw [e3, e1, e2]
  · rw [← hlo]
    exact chain_append _ _ _ _ _ cT1 q4
  · rw [← q3]
    exact u2
  · show sBit < _
    omega

/-! ## 10. The four sumchecks of the head -/

/-- The claim of the product layer of the squares has a slot of its own between the slots of the
sums of limb products and the layer's end values. -/
theorem hearSquares_chain {h : Model.Head.Shape} {PV gp : Array E} {sW : ℕ} {wpl : Model.Level}
    {F G : Fork} {C D : Ctx} (H : Ok (Model.Head.hearSquares h PV) F C (sW, gp, wpl) G D) :
    RowChain ρ [wpl.row] (sW + Model.ledNS h.XL) wpl.sL := by
  unfold Model.Head.hearSquares at H
  try dsimp only at H
  rw [ok_bind] at H
  obtain ⟨s, F1, C1, h1, H⟩ := H
  obtain ⟨e1, e2⟩ := claimsIn_ok h1
  rw [ok_bind] at H
  obtain ⟨g, F2, C2, h2, H⟩ := H
  have e3 := congrArg Fork.next (lift_stay h2)
  try dsimp only at H
  rw [ok_bind] at H
  obtain ⟨o, F3, C3, h3, H⟩ := H
  obtain ⟨j, hi, t1, t2, T⟩ := levelIn_tri ρ h3
    (below_foldl (fun t => s + t) _ _ _ (below_empty ρ _) fun t ht => by
      have k := List.mem_range.mp ht
      show s + t < F2.next
      omega)
  have t3 : s + Model.ledNS h.XL ≤ j := by omega
  rw [ok_pure] at H
  obtain ⟨e7, _, _⟩ := H
  cases e7
  exact chain_one t3 T t2

/-- The rounds of a token sumcheck: it starts from the slot of its claimed sum, and its own slots
begin behind that slot. -/
theorem tscRounds_at {P : Array E} {lt : ℕ} {o : Model.Tsc} {F G : Fork} {C D : Ctx}
    (h : Ok (Model.tscRounds P lt) F C o G D) :
    PscAt o.p G.next (Aff.slot o.sCl) (o.sCl + 1) := by
  unfold Model.tscRounds at h
  rw [ok_bind] at h
  obtain ⟨_, F1, C1, h1, h⟩ := h
  rw [ok_bind] at h
  obtain ⟨sCl, F2, C2, h2, h⟩ := h
  obtain ⟨e2, e3⟩ := claimsIn_ok h2
  rw [ok_bind] at h
  obtain ⟨p, F3, C3, h3, h⟩ := h
  have A3 := pscBegin_at h3
  rw [ok_bind] at h
  obtain ⟨⟨r, p1⟩, F4, C4, h4, h⟩ := h
  have A4 := tscLoop_at _ _ _ _ _ _ _ _ h4 A3
  try dsimp only at h
  rw [ok_pure] at h
  obtain ⟨e6, e7, _⟩ := h
  subst e6
  rw [e7]
  have e8 : F2.next = sCl + 1 := by omega
  rw [e8] at A4
  exact A4

/-- A whole token sumcheck: the slots of its hiding polynomial's coefficients end at or before its
first end value. -/
theorem tscIn_at {P : Array E} {lt n dY : ℕ} {o : Model.Tsc} {F G : Fork} {C D : Ctx}
    (h : Ok (Model.tscIn P lt n dY) F C o G D) :
    PscAt o.p o.sEnd (Aff.slot o.sCl) (o.sCl + 1) := by
  unfold Model.tscIn at h
  rw [ok_bind] at h
  obtain ⟨o1, F1, C1, h1, h⟩ := h
  have A1 := tscRounds_at h1
  rw [ok_bind] at h
  obtain ⟨⟨sEnd, p⟩, F2, C2, h2, h⟩ := h
  have A2 := pscEnds_at h2 A1
  try dsimp only at h
  rw [ok_pure] at h
  obtain ⟨e5, _, _⟩ := h
  subst e5
  exact A2

/-- The claim of the products' sumcheck has a slot of its own behind the slot of the claimed sum
and before the end values. -/
theorem hearProducts_chain {h : Model.Head.Shape} {PV omV : Array E} {sPv : ℕ} {tV : Model.Tsc}
    {F G : Fork} {C D : Ctx} (H : Ok (Model.Head.hearProducts h PV) F C (sPv, omV, tV) G D) :
    RowChain ρ [tV.rowU] (tV.sCl + 1) tV.sEnd := by
  unfold Model.Head.hearProducts at H
  rw [ok_bind] at H
  obtain ⟨s, F1, C1, h1, H⟩ := H
  rw [ok_bind] at H
  obtain ⟨g, F2, C2, h2, H⟩ := H
  rw [ok_bind] at H
  obtain ⟨o, F3, C3, h3, H⟩ := H
  have A3 := tscIn_at h3
  rw [ok_bind] at H
  obtain ⟨sh, F4, C4, h4, H⟩ := H
  rw [ok_bind] at H
  obtain ⟨⟨row, p⟩, F5, C5, h5, H⟩ := H
  try dsimp only at H
  rw [ok_pure] at H
  obtain ⟨e9, _, _⟩ := H
  cases e9
  obtain ⟨j, hi, t1, t2, T⟩ := pscRow_tri ρ h5 A3 (below_slot ρ (Nat.lt_succ_self _))
    (below_empty ρ _)
  exact chain_one t1 T t2

/-- The same for the sumcheck of the stream times the reciprocal. -/
theorem hearStream_chain {h : Model.Head.Shape} {zt : Array E} {tN : Model.Tsc} {F G : Fork}
    {C D : Ctx} (H : Ok (Model.Head.hearStream h zt) F C tN G D) :
    RowChain ρ [tN.rowU] (tN.sCl + 1) tN.sEnd := by
  unfold Model.Head.hearStream at H
  rw [ok_bind] at H
  obtain ⟨o, F1, C1, h1, H⟩ := H
  have A1 := tscIn_at h1
  rw [ok_bind] at H
  obtain ⟨a, F2, C2, h2, H⟩ := H
  rw [ok_bind] at H
  obtain ⟨b, F3, C3, h3, H⟩ := H
  rw [ok_bind] at H
  obtain ⟨⟨row, p⟩, F4, C4, h4, H⟩ := H
  try dsimp only at H
  rw [ok_pure] at H
  obtain ⟨e7, _, _⟩ := H
  subst e7
  obtain ⟨j, hi, t1, t2, T⟩ := pscRow_tri ρ h4 A1 (below_slot ρ (Nat.lt_succ_self _))
    (below_empty ρ _)
  exact chain_one t1 T t2

/-- The same for the sumcheck of the activations times the head's weights. -/
theorem hearLogits_chain {h : Model.Head.Shape} {lam : ℕ} {zt rs : Array E} {tH : Model.Tsc}
    {F G : Fork} {C D : Ctx} (H : Ok (Model.Head.hearLogits h lam zt) F C (tH, rs) G D) :
    RowChain ρ [tH.rowU] (tH.sCl + 1) tH.sEnd := by
  unfold Model.Head.hearLogits at H
  rw [ok_bind] at H
  obtain ⟨o, F1, C1, h1, H⟩ := H
  have A1 := tscRounds_at h1
  rw [ok_bind] at H
  obtain ⟨⟨r, p⟩, F2, C2, h2, H⟩ := H
  have A2 := channelRounds_at _ _ _ _ _ _ _ _ h2 A1
  try dsimp only at H
  rw [ok_bind] at H
  obtain ⟨⟨sEnd, p1⟩, F3, C3, h3, H⟩ := H
  have A3 := pscEnds_at h3 A2
  try dsimp only at H
  rw [ok_bind] at H
  obtain ⟨a, F4, C4, h4, H⟩ := H
  rw [ok_bind] at H
  obtain ⟨b, F5, C5, h5, H⟩ := H
  rw [ok_bind] at H
  obtain ⟨⟨row, p2⟩, F6, C6, h6, H⟩ := H
  try dsimp only at H
  rw [ok_pure] at H
  obtain ⟨e9, _, _⟩ := H
  cases e9
  obtain ⟨j, hi, t1, t2, T⟩ := pscRow_tri ρ h6 A3 (below_slot ρ (Nat.lt_succ_self _))
    (below_empty ρ _)
  exact chain_one t1 T t2

/-! ## 11. All that hear returns -/

/-- The claims that the sumchecks of what was heard leave, in the order of their slots. See
pad_chain for the lookup's; the first list's range is stated from slot 0 on here, since nothing
that is used of hear lies before the lookup. The four of the head: each has a slot of its own
behind the slots of the values from which its sumcheck starts and before its end values. -/
structure HeardRows (XL : ℕ) (x : Model.Head.Heard) (l1 l2 : List Aff) (bRow : Aff) (cL : ℕ)
    (tau : E) (C0 : Aff) (m1 m2 : ℕ) : Prop where
  rows : x.g1.rows.toList = l1 ++ l2 ++ [bRow]
  cEnd : x.g1.cEnd =
    Aff.scale (Aff.slot cL) (subE oneE tau) + Aff.scale (Aff.slot (cL + 1)) tau
  c1 : RowChain ρ l1 0 cL
  c2 : RowChain ρ l2 (cL + 2) m1
  leaves : PscAt x.g1.leaves m2 C0 m1
  leaves0 : Below ρ C0 m1
  c3 : RowChain ρ [bRow] m2 x.g1.sBit
  bit : x.g1.sBit < x.sW
  w : RowChain ρ [x.wpl.row] (x.sW + Model.ledNS XL) x.wpl.sL
  tV : RowChain ρ [x.tV.rowU] (x.tV.sCl + 1) x.tV.sEnd
  tN : RowChain ρ [x.tN.rowU] (x.tN.sCl + 1) x.tN.sEnd
  tH : RowChain ρ [x.tH.rowU] (x.tH.sCl + 1) x.tH.sEnd

/-- **What hear returns has these claims.** -/
theorem hear_rows {h : Model.Head.Shape} {L : Model.Head.HL} {hp : Model.Head.HPlanH2}
    {cov : Model.Head.Covered} {plain : Array E} {x : Model.Head.Heard} {F G : Fork} {C D : Ctx}
    (hx : Ok (Model.Head.hear h L hp cov plain) F C x G D) :
    ∃ l1 l2 bRow cL tau C0 m1 m2, HeardRows ρ h.XL x l1 l2 bRow cL tau C0 m1 m2 := by
  obtain ⟨yTok, F1, C1, F2, C2, g1, F3, C3, Zl, F4, C4, PV, F5, C5, sW, gp, wpl, F6, C6, sPv, omV,
    tV, F7, C7, qN, qH, tN, F8, C8, tH, rs, F9, C9, _, _, k3, k4, k5, k6, k7, _, _, k8, k9, _,
    ex⟩ := hear_steps hx
  obtain ⟨l1, l2, bRow, cL, tau, C0, m1, m2, a1, a2, a3, a4, a5, a6, a7, a8⟩ := pad_chain ρ k3
  have m4 := congrArg Fork.next (mergedPoint_stay k4)
  have m5 := congrArg Fork.next (lift_stay k5)
  obtain ⟨s1, _, _, _⟩ := hearSquares_ok k6
  subst ex
  exact ⟨l1, l2, bRow, cL, tau, C0, m1, m2, a1, a2, chain_lower _ _ 0 _ a3 (Nat.zero_le _), a4, a5,
    a6, a7, by
      show g1.sBit < sW
      omega,
    hearSquares_chain ρ k6, hearProducts_chain ρ k7, hearStream_chain ρ k8,
    hearLogits_chain ρ k9⟩

end Row

#print axioms walk_shape
#print axioms tri_rowForm
#print axioms chain_solve
#print axioms pscRow_tri
#print axioms pad_chain
#print axioms hear_rows

end OnBytes.Road.Hd
