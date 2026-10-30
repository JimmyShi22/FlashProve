-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/KeptEquiv.lean: THE BIJECTION OF THE KEPT SLOTS OF TWO TYPED GROUPS THAT
`carryAt_renamed` (CarryRenamed.lean) ASKS, FROM ONE SENTENCE ON NUMBERS: at every number n the two
lists' messages number n have as many kept rows. Definitions and theorems. No text already in the library turns.

  `slotKey`: a kept slot's member's number in the list, and its row. `slotKey_inj`: a kept slot is
    known by these two numbers.
  `keptRowsAt l mem kp n`: the main rows of the list's message number n where it is a kept member;
    0 elsewhere. With code where mem and kp have code. `slot_iff`: there is a kept slot with the
    numbers (n, j) just where j < keptRowsAt … n.
  `keptRowsAt_beyond`, `keptRows_of_below`: beyond the list it is 0: so the sentence «at every n»
    follows from its cases below a bound on both lengths.
  `keptEquiv_of`: (∀ κ, ∃ κ', slotKey κ' = slotKey κ) · (∀ κ', ∃ κ, slotKey κ = slotKey κ') ⊢ ∃ φ :
    R.Kp ≃ R'.Kp, ∀ κ, (φ κ).1.1.1.val = κ.1.1.1.val ∧ (φ κ).2.val = κ.2.val, at R := (rowsPort cs l
    mem s e oM oZ hM hZ).keep kp and R' the like at other letters.
  `keptEquiv_rows`: **(∀ n, keptRowsAt l mem kp n = keptRowsAt l' mem' kp' n) ⊢ the same φ.**
Limits. The sentence is a premise. φ is chosen, not computed. Nothing on soundness.

-/
import Johnson.Top.H.SwitchKept

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Slice Cb Johnson.Top.H Johnson.Pack

section
variable (cs : OnBytes.Codes) (l : List (OnBytes.OracleShape × ℕ))
  (mem : Fin l.length → Prop) [DecidablePred mem] (s : Sg) (e : ℕ) (oM oZ : Fin l.length → ℕ)
  (hM : ∀ i, mem i → (l.get i).1.mainRows ≠ 0 → cMain cs (l.get i).1 = s.C)
  (hZ : ∀ i, mem i → (l.get i).1.maskRows ≠ 0 → cMask cs (l.get i).1 = s.Z)
  (kp : {i // mem i} → Prop) [DecidablePred kp]

/-- A kept slot's member's number in the list, and its row. -/
def slotKey (κ : (Johnson.Top.H.Rows.keep (rowsPort cs l mem s e oM oZ hM hZ) kp).Kp) : ℕ × ℕ :=
  (κ.1.1.1.val, κ.2.val)

theorem slotKey_inj : Function.Injective (slotKey cs l mem s e oM oZ hM hZ kp) := by
  intro κ₁ κ₂ h
  obtain ⟨⟨⟨⟨n₁, a₁⟩, b₁⟩, c₁⟩, ⟨j₁, d₁⟩⟩ := κ₁
  obtain ⟨⟨⟨⟨n₂, a₂⟩, b₂⟩, c₂⟩, ⟨j₂, d₂⟩⟩ := κ₂
  have h1 : n₁ = n₂ := congrArg Prod.fst h
  have h2 : j₁ = j₂ := congrArg Prod.snd h
  subst h1 h2
  rfl

/-- How many kept rows the list's message number n has: its main rows where it is a kept member;
0 elsewhere. -/
def keptRowsAt (n : ℕ) : ℕ :=
  if h : n < l.length then
    if hm : mem ⟨n, h⟩ then if kp ⟨⟨n, h⟩, hm⟩ then (l.get ⟨n, h⟩).1.mainRows else 0 else 0
  else 0

/-- There is a kept slot with the numbers (n, j) just where j is below the kept rows at n. -/
theorem slot_iff (n j : ℕ) :
    (∃ κ, slotKey cs l mem s e oM oZ hM hZ kp κ = (n, j)) ↔ j < keptRowsAt l mem kp n := by
  constructor
  · rintro ⟨⟨⟨⟨⟨n', a⟩, b⟩, c⟩, ⟨j', d⟩⟩, h⟩
    have h1 : n' = n := congrArg Prod.fst h
    have h2 : j' = j := congrArg Prod.snd h
    subst h1 h2
    have b' : mem ⟨n', a⟩ := b
    have c' : kp ⟨⟨n', a⟩, b'⟩ := c
    unfold keptRowsAt
    rw [dif_pos a, dif_pos b', if_pos c']
    exact d
  · intro h
    unfold keptRowsAt at h
    split at h
    · rename_i a
      split at h
      · rename_i b
        split at h
        · rename_i c
          exact ⟨⟨⟨⟨⟨n, a⟩, b⟩, c⟩, ⟨j, h⟩⟩, rfl⟩
        · exact absurd h (Nat.not_lt_zero _)
      · exact absurd h (Nat.not_lt_zero _)
    · exact absurd h (Nat.not_lt_zero _)

theorem keptRowsAt_beyond {n : ℕ} (h : l.length ≤ n) : keptRowsAt l mem kp n = 0 := by
  unfold keptRowsAt
  exact dif_neg (Nat.not_lt.2 h)

end

/-- The sentence on numbers, from its cases below a bound on both lists' lengths: a closed test
where the lists and the predicates are closed terms with code. -/
theorem keptRows_of_below (l : List (OnBytes.OracleShape × ℕ)) (mem : Fin l.length → Prop)
    [DecidablePred mem] (kp : {i // mem i} → Prop) [DecidablePred kp]
    (l' : List (OnBytes.OracleShape × ℕ)) (mem' : Fin l'.length → Prop) [DecidablePred mem']
    (kp' : {i // mem' i} → Prop) [DecidablePred kp'] (M : ℕ) (h1 : l.length ≤ M)
    (h2 : l'.length ≤ M) (h : ∀ n, n < M → keptRowsAt l mem kp n = keptRowsAt l' mem' kp' n)
    (n : ℕ) : keptRowsAt l mem kp n = keptRowsAt l' mem' kp' n := by
  by_cases hn : n < M
  · exact h n hn
  · rw [keptRowsAt_beyond l mem kp (Nat.le_trans h1 (Nat.not_lt.1 hn)),
      keptRowsAt_beyond l' mem' kp' (Nat.le_trans h2 (Nat.not_lt.1 hn))]

/-- **THE BIJECTION.** -/
theorem keptEquiv_of (cs : OnBytes.Codes) (l : List (OnBytes.OracleShape × ℕ))
    (mem : Fin l.length → Prop) [DecidablePred mem] (s : Sg) (e : ℕ) (oM oZ : Fin l.length → ℕ)
    (hM : ∀ i, mem i → (l.get i).1.mainRows ≠ 0 → cMain cs (l.get i).1 = s.C)
    (hZ : ∀ i, mem i → (l.get i).1.maskRows ≠ 0 → cMask cs (l.get i).1 = s.Z)
    (kp : {i // mem i} → Prop) [DecidablePred kp]
    (cs' : OnBytes.Codes) (l' : List (OnBytes.OracleShape × ℕ))
    (mem' : Fin l'.length → Prop) [DecidablePred mem'] (s' : Sg) (e' : ℕ)
    (oM' oZ' : Fin l'.length → ℕ)
    (hM' : ∀ i, mem' i → (l'.get i).1.mainRows ≠ 0 → cMain cs' (l'.get i).1 = s'.C)
    (hZ' : ∀ i, mem' i → (l'.get i).1.maskRows ≠ 0 → cMask cs' (l'.get i).1 = s'.Z)
    (kp' : {i // mem' i} → Prop) [DecidablePred kp']
    (h1 : ∀ κ, ∃ κ', slotKey cs' l' mem' s' e' oM' oZ' hM' hZ' kp' κ' =
      slotKey cs l mem s e oM oZ hM hZ kp κ)
    (h2 : ∀ κ', ∃ κ, slotKey cs l mem s e oM oZ hM hZ kp κ =
      slotKey cs' l' mem' s' e' oM' oZ' hM' hZ' kp' κ') :
    ∃ φ : (Johnson.Top.H.Rows.keep (rowsPort cs l mem s e oM oZ hM hZ) kp).Kp ≃
        (Johnson.Top.H.Rows.keep (rowsPort cs' l' mem' s' e' oM' oZ' hM' hZ') kp').Kp,
      ∀ κ, (φ κ).1.1.1.val = κ.1.1.1.val ∧ (φ κ).2.val = κ.2.val := by
  choose f hf using h1
  have hb : Function.Bijective f := by
    refine ⟨fun a b hab => ?_, fun κ' => ?_⟩
    · exact slotKey_inj cs l mem s e oM oZ hM hZ kp
        ((hf a).symm.trans ((congrArg _ hab).trans (hf b)))
    · obtain ⟨κ, hκ⟩ := h2 κ'
      exact ⟨κ, slotKey_inj cs' l' mem' s' e' oM' oZ' hM' hZ' kp' ((hf κ).trans hκ)⟩
  exact ⟨Equiv.ofBijective f hb, fun κ =>
    ⟨congrArg Prod.fst (hf κ), congrArg Prod.snd (hf κ)⟩⟩

/-- **THE BIJECTION, FROM ONE SENTENCE ON NUMBERS.** -/
theorem keptEquiv_rows (cs : OnBytes.Codes) (l : List (OnBytes.OracleShape × ℕ))
    (mem : Fin l.length → Prop) [DecidablePred mem] (s : Sg) (e : ℕ) (oM oZ : Fin l.length → ℕ)
    (hM : ∀ i, mem i → (l.get i).1.mainRows ≠ 0 → cMain cs (l.get i).1 = s.C)
    (hZ : ∀ i, mem i → (l.get i).1.maskRows ≠ 0 → cMask cs (l.get i).1 = s.Z)
    (kp : {i // mem i} → Prop) [DecidablePred kp]
    (cs' : OnBytes.Codes) (l' : List (OnBytes.OracleShape × ℕ))
    (mem' : Fin l'.length → Prop) [DecidablePred mem'] (s' : Sg) (e' : ℕ)
    (oM' oZ' : Fin l'.length → ℕ)
    (hM' : ∀ i, mem' i → (l'.get i).1.mainRows ≠ 0 → cMain cs' (l'.get i).1 = s'.C)
    (hZ' : ∀ i, mem' i → (l'.get i).1.maskRows ≠ 0 → cMask cs' (l'.get i).1 = s'.Z)
    (kp' : {i // mem' i} → Prop) [DecidablePred kp']
    (h : ∀ n, keptRowsAt l mem kp n = keptRowsAt l' mem' kp' n) :
    ∃ φ : (Johnson.Top.H.Rows.keep (rowsPort cs l mem s e oM oZ hM hZ) kp).Kp ≃
        (Johnson.Top.H.Rows.keep (rowsPort cs' l' mem' s' e' oM' oZ' hM' hZ') kp').Kp,
      ∀ κ, (φ κ).1.1.1.val = κ.1.1.1.val ∧ (φ κ).2.val = κ.2.val :=
  keptEquiv_of cs l mem s e oM oZ hM hZ kp cs' l' mem' s' e' oM' oZ' hM' hZ' kp'
    (fun κ => (slot_iff cs' l' mem' s' e' oM' oZ' hM' hZ' kp' _ _).2
      (h _ ▸ (slot_iff cs l mem s e oM oZ hM hZ kp _ _).1 ⟨κ, rfl⟩))
    (fun κ' => (slot_iff cs l mem s e oM oZ hM hZ kp _ _).2
      ((h _).symm ▸ (slot_iff cs' l' mem' s' e' oM' oZ' hM' hZ' kp' _ _).1 ⟨κ', rfl⟩))

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.keptRows_of_below
#print axioms VerifiableInference.Desc.LinkJoin.slot_iff
#print axioms VerifiableInference.Desc.LinkJoin.keptEquiv_rows
#print axioms VerifiableInference.Desc.LinkJoin.slotKey_inj
#print axioms VerifiableInference.Desc.LinkJoin.keptEquiv_of
