-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/Rule/RowLens.lean: one row of a run's coins (Honest/Frame.lean:
`Purse`, `Coins`) as a lens (Prob/LensLaw.lean): a getter and a setter, typed at the row's own
count; and what `Coins.look` returns at a run's coins in which one row has been set anew. No part,
no description and no run of a protocol occurs here.

  1  `Cs.sub0`, `Cs.cut_zero`   coins of the count 0; the cut from 0 on, of the whole count
  2  `dueAt_cons`, `Purse.find?_none`, `Purse.lens`   a table of rows: the first row at an address
  3  `noCoin`, `pick`, `Coins.look_pick`   `Coins.look` as a function of three look-ups
  4  `lens_comp`, `Coins.lens₀`, `Coins.lens₁`, `Coins.lens₂`, `Coins.lens`   the lens on a run's
     coins, at an address that has rows in one table alone. The case of an address without a row is
     included: the count is 0, and the lens shows the one element of that type

What `Coins.lens` says. `t`: the number, from 0, of the chain in whose table the address may have a
row. (i) The lens laws hold. (ii) At another address `look` does not read the row. (iii) At the
address itself, in the address's own chain and in the second chain (number 2), `look` returns
exactly what the lens shows, at the row's count.

Limits.
  * That an address has rows in one table alone is a hypothesis here: it is a matter of the book's
    tests (`ProverCoinCounts.noRow₁`, `ProverCoinCounts.noRow₂`, `ProverCoinCounts.noRow₃`, Honest/Law/Rule/Tests.lean).
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Frame
import Prob.LensLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open Prob

/-! ## 1 Coins -/

/-- The count 0 has one element. -/
theorem Cs.sub0 (z : Cs ⟨0, 0⟩) : z = Cs.empty := by
  obtain ⟨zf, ze⟩ := z
  have hf : zf = fun i => i.elim0 := funext fun i => i.elim0
  have he : ze = fun i => i.elim0 := funext fun i => i.elim0
  subst hf
  subst he
  rfl

/-- The cut from 0 on, of the whole count, is the whole. -/
theorem Cs.cut_zero {d : Due} (c : Cs d) : c.cut ⟨0, 0⟩ d = some c := by
  have h : (⟨0, 0⟩ : Due).f + d.f ≤ d.f ∧ (⟨0, 0⟩ : Due).e + d.e ≤ d.e :=
    ⟨Nat.le_of_eq (Nat.zero_add _), Nat.le_of_eq (Nat.zero_add _)⟩
  obtain ⟨cf, ce⟩ := c
  unfold Cs.cut
  rw [dif_pos h]
  refine congrArg some ?_
  simp only [Cs.mk.injEq]
  exact ⟨funext fun i => congrArg cf (Fin.ext (Nat.zero_add _)),
    funext fun i => congrArg ce (Fin.ext (Nat.zero_add _))⟩

/-! ## 2 A table of rows -/

theorem dueAt_cons (r : Addr × Due) (l : List (Addr × Due)) (a : Addr) :
    dueAt (r :: l) a = if r.1 = a then r.2 else dueAt l a := by
  obtain ⟨ra, rd⟩ := r
  unfold dueAt
  by_cases h : ra = a
  · subst h
    simp
  · have hb : (a == ra) = false := beq_eq_false_iff_ne.2 fun e => h e.symm
    simp [List.lookup, hb, h]

theorem Purse.find?_none : ∀ (l : List (Addr × Due)) (c : Purse l) (a : Addr),
    l.any (fun r => r.1 == a) = false → Purse.find? l c a = none
  | [], _, _, _ => rfl
  | r :: l, c, a, h => by
    simp only [List.any_cons, Bool.or_eq_false_iff] at h
    have hne : ¬ (r.1 == a) = true := by
      rw [h.1]
      exact Bool.false_ne_true
    rw [Purse.find?, if_neg hne]
    exact Purse.find?_none l c.2 a h.2

/-- No coin, as `Coins.look` returns it where an address has no row. -/
def noCoin : (d : Due) × Cs d := ⟨⟨0, 0⟩, Cs.empty⟩

/-- **The first row at an address, as a lens**, typed at the table's count for the address. -/
theorem Purse.lens : ∀ (l : List (Addr × Due)) (a : Addr) (d : Due), dueAt l a = d →
    ∃ (get : Purse l → Cs d) (put : Cs d → Purse l → Purse l), Lens.OK get put ∧
      (∀ c, (Purse.find? l c a).getD noCoin = ⟨d, get c⟩) ∧
      ∀ x c b, b ≠ a → Purse.find? l (put x c) b = Purse.find? l c b
  | [], _, d, h => by
    have hd : (⟨0, 0⟩ : Due) = d := h
    subst hd
    exact ⟨fun _ => Cs.empty, fun _ c => c,
      ⟨fun z _ => (Cs.sub0 z).symm, fun _ => rfl, fun _ _ _ => rfl⟩, fun _ => rfl,
      fun _ _ _ _ => rfl⟩
  | r :: l, a, d, h => by
    rw [dueAt_cons] at h
    by_cases hr : r.1 = a
    · rw [if_pos hr] at h
      subst h
      have hpos : (r.1 == a) = true := beq_iff_eq.2 hr
      refine ⟨fun (c : Cs r.2 × Purse l) => c.1, fun x (c : Cs r.2 × Purse l) => (x, c.2),
        ⟨fun _ _ => rfl, fun _ => rfl, fun _ _ _ => rfl⟩, ?_, ?_⟩
      · intro c
        have e : Purse.find? (r :: l) c a = some ⟨r.2, (c : Cs r.2 × Purse l).1⟩ := by
          rw [Purse.find?, if_pos hpos]
        exact congrArg (fun o => Option.getD o noCoin) e
      · intro x c b hb
        have hne : ¬ (r.1 == b) = true := fun e => hb ((beq_iff_eq.1 e).symm.trans hr)
        rw [Purse.find?, Purse.find?, if_neg hne, if_neg hne]
    · rw [if_neg hr] at h
      obtain ⟨get, put, ok, h1, h2⟩ := Purse.lens l a d h
      have hne : ¬ (r.1 == a) = true := fun e => hr (beq_iff_eq.1 e)
      refine ⟨fun (c : Cs r.2 × Purse l) => get c.2,
        fun x (c : Cs r.2 × Purse l) => (c.1, put x c.2),
        ⟨fun z c => ok.tst_set z _,
          fun c => congrArg (fun t => ((c : Cs r.2 × Purse l).1, t)) (ok.set_tst _),
          fun z z' c => congrArg (fun t => ((c : Cs r.2 × Purse l).1, t)) (ok.set_set z z' _)⟩,
        ?_, ?_⟩
      · intro c
        rw [Purse.find?, if_neg hne]
        exact h1 _
      · intro x c b hb
        rw [Purse.find?, Purse.find?]
        by_cases hrb : (r.1 == b) = true
        · simp only [if_pos hrb]
        · simp only [if_neg hrb]
          exact h2 x _ b hb

/-! ## 3 The look-up -/

/-- `Coins.look`, from the three tables' look-ups. -/
def pick (ch : Nat) (o₁ o₂ o₃ : Option ((d : Due) × Cs d)) : (d : Due) × Cs d :=
  if ch == 0 then o₁.getD noCoin
  else if ch == 1 then o₂.getD noCoin
  else ((o₁.or o₂).or o₃).getD noCoin

theorem Coins.look_pick {B : ProverCoinCounts} (c : Coins B) (ch : Nat) (a : Addr) :
    c.look ch a = pick ch (Purse.find? B.first c.first a) (Purse.find? B.shared c.shared a)
      (Purse.find? B.second c.second a) := rfl

/-! ## 4 The lens on a run's coins -/

/-- Two lenses, the second on what the first shows. -/
theorem lens_comp {K M C : Type} {g₁ : K → M} {p₁ : M → K → K} {g₂ : M → C} {p₂ : C → M → M}
    (h₁ : Lens.OK g₁ p₁) (h₂ : Lens.OK g₂ p₂) :
    Lens.OK (fun k => g₂ (g₁ k)) (fun z k => p₁ (p₂ z (g₁ k)) k) where
  tst_set z k := by
    show g₂ (g₁ (p₁ (p₂ z (g₁ k)) k)) = z
    rw [h₁.tst_set, h₂.tst_set]
  set_tst k := by
    show p₁ (p₂ (g₂ (g₁ k)) (g₁ k)) k = k
    rw [h₂.set_tst, h₁.set_tst]
  set_set z z' k := by
    show p₁ (p₂ z (g₁ (p₁ (p₂ z' (g₁ k)) k))) (p₁ (p₂ z' (g₁ k)) k) = p₁ (p₂ z (g₁ k)) k
    rw [h₁.tst_set, h₂.set_set, h₁.set_set]

section
variable {B : ProverCoinCounts} (a : Addr) (d : Due)

theorem Coins.lens₀ (hd : dueAt B.first a = d) (h₂ : B.shared.any (fun r => r.1 == a) = false)
    (h₃ : B.second.any (fun r => r.1 == a) = false) :
    ∃ (get : Coins B → Cs d) (put : Cs d → Coins B → Coins B), Lens.OK get put ∧
      (∀ x k ch b, b ≠ a → (put x k).look ch b = k.look ch b) ∧
      ∀ ch, ch = 0 ∨ ch = 2 → ∀ k : Coins B, k.look ch a = ⟨d, get k⟩ := by
  obtain ⟨get, put, ok, e1, e2⟩ := Purse.lens B.first a d hd
  have okF : Lens.OK (fun k : Coins B => k.first) (fun p k => { k with first := p }) :=
    ⟨fun _ _ => rfl, fun _ => rfl, fun _ _ _ => rfl⟩
  refine ⟨_, _, lens_comp okF ok, ?_, ?_⟩
  · intro x k ch b hb
    rw [Coins.look_pick, Coins.look_pick]
    show pick ch (Purse.find? B.first (put x k.first) b) _ _ = _
    rw [e2 x k.first b hb]
  · intro ch hch k
    rw [Coins.look_pick, Purse.find?_none B.shared k.shared a h₂,
      Purse.find?_none B.second k.second a h₃, ← e1 k.first]
    rcases hch with rfl | rfl
    · rfl
    · cases Purse.find? B.first k.first a <;> rfl

theorem Coins.lens₁ (hd : dueAt B.shared a = d) (h₁ : B.first.any (fun r => r.1 == a) = false)
    (h₃ : B.second.any (fun r => r.1 == a) = false) :
    ∃ (get : Coins B → Cs d) (put : Cs d → Coins B → Coins B), Lens.OK get put ∧
      (∀ x k ch b, b ≠ a → (put x k).look ch b = k.look ch b) ∧
      ∀ ch, ch = 1 ∨ ch = 2 → ∀ k : Coins B, k.look ch a = ⟨d, get k⟩ := by
  obtain ⟨get, put, ok, e1, e2⟩ := Purse.lens B.shared a d hd
  have okF : Lens.OK (fun k : Coins B => k.shared) (fun p k => { k with shared := p }) :=
    ⟨fun _ _ => rfl, fun _ => rfl, fun _ _ _ => rfl⟩
  refine ⟨_, _, lens_comp okF ok, ?_, ?_⟩
  · intro x k ch b hb
    rw [Coins.look_pick, Coins.look_pick]
    show pick ch _ (Purse.find? B.shared (put x k.shared) b) _ = _
    rw [e2 x k.shared b hb]
  · intro ch hch k
    rw [Coins.look_pick, Purse.find?_none B.first k.first a h₁,
      Purse.find?_none B.second k.second a h₃, ← e1 k.shared]
    rcases hch with rfl | rfl
    · rfl
    · cases Purse.find? B.shared k.shared a <;> rfl

theorem Coins.lens₂ (hd : dueAt B.second a = d) (h₁ : B.first.any (fun r => r.1 == a) = false)
    (h₂ : B.shared.any (fun r => r.1 == a) = false) :
    ∃ (get : Coins B → Cs d) (put : Cs d → Coins B → Coins B), Lens.OK get put ∧
      (∀ x k ch b, b ≠ a → (put x k).look ch b = k.look ch b) ∧
      ∀ ch, ch = 2 → ∀ k : Coins B, k.look ch a = ⟨d, get k⟩ := by
  obtain ⟨get, put, ok, e1, e2⟩ := Purse.lens B.second a d hd
  have okF : Lens.OK (fun k : Coins B => k.second) (fun p k => { k with second := p }) :=
    ⟨fun _ _ => rfl, fun _ => rfl, fun _ _ _ => rfl⟩
  refine ⟨_, _, lens_comp okF ok, ?_, ?_⟩
  · intro x k ch b hb
    rw [Coins.look_pick, Coins.look_pick]
    show pick ch _ _ (Purse.find? B.second (put x k.second) b) = _
    rw [e2 x k.second b hb]
  · intro ch hch k
    subst hch
    rw [Coins.look_pick, Purse.find?_none B.first k.first a h₁,
      Purse.find?_none B.shared k.shared a h₂, ← e1 k.second]
    rfl

/-- **The lens on a run's coins**, at an address that has rows in the table of the chain number t
alone. -/
theorem Coins.lens (t : Nat) (ht : t = 0 ∨ t = 1 ∨ t = 2) (hd : dueAt (B.rowsOf t) a = d)
    (h₁ : t ≠ 0 → B.first.any (fun r => r.1 == a) = false)
    (h₂ : t ≠ 1 → B.shared.any (fun r => r.1 == a) = false)
    (h₃ : t ≠ 2 → B.second.any (fun r => r.1 == a) = false) :
    ∃ (get : Coins B → Cs d) (put : Cs d → Coins B → Coins B), Lens.OK get put ∧
      (∀ x k ch b, b ≠ a → (put x k).look ch b = k.look ch b) ∧
      ∀ ch, ch = t ∨ ch = 2 → ∀ k : Coins B, k.look ch a = ⟨d, get k⟩ := by
  rcases ht with rfl | rfl | rfl
  · exact Coins.lens₀ a d hd (h₂ (by decide)) (h₃ (by decide))
  · exact Coins.lens₁ a d hd (h₁ (by decide)) (h₃ (by decide))
  · obtain ⟨get, put, ok, e1, e2⟩ := Coins.lens₂ a d hd (h₁ (by decide)) (h₂ (by decide))
    exact ⟨get, put, ok, e1, fun ch hch => e2 ch (hch.elim id id)⟩

end

end ProofFile.Honest

#print axioms ProofFile.Honest.Cs.sub0
#print axioms ProofFile.Honest.Cs.cut_zero
#print axioms ProofFile.Honest.dueAt_cons
#print axioms ProofFile.Honest.Purse.find?_none
#print axioms ProofFile.Honest.Purse.lens
#print axioms ProofFile.Honest.Coins.look_pick
#print axioms ProofFile.Honest.lens_comp
#print axioms ProofFile.Honest.Coins.lens₀
#print axioms ProofFile.Honest.Coins.lens₁
#print axioms ProofFile.Honest.Coins.lens₂
#print axioms ProofFile.Honest.Coins.lens
