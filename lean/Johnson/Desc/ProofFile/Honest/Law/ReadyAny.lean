-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/ReadyAny.lean: whether `ready` (Honest/Frame.lean) returns depends
on no coin's value, and on the input only through the test on the range and through whether the
request has a trace. The book's lending cuts blocks out of coins by counts alone. So if `ready`
returns at one input and one run's coins, it returns at every input in range that has a trace, at
every run's coins (`ready_any`): one proof that `ready` returns, at one input and one run's coins,
is enough for "`ready` returns at every coin".

  1  `find_due`, `look_due`, `getD_due`, `or_due`, `cut_some`   a purse's counts; a cut goes by the
     counts
  2  `lend_any`, `lendPart_any`, `lendRow_any`, `chainSteps_any`   the lending; a chain's `Step`s
  3  `ready_any`   the main lemma

Limits.
  * What `ready` returns does depend on the coins.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.Run

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc

variable {S Cl V W Y Xi W₀ Rc Ky Tr X₀ X : Type}

/-! ## 1 Counts -/

theorem find_due : ∀ (l : List (Addr × Due)) (c c' : Purse l) (a : Addr),
    (Purse.find? l c a).map (·.1) = (Purse.find? l c' a).map (·.1)
  | [], _, _, _ => rfl
  | r :: l, c, c', a => by
    unfold Purse.find?
    by_cases h : (r.1 == a) = true
    · rw [if_pos h, if_pos h]
      rfl
    · rw [if_neg h, if_neg h]
      exact find_due l c.2 c'.2 a

theorem getD_due {o o' : Option ((d : Due) × Cs d)} (h : o.map (·.1) = o'.map (·.1))
    (no : (d : Due) × Cs d) : (o.getD no).1 = (o'.getD no).1 := by
  cases o <;> cases o' <;> simp_all

theorem or_due {a a' b b' : Option ((d : Due) × Cs d)} (h : a.map (·.1) = a'.map (·.1))
    (g : b.map (·.1) = b'.map (·.1)) : (a.or b).map (·.1) = (a'.or b').map (·.1) := by
  cases a <;> cases a' <;> simp_all

theorem look_due {B : ProverCoinCounts} (c c' : Coins B) (ch : Nat) (a : Addr) :
    (c.look ch a).1 = (c'.look ch a).1 := by
  unfold Coins.look sharedLook
  simp only
  split
  · exact getD_due (find_due _ _ _ a) _
  · split
    · exact getD_due (find_due _ _ _ a) _
    · exact getD_due (or_due (or_due (find_due _ _ _ a) (find_due _ _ _ a)) (find_due _ _ _ a)) _

theorem cut_some {x x' : (d : Due) × Cs d} (h : x.1 = x'.1) (a n : Due) {y : Cs n}
    (hy : x.2.cut a n = some y) : ∃ y', x'.2.cut a n = some y' := by
  obtain ⟨d, c⟩ := x
  obtain ⟨d', c'⟩ := x'
  have h' : d = d' := h
  subst h'
  unfold Cs.cut at hy ⊢
  by_cases g : a.f + n.f ≤ d.f ∧ a.e + n.e ≤ d.e
  · rw [dif_pos g]
    exact ⟨_, rfl⟩
  · rw [dif_neg g] at hy
    cases hy

/-! ## 2 The lending -/

section
variable {look look' : Addr → (d : Due) × Cs d} (hL : ∀ a, (look a).1 = (look' a).1)
include hL

theorem lend_any : ∀ (ds : List (String × Due)) (l : List Ahead) (y : CsAll ds),
    lend look ds l = .ok y → ∃ y', lend look' ds l = .ok y'
  | [], [], _, _ => ⟨(), rfl⟩
  | [], _ :: _, _, h => by simp [lend] at h
  | _ :: _, [], _, h => by simp [lend] at h
  | d :: ds, a :: l, y, h => by
    unfold lend at h ⊢
    by_cases h1 : (a.name != d.1) = true
    · rw [if_pos h1] at h
      cases h
    · rw [if_neg h1] at h ⊢
      by_cases h2 : (a.count != d.2) = true
      · rw [if_pos h2] at h
        cases h
      · rw [if_neg h2] at h ⊢
        cases hc : (look a.owner).2.cut a.start d.2 with
        | none =>
          rw [hc] at h
          cases h
        | some x =>
          rw [hc] at h
          obtain ⟨x', hx'⟩ := cut_some (hL a.owner) a.start d.2 hc
          obtain ⟨w, hw, -⟩ := exMap_ok h
          obtain ⟨w', hw'⟩ := lend_any ds l w hw
          rw [hx', hw']
          exact ⟨_, rfl⟩

theorem lendPart_any (B : ProverCoinCounts) (rows : List (Addr × Due)) (a : Addr) (p : Part V W Y)
    {y : p.Coins} (h : lendPart B rows look a p = .ok y) :
    ∃ y', lendPart B rows look' a p = .ok y' := by
  unfold lendPart at h ⊢
  simp only at h ⊢
  by_cases h1 : (p.takes != dueAt rows a) = true
  · rw [if_pos h1] at h
    cases h
  · rw [if_neg h1] at h ⊢
    cases hc : (look a).2.cut ⟨0, 0⟩ p.takes with
    | none =>
      rw [hc] at h
      cases h
    | some x =>
      rw [hc] at h
      obtain ⟨x', hx'⟩ := cut_some (hL a) ⟨0, 0⟩ p.takes hc
      obtain ⟨sp, hsp, h'⟩ := exBind_ok h
      obtain ⟨ca, hca, -⟩ := exMap_ok h'
      obtain ⟨sp', hsp'⟩ := lend_any hL _ _ sp hsp
      obtain ⟨ca', hca'⟩ := lend_any hL _ _ ca hca
      rw [hx']
      show ∃ y', ((lend look' p.spends _).bind fun sp =>
        (lend look' p.carries _).map fun ca => (x', sp, ca)) = .ok y'
      rw [hsp']
      show ∃ y', ((lend look' p.carries _).map fun ca => (x', sp', ca)) = .ok y'
      rw [hca']
      exact ⟨_, rfl⟩

theorem lendRow_any (B : ProverCoinCounts) (rows : List (Addr × Due)) (a : Place) :
    ∀ (ps : List (Part V W Y)) (j : Nat) (y : RowCoins ps),
    lendRow B rows look a ps j = .ok y → ∃ y', lendRow B rows look' a ps j = .ok y'
  | [], _, _, _ => ⟨(), rfl⟩
  | p :: ps, j, y, h => by
    unfold lendRow at h ⊢
    obtain ⟨c, hc, h'⟩ := exBind_ok h
    obtain ⟨r, hr, -⟩ := exMap_ok h'
    cases hp : lendPart B rows look ⟨a, j⟩ p with
    | error e =>
      rw [hp] at hc
      cases hc
    | ok c₀ =>
      obtain ⟨c', hc'⟩ := lendPart_any hL B rows ⟨a, j⟩ p hp
      obtain ⟨r', hr'⟩ := lendRow_any B rows a ps (j + 1) r hr
      rw [hc']
      show ∃ y', ((lendRow B rows look' a ps (j + 1)).map fun r => (c', r)) = .ok y'
      rw [hr']
      exact ⟨_, rfl⟩

theorem chainSteps_any (B : ProverCoinCounts) (rows : List (Addr × Due)) (v v' : Option V)
    (hs : List (Placed V W Y)) : ∀ (bs : List (Block S Cl)) (l : List (Step W Y)),
    chainSteps B rows look v bs hs = .ok l → ∃ l', chainSteps B rows look' v' bs hs = .ok l'
  | [], _, _ => ⟨[], rfl⟩
  | b :: bs, l, h => by
    unfold chainSteps at h ⊢
    by_cases h0 : (b.oracles.length != b.rounds.length) = true
    · rw [if_pos h0] at h
      cases h
    · rw [if_neg h0] at h ⊢
      cases hf : hs.find? fun g => g.place == b.place with
      | none =>
        rw [hf] at h
        obtain ⟨w, hw, -⟩ := exMap_ok h
        obtain ⟨w', hw'⟩ := chainSteps_any B rows v v' hs bs w hw
        show ∃ l', ((chainSteps B rows look' v' bs hs).map _) = .ok l'
        rw [hw']
        exact ⟨_, rfl⟩
      | some g =>
        rw [hf] at h
        simp only at h ⊢
        by_cases h1 : (g.rounds != b.rounds.length) = true
        · rw [if_pos h1] at h
          cases h
        · rw [if_neg h1] at h ⊢
          by_cases h2 : (B.cuts.lookup b.place != some (g.parts.map (·.moves.length))) = true
          · rw [if_pos h2] at h
            cases h
          · rw [if_neg h2] at h ⊢
            by_cases h3 : (rows.any fun r =>
                r.1.place == b.place && decide (g.parts.length ≤ r.1.part)) = true
            · rw [if_pos h3] at h
              cases h
            · rw [if_neg h3] at h ⊢
              by_cases h4 : (B.ahead.any fun e =>
                  e.spender.place == b.place && decide (g.parts.length ≤ e.spender.part)) = true
              · rw [if_pos h4] at h
                cases h
              · rw [if_neg h4] at h ⊢
                obtain ⟨c, hc, h'⟩ := exBind_ok h
                obtain ⟨w, hw, -⟩ := exMap_ok h'
                cases hr : lendRow B rows look b.place g.parts 0 with
                | error e =>
                  rw [hr] at hc
                  cases hc
                | ok c₀ =>
                  obtain ⟨c', hc'⟩ := lendRow_any hL B rows b.place g.parts 0 c₀ hr
                  obtain ⟨w', hw'⟩ := chainSteps_any B rows v v' hs bs w hw
                  rw [hc']
                  show ∃ l', ((chainSteps B rows look' v' bs hs).map fun l =>
                    g.steps b v' c' ++ l) = .ok l'
                  rw [hw']
                  exact ⟨_, rfl⟩

end

/-! ## 3 The main lemma -/

/-- **If `ready` returns at one input and one run's coins, it returns at every input in range that
has a trace, at every run's coins.** -/
theorem ready_any {F : FileDescription Xi} {B : ProverCoinCounts} {H : Prover W₀ Rc Xi Ky Tr X₀ X} {w₀ w₀' : W₀}
    {rc rc' : Rc} {x x' : Xi} {c : Coins B} {R : Ready W₀ Rc Xi Ky Tr X₀ X}
    (h : ready F B H w₀ rc x c = .ok R) (hr : H.inRange w₀' = true)
    (ht : (H.trace w₀' x').isSome = true) (c' : Coins B) :
    ∃ R', ready F B H w₀' rc' x' c' = .ok R' := by
  obtain ⟨hT, tr, -, hown, hcom, s1, s2, s3⟩ := ready_ok h
  obtain ⟨tr', htr'⟩ := Option.isSome_iff_exists.1 ht
  have hT' : readyTests F B H w₀' = .ok () := by
    unfold readyTests at hT ⊢
    split at hT
    · cases hT
    · rename_i g1
      rw [if_neg g1]
      split at hT
      · cases hT
      · rename_i g2
        rw [if_neg g2]
        split at hT
        · cases hT
        · rename_i g3
          rw [if_neg g3]
          split at hT
          · cases hT
          · rename_i g4
            rw [if_neg g4]
            split at hT
            · cases hT
            · rw [if_neg (by rw [hr]; simp)]
              exact hT
  obtain ⟨l1, e1⟩ := chainSteps_any (look_due c c' 0) B (B.rowsOf 0) _
    (Face.own.sees (⟨w₀', rc', x', tr'⟩ : Local W₀ Rc Xi Tr)) H.first _ _ s1
  obtain ⟨l2, e2⟩ := chainSteps_any (look_due c c' 1) B (B.rowsOf 1) _
    (Face.shared.sees (⟨w₀', rc', H.key x'⟩ : Common W₀ Rc Ky)) H.shared _ _ s2
  obtain ⟨l3, e3⟩ := chainSteps_any (look_due c c' 2) B (B.rowsOf 2) _
    (Face.own.sees (⟨w₀', rc', x', tr'⟩ : Local W₀ Rc Xi Tr)) H.second _ _ s3
  have e2' : sharedSteps F B H ⟨w₀', rc', H.key x'⟩ c'.shared = .ok l2 := by
    unfold sharedSteps
    have g : chainSteps B (B.rowsOf 1) (sharedLook B c'.shared)
        (Face.shared.sees (⟨w₀', rc', H.key x'⟩ : Common W₀ Rc Ky)) F.shared.blocksInOrder H.shared =
        .ok l2 := e2
    rw [g]
    rfl
  refine ⟨⟨⟨w₀', rc', x', tr'⟩, ⟨w₀', rc', H.key x'⟩, l1, l2, l3⟩, ?_⟩
  unfold ready
  rw [hT', htr']
  show ((unfit (chainSteps B (B.rowsOf 0) (c'.look 0)
    (Face.own.sees (⟨w₀', rc', x', tr'⟩ : Local W₀ Rc Xi Tr)) F.first.blocksInOrder H.first)).bind
    fun m₁ => (sharedSteps F B H ⟨w₀', rc', H.key x'⟩ c'.shared).bind fun m₂ =>
      (unfit (chainSteps B (B.rowsOf 2) (c'.look 2)
        (Face.own.sees (⟨w₀', rc', x', tr'⟩ : Local W₀ Rc Xi Tr)) F.second.blocksInOrder H.second)).map
        fun m₃ => (⟨⟨w₀', rc', x', tr'⟩, ⟨w₀', rc', H.key x'⟩, m₁, m₂, m₃⟩ :
          Ready W₀ Rc Xi Ky Tr X₀ X)) = _
  rw [e1, e2', e3]
  rfl

end ProofFile.Honest

#print axioms ProofFile.Honest.find_due
#print axioms ProofFile.Honest.getD_due
#print axioms ProofFile.Honest.or_due
#print axioms ProofFile.Honest.look_due
#print axioms ProofFile.Honest.cut_some
#print axioms ProofFile.Honest.lend_any
#print axioms ProofFile.Honest.lendPart_any
#print axioms ProofFile.Honest.lendRow_any
#print axioms ProofFile.Honest.chainSteps_any
#print axioms ProofFile.Honest.ready_any
