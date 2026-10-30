-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K2/Law/CarriedWithin.lean: the kind "the code switch" (K2): BESIDE
Honest/K2/Law/CarriedOfLend.lean: NO ENTRY OF A CARRIED STRETCH IS A DEFAULT: the frame's `Cs.cut`
answers nothing where the run asked for is not all there; so, wherever the lending returns, each
entry's start and count lie within its owner's count. And: the switch's part spends no run. Five
statements with their proofs; no definition.

  `cut_within`        where `Cs.cut` answers, start + count lies within the count, sort by sort
  `lent_within`       of the frame's `lend`: general
  `part_within`       of `lendPart`, at a part of any kind
  `handed_within`     at the switch's part: of what `handed` hands
  `switchPart_spends` the switch's part spends no run: by its text

Had already, not typed anew: WHICH ELEMENT IS WHICH: `Reads.cut_eAt` (Honest/K2/Law/Reads.lean),
`Reads.cut_fAt` (Honest/K2/Law/Room.lean): element number i of a cut from a on is element number a +
i of the run cut. By type (`Cs`, Honest/Frame.lean) there is no element beyond the count.

Near, not called: `cut_isSome` (Honest/K1/ScriptAtLaw.lean, of other authors): whether a cut FROM 0
ON answers, as a test on the counts: `cut_within` is the one direction at any start.

Limits. On counts: nothing on how a run's coins are drawn. That the lending returns is a premise.
That an entry's owner is the sender that the place's public data mean is not said here. Nothing on
any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.CarriedOfLend

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law

/-- Where `Cs.cut` answers, the run asked for is all there. -/
theorem cut_within {d : Due} (c : Cs d) (a n : Due) {y : Cs n} (h : c.cut a n = some y) :
    a.f + n.f ≤ d.f ∧ a.e + n.e ≤ d.e := by
  unfold Cs.cut at h
  by_cases g : a.f + n.f ≤ d.f ∧ a.e + n.e ≤ d.e
  · exact g
  · rw [dif_neg g] at h
    cases h

/-- **Of the frame's `lend`**: each entry's run lies within its owner's count. -/
theorem lent_within (look : Addr → (d : Due) × Cs d) :
    ∀ (ds : List (String × Due)) (l : List Ahead) (y : CsAll ds), lend look ds l = .ok y →
      ∀ (i : Nat) (e : Ahead), l[i]? = some e →
        e.start.f + e.count.f ≤ (look e.owner).1.f ∧ e.start.e + e.count.e ≤ (look e.owner).1.e
  | [], [], _, _, i, e, he => by simp at he
  | [], _ :: _, _, h, _, _, _ => by simp [lend] at h
  | _ :: _, [], _, h, _, _, _ => by simp [lend] at h
  | d :: ds, a :: l, y, h, i, e, he => by
    unfold lend at h
    by_cases h1 : (a.name != d.1) = true
    · rw [if_pos h1] at h
      cases h
    · rw [if_neg h1] at h
      by_cases h2 : (a.count != d.2) = true
      · rw [if_pos h2] at h
        cases h
      · rw [if_neg h2] at h
        have hcount : a.count = d.2 := by simpa using h2
        cases hc : (look a.owner).2.cut a.start d.2 with
        | none =>
          rw [hc] at h
          cases h
        | some x =>
          rw [hc] at h
          obtain ⟨y', hy', -⟩ := exMap_ok h
          cases i with
          | zero =>
            have ea : a = e := by simpa using he
            subst ea
            rw [hcount]
            exact cut_within _ _ _ hc
          | succ n =>
            exact lent_within look ds l y' hy' n e (by simpa using he)

variable {V W X : Type}

/-- **Of `lendPart`, at a part of any kind.** -/
theorem part_within (B : ProverCoinCounts) (rows : List (Addr × Due)) (look : Addr → (d : Due) × Cs d)
    (a : Addr) (p : Part V W X) (c : p.Coins) (h : lendPart B rows look a p = .ok c) (i : Nat)
    (e : Ahead)
    (he : ((B.ahead.filter fun x => x.spender == a).filter (!·.once))[i]? = some e) :
    e.start.f + e.count.f ≤ (look e.owner).1.f ∧ e.start.e + e.count.e ≤ (look e.owner).1.e := by
  unfold lendPart at h
  simp only at h
  by_cases h1 : (p.takes != dueAt rows a) = true
  · rw [if_pos h1] at h
    cases h
  · rw [if_neg h1] at h
    cases hc : (look a).2.cut ⟨0, 0⟩ p.takes with
    | none =>
      rw [hc] at h
      cases h
    | some own =>
      rw [hc] at h
      obtain ⟨sp, -, h'⟩ := exBind_ok h
      obtain ⟨ca, hca, -⟩ := exMap_ok h'
      exact lent_within look p.carries _ ca hca i e he

variable {Bk : ProverCoinCounts}

/-- **At the switch's part.** -/
theorem handed_within (ch : Nat) (p : SwitchPlace) (k : Coins Bk)
    (c : SwitchCoins p.sizes p.others p.foldVars p.carries) (h : handed ch p k = some c) (i : Nat)
    (e : Ahead)
    (he : ((Bk.ahead.filter fun x => x.spender == ⟨p.place, 0⟩).filter (!·.once))[i]? = some e) :
    e.start.f + e.count.f ≤ (k.look ch e.owner).1.f ∧
      e.start.e + e.count.e ≤ (k.look ch e.owner).1.e := by
  unfold handed at h
  cases hl : lendPart Bk (Bk.rowsOf ch) (k.look ch) ⟨p.place, 0⟩
      (switchPart (coreSender freshTable) p.sizes p.others p.foldVars p.carries) with
  | error _ =>
    rw [hl] at h
    cases h
  | ok c' => exact part_within Bk (Bk.rowsOf ch) (k.look ch) ⟨p.place, 0⟩ _ c' hl i e he

/-- **The switch's part spends no run.** -/
theorem switchPart_spends (Sd : Sender) (Z : VerifiableInference.Desc.K2.Honest.Sizes)
    (others : Array OnBytes.OracleNotice) (k : Nat) (carries : List (String × Due)) :
    (switchPart Sd Z others k carries).spends = [] := rfl

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.cut_within
#print axioms ProofFile.Honest.K2.Law.lent_within
#print axioms ProofFile.Honest.K2.Law.part_within
#print axioms ProofFile.Honest.K2.Law.handed_within
#print axioms ProofFile.Honest.K2.Law.switchPart_spends
