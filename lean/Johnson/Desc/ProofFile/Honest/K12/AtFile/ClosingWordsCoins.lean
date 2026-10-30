-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/ClosingWordsCoins.lean: the coins that the switch's part is
handed, and those that the closing test's second part is handed, are the same where the book's
entries name the same owner, start and count. General in the run's coins.

  lend_of_lendPart_words   where a part is lent its coins, the carried entries are lent
  own_of_lendPart_words    and its own cut is the one at 0
  carried_of_lend    a carried stretch, as part 1's text reads it, is the cut of its entry
  carried_tie        the stretches that the job hands the closing are those the part reads
  cut_cut_zero, own_tie   the first message's cut of the part's own coins is the owner's cut

By what. lend_stretch, stretch_tie (K12/AgreeBook.lean), asK2_stretchOf (AtProof/JobL.lean).

Limits. The book's entries are premises here. They are public, and no test on this pair of parts is
written yet.
Nothing on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K12.AgreeBook
import Johnson.Desc.ProofFile.Honest.K12.AtProof.JobL
import Johnson.Desc.ProofFile.Honest.K2.Law.Reads
import Johnson.Desc.ProofFile.Honest.Law.Play

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.AtProof

section
variable {V W X : Type}

theorem lend_of_lendPart_words {B : ProverCoinCounts} {rows : List (Addr × Due)} {look : Addr → (d : Due) × Cs d}
    {a : Addr} {p : Part V W X} {c : p.Coins} (h : lendPart B rows look a p = .ok c) :
    lend look p.carries (ProofFile.Honest.carryE B a) = .ok c.2.2 := by
  unfold lendPart at h
  split at h
  · cases h
  split at h
  · cases h
  obtain ⟨sp, hsp, h2⟩ := ProofFile.Honest.K2.Reads.bind_ok' h
  obtain ⟨ca, hca, rfl⟩ := ProofFile.Honest.K2.Reads.map_ok h2
  exact hca

theorem own_of_lendPart_words {B : ProverCoinCounts} {rows : List (Addr × Due)} {look : Addr → (d : Due) × Cs d}
    {a : Addr} {p : Part V W X} {c : p.Coins} (h : lendPart B rows look a p = .ok c) :
    (look a).2.cut ⟨0, 0⟩ p.takes = some c.1 := by
  unfold lendPart at h
  split at h
  · cases h
  split at h
  · cases h
  rename_i own hown
  obtain ⟨sp, hsp, h2⟩ := ProofFile.Honest.K2.Reads.bind_ok' h
  obtain ⟨ca, hca, rfl⟩ := ProofFile.Honest.K2.Reads.map_ok h2
  exact hown

end

/-- **A carried stretch, as part 1's text reads it, is the cut of its entry.** -/
theorem carried_of_lend (look : Addr → (d : Due) × Cs d) : ∀ (ds : List (String × Due))
    (l : List Ahead) (y : CsAll ds), lend look ds l = .ok y → ∀ (n : ℕ) (a : Ahead),
    l[n]? = some a →
      ∃ x : Cs a.count, (look a.owner).2.cut a.start a.count = some x ∧
        K2.Stretch.carried ds y n = .ok (K2.Stretch.of x)
  | [], [], _, _, n, a, hn => by simp at hn
  | [], _ :: _, _, h, _, _, _ => by cases h
  | _ :: _, [], _, h, _, _, _ => by cases h
  | d :: ds, e :: l, y, h, n, a, hn => by
    simp only [lend] at h
    split at h
    · cases h
    split at h
    · cases h
    rename_i hcount
    split at h
    · cases h
    rename_i x hx
    obtain ⟨y', hy, rfl⟩ := exMap_ok h
    cases n with
    | zero =>
      obtain rfl : e = a := Option.some.inj hn
      have hc : e.count = d.2 := by simpa using hcount
      obtain ⟨dn, dd⟩ := d
      obtain ⟨en, eo, es, ec, ep, eb⟩ := e
      obtain rfl : ec = dd := hc
      exact ⟨x, hx, rfl⟩
    | succ m => exact carried_of_lend look ds l y' hy m a hn

/-- Beyond the list part 1's reader refuses. -/
theorem carried_beyond_words : ∀ (ds : List (String × Due)) (y : CsAll ds) (n : ℕ), ds.length ≤ n →
    K2.Stretch.carried ds y n = .error "a stretch is asked beyond the list"
  | [], _, _, _ => by
    unfold K2.Stretch.carried
    rfl
  | _ :: ds, y, 0, h => by simp at h
  | _ :: ds, y, n + 1, h => by
    exact carried_beyond_words ds y.2 n (by simpa using h)

/-- **The stretches that the job hands the closing are those that the part reads.** -/
theorem carried_tie (look : Addr → (d : Due) × Cs d) (p : K2.SwitchPlace)
    {l₁ l₂ : List Ahead} {ds₂ : List (String × Due)} {y₁ : CsAll p.carries} {y₂ : CsAll ds₂}
    (h₁ : lend look p.carries l₁ = .ok y₁) (h₂ : lend look ds₂ l₂ = .ok y₂)
    (hlen : p.front.length ≤ l₁.length)
    (hsame : ∀ n a, n < p.front.length → l₁[n]? = some a → ∃ a', l₂[n]? = some a' ∧
      a'.owner = a.owner ∧ a'.start = a.start ∧ a'.count = a.count) :
    (fun n => match p.front[n]? with
      | some x => Except.ok (asK2 x.2.2 (stretches ds₂ y₂ n))
      | none => Except.error "a stretch is asked beyond the list") =
      K2.Stretch.carried p.carries y₁ := by
  funext n
  cases hn : p.front[n]? with
  | none =>
    have hge : p.front.length ≤ n := by simpa using hn
    rw [carried_beyond_words _ _ _ (by simpa [K2.SwitchPlace.carries] using hge)]
  | some x =>
    have hlt : n < p.front.length := (List.getElem?_eq_some_iff.1 hn).1
    obtain ⟨a, ha⟩ : ∃ a, l₁[n]? = some a :=
      ⟨l₁[n]'(by omega), List.getElem?_eq_getElem (by omega)⟩
    obtain ⟨a', ha', eo, es, ec⟩ := hsame n a hlt ha
    obtain ⟨hd, x₁, hx₁, e₁⟩ := ProofFile.Honest.K12.lend_stretch look _ _ _ h₁ n a ha
    obtain ⟨x₁', hx₁', e₁'⟩ := carried_of_lend look _ _ _ h₁ n a ha
    obtain ⟨-, x₂, hx₂, e₂⟩ := ProofFile.Honest.K12.lend_stretch look _ _ _ h₂ n a' ha'
    obtain rfl : x₁ = x₁' := Option.some.inj (hx₁.symm.trans hx₁')
    have hc : x.2.2 = a.count := by
      have e : (p.carries[n]?).map (·.2) = some x.2.2 := by
        simp [K2.SwitchPlace.carries, hn]
      rw [e] at hd
      exact Option.some.inj hd
    have hs := ProofFile.Honest.K12.stretch_tie look a' a x₂ x₁ hx₂ hx₁ eo es ec
    show Except.ok (asK2 x.2.2 (stretches ds₂ y₂ n)) = _
    rw [e₁', e₂, hs, hc, asK2_stretchOf]

/-- A cut at 0 of a cut at 0 is a cut at 0. -/
theorem cut_cut_zero {d t n : Due} {L : Cs d} {c₁ : Cs t} {c' x : Cs n}
    (h1 : L.cut ⟨0, 0⟩ t = some c₁) (h2 : c₁.cut ⟨0, 0⟩ n = some c') (h3 : L.cut ⟨0, 0⟩ n = some x) :
    c' = x := by
  unfold Cs.cut at h1 h2 h3
  split at h1
  · split at h2
    · split at h3
      · cases h1
        cases h2
        cases h3
        congr 1 <;> funext i <;> simp only [Nat.zero_add]
      · cases h3
    · cases h2
  · cases h1

end ProofFile.Honest.K12.AtProof

#print axioms ProofFile.Honest.K12.AtProof.carried_tie
#print axioms ProofFile.Honest.K12.AtProof.cut_cut_zero
