-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Params/GroupPrices.lean: the proof library's bound on a list against the planner's list
sizes in a group under the rule `johnson`; and that the prices of a fold's rounds and of a last
step's first round cover the library's numbers.

The first part carries OnBytes/Params/TableJohnson.lean's law on the list size from a code at its
own m to a code that is read at a given agreement. `surelyLt` is sound over the real numbers
(`surelyLtR_sound`). The planner's list formula at any agreement that encloses a, where a is at
least the agreement that belongs to some m > 0 as printed, and a radius e that is at most (1 - a) n:
n (n - e - k) < (list + 1) ((n - e) ^ 2 - k n) (`list_whole_at`); from such an inequality the
library's `Cb.listMax n (n - k) e` is at most the list size (`listMax_le_of_whole`). `atDistance`
takes that formula unless twice the distance times n is surely below n - k, where it takes 1
(`listPair`, `atDistance_list_eq`); for a radius of at least half of the distance, n - k ≤ 2 e, it
takes the formula, so the library's bound is at most its list size (`listMax_le_atDistance`). So for
both codes of a group under the rule `johnson` (`listMax_le_main`, `listMax_le_mask`); and where the
main code gives the distance, the group's list size is the larger of the two (`analysisOfM_list`).
The second part is on prices. At every analysis: the price of round j of a fold covers (BM + L 2 +
twice BK, while mask rows are folded) / q, and that of the first round of a test's last step (BM + L
+ BK) / q, for numbers BM and BK that are at most what the two counts enclose and L at most the
group's list size (`fold_covers`, `base_covers`). `JohnsonGroup s g e` gathers fourteen conditions
on a group with mask rows and a radius e. Under them the planner's analysis is `analysisOfM`
(`JohnsonGroup.analysis_eq`), the library's bound on the main code's list is at most the group's
list size (`listMax_le_group`), the repeated mask code's k is at most the main code's, and so the
main code's distance is the smaller of the two (`analysisOfM_noFault`, `JohnsonGroup.maskK_le`,
`JohnsonGroup.min_distance`); BM can be the library's `Cb.bchksBound` at the main code, L its
`Cb.listMax` at the main code, and BK its `Cb.bchksBound` at the repeated mask code and its
`Cb.listMax` at that code more (`fold_covers_johnson`, `base_covers_johnson`); and the like in whole
numbers, with the two counts rounded down (`bchksBound_nonneg`, `fold_covers_floor`,
`base_covers_floor`). The conditions follow from a yes of a test in the planner's own arithmetic
(`johnsonGroupTest`, `johnsonGroup_of_test`); OnBytes/Params/GroupPricesRecord.lean evaluates it at
five groups.

Main definitions: `listPair`, `JohnsonGroup`, `johnsonGroupTest`.
Main theorems: `surelyLtR_sound`, `list_whole_at`, `listMax_le_of_whole`, `atDistance_list_eq`,
`listMax_le_atDistance`, `listMax_le_main`, `listMax_le_mask`, `analysisOfM_list`, `fold_covers`,
`base_covers`, `JohnsonGroup.analysis_eq`, `listMax_le_group`, `analysisOfM_noFault`,
`JohnsonGroup.maskK_le`, `JohnsonGroup.min_distance`, `fold_covers_johnson`, `base_covers_johnson`,
`bchksBound_nonneg`, `fold_covers_floor`, `base_covers_floor`, `johnsonGroup_of_test`.
What is not claimed: that the numbers on the left bound a prover's chance in these rounds. Their
form (one count for the main rows, two for the mask rows in a fold's round and one in the last
step's, the list twice or once, no factor for the rows) is meant to be that of the library's lemmas
on the two blocks; no such lemma is imported or compared here. OnBytes/Slice/PricedRound.lean makes
the comparison (`fold_share`, `fold_share_mask`, `lambda_share`): at the format's field, for a stage
whose distance is that of its main rows, the counts of these rounds in a chain of stages are at most
`foldCount` and `lastStepCount` (OnBytes/Params/EntryCovered.lean: the numbers on the left of
`fold_covers_floor` and `base_covers_floor`) times the number of the round's typed values.
`Cb.bchksBound` is a real number. The laws cover it, and so every number that is at most it, such as
its floor. They do not cover a whole number above it. `fold_covers` and `base_covers` cover such a
number if it is at most what the planner's count encloses; no law here says that it is. What the
heads of OnBytes/Params/LibraryJohnson.lean and OnBytes/Params/ClosePrices.lean do not claim, above
all on the mask code's repetition. A group in which the mask code gives the distance:
`listMax_le_main` and `listMax_le_mask` speak of it, the laws on prices do not, because its list
size is taken from a reading of the mask code that the analysis then replaces. A group without mask
rows. A radius below half of a code's distance: there `atDistance` can have the list size 1. That a
price is not marked bad is a hypothesis. That a round of a plan under the name FOLD round has the
price `foldRoundError` at its j; the factor of the setting's instances in the scope of a request;
the distance from uniform of a round's draws, which the planner adds before it compares. Nothing on
rounds that draw positions, batch rows or sample a message (OnBytes/Params/MorePrices.lean), on the
test on a table or on a link's rounds (OnBytes/Params/LinkPrices.lean). For proofs only; the
program, that is the Lean port built from OnBytes/, does not import this file.

-/
import OnBytes.Params.ClosePrices

set_option autoImplicit false

namespace OnBytes.Params
open Binary Bound

/-- If `surelyLt` says yes of two bounds that enclose x and y, then x < y; over the real numbers. -/
theorem surelyLtR_sound {A B : Bound} {x y : ℝ} (hA : EnclR A x) (hB : EnclR B y)
    (h : surelyLt A B = true) : x < y := by
  unfold surelyLt at h
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨g1, g2⟩, g3⟩ := h
  have h3 : ((A.hi.val : ℚ) : ℝ) < ((B.lo.val : ℚ) : ℝ) := by exact_mod_cast lt_sound _ _ g3
  exact ((hA g1).2.trans_lt h3).trans_le (hB g2).1

/-- **The planner's list size at any agreement against a radius in whole positions.** agree encloses
a, which is at least the agreement that belongs to some m > 0 as printed; e is at most (1 - a) n. -/
theorem list_whole_at {c : Word} {agree : Bound} {a : ℝ} {m e : ℕ} (ha : EnclR agree a)
    (h : (johnsonList agree (rhoOf c)).2 = false) (hm : 0 < m) (hk : 0 < c.k) (hkn : c.k < c.n)
    (ham : c.agreeAt m true ≤ a) (he : (e : ℝ) ≤ (1 - a) * (c.n : ℝ)) :
    (c.n : ℝ) * (((c.n : ℝ) - (e : ℝ)) - (c.k : ℝ)) <
      (((johnsonList agree (rhoOf c)).1 : ℝ) + 1) *
        (((c.n : ℝ) - (e : ℝ)) * ((c.n : ℝ) - (e : ℝ)) - (c.k : ℝ) * (c.n : ℝ)) := by
  have hn : (0 : ℝ) < (c.n : ℝ) := by
    have : 0 < c.n := by omega
    exact_mod_cast this
  have hk' : (0 : ℝ) < (c.k : ℝ) := by exact_mod_cast hk
  have hkn' : (c.k : ℝ) < (c.n : ℝ) := by exact_mod_cast hkn
  have hm' : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hr0 : 0 < c.rho := by unfold Word.rho; positivity
  have hr1 : c.rho ≤ 1 := by
    unfold Word.rho
    rw [div_le_one hn]
    exact hkn'.le
  set s := Real.sqrt c.rho with hs
  have hs0 : 0 < s := Real.sqrt_pos.mpr hr0
  have hss : s * s = c.rho := Real.mul_self_sqrt hr0.le
  have hag : c.agreeAt m true = s + s / (m : ℝ) := by
    unfold Word.agreeAt
    simp [hs]
  have hsm : 0 < s / (m : ℝ) := by positivity
  have has : s < a := by linarith
  have ha0 : 0 ≤ a := by linarith
  have haa : c.rho < a * a := by
    rw [← hss]
    exact mul_self_lt_mul_self hs0.le has
  set t := (c.n : ℝ) - (e : ℝ) with ht
  have hta : a * (c.n : ℝ) ≤ t := by rw [ht]; linarith
  have hx : a ≤ t / (c.n : ℝ) := by rw [le_div_iff₀ hn]; exact hta
  have hc := counting_anti hr0.le hr1 ha0 haa hx
  have hl := johnsonList_lt ha (enclR_rhoOf c) h
  have hlt := lt_of_le_of_lt hc hl
  have hxx : a * a ≤ t / (c.n : ℝ) * (t / (c.n : ℝ)) := mul_self_le_mul_self ha0 hx
  have hd : 0 < t / (c.n : ℝ) * (t / (c.n : ℝ)) - c.rho := by linarith
  rw [div_lt_iff₀ hd] at hlt
  have e1 : t / (c.n : ℝ) - c.rho = (t - (c.k : ℝ)) / (c.n : ℝ) := by
    unfold Word.rho
    field_simp
  have e2 : t / (c.n : ℝ) * (t / (c.n : ℝ)) - c.rho =
      (t * t - (c.k : ℝ) * (c.n : ℝ)) / ((c.n : ℝ) * (c.n : ℝ)) := by
    unfold Word.rho
    field_simp
  rw [e1, e2] at hlt
  have hnn : 0 < (c.n : ℝ) * (c.n : ℝ) := by positivity
  have h5 := mul_lt_mul_of_pos_right hlt hnn
  have l1 : (t - (c.k : ℝ)) / (c.n : ℝ) * ((c.n : ℝ) * (c.n : ℝ)) =
      (c.n : ℝ) * (t - (c.k : ℝ)) := by
    field_simp
  have l2 : (((johnsonList agree (rhoOf c)).1 : ℝ) + 1) *
      ((t * t - (c.k : ℝ) * (c.n : ℝ)) / ((c.n : ℝ) * (c.n : ℝ))) * ((c.n : ℝ) * (c.n : ℝ)) =
      (((johnsonList agree (rhoOf c)).1 : ℝ) + 1) * (t * t - (c.k : ℝ) * (c.n : ℝ)) := by
    field_simp
  rw [l1, l2] at h5
  exact h5

/-- From that inequality over the real numbers to the library's bound on the list. -/
theorem listMax_le_of_whole {n k e L : ℕ} (hkn : k < n) (hen : e ≤ n)
    (hJ : n * k < (n - e) * (n - e))
    (hw : (n : ℝ) * (((n : ℝ) - (e : ℝ)) - (k : ℝ)) <
      ((L : ℝ) + 1) * (((n : ℝ) - (e : ℝ)) * ((n : ℝ) - (e : ℝ)) - (k : ℝ) * (n : ℝ))) :
    Cb.listMax n (n - k) e ≤ L := by
  unfold Cb.listMax
  have e1 : n - (n - k) = k := by omega
  rw [e1, sq]
  have hpos : 0 < (n - e) * (n - e) - n * k := by omega
  rw [← Nat.lt_succ_iff, Nat.div_lt_iff_lt_mul hpos]
  by_cases hle : n - k ≤ e
  · have z : n - k - e = 0 := by omega
    rw [z, Nat.mul_zero]
    positivity
  · have hlt : e < n - k := by omega
    have c1 : ((n - k - e : ℕ) : ℝ) = (n : ℝ) - (e : ℝ) - (k : ℝ) := by
      rw [Nat.cast_sub hlt.le, Nat.cast_sub hkn.le]
      ring
    have c2 : (((n - e) * (n - e) - n * k : ℕ) : ℝ) =
        ((n : ℝ) - (e : ℝ)) * ((n : ℝ) - (e : ℝ)) - (k : ℝ) * (n : ℝ) := by
      rw [Nat.cast_sub hJ.le]
      push_cast [Nat.cast_sub hen]
      ring
    have goalR : ((n * (n - k - e) : ℕ) : ℝ) <
        ((L.succ * ((n - e) * (n - e) - n * k) : ℕ) : ℝ) := by
      rw [Nat.cast_mul, Nat.cast_mul, c1, c2, Nat.cast_succ]
      exact hw
    exact_mod_cast goalR

/-- The pair of list size and mark that `atDistance` takes where it gives the source `.johnson` and
has found an m. -/
def listPair (c : Word) (agree : Bound) : ℕ × Bool :=
  if (!surelyLt (Bound.ofWord 2 * (Bound.ofWord 1 - agree) * Bound.ofNat c.n)
      (Bound.ofNat (c.n - c.k))) = true then johnsonList agree (rhoOf c) else (1, false)

/-- Where `atDistance` gives the source `.johnson` and a count that is not marked bad: its list size
is that pair's, the pair's mark is good, and k < n. -/
theorem atDistance_list_eq {s : Setting} {c : Word} {agree : Bound}
    (hs : (atDistance s c agree).source = .johnson)
    (hg : (atDistance s c agree).count.bad = false) :
    (atDistance s c agree).list = (listPair c agree).1 ∧ (listPair c agree).2 = false ∧
      c.k < c.n := by
  unfold listPair
  unfold atDistance at hs hg ⊢
  dsimp only at hs hg ⊢
  by_cases h1 : (agree.bad || decide (c.n ≤ c.k)) = true
  · rw [if_pos h1] at hg
    cases hg
  · rw [if_neg h1] at hs hg ⊢
    have hkn : c.k < c.n := by
      simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, not_le] at h1
      exact h1.2
    by_cases h2 : (Bound.ofWord 1 - agree).bad = true
    · rw [if_pos h2] at hg
      cases hg
    · rw [if_neg h2] at hs hg ⊢
      by_cases h3 : 3 * ((Bound.ofWord 1 - agree) * Bound.ofNat c.n).hi.floor < c.n - c.k
      · rw [if_pos h3] at hs
        cases hs
      · rw [if_neg h3] at hs hg ⊢
        · by_cases h5 : ((Bound.sqrt (rhoOf c) / (if s.printed = true
              then agree - Bound.sqrt (rhoOf c)
              else Bound.ofWord 2 * (agree - Bound.sqrt (rhoOf c)))).bad ||
              decide (2 ^ 64 ≤ (Bound.sqrt (rhoOf c) / (if s.printed = true
                then agree - Bound.sqrt (rhoOf c)
                else Bound.ofWord 2 * (agree - Bound.sqrt (rhoOf c)))).hi.ceil)) = true
          · rw [if_pos h5] at hg
            cases hg
          · rw [if_neg h5] at hs hg ⊢
            dsimp only at hg ⊢
            refine ⟨rfl, ?_, hkn⟩
            split at hg
            · rename_i h7
              rw [if_pos h7]
              split at hg
              · cases hg
              · rename_i h6
                simpa using h6
            · rename_i h7
              rw [if_neg h7]

/-- **The library's bound on the list is at most the list size of a code that is read at a given
agreement, beyond half of the distance**: where the source is `.johnson`, the count is not marked
bad, m is as printed and k > 0; a is what the agreement encloses, e is at most (1 - a) n, and
n - k ≤ 2 e. -/
theorem listMax_le_atDistance {s : Setting} {c : Word} {agree : Bound} {a : ℝ} {e : ℕ}
    (ha : EnclR agree a) (hs : (atDistance s c agree).source = .johnson)
    (hg : (atDistance s c agree).count.bad = false) (hp : s.printed = true) (hk : 0 < c.k)
    (he : (e : ℝ) ≤ (1 - a) * (c.n : ℝ)) (h2 : c.n - c.k ≤ 2 * e) :
    Cb.listMax c.n (c.n - c.k) e ≤ (atDistance s c agree).list := by
  obtain ⟨l1, l2, hkn⟩ := atDistance_list_eq hs hg
  obtain ⟨_, _, h3, h4⟩ := atDistance_johnson ha hs hg
  obtain ⟨hen, hsl⟩ := atDistance_slack ha hs hg hp he
  have hn0 : 0 < c.n := by omega
  have hJ := inJohnson_of_slack (Nat.mul_pos hk hn0) hsl
  have hnot : surelyLt (Bound.ofWord 2 * (Bound.ofWord 1 - agree) * Bound.ofNat c.n)
      (Bound.ofNat (c.n - c.k)) = false := by
    by_contra hc
    have hc' : surelyLt (Bound.ofWord 2 * (Bound.ofWord 1 - agree) * Bound.ofNat c.n)
        (Bound.ofNat (c.n - c.k)) = true := by simpa using hc
    have hd : EnclR (Bound.ofWord 1 - agree) (((1 : ℕ) : ℝ) - a) := enclR_sub (enclR_ofWord 1) ha
    have hlt := surelyLtR_sound
      (enclR_mul (enclR_mul (enclR_ofWord 2) hd) (enclR_ofNat c.n)) (enclR_ofNat (c.n - c.k)) hc'
    have h2' : ((c.n - c.k : ℕ) : ℝ) ≤ 2 * (e : ℝ) := by exact_mod_cast h2
    push_cast at hlt
    linarith
  have hpair : listPair c agree = johnsonList agree (rhoOf c) := by
    unfold listPair
    rw [hnot]
    rfl
  rw [l1, hpair]
  rw [hpair] at l2
  exact listMax_le_of_whole hkn hen hJ
    (list_whole_at ha l2 (by omega : 0 < (atDistance s c agree).m) hk hkn (h4 hp) he)

/-- **The main code's list size in a group's analysis under the rule `johnson`**, at least half of
its distance. -/
theorem listMax_le_main {s : Setting} {g : GroupSize} {e : ℕ}
    (hs : (analysisOfM s g).mainAt.source = .johnson)
    (hg : (analysisOfM s g).mainAt.count.bad = false) (hp : s.printed = true)
    (hk : 0 < (wordOf g.main).k)
    (he : (e : ℝ) ≤ (1 - groupAgree s g) * ((wordOf g.main).n : ℝ))
    (h2 : (wordOf g.main).n - (wordOf g.main).k ≤ 2 * e) :
    Cb.listMax (wordOf g.main).n ((wordOf g.main).n - (wordOf g.main).k) e ≤
      (analysisOfM s g).mainAt.list := by
  unfold groupAgree rulingWord at he
  by_cases hm : maskRules g = true
  · rw [if_pos hm] at he
    have hA : (analysisOfM s g).mainAt =
        (analysisAt s g (atDistance s (wordOf g.main)
          (johnson (repeated g.mask g.main.logN) g.m s.printed).agree)).mainAt := by
      unfold analysisOfM
      simp only [hm, Bool.not_true, Bool.false_eq_true, if_false]
    rw [hA] at hs hg ⊢
    obtain ⟨e1, hg'⟩ := analysisAt_mainAt hg
    rw [e1] at hs ⊢
    exact listMax_le_atDistance (enclR_johnson_agree _ _ _) hs hg' hp hk he h2
  · rw [if_neg hm] at he
    have hm' : maskRules g = false := by simpa using hm
    have hA : (analysisOfM s g).mainAt =
        (analysisAt s g (johnson (wordOf g.main) g.m s.printed)).mainAt := by
      unfold analysisOfM
      simp only [hm', Bool.not_false, if_true]
    rw [hA] at hs hg ⊢
    obtain ⟨e1, hg'⟩ := analysisAt_mainAt hg
    rw [e1]
    rw [hp] at he hg' ⊢
    exact listMax_le_list hg' hk he

/-- **The like for the mask code**, as its repetition to the main code's length. -/
theorem listMax_le_mask {s : Setting} {g : GroupSize} {e : ℕ} (hh : g.hasMask = true)
    (hs : (analysisOfM s g).maskAt.source = .johnson)
    (hg : (analysisOfM s g).maskAt.count.bad = false) (hp : s.printed = true)
    (hk : 0 < (repeated g.mask g.main.logN).k)
    (he : (e : ℝ) ≤ (1 - groupAgree s g) * ((repeated g.mask g.main.logN).n : ℝ))
    (h2 : (repeated g.mask g.main.logN).n - (repeated g.mask g.main.logN).k ≤ 2 * e) :
    Cb.listMax (repeated g.mask g.main.logN).n
        ((repeated g.mask g.main.logN).n - (repeated g.mask g.main.logN).k) e ≤
      (analysisOfM s g).maskAt.list := by
  unfold groupAgree rulingWord at he
  by_cases hm : maskRules g = true
  · rw [if_pos hm] at he
    have hA : (analysisOfM s g).maskAt =
        { johnson (repeated g.mask g.main.logN) g.m s.printed with
          count := (johnson (repeated g.mask g.main.logN) g.m s.printed).count +
            Bound.ofNat (johnson (repeated g.mask g.main.logN) g.m s.printed).list } := by
      unfold analysisOfM
      simp only [hm, Bool.not_true, Bool.false_eq_true, if_false]
    rw [hA] at hg ⊢
    dsimp only at hg ⊢
    obtain ⟨g1, _⟩ := add_good hg
    rw [hp] at he g1 ⊢
    exact listMax_le_list g1 hk he
  · rw [if_neg hm] at he
    have hm' : maskRules g = false := by simpa using hm
    have hA : (analysisOfM s g).maskAt =
        (analysisAt s g (johnson (wordOf g.main) g.m s.printed)).maskAt := by
      unfold analysisOfM
      simp only [hm', Bool.not_false, if_true]
    rw [hA] at hs hg ⊢
    have e1 :=
      analysisAt_maskAt (s := s) (g := g) (x := johnson (wordOf g.main) g.m s.printed) hh hs
    generalize (analysisAt s g (johnson (wordOf g.main) g.m s.printed)).maskAt = Z at e1 hs hg ⊢
    subst e1
    dsimp only at hs hg ⊢
    obtain ⟨g1, _⟩ := add_good hg
    exact listMax_le_atDistance (enclR_johnson_agree _ _ _) hs g1 hp hk he h2

/-- Where the main code gives the distance, the list size of a group with mask rows is the larger of
the two codes' list sizes as the analysis has them, if the main code's count is not marked bad and
the mask code's source is `.johnson`. -/
theorem analysisOfM_list {s : Setting} {g : GroupSize} (hh : g.hasMask = true)
    (hm : maskRules g = false) (hg : (analysisOfM s g).mainAt.count.bad = false)
    (hs : (analysisOfM s g).maskAt.source = .johnson) :
    (analysisOfM s g).list =
      max (analysisOfM s g).mainAt.list (analysisOfM s g).maskAt.list := by
  have hA : analysisOfM s g = analysisAt s g (johnson (wordOf g.main) g.m s.printed) := by
    unfold analysisOfM
    simp only [hm, Bool.not_false, if_true]
  rw [hA] at hg hs ⊢
  obtain ⟨e1, _⟩ := analysisAt_mainAt hg
  have e2 := analysisAt_maskAt (s := s) (g := g) (x := johnson (wordOf g.main) g.m s.printed) hh hs
  rw [e1, e2]
  unfold analysisAt
  dsimp only
  rw [if_pos hh]

/-- **The price of round j of a fold covers (BM + L 2 + twice BK, while mask rows are folded) / q**,
for numbers BM, BK that are at most what the two counts enclose and L at most the group's list size,
where what the counts enclose is not negative, the group has a slot or more and the price is not
marked bad. -/
theorem fold_covers (s : Setting) (g : GroupSize) (a : Analysis) (j : ℕ) {cM cK BM BK : ℝ} {L : ℕ}
    (hM : EnclR a.mainAt.count cM) (hK : EnclR a.maskAt.count cK) (hBM : BM ≤ cM) (hBK : BK ≤ cK)
    (h0M : 0 ≤ cM) (h0K : 0 ≤ cK) (hL : L ≤ a.list) (hsl : 1 ≤ g.slots)
    (gd : (foldRoundError s g a j).bad = false) :
    (BM + (L : ℝ) * 2 + (if (g.hasMask && decide (j ≤ g.h)) = true then 2 * BK else 0)) /
        (s.cardE : ℝ) ≤ (((foldRoundError s g a j).error.val : ℚ) : ℝ) := by
  refine le_trans ?_ (le_errorR (enclR_foldRoundError s g a j hM hK) gd)
  unfold foldShare
  have hq : (0 : ℝ) ≤ (s.cardE : ℝ) := Nat.cast_nonneg _
  have hrows : 1 ≤ 2 ^ (g.k - j) * g.slots := Nat.mul_pos (by positivity) hsl
  have t1 : BM / (s.cardE : ℝ) ≤ mcaShare s a.mainAt (2 ^ (g.k - j) * g.slots) cM :=
    (div_le_div_of_nonneg_right hBM hq).trans (le_mcaShare s _ h0M hrows)
  have hL' : (L : ℝ) ≤ (a.list : ℝ) := by exact_mod_cast hL
  have t2 : (L : ℝ) * 2 / (s.cardE : ℝ) ≤ (a.list : ℝ) * (((2 : ℕ) : ℝ) / (s.cardE : ℝ)) := by
    rw [mul_div_assoc]
    push_cast
    exact mul_le_mul_of_nonneg_right hL' (by positivity)
  split
  · have t3 : BK / (s.cardE : ℝ) ≤ mcaShare s a.maskAt (2 ^ (g.h - j)) cK :=
      (div_le_div_of_nonneg_right hBK hq).trans (le_mcaShare s _ h0K Nat.one_le_two_pow)
    rw [add_div, add_div]
    push_cast
    have t3' : 2 * BK / (s.cardE : ℝ) ≤ 2 * mcaShare s a.maskAt (2 ^ (g.h - j)) cK := by
      rw [mul_div_assoc]
      linarith
    push_cast at t2
    linarith
  · rw [add_zero, add_zero, add_div]
    linarith

/-- **The price of the first round of a test's last step covers (BM + L + BK, with mask rows) / q**,
under the like conditions. -/
theorem base_covers (s : Setting) (g : GroupSize) (a : Analysis) {cM cK BM BK : ℝ} {L : ℕ}
    (hM : EnclR a.mainAt.count cM) (hK : EnclR a.maskAt.count cK) (hBM : BM ≤ cM) (hBK : BK ≤ cK)
    (h0M : 0 ≤ cM) (h0K : 0 ≤ cK) (hL : L ≤ a.list) (hsl : 1 ≤ g.slots)
    (gd : (baseError s g a).bad = false) :
    (BM + (L : ℝ) + (if g.hasMask = true then BK else 0)) / (s.cardE : ℝ) ≤
      (((baseError s g a).error.val : ℚ) : ℝ) := by
  refine le_trans ?_ (le_errorR (enclR_baseError s g a hM hK) gd)
  unfold baseShare
  have hq : (0 : ℝ) ≤ (s.cardE : ℝ) := Nat.cast_nonneg _
  have t1 : BM / (s.cardE : ℝ) ≤ mcaShare s a.mainAt g.slots cM :=
    (div_le_div_of_nonneg_right hBM hq).trans (le_mcaShare s _ h0M hsl)
  have hL' : (L : ℝ) ≤ (a.list : ℝ) := by exact_mod_cast hL
  have t2 : (L : ℝ) / (s.cardE : ℝ) ≤ (a.list : ℝ) * (((1 : ℕ) : ℝ) / (s.cardE : ℝ)) := by
    push_cast
    rw [mul_one_div]
    exact div_le_div_of_nonneg_right hL' hq
  split
  · have t3 : BK / (s.cardE : ℝ) ≤ mcaShare s a.maskAt 1 cK :=
      (div_le_div_of_nonneg_right hBK hq).trans (le_mcaShare s _ h0K le_rfl)
    rw [add_div, add_div]
    linarith
  · rw [add_zero, add_zero, add_div]
    linarith

/-- What the covering laws below ask of a group with mask rows and of a radius e: the group's rule
is `johnson`, so that the planner prices it by `analysisOfM s g`; the main code gives the distance;
both codes have the source `.johnson` and counts that are not marked bad; m is as printed; both k
are above 0; e is at most 1 less the group's agreement, times the length, and at least half of both
codes' distances; the group has a slot or more. -/
structure JohnsonGroup (s : Setting) (g : GroupSize) (e : ℕ) : Prop where
  rule : g.rule = .johnson
  hasMask : g.hasMask = true
  mainRules : maskRules g = false
  mainSource : (analysisOfM s g).mainAt.source = .johnson
  mainGood : (analysisOfM s g).mainAt.count.bad = false
  maskSource : (analysisOfM s g).maskAt.source = .johnson
  maskGood : (analysisOfM s g).maskAt.count.bad = false
  printed : s.printed = true
  mainK : 0 < (wordOf g.main).k
  maskK : 0 < (repeated g.mask g.main.logN).k
  radius : (e : ℝ) ≤ (1 - groupAgree s g) * ((wordOf g.main).n : ℝ)
  mainFar : (wordOf g.main).n - (wordOf g.main).k ≤ 2 * e
  maskFar : (wordOf g.main).n - (repeated g.mask g.main.logN).k ≤ 2 * e
  slots : 1 ≤ g.slots

/-- Under these conditions the planner's analysis of the group is `analysisOfM`. -/
theorem JohnsonGroup.analysis_eq {s : Setting} {g : GroupSize} {e : ℕ} (J : JohnsonGroup s g e) :
    analysis s g = analysisOfM s g := analysis_johnson J.rule

/-- Under these conditions the library's bound on the main code's list is at most the group's list
size. -/
theorem listMax_le_group {s : Setting} {g : GroupSize} {e : ℕ} (J : JohnsonGroup s g e) :
    Cb.listMax (wordOf g.main).n ((wordOf g.main).n - (wordOf g.main).k) e ≤
      (analysisOfM s g).list := by
  rw [analysisOfM_list J.hasMask J.mainRules J.mainGood J.maskSource]
  exact (listMax_le_main J.mainSource J.mainGood J.printed J.mainK J.radius J.mainFar).trans
    (le_max_left _ _)

/-- Where the main code's count in a group's analysis under the rule `johnson` is not marked bad,
the group has no shape fault. -/
theorem analysisOfM_noFault {s : Setting} {g : GroupSize}
    (hg : (analysisOfM s g).mainAt.count.bad = false) : shapeFault g = false := by
  by_cases hm : maskRules g = true
  · have hA : (analysisOfM s g).mainAt =
        (analysisAt s g (atDistance s (wordOf g.main)
          (johnson (repeated g.mask g.main.logN) g.m s.printed).agree)).mainAt := by
      unfold analysisOfM
      simp only [hm, Bool.not_true, Bool.false_eq_true, if_false]
    rw [hA] at hg
    exact analysisAt_noFault hg
  · have hm' : maskRules g = false := by simpa using hm
    have hA : (analysisOfM s g).mainAt =
        (analysisAt s g (johnson (wordOf g.main) g.m s.printed)).mainAt := by
      unfold analysisOfM
      simp only [hm', Bool.not_false, if_true]
    rw [hA] at hg
    exact analysisAt_noFault hg

/-- Under these conditions the repeated mask code's k is at most the main code's. -/
theorem JohnsonGroup.maskK_le {s : Setting} {g : GroupSize} {e : ℕ} (J : JohnsonGroup s g e) :
    (repeated g.mask g.main.logN).k ≤ (wordOf g.main).k := by
  have hf := analysisOfM_noFault J.mainGood
  unfold shapeFault at hf
  simp only [J.hasMask, Bool.not_true, Bool.false_eq_true, if_false, Bool.or_eq_false_iff,
    decide_eq_false_iff_not, not_lt] at hf
  have hle : g.mask.logN ≤ g.main.logN := hf.1.1
  have hr := J.mainRules
  unfold maskRules at hr
  simp only [J.hasMask, Bool.true_and, decide_eq_false_iff_not, not_lt] at hr
  unfold CodeSize.n at hr
  show (repeated g.mask g.main.logN).k ≤ g.main.k
  unfold repeated
  split
  · rename_i h'
    have e1 : g.mask.logN = g.main.logN := le_antisymm hle h'
    rw [e1] at hr
    exact Nat.le_of_mul_le_mul_right hr (by positivity)
  · refine (Nat.mod_le _ _).trans ?_
    have e2 : 2 ^ g.main.logN = 2 ^ (g.main.logN - g.mask.logN) * 2 ^ g.mask.logN := by
      rw [← pow_add]
      congr 1
      omega
    rw [e2, ← Nat.mul_assoc] at hr
    exact Nat.le_of_mul_le_mul_right hr (by positivity)

/-- So the main code's distance is the smaller of the two. -/
theorem JohnsonGroup.min_distance {s : Setting} {g : GroupSize} {e : ℕ} (J : JohnsonGroup s g e) :
    min ((wordOf g.main).n - (wordOf g.main).k)
        ((wordOf g.main).n - (repeated g.mask g.main.logN).k) =
      (wordOf g.main).n - (wordOf g.main).k :=
  min_eq_left (Nat.sub_le_sub_left J.maskK_le _)

/-- **The price of round j of a fold, under these conditions, covers the library's numbers**: its
count at the main code, twice its bound on the main code's list and, while mask rows are folded,
twice its count at the repeated mask code with its bound on that code's list; all over q. -/
theorem fold_covers_johnson {s : Setting} {g : GroupSize} {e : ℕ} (J : JohnsonGroup s g e) (j : ℕ)
    (gd : (foldRoundError s g (analysisOfM s g) j).bad = false) :
    (Cb.bchksBound (wordOf g.main).n (wordOf g.main).k e +
        (Cb.listMax (wordOf g.main).n ((wordOf g.main).n - (wordOf g.main).k) e : ℝ) * 2 +
        (if (g.hasMask && decide (j ≤ g.h)) = true then
          2 * (Cb.bchksBound (wordOf g.main).n (repeated g.mask g.main.logN).k e +
            (Cb.listMax (wordOf g.main).n
              ((wordOf g.main).n - (repeated g.mask g.main.logN).k) e : ℝ)) else 0)) /
        (s.cardE : ℝ) ≤ (((foldRoundError s g (analysisOfM s g) j).error.val : ℚ) : ℝ) := by
  have hn := analysisOfM_oneLength J.hasMask J.mainGood
  obtain ⟨_, _, m2, m3, m4⟩ := analysisOfM_main J.mainSource J.mainGood
  obtain ⟨_, _, k2, k3, k4⟩ := analysisOfM_mask J.hasMask J.maskSource J.maskGood
  have heK : (e : ℝ) ≤ (1 - groupAgree s g) * ((repeated g.mask g.main.logN).n : ℝ) := by
    rw [hn]
    exact J.radius
  have lK := listMax_le_mask J.hasMask J.maskSource J.maskGood J.printed J.maskK heK
    (by rw [hn]; exact J.maskFar)
  have lM := listMax_le_main J.mainSource J.mainGood J.printed J.mainK J.radius J.mainFar
  have bK := bchksBound_le_countAt k3 J.maskK (k4 J.printed) heK
  rw [hn] at lK bK
  have lK' : (Cb.listMax (wordOf g.main).n
      ((wordOf g.main).n - (repeated g.mask g.main.logN).k) e : ℝ) ≤
      ((analysisOfM s g).maskAt.list : ℝ) := by exact_mod_cast lK
  refine fold_covers s g (analysisOfM s g) j m2 k2
    (bchksBound_le_countAt m3 J.mainK (m4 J.printed) J.radius) ?_ (enclR_nonneg m2 J.mainGood)
    (enclR_nonneg k2 J.maskGood) ?_ J.slots gd
  · rw [hn]
    exact add_le_add bK lK'
  · rw [analysisOfM_list J.hasMask J.mainRules J.mainGood J.maskSource]
    exact lM.trans (le_max_left _ _)

/-- **The like for the first round of a test's last step**: the library's count at the main code,
its bound on the main code's list, and its count at the repeated mask code with its bound on that
code's list; all over q. -/
theorem base_covers_johnson {s : Setting} {g : GroupSize} {e : ℕ} (J : JohnsonGroup s g e)
    (gd : (baseError s g (analysisOfM s g)).bad = false) :
    (Cb.bchksBound (wordOf g.main).n (wordOf g.main).k e +
        (Cb.listMax (wordOf g.main).n ((wordOf g.main).n - (wordOf g.main).k) e : ℝ) +
        (Cb.bchksBound (wordOf g.main).n (repeated g.mask g.main.logN).k e +
          (Cb.listMax (wordOf g.main).n
            ((wordOf g.main).n - (repeated g.mask g.main.logN).k) e : ℝ))) /
        (s.cardE : ℝ) ≤ (((baseError s g (analysisOfM s g)).error.val : ℚ) : ℝ) := by
  have hn := analysisOfM_oneLength J.hasMask J.mainGood
  obtain ⟨_, _, m2, m3, m4⟩ := analysisOfM_main J.mainSource J.mainGood
  obtain ⟨_, _, k2, k3, k4⟩ := analysisOfM_mask J.hasMask J.maskSource J.maskGood
  have heK : (e : ℝ) ≤ (1 - groupAgree s g) * ((repeated g.mask g.main.logN).n : ℝ) := by
    rw [hn]
    exact J.radius
  have lK := listMax_le_mask J.hasMask J.maskSource J.maskGood J.printed J.maskK heK
    (by rw [hn]; exact J.maskFar)
  have lM := listMax_le_main J.mainSource J.mainGood J.printed J.mainK J.radius J.mainFar
  have bK := bchksBound_le_countAt k3 J.maskK (k4 J.printed) heK
  rw [hn] at lK bK
  have lK' : (Cb.listMax (wordOf g.main).n
      ((wordOf g.main).n - (repeated g.mask g.main.logN).k) e : ℝ) ≤
      ((analysisOfM s g).maskAt.list : ℝ) := by exact_mod_cast lK
  have h := base_covers s g (analysisOfM s g) m2 k2
    (bchksBound_le_countAt m3 J.mainK (m4 J.printed) J.radius)
    (BK := Cb.bchksBound (wordOf g.main).n (repeated g.mask g.main.logN).k e +
      (Cb.listMax (wordOf g.main).n
        ((wordOf g.main).n - (repeated g.mask g.main.logN).k) e : ℝ))
    (by rw [hn]; exact add_le_add bK lK') (enclR_nonneg m2 J.mainGood)
    (enclR_nonneg k2 J.maskGood)
    (L := Cb.listMax (wordOf g.main).n ((wordOf g.main).n - (wordOf g.main).k) e)
    (by
      rw [analysisOfM_list J.hasMask J.mainRules J.mainGood J.maskSource]
      exact lM.trans (le_max_left _ _)) J.slots gd
  rw [if_pos J.hasMask] at h
  exact h

/-- The library's count is not negative. -/
theorem bchksBound_nonneg (n k e : ℕ) : 0 ≤ Cb.bchksBound n k e := by
  have hM : (0 : ℝ) ≤ Cb.bchksM n k e := by
    unfold Cb.bchksM
    exact le_trans (by norm_num) (le_max_right _ _)
  unfold Cb.bchksBound
  positivity

/-- **The law on a fold's rounds in whole numbers**: with the library's two counts rounded down. -/
theorem fold_covers_floor {s : Setting} {g : GroupSize} {e : ℕ} (J : JohnsonGroup s g e) (j : ℕ)
    (gd : (foldRoundError s g (analysisOfM s g) j).bad = false) :
    (((⌊Cb.bchksBound (wordOf g.main).n (wordOf g.main).k e⌋₊ +
        Cb.listMax (wordOf g.main).n ((wordOf g.main).n - (wordOf g.main).k) e * 2 +
        (if (g.hasMask && decide (j ≤ g.h)) = true then
          2 * (⌊Cb.bchksBound (wordOf g.main).n (repeated g.mask g.main.logN).k e⌋₊ +
            Cb.listMax (wordOf g.main).n
              ((wordOf g.main).n - (repeated g.mask g.main.logN).k) e) else 0) : ℕ) : ℝ)) /
        (s.cardE : ℝ) ≤ (((foldRoundError s g (analysisOfM s g) j).error.val : ℚ) : ℝ) := by
  refine le_trans (div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)) (fold_covers_johnson J j gd)
  have f1 := Nat.floor_le (bchksBound_nonneg (wordOf g.main).n (wordOf g.main).k e)
  have f2 := Nat.floor_le
    (bchksBound_nonneg (wordOf g.main).n (repeated g.mask g.main.logN).k e)
  split
  · push_cast
    linarith
  · push_cast
    linarith

/-- **The law on the last step's first round in whole numbers.** -/
theorem base_covers_floor {s : Setting} {g : GroupSize} {e : ℕ} (J : JohnsonGroup s g e)
    (gd : (baseError s g (analysisOfM s g)).bad = false) :
    (((⌊Cb.bchksBound (wordOf g.main).n (wordOf g.main).k e⌋₊ +
        Cb.listMax (wordOf g.main).n ((wordOf g.main).n - (wordOf g.main).k) e +
        (⌊Cb.bchksBound (wordOf g.main).n (repeated g.mask g.main.logN).k e⌋₊ +
          Cb.listMax (wordOf g.main).n
            ((wordOf g.main).n - (repeated g.mask g.main.logN).k) e) : ℕ) : ℝ)) /
        (s.cardE : ℝ) ≤ (((baseError s g (analysisOfM s g)).error.val : ℚ) : ℝ) := by
  refine le_trans (div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)) (base_covers_johnson J gd)
  have f1 := Nat.floor_le (bchksBound_nonneg (wordOf g.main).n (wordOf g.main).k e)
  have f2 := Nat.floor_le
    (bchksBound_nonneg (wordOf g.main).n (repeated g.mask g.main.logN).k e)
  push_cast
  linarith

/-- A test, by the planner's own arithmetic, from which `JohnsonGroup s g e` follows. The radius is
held against the lower end of the main code's distance times the length, rounded down. -/
def johnsonGroupTest (s : Setting) (g : GroupSize) (e : ℕ) : Bool :=
  decide (g.rule = .johnson) && g.hasMask && !maskRules g &&
    decide ((analysisOfM s g).mainAt.source = .johnson) && !(analysisOfM s g).mainAt.count.bad &&
    decide ((analysisOfM s g).maskAt.source = .johnson) && !(analysisOfM s g).maskAt.count.bad &&
    s.printed && decide (0 < (wordOf g.main).k) && decide (0 < (repeated g.mask g.main.logN).k) &&
    !((analysisOfM s g).mainAt.delta * Bound.ofNat (wordOf g.main).n).bad &&
    decide (e ≤ lowerRadius (analysisOfM s g).mainAt.delta (wordOf g.main).n) &&
    decide ((wordOf g.main).n - (wordOf g.main).k ≤ 2 * e) &&
    decide ((wordOf g.main).n - (repeated g.mask g.main.logN).k ≤ 2 * e) && decide (1 ≤ g.slots)

/-- **A yes of that test gives the conditions.** -/
theorem johnsonGroup_of_test {s : Setting} {g : GroupSize} {e : ℕ}
    (h : johnsonGroupTest s g e = true) : JohnsonGroup s g e := by
  unfold johnsonGroupTest at h
  simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨a0, a1⟩, a2⟩, a3⟩, a4⟩, a5⟩, a6⟩, a7⟩, a8⟩, a9⟩, a10⟩, a11⟩, a12⟩, a13⟩,
    a14⟩ := h
  obtain ⟨_, d2, _, _, _⟩ := analysisOfM_main a3 a4
  have hr := lowerRadius_le d2 a10
  have he : (e : ℝ) ≤ (lowerRadius (analysisOfM s g).mainAt.delta (wordOf g.main).n : ℝ) := by
    exact_mod_cast a11
  exact ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, he.trans hr, a12, a13, a14⟩

end OnBytes.Params

#print axioms OnBytes.Params.johnsonGroup_of_test
#print axioms OnBytes.Params.JohnsonGroup.analysis_eq
#print axioms OnBytes.Params.listMax_le_group
#print axioms OnBytes.Params.analysisOfM_noFault
#print axioms OnBytes.Params.JohnsonGroup.maskK_le
#print axioms OnBytes.Params.JohnsonGroup.min_distance
#print axioms OnBytes.Params.bchksBound_nonneg
#print axioms OnBytes.Params.fold_covers_floor
#print axioms OnBytes.Params.base_covers_floor
#print axioms OnBytes.Params.fold_covers_johnson
#print axioms OnBytes.Params.base_covers_johnson
#print axioms OnBytes.Params.fold_covers
#print axioms OnBytes.Params.base_covers
#print axioms OnBytes.Params.listMax_le_main
#print axioms OnBytes.Params.listMax_le_mask
#print axioms OnBytes.Params.analysisOfM_list
#print axioms OnBytes.Params.atDistance_list_eq
#print axioms OnBytes.Params.listMax_le_atDistance
#print axioms OnBytes.Params.surelyLtR_sound
#print axioms OnBytes.Params.list_whole_at
#print axioms OnBytes.Params.listMax_le_of_whole
