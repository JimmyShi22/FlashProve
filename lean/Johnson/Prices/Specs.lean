-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prices/Specs.lean: from a round's description in a finished plan's list to a count that the
round pays: field rounds, batching by powers, and the seeds of a sending of several oracle messages.

A finished plan that holds has the rounds of a list of descriptions (`PlanIs P s c l`,
OnBytes/Params/PlanListsChains.lean). `spec_pays`: a member y of the list whose round covers a count
has its round in the plan, its bound not marked bad where it is a round with a verifier's message,
and the count within the target. `plainScope s c`: the planner does not multiply a round's error by
the setting's instances (every scope but a request's; a request's where the setting has at most one
instance, as `settingOf` leaves it). Under it:
 - `field_pays`: a round priced `fieldError s k` pays for k |E| ^ m of |E| ^ (m + 1), for every m.
   At m = 0: k of |E|, the roots of a polynomial of degree k in one drawn element (PSC epsilon: k =
   1; a PSC round of degree below 3: k = 2; LINE). At m = k - 1: the zeros of a multilinear form in
   k drawn elements (ZERO, JOIN, LIN zeta, LINK phi).
 - `powers_pays`: a round priced `powersError s rows` pays for rows - 1 of |E| (BAT-sigma).
 - `send_pays`: the round of the seeds of a sending of the oracle messages o pays for `sendCount`:
   the sum over the messages of (L choose 2) times the clashing seeds of the message's own cube, to
   the power of the answers, times R, the number of ways to fill the rest of the joint seeds; L at
   most the planner's list size for the message; and all seeds of the message's own cube, to that
   power, times R, are the N joint seeds.

Main definitions: `plainScope`, `sendCount`.
Main theorems: `spec_pays`, `said_error`, `covers_ratio`, `field_pays`, `powers_pays`,
`sample_term_le`, `send_sum_le`, `send_covers`, `send_pays`.
What is not claimed: at which place of a plan a description stands: that is the matter of the laws
on the chains' lists. That a count bounds a prover's chance. That `clashSeeds` and `allSeeds`
(OnBytes/Params/RecordPrice.lean) are the numbers of any sample map. What the head of
Johnson/Prices/Pays.lean does not claim.

-/
import Johnson.Prices.Pays
import OnBytes.Params.MorePrices

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Params.Prices
open Bound

/-- The planner does not multiply a round's error by the setting's instances. -/
def plainScope (s : Setting) (c : Scope) : Prop :=
  (c == Scope.request && decide (1 < s.instances)) = false

/-- The scope of a batch is plain. -/
theorem plainScope_shared (s : Setting) : plainScope s .shared := rfl

/-- The scope of a commitment is plain. -/
theorem plainScope_once (s : Setting) : plainScope s .once := rfl

/-- Every scope is plain at the setting of a parameter file's lines. -/
theorem plainScope_settingOf (l : Lines) (c : Scope) : plainScope (settingOf l) c := by
  unfold plainScope
  have : (settingOf l).instances = 1 := rfl
  rw [this]
  simp

/-- Under a plain scope the bound that is priced is the routine's. -/
theorem said_bound {s : Setting} {c : Scope} (h : plainScope s c) (name : String) (why : ErrorKind)
    (error : Bound) (d : Draws) (bytes roots answers : ℕ) :
    (RoundSpec.said name why error d bytes roots answers).bound s c = error := by
  unfold plainScope at h
  simp only [RoundSpec.bound, h, Bool.false_eq_true, ↓reduceIte]

/-- Under a plain scope a round's error is that of the routine's bound. -/
theorem said_error {s : Setting} {c : Scope} (h : plainScope s c) (name : String) (why : ErrorKind)
    (error : Bound) (d : Draws) (bytes roots answers : ℕ) :
    ((RoundSpec.said name why error d bytes roots answers).round s c).error = error.error := by
  show ((RoundSpec.said name why error d bytes roots answers).bound s c).error = _
  rw [said_bound h]

/-- **A member of a finished plan's list whose round covers a count**: the round is in the plan, and
the count is within the target. -/
theorem spec_pays {P : Planned} {s : Setting} {c : Scope} {l : List RoundSpec}
    (hP : PlanIs P s c l) {y : RoundSpec} (hy : y ∈ l) {count total : ℕ}
    (hc : Covers (y.round s c) count total) :
    y.round s c ∈ P.rounds ∧ Within s.target (y.round s c).entry.work count total :=
  ⟨by rw [hP.rounds]; exact List.mem_map_of_mem hy, within_of_covers (hP.holds y hy) hc⟩

/-- **The price a / q covers a q ^ m of q ^ (m + 1).** -/
theorem covers_ratio {r : PlanRound} {a q : ℕ} (m : ℕ) (he : r.error = (Bound.ratio a q).error)
    (hb : (Bound.ratio a q).bad = false) : Covers r (a * q ^ m) (q ^ (m + 1)) := by
  have hq0 : 0 < q := by
    rcases Nat.eq_zero_or_pos q with h0 | h0
    · rw [h0, ratio_zero_bad] at hb
      cases hb
    · exact h0
  have hq : (0 : ℚ) < (q : ℚ) := by exact_mod_cast hq0
  have h1 : (a : ℚ) / (q : ℚ) ≤ r.error.val := by
    rw [he]
    exact le_error (encl_ratio a q) hb
  have h2 : ((a * q ^ m : ℕ) : ℚ) = (a : ℚ) / (q : ℚ) * ((q ^ (m + 1) : ℕ) : ℚ) := by
    push_cast
    rw [pow_succ]
    field_simp
  unfold Covers
  rw [h2]
  exact mul_le_mul_of_nonneg_right h1 (Nat.cast_nonneg _)

/-- **A round priced `fieldError s k` pays for k |E| ^ m of |E| ^ (m + 1).** -/
theorem field_pays {P : Planned} {s : Setting} {c : Scope} {l : List RoundSpec}
    (hP : PlanIs P s c l) (hs : plainScope s c) {name : String} {why : ErrorKind} {k : ℕ}
    {d : Draws} {bytes roots answers : ℕ}
    (hy : RoundSpec.said name why (fieldError s k) d bytes roots answers ∈ l) (m : ℕ) :
    (RoundSpec.said name why (fieldError s k) d bytes roots answers).round s c ∈ P.rounds ∧
      Covers ((RoundSpec.said name why (fieldError s k) d bytes roots answers).round s c)
        (k * s.cardE ^ m) (s.cardE ^ (m + 1)) ∧
      Within s.target (s.workOf why c) (k * s.cardE ^ m) (s.cardE ^ (m + 1)) := by
  have hg : (fieldError s k).bad = false := by
    have := (hP.good _ hy).1
    rwa [said_bound hs] at this
  have hc := covers_ratio (r := (RoundSpec.said name why (fieldError s k) d bytes roots
    answers).round s c) m (said_error hs _ _ _ _ _ _ _) hg
  exact ⟨(spec_pays hP hy hc).1, hc, (spec_pays hP hy hc).2⟩

/-- **A round priced `powersError s rows` pays for rows - 1 of |E|.** -/
theorem powers_pays {P : Planned} {s : Setting} {c : Scope} {l : List RoundSpec}
    (hP : PlanIs P s c l) (hs : plainScope s c) {name : String} {why : ErrorKind} {rows : ℕ}
    {d : Draws} {bytes roots answers : ℕ}
    (hy : RoundSpec.said name why (powersError s rows) d bytes roots answers ∈ l) :
    (RoundSpec.said name why (powersError s rows) d bytes roots answers).round s c ∈ P.rounds ∧
      Covers ((RoundSpec.said name why (powersError s rows) d bytes roots answers).round s c)
        (rows - 1) s.cardE ∧
      Within s.target (s.workOf why c) (rows - 1) s.cardE := by
  have hg : (powersError s rows).bad = false := by
    have := (hP.good _ hy).1
    rwa [said_bound hs] at this
  have hc0 := covers_ratio (r := (RoundSpec.said name why (powersError s rows) d bytes roots
    answers).round s c) 0 (said_error hs _ _ _ _ _ _ _) hg
  have hc : Covers ((RoundSpec.said name why (powersError s rows) d bytes roots answers).round s c)
      (rows - 1) s.cardE := by simpa using hc0
  exact ⟨(spec_pays hP hy hc).1, hc, (spec_pays hP hy hc).2⟩

/-! ## The seeds of a sending -/

/-- The planner's list size for a message is at least 1. -/
theorem largestList_pos (s : Setting) : ∀ gs : List GroupSize, 1 ≤ largestList s gs
  | [] => le_rfl
  | _ :: gs => le_trans (largestList_pos s gs) (le_max_right _ _)

/-- The count of the seeds of a sending at which some message's list has two members with the same
answers. Of each message: its sizes, a bound L on its list, and the number R of ways to fill the
rest of the joint seeds. -/
def sendCount (q a : ℕ) : List (SampleSize × ℕ × ℕ) → ℕ
  | [] => 0
  | z :: t => z.2.1.choose 2 * clashSeeds q z.1.cubeBits ^ a * z.2.2 + sendCount q a t

/-- One message's term is at most what `sampleError` encloses, times the joint seeds. -/
theorem sample_term_le (s : Setting) (hq : 2 ≤ s.cardE) {L R N a lg list : ℕ} (hL : L ≤ list)
    (h1 : 1 ≤ list) (hN : allSeeds s.cardE lg ^ a * R = N) :
    ((L.choose 2 * clashSeeds s.cardE lg ^ a * R : ℕ) : ℚ) ≤ sampleShare s list lg a * (N : ℚ) := by
  have h := record_share_le s (L := L) (list := list) (lg := lg) (a := a) (b := 0) (x := 0) hq hL
    le_rfl (by simp) h1
  simp only [add_zero, pow_zero, one_mul] at h
  have hall : 0 < allSeeds s.cardE lg ^ a := by
    apply Nat.pow_pos
    unfold allSeeds
    exact Nat.mul_pos (Nat.pow_pos (by omega)) (by omega)
  have hall' : (0 : ℝ) < ((allSeeds s.cardE lg ^ a : ℕ) : ℝ) := by exact_mod_cast hall
  have hR : ((L.choose 2 * clashSeeds s.cardE lg ^ a * R : ℕ) : ℝ) ≤
      ((sampleShare s list lg a : ℚ) : ℝ) * (N : ℝ) := by
    rw [← hN]
    rw [div_le_iff₀ hall'] at h
    have hR0 : (0 : ℝ) ≤ (R : ℝ) := Nat.cast_nonneg _
    have := mul_le_mul_of_nonneg_right h hR0
    calc ((L.choose 2 * clashSeeds s.cardE lg ^ a * R : ℕ) : ℝ)
        = ((L.choose 2 * clashSeeds s.cardE lg ^ a : ℕ) : ℝ) * (R : ℝ) := by push_cast; ring
      _ ≤ ((sampleShare s list lg a : ℚ) : ℝ) * ((allSeeds s.cardE lg ^ a : ℕ) : ℝ) * (R : ℝ) :=
          this
      _ = ((sampleShare s list lg a : ℚ) : ℝ) * ((allSeeds s.cardE lg ^ a * R : ℕ) : ℝ) := by
          push_cast; ring
  exact_mod_cast hR

/-- The count of a sending, from y on, against what `sampleSum` encloses. -/
theorem send_sum_le (s : Setting) (hq : 2 ≤ s.cardE) (N : ℕ) :
    ∀ (t : List (SampleSize × ℕ × ℕ)) (y : ℚ),
      (∀ z ∈ t, z.2.1 ≤ largestList s z.1.groups ∧
        allSeeds s.cardE z.1.cubeBits ^ s.samples * z.2.2 = N) →
      y * (N : ℚ) + (sendCount s.cardE s.samples t : ℚ) ≤
        sampleShares s (t.map (·.1)) y * (N : ℚ)
  | [], y, _ => by simp [sendCount, sampleShares]
  | z :: t, y, h => by
    have hz := h z (List.mem_cons_self ..)
    have ih := send_sum_le s hq N t
      (y + sampleShare s (largestList s z.1.groups) z.1.cubeBits s.samples)
      fun w hw => h w (List.mem_cons_of_mem _ hw)
    have ht := sample_term_le s hq hz.1 (largestList_pos s z.1.groups) hz.2
    show _ ≤ sampleShares s (t.map (·.1))
      (y + sampleShare s (largestList s z.1.groups) z.1.cubeBits s.samples) * (N : ℚ)
    unfold sendCount
    push_cast at ht ih ⊢
    linarith

/-- **The price of the seeds of a sending covers the count.** -/
theorem send_covers {s : Setting} {r : PlanRound} (hq : 2 ≤ s.cardE) {N : ℕ}
    {t : List (SampleSize × ℕ × ℕ)}
    (h : ∀ z ∈ t, z.2.1 ≤ largestList s z.1.groups ∧
      allSeeds s.cardE z.1.cubeBits ^ s.samples * z.2.2 = N)
    (he : r.error = (sampleSum s (t.map (·.1)) (Bound.ofWord 0)).error)
    (hb : (sampleSum s (t.map (·.1)) (Bound.ofWord 0)).bad = false) :
    Covers r (sendCount s.cardE s.samples t) N := by
  have h1 := send_sum_le s hq N t 0 h
  have h2 : sampleShares s (t.map (·.1)) 0 ≤ r.error.val := by
    rw [he]
    have e0 : Encl (Bound.ofWord 0) (0 : ℚ) := by simpa using encl_ofWord 0
    exact le_error (encl_sampleSum s _ e0) hb
  unfold Covers
  rw [zero_mul, zero_add] at h1
  exact h1.trans (mul_le_mul_of_nonneg_right h2 (Nat.cast_nonneg _))

/-- **The round of the seeds of a sending pays for the count.** -/
theorem send_pays {P : Planned} {s : Setting} {c : Scope} {l : List RoundSpec}
    (hP : PlanIs P s c l) (hs : plainScope s c) (hq : 2 ≤ s.cardE) {N roots : ℕ}
    {t : List (SampleSize × ℕ × ℕ)} (hy : sendSeed s (t.map (·.1)) roots ∈ l)
    (h : ∀ z ∈ t, z.2.1 ≤ largestList s z.1.groups ∧
      allSeeds s.cardE z.1.cubeBits ^ s.samples * z.2.2 = N) :
    (sendSeed s (t.map (·.1)) roots).round s c ∈ P.rounds ∧
      Covers ((sendSeed s (t.map (·.1)) roots).round s c) (sendCount s.cardE s.samples t) N ∧
      Within s.target (s.workOf .sample c) (sendCount s.cardE s.samples t) N := by
  have hg : (sampleSum s (t.map (·.1)) (Bound.ofWord 0)).bad = false := by
    have := (hP.good _ hy).1
    unfold sendSeed at this
    rwa [said_bound hs] at this
  have he : ((sendSeed s (t.map (·.1)) roots).round s c).error =
      (sampleSum s (t.map (·.1)) (Bound.ofWord 0)).error := by
    unfold sendSeed
    exact said_error hs _ _ _ _ _ _ _
  have hc := send_covers hq h he hg
  exact ⟨(spec_pays hP hy hc).1, hc, (spec_pays hP hy hc).2⟩

end OnBytes.Params.Prices
