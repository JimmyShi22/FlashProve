-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/IMR/WaitsInLink.lean

Lemmas along the first chain's fold, in the goals' scope, at the concrete earlier hash: each hearing
sub-protocol of a link but its first, and but the head's second, carries "no count of rows waits"
(S.noneWaits, Johnson/Desc/First/State.lean) from the state in front of it to the state behind, at
every state; so along the fold it is carried from any border behind these to the border in front of
the link's batching.
This file states no goal.

Words. A border is a number k from 0 to 358: the place between the sub-protocols number k - 1 and k
of the first chain's flat list c.blocksInOrder. Link l, l < 25, has its hearing sub-protocols at the numbers
14 l + i + 2, i < IM.nAt l (7; at the head's link, l = 24: 9), and its batching at 14 l + IM.nAt l +
2 (FlatCase.batch with flat_cases, Johnson/IMR/FlatCases.lean).

Main definitions and theorems:
* "hearKinds_fit": a closed test on the written list of kinds, by Lean's kernel: every hearing
  sub-protocol but a link's first, and but the head's second, is of one of the six quiet kinds (K3,
  K4, K5, K6, K8, K11) or of kind K1.
* "hearKinds_bent_fails": the same test without its two exceptions fails.
* "hear_carries": each of these sub-protocols carries "no count waits".
* "hear_along": so it is carried from the border 14 l + j + 2 to any later border of the link up to
  its batching; j ≥ 1, and j ≥ 2 at the head's link; in the fold's form.

How. The quiet kinds: IM.chain_hear_alone (Johnson/IMR/LaidFirst.lean) hands the lot's own
sub-protocol beneath the seated one, IM.quiet_lot (Johnson/IMR/QuietLot.lean) says that its every
yes is Quiet, and Quiet.waits (Johnson/Goal/Meaning/RecQuiet.lean) is the sentence. Kind K1:
IM.k1_later (Johnson/IMR/K1Seat.lean) with k1Reads_stand and commitAtS_stand, as in k1_at_stand
(Johnson/IMR/SortDigits.lean), which is stated in front of the head's link alone. Along the fold:
fold_back and fold_next, as in stand_at (the same file).

Limits. That no count waits at any state is shown nowhere here: it is a premise (w).
Johnson/IMR/WaitsBehindSwitch.lean shows it at the states reached strictly behind a link's code
switching (in link 0: its first sending) and up to the border in front of the link's batching.
Nothing at a border behind a batching; at the two next behind it a count may wait (mayWait,
Johnson/Desc/First/Borders.lean). This file shows of no state that it is reached; what the library
has on that: the head of Johnson/IMR/WaitsBehindSwitch.lean.

Not claimed: anything on what a verifier accepts or on an honest prover; any property of the
protocol.

-/
import Johnson.IMR.AtReach
import Johnson.IMR.SortDigits
import Johnson.IMR.QuietLot

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.K2

open OnBytes OnBytes.Model
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open VerifiableInference.Desc.Keeps (Whole Decides)
open ProofFile (Cl)

variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- The test of hearKinds_fit. -/
def hearKindsFit : Bool :=
  (List.range 25).all fun l => (List.range (IM.nAt l)).all fun i =>
    i == 0 || (l == 24 && i == 1) ||
      match (kindsBeforeBatching (IM.subAt l) (l == 0))[i]? with
      | some k => IM.quietMaker k || k == .K1
      | none => false

theorem hearKinds_fit : hearKindsFit = true := by decide +kernel

/-- The same test without its two exceptions: it meets the kinds K2 and K7. -/
def hearKindsBent : Bool :=
  (List.range 25).all fun l => (List.range (IM.nAt l)).all fun i =>
    match (kindsBeforeBatching (IM.subAt l) (l == 0))[i]? with
    | some k => IM.quietMaker k || k == .K1
    | none => false

theorem hearKinds_bent_fails : hearKindsBent = false := by decide +kernel

/-- **Every hearing sub-protocol of a link but its first, and but the head's second, carries "no
count of rows waits".** -/
theorem hear_carries (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l i : ℕ} (hl : l < 25)
    (h1 : 1 ≤ i) (hi : i < IM.nAt l) (h24 : l = 24 → 2 ≤ i) {b : Block S Cl}
    (hb : c.blocksInOrder[14 * l + i + 2]? = some b) {s t : S} {rs : List Fmt.RoundView}
    {gs : List (List (ℕ × List UInt64))} (d : b.decide s rs gs = .ok t)
    (w : s.noneWaits = true) : t.noneWaits = true := by
  have h9 : i + 1 ≤ 9 := by
    unfold IM.nAt at hi
    split at hi <;> omega
  have T := List.all_eq_true.1 (List.all_eq_true.1 hearKinds_fit l (List.mem_range.2 hl)) i
    (List.mem_range.2 hi)
  have n0 : (i == 0) = false := by simpa using (by omega : i ≠ 0)
  have n1 : (l == 24 && i == 1) = false := by
    by_cases e : l = 24
    · have h2 : i ≠ 1 := by
        have := h24 e
        omega
      simp [h2]
    · simp [e]
  simp only [n0, n1, Bool.false_or] at T
  cases hk : (kindsBeforeBatching (IM.subAt l) (l == 0))[i]? with
  | none => simp only [hk] at T; cases T
  | some k =>
    simp only [hk] at T
    rw [Bool.or_eq_true] at T
    rcases T with hq | hq
    · obtain ⟨Lk, b₁, e1, e2, sp, -, L, hL, b', hb', -, ep, hla⟩ :=
        IM.chain_hear_alone O.made O.places O.chain l (IM.subAt l) (IM.subs_scope hS hR O l hl) i k
          hk (by rintro rfl; exact absurd hq (by decide))
          (by rintro rfl; exact absurd hq (by decide)) ⟨by omega, h9⟩
      have ib : c.blocksInOrder[14 * l + i + 2]? = some b₁ := by
        have q := IM.hear_at_flat e1 e2
        rwa [IM.flatIx_scope hS hR O (by omega : l ≤ 24) i] at q
      obtain rfl : b = b₁ := Option.some.inj (hb.symm.trans ib)
      have d' := ((IM.yes_alone hla
        (by show k ≠ KindName.K7; rintro rfl; exact absurd hq (by decide)) s t rs gs).1 d).1
      exact Quiet.waits (IM.quiet_lot hL hb' (by rw [ep]; exact hq) s rs gs t d') w
    · obtain rfl : k = KindName.K1 := by
        cases k <;> first | rfl | exact absurd hq (by decide)
      obtain ⟨Lk, b₁, Xl, pr, pd, reads, digits, e1, e2, -, -, harm⟩ :=
        IM.k1_later O l (IM.subAt l) (IM.subs_scope hS hR O l hl) i hk ⟨by omega, h9⟩
      have ib : c.blocksInOrder[14 * l + i + 2]? = some b₁ := by
        have q := IM.hear_at_flat e1 e2
        rwa [IM.flatIx_scope hS hR O (by omega : l ≤ 24) i] at q
      obtain rfl : b = b₁ := Option.some.inj (hb.symm.trans ib)
      rcases harm with ⟨-, la⟩ | ⟨-, la⟩
      · exact (alone_stand (by intro k; cases k) la
          (fun s rs gs t h => k1Reads_stand _ _ _ _ _ s rs gs t h) s rs gs t d).2.1 w
      · exact (alone_stand (by intro k; cases k) la
          (fun s rs gs t h => (commitAtS_stand (Cl := Unit) _ _ _ _).1 s rs gs t h)
          s rs gs t d).2.1 w

/-- **"No count of rows waits" is carried along a link's hearing sub-protocols**, from the border
14 l + j + 2 to every later border up to the link's batching; j ≥ 1, and j ≥ 2 at the head's link:
behind the link's first hearing sub-protocol (at the head's link: its second, the code switching).
In the fold's form. -/
theorem hear_along (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l j : ℕ} (hl : l < 25)
    (h1 : 1 ≤ j) (h24 : l = 24 → 2 ≤ j) {s : S} {R : List Fmt.RoundView}
    {C : List VerifiableInference.Desc.OpenedColumn} {t₁ : S} {R₁ : List Fmt.RoundView}
    {C₁ : List VerifiableInference.Desc.OpenedColumn}
    (f₁ : foldBlocks 0 (c.blocksInOrder.take (14 * l + j + 2)) s R C = .ok (t₁, R₁, C₁))
    (w : t₁.noneWaits = true) :
    ∀ n, j + n ≤ IM.nAt l → ∀ (t : S) (R' : List Fmt.RoundView) (C' : List VerifiableInference.Desc.OpenedColumn),
      foldBlocks 0 (c.blocksInOrder.take (14 * l + j + 2 + n)) s R C = .ok (t, R', C') →
      t.noneWaits = true
  | 0, _, t, R', C', f => by
    have e : (t₁, R₁, C₁) = (t, R', C') := Except.ok.inj (f₁.symm.trans f)
    rw [← (Prod.mk.inj e).1]
    exact w
  | n + 1, hn, t, R', C', f => by
    obtain ⟨u, Ru, Cu, fu⟩ := fold_back (k := 14 * l + j + 2 + n) f
    have wu := hear_along hS hR O hl h1 h24 f₁ w n (by omega) u Ru Cu fu
    have hlen : c.blocksInOrder.length = 358 := by
      rw [← List.length_map (f := (·.place)), IM.places_scope hS hR O, IM.places_len]
    have h9 : IM.nAt l ≤ 9 := by
      unfold IM.nAt
      split <;> omega
    obtain ⟨b, hb⟩ : ∃ b, c.blocksInOrder[14 * l + j + 2 + n]? = some b :=
      ⟨_, List.getElem?_eq_getElem (by omega : 14 * l + j + 2 + n < c.blocksInOrder.length)⟩
    obtain ⟨rs, gs, d⟩ := fold_next hb fu f
    have hb' : c.blocksInOrder[14 * l + (j + n) + 2]? = some b := by
      rwa [show 14 * l + (j + n) + 2 = 14 * l + j + 2 + n by omega]
    exact hear_carries hS hR O hl (by omega) (by omega) (fun e => by have := h24 e; omega) hb' d wu

end Meaning.K2

#print axioms Meaning.K2.hearKinds_fit
#print axioms Meaning.K2.hearKinds_bent_fails
#print axioms Meaning.K2.hear_carries
#print axioms Meaning.K2.hear_along
