-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K9/MomLot.lean: HOW MANY MOMENTS OF A SEGMENT HAVE PASSED IN FRONT OF ITS BATCHING: in the goals'
scope, at each of the 25 segments of the first chain: every sub-protocol of the segment in front of the batching, but its first
(at the head's segment: but its first two), leaves the book-keeping's count of moments, or, if it is a sending (kind K1), raises
it by one; so along the stretch it rises by the number of sendings; and with the one moment that the opening counts that is the
number of moments which the full size's shape gives the segment.

  `KeepsM d s s'`   where book-keeping is open at s', it is open at s, and the count behind is the count in front and d
  `keepsM_quiet`, `keepsM_trans`, `keepsM_commit`, `k1Reads_m`
  `k1At l i`, `k1From l j n`   1 where the written list of kinds has K1 at place i of segment l; their sum over j ≤ i < j + n
  **`hear_moment`**   the sub-protocol number 14 l + i + 2 of the flat list, 1 ≤ i < `IM.nAt l` (2 ≤ i at l = 24)
  **`hear_moments`**  along the fold
  `momentsB`, **`moments_all`**, `moments_at`   the closed test at the full size's shape, by Lean's kernel, and what it gives at
                        one segment

How. The cut by kinds and by places is the library's (`hear_carries`, `hear_along`: Johnson/IMR/WaitsInLink.lean); the quiet
kinds by `IM.quiet_lot` and `quiet_back` (Johnson/IMR/ListsAtDraw.lean); a sending by `K1.commitAtS_moments`
(Johnson/Desc/K1/Law/LinkAtLater.lean).

Limits. In the goals' scope, at the hash function `secondHashFunction`; the closed test at the full size's shape alone. It shows of no state
that it is reached. This file proves no property of a prover or a protocol.
-/
import Johnson.IMR.WaitsInLink
import Johnson.IMR.ListsAtDraw
import Johnson.Desc.K1.Law.LinkAtLater
import Johnson.Desc.ReqLit.Full

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open VerifiableInference.Desc.Keeps (Whole Decides)
open VerifiableInference.Desc.ReqLit (shapeFull)
open Meaning.K2
open ProofFile (Cl)

/-- Where book-keeping is open behind, it is open in front, and the count of moments has risen by d. -/
def KeepsM (d : ℕ) (s s' : S) : Prop :=
  ∀ L', s'.link? = some L' → ∃ L, s.link? = some L ∧ L'.moments = L.moments + d

theorem keepsM_refl (s : S) : KeepsM 0 s s := fun L h => ⟨L, h, rfl⟩

theorem keepsM_trans {a b : ℕ} {s t u : S} (h : KeepsM a s t) (k : KeepsM b t u) : KeepsM (a + b) s u := by
  intro L'' h2
  obtain ⟨L', h1, e1⟩ := k L'' h2
  obtain ⟨L, h0, e0⟩ := h L' h1
  exact ⟨L, h0, by omega⟩

theorem keepsM_quiet {s t : S} (q : Quiet s t) : KeepsM 0 s t := by
  intro L' h
  obtain ⟨L, h1, -, e, -⟩ := quiet_back q h
  exact ⟨L, h1, e⟩

theorem keepsM_commit {Cl' : Type} (P : K1.Par) (link moment : Nat) (arrays : Option (List Nat)) :
    Decides (KeepsM 1) (K1.commitAtS P link moment arrays : Block S Cl') := by
  intro s rs gs s' h L'' h2
  obtain ⟨L, L', a, b, e, -⟩ := K1.commitAtS_moments P link moment arrays s s' rs gs h
  obtain rfl : L' = L'' := Option.some.inj (b.symm.trans h2)
  exact ⟨L, a, e⟩

/-- K1's sending of the reads, with the step without a round behind it. -/
theorem k1Reads_m {Z : ProofFile.Pub} (G : ProofFile.Ground) (l : Nat) (X : Stages.LinkH) (pr : Nat)
    (reads : Option (List Nat)) : Decides (KeepsM 1) (IM.k1Reads Z G l X pr reads) :=
  fun s rs gs t h => by
    obtain ⟨v, a1, a2⟩ := andThen_yes h
    exact keepsM_trans (a := 1) (b := 0) (keepsM_commit _ _ _ _ s _ _ v a1)
      (keepsM_quiet ((orLoud_whole fun b hb => readsQuietAt_quiet hb).1 v _ _ t a2))

/-- 1 where the written list of kinds has a sending at place i of segment l. -/
def k1At (l i : ℕ) : ℕ :=
  if ((kindsBeforeBatching (IM.subAt l) (l == 0))[i]?).any (· == KindName.K1) then 1 else 0

/-- The number of sendings at the places j ≤ i < j + n. -/
def k1From (l j : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => k1From l j n + k1At l (j + n)

variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **Every sub-protocol of a segment in front of its batching, but the first, and but the head's second.** -/
theorem hear_moment (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l i : ℕ} (hl : l < 25)
    (h1 : 1 ≤ i) (hi : i < IM.nAt l) (h24 : l = 24 → 2 ≤ i) {b : Block S Cl}
    (hb : c.blocksInOrder[14 * l + i + 2]? = some b) : Decides (KeepsM (k1At l i)) b := by
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
    · have hk1 : (k == KindName.K1) = false := by
        cases k <;> first | rfl | exact absurd hq (by decide)
      have e0 : k1At l i = 0 := by
        unfold k1At
        rw [hk, Option.any_some, hk1]
        rfl
      rw [e0]
      obtain ⟨Lk, b₁, e1, e2, sp, -, L, hL, b', hb', -, ep, hla⟩ :=
        IM.chain_hear_alone O.made O.places O.chain l (IM.subAt l) (IM.subs_scope hS hR O l hl) i k
          hk (by rintro rfl; exact absurd hq (by decide))
          (by rintro rfl; exact absurd hq (by decide)) ⟨by omega, h9⟩
      have ib : c.blocksInOrder[14 * l + i + 2]? = some b₁ := by
        have q := IM.hear_at_flat e1 e2
        rwa [IM.flatIx_scope hS hR O (by omega : l ≤ 24) i] at q
      obtain rfl : b = b₁ := Option.some.inj (hb.symm.trans ib)
      intro s rs gs t d
      have d' := ((IM.yes_alone hla
        (by show k ≠ KindName.K7; rintro rfl; exact absurd hq (by decide)) s t rs gs).1 d).1
      exact keepsM_quiet (IM.quiet_lot hL hb' (by rw [ep]; exact hq) s rs gs t d')
    · obtain rfl : k = KindName.K1 := by
        cases k <;> first | rfl | exact absurd hq (by decide)
      have e1' : k1At l i = 1 := by
        unfold k1At
        rw [hk]
        rfl
      rw [e1']
      obtain ⟨Lk, b₁, Xl, pr, pd, reads, digits, e1, e2, -, -, harm⟩ :=
        IM.k1_later O l (IM.subAt l) (IM.subs_scope hS hR O l hl) i hk ⟨by omega, h9⟩
      have ib : c.blocksInOrder[14 * l + i + 2]? = some b₁ := by
        have q := IM.hear_at_flat e1 e2
        rwa [IM.flatIx_scope hS hR O (by omega : l ≤ 24) i] at q
      obtain rfl : b = b₁ := Option.some.inj (hb.symm.trans ib)
      rcases harm with ⟨-, la⟩ | ⟨-, la⟩
      · exact fun s rs gs t h => k1Reads_m _ _ _ _ _ s rs gs t
          ((IM.yes_alone la (by intro k; cases k) s t rs gs).1 h).1
      · exact fun s rs gs t h => keepsM_commit (Cl' := Unit) _ _ _ _ s rs gs t
          ((IM.yes_alone la (by intro k; cases k) s t rs gs).1 h).1

/-- **Along a segment's sub-protocols**, in the fold's form. -/
theorem hear_moments (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l j : ℕ} (hl : l < 25)
    (h1 : 1 ≤ j) (h24 : l = 24 → 2 ≤ j) {s : S} {R : List Fmt.RoundView}
    {C : List VerifiableInference.Desc.OpenedColumn} {t₁ : S} {R₁ : List Fmt.RoundView}
    {C₁ : List VerifiableInference.Desc.OpenedColumn}
    (f₁ : foldBlocks 0 (c.blocksInOrder.take (14 * l + j + 2)) s R C = .ok (t₁, R₁, C₁)) :
    ∀ n, j + n ≤ IM.nAt l → ∀ (t : S) (R' : List Fmt.RoundView) (C' : List VerifiableInference.Desc.OpenedColumn),
      foldBlocks 0 (c.blocksInOrder.take (14 * l + j + 2 + n)) s R C = .ok (t, R', C') →
      KeepsM (k1From l j n) t₁ t
  | 0, _, t, R', C', f => by
    have e : (t₁, R₁, C₁) = (t, R', C') := Except.ok.inj (f₁.symm.trans f)
    rw [← (Prod.mk.inj e).1]
    exact keepsM_refl _
  | n + 1, hn, t, R', C', f => by
    obtain ⟨u, Ru, Cu, fu⟩ := fold_back (k := 14 * l + j + 2 + n) f
    have wu := hear_moments hS hR O hl h1 h24 f₁ n (by omega) u Ru Cu fu
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
    exact keepsM_trans wu
      (hear_moment hS hR O hl (by omega) (by omega) (fun e => by have := h24 e; omega) hb' u rs gs t d)

/-- The closed test: at each segment of the full size's shape: the one moment of the opening and the sendings behind it
are the shape's number of moments. -/
def momentsB : Bool :=
  (List.range 25).all fun l =>
    (shapeFull.link[l]?).any fun Lk =>
      reqMoments Lk == 1 + k1From l ((if l = 24 then 1 else 0) + 1) (IM.nAt l - ((if l = 24 then 1 else 0) + 1))

/-- It accepts: by Lean's kernel. -/
theorem moments_all : momentsB = true := by decide +kernel

theorem moments_at {l : ℕ} (hl : l < 25) :
    ((shapeFull.link[l]?).map reqMoments).getD 0 =
      1 + k1From l ((if l = 24 then 1 else 0) + 1) (IM.nAt l - ((if l = 24 then 1 else 0) + 1)) := by
  have k := List.all_eq_true.1 moments_all l (List.mem_range.2 hl)
  cases e : shapeFull.link[l]? with
  | none =>
    rw [e] at k
    cases k
  | some Lk =>
    rw [e, Option.any_some] at k
    exact beq_iff_eq.1 k

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.keepsM_refl
#print axioms ProofFile.Honest.K9.keepsM_trans
#print axioms ProofFile.Honest.K9.keepsM_quiet
#print axioms ProofFile.Honest.K9.keepsM_commit
#print axioms ProofFile.Honest.K9.k1Reads_m
#print axioms ProofFile.Honest.K9.hear_moment
#print axioms ProofFile.Honest.K9.hear_moments
#print axioms ProofFile.Honest.K9.moments_all
#print axioms ProofFile.Honest.K9.moments_at
