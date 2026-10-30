-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K9/TrLot.lean: BETWEEN A SEGMENT's OPENING AND ITS BATCHING NOTHING TURNS WHAT THE DRAW WILL TEST:
in the goals' scope, at each of the 25 segments of the first chain: every sub-protocol of the segment in front of the batching,
but its first (at the head's segment: but its first two), is `KeepsTr` (Honest/K9/TrAre.lean) at every accepting decision; and
so is the stretch of them, along the fold.

  `tr_lot`       a sub-protocol of the description's lots of one of the six kinds K3, K4, K5, K6, K8, K11
  `k1Reads_tr`   K1's sending of the reads with the step without a round behind it
  **`hear_keepsT`**   the sub-protocol number 14 l + i + 2 of the flat list, 1 ≤ i < `IM.nAt l` (2 ≤ i at l = 24)
  **`hear_backT`**    from the border 14 l + j + 2 to every later border up to the batching's, in the fold's form

How. The cut by kinds and by places is the library's (`IM.quiet_lot`, Johnson/IMR/QuietLot.lean; `hear_carries` and
`hear_along`, Johnson/IMR/WaitsInLink.lean), with the relation exchanged.

One of nine files (Honest/K9/TrAre.lean, TrFl, TrWalk, TrK4, TrK5, TrK6, TrSeated, TrVia, TrLot) that say of the sub-protocols
which stand between a segment's opening and its batching: an accepting decision leaves the ledger's arrays, but for the mark
"the commitment is received" (`tr`), and what the batching's draw will test of the segment's book-keeping (`lnk`). They are the
nine files Honest/K9/TrAre.lean to TrLot.lean, carried over by program from the reading `tr` to the reading `tr`, name by name;
these in turn carry the library's own walk for the ledger's two numbers (Johnson/Desc/First/Link/Law/FlSlots.lean and the files
Slots*.lean beside it).

Limits. In the goals' scope, at the hash function `secondHashFunction`. Nothing at a segment's first sub-protocol. It shows of no state that
it is reached. This file proves no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K9.TrVia
import Johnson.Desc.ProofFile.Honest.K9.CrLot
import Johnson.IMR.WaitsInLink

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open VerifiableInference.Desc.Keeps (Whole Decides)
open VerifiableInference.Desc.LinkJoin
open Meaning.K2
open ProofFile (Cl)

/-- **A sub-protocol of the lots of one of the six kinds.** -/
theorem tr_lot {Z : ProofFile.Pub} {G : ProofFile.Ground} {L : ProofFile.Lot} (hL : L ∈ ProofFile.onlineFirstChainBlockTables Z)
    {b' : Block S Cl} (hb : b' ∈ L.blocks G) (hk : IM.quietMaker b'.place.kind = true) :
    Decides KeepsTr b' := by
  have hc : ∀ {L' : ProofFile.Lot}, L = L' → (L'.own G = []) → b' ∈ L'.hearC G := by
    rintro L' rfl ho
    rcases IM.blocks_mem hb with ⟨x, hx, -⟩ | h
    · rw [ho] at hx
      cases hx
    · exact h
  cases hkk : b'.place.kind <;> rw [hkk] at hk <;> (try exact absurd hk (by decide))
  · have h := hc (IM.lot_of_kind hL hb (by rw [hkk]; rfl)) rfl
    exact (theStated_wholeT _ _ _ _ _ _ (IM.k3Hear_mem h)).1
  · have h := hc (IM.lot_of_kind hL hb (by rw [hkk]; rfl)) rfl
    obtain ⟨x, -, rfl⟩ := List.mem_map.1 h
    exact fun s rs gs t d => k4C_stepsT { x.2 with k3Runs := true } s rs gs t d
  · have h := hc (IM.lot_of_kind hL hb (by rw [hkk]; rfl)) rfl
    obtain ⟨l, Xl, b₀, -, -, e, rfl⟩ := IM.k5OwnN_mem h
    exact fun s rs gs t d => k5_steps_atT e s rs gs t d
  · have h := hc (IM.lot_of_kind hL hb (by rw [hkk]; rfl)) rfl
    have h' : b' ∈ ((P4.headBefore Z G).bind fun ms =>
        VerifiableInference.Desc.Kinds.Head.seatedClaims G.W (G.built.size - 1) ms).toList := h
    rw [Option.mem_toList] at h'
    obtain ⟨ms, -, hsc⟩ := Option.bind_eq_some_iff.1 h'
    exact fun s rs gs t d => k6_steps_seatedT hsc s rs gs t d
  · have h := hc (IM.lot_of_kind hL hb (by rw [hkk]; rfl)) rfl
    obtain ⟨l, Xl, -, rfl⟩ := IM.k8Whole_mem h
    exact fun s rs gs t d => k8W_stepsT _ s rs gs t d
  · have h := hc (IM.lot_of_kind hL hb (by rw [hkk]; rfl)) rfl
    obtain rfl := List.mem_singleton.1 h
    exact fun s rs gs t d => k11_stepsT _ s rs gs t d

/-- K1's sending of the reads, with the step without a round behind it. -/
theorem k1Reads_tr {Z : ProofFile.Pub} (G : ProofFile.Ground) (l : Nat) (X : Stages.LinkH) (pr : Nat)
    (reads : Option (List Nat)) : Decides KeepsTr (IM.k1Reads Z G l X pr reads) :=
  fun s rs gs t h => by
    obtain ⟨v, a1, a2⟩ := andThen_yes h
    exact keeps_transT _ _ _ (k1_stepsT _ _ _ _ s _ _ v a1)
      ((orLoud_whole fun b hb => readsQuietAt_wholeT hb).1 v _ _ t a2)

variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **Every sub-protocol of a segment in front of its batching, but the first, and but the head's second.** -/
theorem hear_keepsT (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l i : ℕ} (hl : l < 25)
    (h1 : 1 ≤ i) (hi : i < IM.nAt l) (h24 : l = 24 → 2 ≤ i) {b : Block S Cl}
    (hb : c.blocksInOrder[14 * l + i + 2]? = some b) : Decides KeepsTr b := by
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
      intro s rs gs t d
      have d' := ((IM.yes_alone hla
        (by show k ≠ KindName.K7; rintro rfl; exact absurd hq (by decide)) s t rs gs).1 d).1
      exact tr_lot hL hb' (by rw [ep]; exact hq) s rs gs t d'
    · obtain rfl : k = KindName.K1 := by
        cases k <;> first | rfl | exact absurd hq (by decide)
      obtain ⟨Lk, b₁, Xl, pr, pd, reads, digits, e1, e2, -, -, harm⟩ :=
        IM.k1_later O l (IM.subAt l) (IM.subs_scope hS hR O l hl) i hk ⟨by omega, h9⟩
      have ib : c.blocksInOrder[14 * l + i + 2]? = some b₁ := by
        have q := IM.hear_at_flat e1 e2
        rwa [IM.flatIx_scope hS hR O (by omega : l ≤ 24) i] at q
      obtain rfl : b = b₁ := Option.some.inj (hb.symm.trans ib)
      rcases harm with ⟨-, la⟩ | ⟨-, la⟩
      · exact alone_dec (by intro k; cases k) la
          (fun s rs gs t h => k1Reads_tr _ _ _ _ _ s rs gs t h)
      · exact alone_dec (by intro k; cases k) la
          (fun s rs gs t h => k1Later_stepsT (Cl := Unit) _ _ _ _ _ _ s rs gs t h)

/-- **Along a segment's sub-protocols**, from the border 14 l + j + 2 to every later border up to the batching's; j ≥ 1,
and j ≥ 2 at the head's segment. In the fold's form. -/
theorem hear_backT (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l j : ℕ} (hl : l < 25)
    (h1 : 1 ≤ j) (h24 : l = 24 → 2 ≤ j) {s : S} {R : List Fmt.RoundView}
    {C : List VerifiableInference.Desc.OpenedColumn} {t₁ : S} {R₁ : List Fmt.RoundView}
    {C₁ : List VerifiableInference.Desc.OpenedColumn}
    (f₁ : foldBlocks 0 (c.blocksInOrder.take (14 * l + j + 2)) s R C = .ok (t₁, R₁, C₁)) :
    ∀ n, j + n ≤ IM.nAt l → ∀ (t : S) (R' : List Fmt.RoundView) (C' : List VerifiableInference.Desc.OpenedColumn),
      foldBlocks 0 (c.blocksInOrder.take (14 * l + j + 2 + n)) s R C = .ok (t, R', C') →
      KeepsTr t₁ t
  | 0, _, t, R', C', f => by
    have e : (t₁, R₁, C₁) = (t, R', C') := Except.ok.inj (f₁.symm.trans f)
    rw [← (Prod.mk.inj e).1]
    exact keeps_reflT _
  | n + 1, hn, t, R', C', f => by
    obtain ⟨u, Ru, Cu, fu⟩ := fold_back (k := 14 * l + j + 2 + n) f
    have wu := hear_backT hS hR O hl h1 h24 f₁ n (by omega) u Ru Cu fu
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
    exact keeps_transT _ _ _ wu
      (hear_keepsT hS hR O hl (by omega) (by omega) (fun e => by have := h24 e; omega) hb' u rs gs t d)

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.tr_lot
#print axioms ProofFile.Honest.K9.k1Reads_tr
#print axioms ProofFile.Honest.K9.hear_keepsT
#print axioms ProofFile.Honest.K9.hear_backT
