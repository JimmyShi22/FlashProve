-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/PricedRound.lean: from the planner's yes on a round to the clause on that round's
error count, below the Johnson radius: the counts of a link with records, of its batching and of a
chain of stages, each as a share of its round's typed values, are at most the numbers of
OnBytes/Params/EntryCovered.lean.

`held_round` (OnBytes/Slice/HeldRound.lean) says: if a round of a plan holds (its error, with the
planner's term for the distance from uniform of its draws, is at most 2 ^ (work - target)) and a
count, as a share of the round's typed values, is at most the round's error, then the count times
the sampler's number is at most 2 ^ -target of the round's written verifier messages, test bits
among them. It asks besides what `SetOK` and `RoundOK` carry here: the format's field, positions of
at most 64 bits, no more elements other than 0 than elements, and work + 66 ≤ target. The laws on
prices (OnBytes/Params/EntryCovered.lean and the files beneath it) bound real numbers by the errors.
This file joins the two. `PricedAt σ c e` says that some round with the entry e holds at the setting
σ and has an error of at least c. In a round with such a price a count of at most c times the number
of typed values meets the clause at 2 ^ -128 (`below_of_priced`). Then, count by count, the
library's natural number is at most the real number of OnBytes/Params/EntryCovered.lean times the
number of the round's typed values. q is the number of elements of the extension field.

Main definitions: `PricedAt`, `SetOK`, `RoundOK`, `Sg.AsGroup`, `Sz.AsTable`.
Main theorems.
 `below_of_priced`   the clause on one round's count, from a price.
 `priced_of_plan`    the rounds of a plan that holds are priced by numbers below their errors.
 `memb_err`, `cs_err1`   the number of a sample row with a pad is `clashSeeds`; in `cs_err1` it
                     stands under the factor (L choose 2).
 `point_share`, `send_share`, `loc_share`, `phi_share`, `bat_share_joh`   the link's four counts
                     and the batching's.
 `eps_share`, `fold_share`, `fold_share_mask`, `seed_share`, `cs_share`, `lambda_share`,
 `base_share`        the counts of a stage.
 `Chain.smallAt_lastAt`, `Chain.smallAt_stepMidAt`, `Chain.smallAt_stepEndAt`,
 `link_chain_below`  from the rounds' clauses to the clause on the list of counts in the conclusion
                     of `link_chain_joh` (OnBytes/Slice/LinkChainJoh.lean).

Not claimed. That any round has a price: `PricedAt` is a hypothesis here. That a radius is below the
Johnson radius: no law asks it. That a count bounds a prover's chance. That proof of work is worth
its bits: a share is a count among all strings of hash blocks and test bits. What the heads of
OnBytes/Slice/HeldRound.lean and of OnBytes/Params/EntryCovered.lean do not claim. No sum over the
rounds. For proofs only; the program, that is the Lean port built from OnBytes/, does not import
this file.

-/
import OnBytes.Params.HoldsLaws
import OnBytes.Slice.CsErr
import OnBytes.Slice.GroupFit
import OnBytes.Slice.HeldCounts
import OnBytes.Slice.KeyMsgCnt
import OnBytes.Slice.LinkChainJoh
import OnBytes.Slice.ManyNumLink

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Prob Cb Cb.Ood _root_.Run OnBytes.Params
open scoped ENNReal

/-! ## A price, and the clause on a count -/

/-- The number c is a price of a round with the entry e at the setting σ: some value of the type of
a plan's rounds has that entry, holds at σ, work counted, and has an error of at least c. -/
def PricedAt (σ : Setting) (c : ℝ) (e : Fmt.Entry) : Prop :=
  ∃ r : PlanRound, r.entry = e ∧ roundHolds σ (capped σ) r = true ∧ c ≤ ((r.error.val : ℚ) : ℝ)

/-- What is asked of the setting: the format's field and the target 128. -/
structure SetOK (σ : Setting) : Prop where
  /-- The base field. -/
  p : σ.p = 2 ^ 64 - 2 ^ 32 + 1
  /-- The extension's degree. -/
  degree : σ.degree = 3
  /-- The target, in bits. -/
  target : σ.target = 128

/-- The setting's extension field has as many elements as the library's. -/
theorem SetOK.card {σ : Setting} (h : SetOK σ) : σ.cardE = Fintype.card GE := by
  rw [card_GE]
  unfold Setting.cardE
  rw [h.p, h.degree]
  rfl

/-- What is asked of a written round: positions of at most 64 bits, no more elements other than 0
than elements, at most 62 bits of work. -/
structure RoundOK (d : PQ.RD) : Prop where
  /-- The bits of a position. -/
  log : d.entry.logN ≤ 64
  /-- The elements other than 0 are among the elements. -/
  nz : d.entry.drawNZ ≤ d.entry.drawE
  /-- The bits of work. -/
  work : d.entry.work + 66 ≤ 128

/-- **In a round with the price c, a count of at most c times the number N of the round's typed
values is at most 2 ^ -128 as a share of the round's written verifier messages**, test bits among
them: of the 128 bits, the round's bits of work are work. -/
theorem below_of_priced {σ : Setting} (hσ : SetOK σ) {d : PQ.RD} (hd : RoundOK d) {c : ℝ}
    (H : PricedAt σ c d.entry) (N : ℕ) (hN : nVals (Fmt.dsOf d.entry d.kind) = N) (count : ℕ)
    (h : (count : ℝ) ≤ c * (N : ℝ)) : RoundBelow count d ((2 : ℝ≥0∞)⁻¹ ^ 128) := by
  obtain ⟨r, he, hold, hc⟩ := H
  have hq : (count : ℚ) ≤ r.error.val * (nVals (Fmt.dsOf d.entry d.kind) : ℚ) := by
    have h1 : (count : ℝ) ≤ ((r.error.val : ℚ) : ℝ) * (N : ℝ) :=
      h.trans (mul_le_mul_of_nonneg_right hc (Nat.cast_nonneg _))
    rw [hN]
    exact_mod_cast h1
  have h2 := held_round σ hσ.p hσ.degree r d he.symm (by rw [he]; exact hd.log)
    (by rw [he]; exact hd.nz) (fun _ => by rw [he, hσ.target]; exact hd.work) hold count hq
  rw [hσ.target] at h2
  exact h2

/-- **The rounds of a plan that holds**: numbers that are at most the rounds' errors, place by
place, are prices of the rounds' entries. -/
theorem priced_of_plan {σ : Setting} {P : Planned} (hs : P.set = σ) (hh : P.holds = true)
    {cs : List ℝ}
    (hc : List.Forall₂ (fun (c : ℝ) (r : PlanRound) => c ≤ ((r.error.val : ℚ) : ℝ)) cs P.rounds) :
    List.Forall₂ (PricedAt σ) cs (P.rounds.map (·.entry)) := by
  have hr : ∀ r ∈ P.rounds, roundHolds σ (capped σ) r = true := by
    unfold Planned.holds at hh
    simp only [Bool.and_eq_true] at hh
    have h1 := hh.1.1
    unfold Planned.roundsHold at h1
    rw [hs] at h1
    exact fun r hr => List.all_eq_true.mp h1 r hr
  exact List.forall₂_map_right_iff.mpr
    (forall₂_weaken hc fun c r hm h => ⟨r, rfl, hr r hm, h⟩)

/-! ## Arithmetic, in variables -/

/-- A count as a share K / q, from a comparison of natural numbers. -/
theorem real_share {count K N q : ℕ} (hq : 0 < q) (h : count * q ≤ K * N) :
    (count : ℝ) ≤ (K : ℝ) / (q : ℝ) * (N : ℝ) := by
  rw [div_mul_eq_mul_div, le_div_iff₀ (by exact_mod_cast hq)]
  exact_mod_cast h

/-- m^i n^j of n^(i + j) is the share (m / n)^i. -/
theorem pos_share_left (m n i j : ℕ) (hn : 0 < n) :
    ((m ^ i * n ^ j : ℕ) : ℝ) = ((m : ℝ) / (n : ℝ)) ^ i * ((n ^ (i + j) : ℕ) : ℝ) := by
  have h0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  push_cast
  rw [div_pow, pow_add]
  field_simp

/-- n^i m^j of n^(i + j) is the share (m / n)^j. -/
theorem pos_share_right (m n i j : ℕ) (hn : 0 < n) :
    ((n ^ i * m ^ j : ℕ) : ℝ) = ((m : ℝ) / (n : ℝ)) ^ j * ((n ^ (i + j) : ℕ) : ℝ) := by
  have h0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  push_cast
  rw [div_pow, pow_add]
  field_simp

/-- The count of a round that draws t positions and one element, as a share. -/
theorem cs_real (X n t q L R : ℕ) (hn : 0 < n) (hq : 0 < q) :
    ((X ^ t * q + n ^ t * (L * R) : ℕ) : ℝ) =
      (((X : ℝ) / (n : ℝ)) ^ t + (L : ℝ) * (R : ℝ) / (q : ℝ)) * ((n ^ t * q : ℕ) : ℝ) := by
  have h0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have h1 : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  push_cast
  rw [div_pow]
  field_simp

/-- The count of a link's fold point: (v + (v b1 + l1 v) + (v b0 + l0 v)) q^(v - 1) of q^v. -/
theorem fold_point_num (v b0 b1 l0 l1 q : ℕ) (hv : 0 < v) :
    (v * b0 * q ^ (v - 1) + l0 * (v * q ^ (v - 1)) +
        (v * b1 * q ^ (v - 1) + l1 * (v * q ^ (v - 1))) + v * q ^ (v - 1)) * q ≤
      (v + (v * b1 + l1 * v) + (v * b0 + l0 * v)) * q ^ v := by
  obtain ⟨w, rfl⟩ : ∃ w, v = w + 1 := ⟨v - 1, by omega⟩
  rewrite [Nat.add_sub_cancel]
  exact le_of_eq (by ring)

/-- The typed values of a seed of m coordinates and a factor other than 0. -/
theorem nVals_seed (m : ℕ) :
    nVals (List.replicate m Fmt.Draw.elem ++ [.elemNZ, .trits 0]) =
      Fintype.card GE ^ m * (Fintype.card GE - 1) := by
  rw [nVals_repE, card_GE]
  simp only [nVals, pow_zero, mul_one]

/-- There is a field element other than 0. -/
theorem card_GE_pred_pos : 0 < Fintype.card GE - 1 :=
  Nat.sub_pos_of_lt (lt_of_lt_of_le (by decide) card_GE_big)

/-! ## Seeds -/

/-- The number of the sample of a folded row's oracle message. -/
theorem memb_err (S : Sz) :
    S.memb.om.Z.err = clashSeeds (Fintype.card GE) (S.P.aR + S.P.aP) := by
  have h : S.memb.om.Z.err = max (Fintype.card (Fin (S.P.aR + S.P.aP)) *
      Fintype.card GE ^ (Fintype.card (Fin (S.P.aR + S.P.aP)) - 1) * Fintype.card GEˣ)
      (Fintype.card GE ^ Fintype.card (Fin (S.P.aR + S.P.aP))) := rfl
  rw [h, Fintype.card_fin, card_units_GE]
  rfl

/-- The count of a code switch's first round, in which the sample's seed is drawn. -/
theorem cs_err1 {s s' : Sg} (hf : CsFit s s') (L : ℕ) :
    (csSw hf).W.err1 L = L.choose 2 * clashSeeds (Fintype.card GE) s'.st.na := by
  have h : (csSw hf).W.err1 L = L.choose 2 * max (Fintype.card (Fin s'.st.na) *
      Fintype.card GE ^ (Fintype.card (Fin s'.st.na) - 1) * Fintype.card GEˣ)
      (Fintype.card GE ^ Fintype.card (Fin s'.st.na)) := rfl
  rw [h, Fintype.card_fin, card_units_GE]
  rfl

/-- (L choose 2) clashing seeds of one answer, as a share of all seeds. -/
theorem seeds_real {σ : Setting} (hσ : SetOK σ) (L cube : ℕ) :
    ((L.choose 2 * clashSeeds (Fintype.card GE) cube : ℕ) : ℝ) =
      seedsShare σ L cube 1 *
        ((Fintype.card GE ^ cube * (Fintype.card GE - 1) : ℕ) : ℝ) := by
  have hpos : (0 : ℝ) < ((Fintype.card GE ^ cube * (Fintype.card GE - 1) : ℕ) : ℝ) := by
    exact_mod_cast Nat.mul_pos (Nat.pow_pos card_GE_pos) card_GE_pred_pos
  unfold seedsShare allSeeds
  rw [hσ.card, pow_one, pow_one, div_mul_cancel₀ _ hpos.ne']

/-! ## The link's rounds -/

/-- The sizes S have the planner's table T: fold variables, length, k and distance. -/
structure Sz.AsTable (S : Sz) (T : TableSize) : Prop where
  /-- The fold variables. -/
  v : T.v = S.P.v
  /-- There is one. -/
  pos : 0 < S.P.v
  /-- The length. -/
  n : (wordOf T.code).n = 2 ^ S.P.T.a
  /-- The dimension less 1. -/
  k : (wordOf T.code).k = S.P.T.r + S.P.T.l - 1
  /-- The distance. -/
  d : 2 ^ S.P.T.a - (S.P.T.r + S.P.T.l - 1) = S.dT

/-- The first round: the fold's point. The numbers v, e0, e1 are letters with equations, here and
below, so that whoever applies a law at written numbers compares no two spellings of a power of the
field's size. -/
theorem point_share {σ : Setting} (hσ : SetOK σ) {S : Sz} {T : TableSize} (A : S.AsTable T)
    {v e0 e1 : ℕ} (hv : S.P.v = v) (h0 : S.e0 = e0) (h1 : S.e1 = e1) :
    ((S.lk.errGam (S.badJ S.e0) (S.badJ S.e1) : ℕ) : ℝ) ≤
      linkPointCount σ T e1 e0 * ((Fintype.card GE ^ v : ℕ) : ℝ) := by
  subst hv h0 h1
  unfold linkPointCount
  rw [hσ.card, A.v, A.n, A.k, A.d]
  refine real_share card_GE_pos ?_
  rewrite [errGam_eq]
  unfold Sz.badJ
  exact fold_point_num _ _ _ _ _ _ A.pos

/-- The second round: the seed of the two folded rows' samples, at lists of at most L. -/
theorem send_share {σ : Setting} (hσ : SetOK σ) (S : Sz) (L : ℕ) {c : ℕ}
    (hc : S.P.aR + S.P.aP = c) :
    ((ldSendFamErr S.lk.N S.seeds (fun _ => L) : ℕ) : ℝ) ≤
      2 * seedsShare σ L c 1 * ((Fintype.card GE ^ c * (Fintype.card GE - 1) : ℕ) : ℝ) := by
  subst hc
  have h : ldSendFamErr S.lk.N S.seeds (fun _ => L) =
      2 * (L.choose 2 * clashSeeds (Fintype.card GE) (S.P.aR + S.P.aP)) := by
    rw [← memb_err]
    unfold ldSendFamErr
    show ∑ _a : Bool, 1 * (L.choose 2 * S.memb.om.Z.err) = _
    rw [Fintype.sum_bool]
    ring
  rw [h, mul_assoc, ← seeds_real hσ]
  push_cast
  exact le_rfl

/-- The fourth round: the positions at which the two folds are tested. -/
theorem loc_share {S : Sz} {T : TableSize} (A : S.AsTable T) {a e0 e1 n0 nj : ℕ}
    (ha : S.P.T.a = a) (h0 : S.e0 = e0) (h1 : S.e1 = e1) (hn0 : S.P.nu0 = n0)
    (hnj : S.P.nuj = nj) :
    ((S.lk.errLoc : ℕ) : ℝ) ≤
      linkPositionsShare T e0 e1 n0 nj * (((2 ^ a) ^ (n0 + nj) : ℕ) : ℝ) := by
  subst ha h0 h1 hn0 hnj
  have hn : 0 < 2 ^ S.P.T.a := Nat.two_pow_pos _
  have hN : (0 : ℝ) ≤ (((2 ^ S.P.T.a) ^ (S.P.nu0 + S.P.nuj) : ℕ) : ℝ) := Nat.cast_nonneg _
  unfold linkPositionsShare
  rw [errLoc_eq, A.n, Nat.cast_max]
  refine max_le ?_ ?_
  · rw [pos_share_left _ _ _ _ hn]
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) hN
  · rw [pos_share_right _ _ _ _ hn]
    exact mul_le_mul_of_nonneg_right (le_max_right _ _) hN

/-- The fifth round: the point at which the compared entries are joined. -/
theorem phi_share {σ : Setting} (hσ : SetOK σ) (S : Sz) {l : ℕ} (hl : S.P.aPhi = l) :
    ((S.lk.errPhi : ℕ) : ℝ) ≤ ((l : ℕ) : ℝ) / (σ.cardE : ℝ) *
      ((Fintype.card GE ^ l : ℕ) : ℝ) := by
  subst hl
  rw [hσ.card, errPhi_eq]
  exact real_share card_GE_pos (phi_num_any _ _)

/-! ## The batching and a stage's rounds -/

/-- The stage s has the sizes of the planner's group g, its distance is its main rows', and the
repeated mask code's k is as the library counts it. -/
structure Sg.AsGroup (s : Sg) (g : GroupSize) : Prop where
  /-- The sizes. -/
  fits : s.FitsGroup g
  /-- The sizes are in order. -/
  sized : s.Sized
  /-- Each code has a coefficient. -/
  pos : s.Pos
  /-- The stage's distance is that of its main rows. -/
  d : s.d = s.dC
  /-- The planner's k of the repeated mask code: the number of copies times the mask code's
  dimension less 1. -/
  kz : (repeated g.mask g.main.logN).k = 2 ^ (s.C.a - s.Z.a) * (s.Z.r + s.Z.l - 1)

namespace Sg.AsGroup
variable {s : Sg} {g : GroupSize}

/-- The list of the main code. -/
theorem lst (A : s.AsGroup g) (e : ℕ) :
    listMax (wordOf g.main).n ((wordOf g.main).n - (wordOf g.main).k) e = s.lstJ e := by
  unfold Sg.lstJ
  rw [A.fits.main_dist A.sized A.pos, A.fits.main_n, A.d]

/-- The count for the main rows. -/
theorem flC (A : s.AsGroup g) (e : ℕ) :
    ⌊bchksBound (wordOf g.main).n (wordOf g.main).k e⌋₊ = s.flC e := by
  unfold Sg.flC
  rw [A.fits.main_n, show (wordOf g.main).k = g.main.k from rfl, A.fits.main_k A.pos]

/-- The count for a table of mask rows. -/
theorem flZ (A : s.AsGroup g) (e : ℕ) :
    ⌊bchksBound (wordOf g.main).n (repeated g.mask g.main.logN).k e⌋₊ +
      listMax (wordOf g.main).n ((wordOf g.main).n - (repeated g.mask g.main.logN).k) e =
        s.flZ e := by
  have h := A.fits.mask_dist A.sized A.pos
  rw [A.fits.mask_n A.sized] at h
  unfold Sg.flZ
  rw [A.fits.main_n, h, A.kz]

end Sg.AsGroup

variable {σ : Setting} {s : Sg} {g : GroupSize}

/-- The batching of rows rows, at the list of the group's stage. -/
theorem bat_share_joh (hσ : SetOK σ) (A : s.AsGroup g) (e rows : ℕ) :
    ((s.lstJ e * (rows - 1) : ℕ) : ℝ) ≤
      (groupList g e : ℝ) * ((rows - 1 : ℕ) : ℝ) / (σ.cardE : ℝ) *
        ((Fintype.card GE : ℕ) : ℝ) := by
  have h := real_share (count := s.lstJ e * (rows - 1)) (K := s.lstJ e * (rows - 1))
    (N := Fintype.card GE) card_GE_pos le_rfl
  unfold groupList
  rw [hσ.card, A.lst]
  rw [Nat.cast_mul] at h ⊢
  exact h

/-- A fold's first round. -/
theorem eps_share (hσ : SetOK σ) (A : s.AsGroup g) (e : ℕ) :
    ((s.lstJ e : ℕ) : ℝ) ≤ (groupList g e : ℝ) / (σ.cardE : ℝ) * ((Fintype.card GE : ℕ) : ℝ) := by
  unfold groupList
  rw [hσ.card, A.lst]
  exact real_share card_GE_pos le_rfl

/-- A fold's round number j in which no mask row is folded. -/
theorem fold_share (hσ : SetOK σ) (A : s.AsGroup g) (e j : ℕ)
    (hj : (g.hasMask && decide (j ≤ g.h)) = false) :
    ((s.flC e + s.lstJ e * 2 : ℕ) : ℝ) ≤ foldCount σ g e j * ((Fintype.card GE : ℕ) : ℝ) := by
  unfold foldCount
  rw [hj, if_neg (by decide), hσ.card, A.lst, A.flC]
  exact real_share card_GE_pos le_rfl

/-- A fold's round number j in which mask rows are folded too. -/
theorem fold_share_mask (hσ : SetOK σ) (A : s.AsGroup g) (e j : ℕ)
    (hj : (g.hasMask && decide (j ≤ g.h)) = true) :
    ((s.flC e + (s.flZ e + s.flZ e) + s.lstJ e * 2 : ℕ) : ℝ) ≤
      foldCount σ g e j * ((Fintype.card GE : ℕ) : ℝ) := by
  unfold foldCount
  rw [if_pos hj, hσ.card, A.lst, A.flC, A.flZ]
  exact real_share card_GE_pos (Nat.mul_le_mul_right _ (le_of_eq
    ((Nat.add_right_comm _ _ _).trans (congrArg _ (Nat.two_mul _).symm))))

/-- A code switch's first round: the seed of the sample of the next stage's message, at that stage's
list. -/
theorem seed_share (hσ : SetOK σ) {s' : Sg} {g' : GroupSize} (A' : s'.AsGroup g')
    (hf : CsFit s s') (e' : ℕ) {c : ℕ} (hc : s'.st.na = c) :
    (((csSw hf).W.err1 (s'.lstJ e') : ℕ) : ℝ) ≤ seedsShare σ (groupList g' e') c 1 *
      ((Fintype.card GE ^ c * (Fintype.card GE - 1) : ℕ) : ℝ) := by
  subst hc
  unfold groupList
  rw [cs_err1, A'.lst, seeds_real hσ]

/-- A code switch's second round: the positions and the batching's element. -/
theorem cs_share (hσ : SetOK σ) (A : s.AsGroup g) {s' : Sg} {g' : GroupSize}
    (A' : s'.AsGroup g') (hf : CsFit s s') (e e' rows : ℕ) {a t : ℕ} (ha : s.C.a = a)
    (ht : s.t = t) (hr : rows - 1 = 1 + 3 * t) :
    (((csSw hf).W.err2 e (s'.lstJ e') : ℕ) : ℝ) ≤
      (positionsShare g e t + (groupList g' e' : ℝ) * ((rows - 1 : ℕ) : ℝ) / (σ.cardE : ℝ)) *
        (((2 ^ a) ^ t * Fintype.card GE : ℕ) : ℝ) := by
  subst ha ht
  unfold groupList positionsShare
  rw [cs_err2, A'.lst, A.fits.main_n, hσ.card, hr,
    cs_real _ _ _ _ _ _ (Nat.two_pow_pos _) card_GE_pos]

/-- The last step's first round. -/
theorem lambda_share (hσ : SetOK σ) (A : s.AsGroup g) (e : ℕ) :
    ((s.flC e + s.flZ e + s.lstJ e : ℕ) : ℝ) ≤
      lastStepCount σ g e * ((Fintype.card GE : ℕ) : ℝ) := by
  unfold lastStepCount
  rw [hσ.card, A.lst, A.flC, A.flZ]
  exact real_share card_GE_pos (Nat.mul_le_mul_right _ (le_of_eq (Nat.add_right_comm _ _ _)))

/-- The last step's second round: the positions. -/
theorem base_share (A : s.AsGroup g) (e : ℕ) {a t : ℕ} (ha : s.C.a = a) (ht : s.t = t) :
    (((2 ^ s.C.a - e - 1) ^ s.t : ℕ) : ℝ) ≤ positionsShare g e t * (((2 ^ a) ^ t : ℕ) : ℝ) := by
  subst ha ht
  have h := pos_share_left (2 ^ s.C.a - e - 1) (2 ^ s.C.a) s.t 0 (Nat.two_pow_pos _)
  unfold positionsShare
  rw [A.fits.main_n]
  rw [pow_zero, mul_one, Nat.add_zero] at h
  exact le_of_eq h

/-! ## From the rounds to the list of counts -/

namespace Chain
variable {L mC mS mW : Sg → ℕ → ℕ} {εs : ℝ≥0∞}

/-- `SmallAt` of a base case. -/
theorem smallAt_lastAt {s : Sg} {e : ℕ} {dL dB : PQ.RD}
    (hL : RoundBelow (mC s e + mS s e + L s e) dL εs)
    (hB : RoundBelow ((2 ^ s.C.a - e - 1) ^ s.t) dB εs) :
    (lastAt L mC mS s e dL dB).SmallAt L mC mS mW εs :=
  ⟨hL, hB⟩

/-- `SmallAt` of a step to a stage that is not the last. e': the next radius. -/
theorem smallAt_stepMidAt {s s' : Sg} (hf : CsFit s s') {e e' : ℕ} {dE dT dS dC : PQ.RD}
    {next : Chain s'} (hr : next.rad = e') (hE : RoundBelow (L s e) dE εs)
    (hT : RoundBelow (mC s e + L s e * 2) dT εs)
    (hM : s.h ≠ 0 → RoundBelow (mC s e + (mS s e + mW s e) + L s e * 2) dT εs)
    (hS : RoundBelow ((csSw hf).W.err1 (L s' e')) dS εs)
    (hC : RoundBelow ((csSw hf).W.err2 e (L s' e')) dC εs)
    (hN : next.SmallAt L mC mS mW εs) :
    (stepMidAt L mC mS mW s s' hf e dE dT dS dC next).SmallAt L mC mS mW εs := by
  subst hr
  exact ⟨hE, hT, hM, hS, hC, hN⟩

/-- `SmallAt` of a step to the last stage. e': the next radius. -/
theorem smallAt_stepEndAt {s s' : Sg} (hf : CsFit s s') {e e' : ℕ} {dE dT dS dC : PQ.RD}
    {next : Chain s'} (hr : next.rad = e') (hE : RoundBelow (L s e) dE εs)
    (hT : RoundBelow (mC s e + L s e * 2) dT εs)
    (hM : s.h ≠ 0 → RoundBelow (mC s e + (mS s e + mW s e) + L s e * 2) dT εs)
    (hS : RoundBelow ((csSw hf).W.err1 (L s' e')) dS εs)
    (hC : RoundBelow ((csSw hf).W.err2 e (L s' e')) dC εs)
    (hN : next.SmallAt L mC mS mW εs) :
    (stepEndAt L mC mS mW s s' hf e dE dT dS dC next).SmallAt L mC mS mW εs := by
  subst hr
  exact ⟨hE, hT, hM, hS, hC, hN⟩

end Chain

/-- **The list of counts in the conclusion of `link_chain_joh`, at any numbers a, b, L in the places
of its first counts and lists**: every count is at most εs as a share of its round's written
verifier messages, if the counts of the link's first, second, fourth and fifth round and of the
batching are, and, for a chain with the letters' numbers (`Chain.PlainAt`), each count of the chain
that is written out (`Chain.SmallAt`). The first entry of the list and the third round's count are
0. e, rows: the chain's first radius and the number of rows, with equations. -/
theorem link_chain_below (S : Sz) (Z : Sample GE S.En) (N : RowNo S Z) {t₀ : ℕ}
    (d1 d2 d3 d4 d5 dA : PQ.RD) (xs : List PQ.XO) (dec : PQ.View → Bool) (a b : ℕ) (L : Bool → ℕ)
    (c : Chain (S.sg t₀)) (εs : ℝ≥0∞) {e rows : ℕ} (he : c.rad = e) (hn : N.n = rows)
    (h1 : RoundBelow (S.lk.errGam a b) d1 εs)
    (h2 : RoundBelow (ldSendFamErr S.lk.N S.seeds L) d2 εs) (h4 : RoundBelow S.lk.errLoc d4 εs)
    (h5 : RoundBelow S.lk.errPhi d5 εs)
    (hA : RoundBelow ((S.sg t₀).lstJ e * (rows - 1)) dA εs)
    (hp : c.PlainAt Sg.lstJ Sg.flC Sg.flZ Sg.flZ)
    (hs : c.SmallAt Sg.lstJ Sg.flC Sg.flZ Sg.flZ εs) :
    Err.Below (s := (written S d1 d2 d3 d4 d5 (dA :: c.rds) xs dec).shape)
      (0, coreErrR S Z d1 d2 d3 d4 d5 a b L (batErrR N ((S.sg t₀).lstJ c.rad) dA, c.errL))
      εs := by
  subst he hn
  have ht : Err.Below (s := PQ.uL (ckP .two) (dA :: c.rds))
      (batErrR N ((S.sg t₀).lstJ c.rad) dA, c.errL) εs :=
    ⟨hA, c.errL_below _ (c.err_below_at _ hp hs)⟩
  rw [coreErrR_eq]
  exact link_below S d1 d2 d3 d4 d5 (dA :: c.rds) xs dec a b L _ εs
    (core_below S d1 d2 d3 d4 d5 a b L (t := PQ.uL (ckP .two) (dA :: c.rds))
      (batErrR N ((S.sg t₀).lstJ c.rad) dA, c.errL) εs h1 h2 h4 h5 ht)

end OnBytes.Slice

#print axioms OnBytes.Slice.Chain.smallAt_lastAt
#print axioms OnBytes.Slice.Chain.smallAt_stepMidAt
#print axioms OnBytes.Slice.Chain.smallAt_stepEndAt
#print axioms OnBytes.Slice.link_chain_below
#print axioms OnBytes.Slice.SetOK.card
#print axioms OnBytes.Slice.below_of_priced
#print axioms OnBytes.Slice.priced_of_plan
#print axioms OnBytes.Slice.real_share
#print axioms OnBytes.Slice.pos_share_left
#print axioms OnBytes.Slice.pos_share_right
#print axioms OnBytes.Slice.cs_real
#print axioms OnBytes.Slice.fold_point_num
#print axioms OnBytes.Slice.nVals_seed
#print axioms OnBytes.Slice.card_GE_pred_pos
#print axioms OnBytes.Slice.memb_err
#print axioms OnBytes.Slice.cs_err1
#print axioms OnBytes.Slice.seeds_real
#print axioms OnBytes.Slice.point_share
#print axioms OnBytes.Slice.send_share
#print axioms OnBytes.Slice.loc_share
#print axioms OnBytes.Slice.phi_share
#print axioms OnBytes.Slice.bat_share_joh
#print axioms OnBytes.Slice.Sg.AsGroup.lst
#print axioms OnBytes.Slice.Sg.AsGroup.flC
#print axioms OnBytes.Slice.Sg.AsGroup.flZ
#print axioms OnBytes.Slice.eps_share
#print axioms OnBytes.Slice.fold_share
#print axioms OnBytes.Slice.fold_share_mask
#print axioms OnBytes.Slice.seed_share
#print axioms OnBytes.Slice.cs_share
#print axioms OnBytes.Slice.lambda_share
#print axioms OnBytes.Slice.base_share
