-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/HeadReq.lean

What the head's keys read of a request and of the output matrix.

The head's conditions are written twice in this library, on the same cells: the plain head
(Cm/TargetPHead.lean: seven families of keys) and the head with the cost ledger
(Policy/Rel/LedgerHead.lean: nine families and four clauses on hidden numbers). Both take a record
"Head.Req" (r, e, a checked token for every number, a policy) and a matrix H on all pairs of
numbers. The theorems that read these conditions take them at one fixed term for the request
("Cm.reqOf x", "Head.Req.of pol x") and one for the matrix. This file shows how little of the two
arguments is read, so that another term can take their place.

Main definitions and theorems:
* "rhoC_eq": the indicator of the counted positions is the indicator of the covered positions below
  position 1,023 and 0 from there on. "NB_eq_sum": the number NB is the sum of that indicator.
* "Alike y y'": at the 1,024 positions the two requests cover the same positions, and at each
  covered position they check the same token. Nothing is asked of r, e, of the tokens at other
  positions or of the policy. "alike_of_fields", "alike_reqOf_of": how it is met.
* "plainKey_req", "ledgerKey_req": alike requests have the same keys at every position below 1,024.
  "dB4_req", "dZ_req", "sB2_req", "sB3_req": the four clauses, which also read words of the policy.
  "plainRF_req", "ledgerRF_req": so the field relations are equivalent.
* "plainKey_mat", "ledgerKey_mat", "plainRF_mat": two matrices that agree on the 5,120 x 202,048
  entries of an output matrix give the same keys, if every covered position checks a token below
  202,048. "cast_H_eq_Hof", "plainRF_Hof": so the matrix that the layout reads from an index and
  the two-byte reading "Head.Hof" can be exchanged.
* "mg_split", "mg_plain": the margin with the ledger is the plain margin plus a term that the
  indicator of the counted positions multiplies.
* "plain_of_ledger": where no position is counted, the relation with the ledger gives the plain one.
* "ledger_free", "rhoC_of_le", "NB_of_le": where no position is counted the four clauses hold
  whatever the cells; that is so for every request with 1,023 ≤ r, so for r = 1,023, e = 1,024.

Not claimed: nothing on what a relation forces or admits, on any protocol, or on where a request or
a matrix comes from. Every theorem is an equation between two terms of the library or an
implication between two of its relations.
-/
import Cm.TargetPRel
import Policy.Rel.LedgerHead

set_option autoImplicit false

namespace OnBytes.Road.HeadReq

open Inst.Model Inst.Model.Head

/-! ## 1. The indicators of a request -/

/-- A position at which ρ is 1 is covered. -/
theorem rho_one {y : Req} {i : ℕ} (h : y.rho i = 1) : y.r ≤ i ∧ i < y.e := by
  unfold Req.rho at h
  by_contra hn
  rw [if_neg hn] at h
  exact absurd h (by norm_num)

/-- The counted positions are the covered positions below 1,023. -/
theorem rhoC_eq (y : Req) (i : ℕ) : y.rhoC i = if i < 1023 then y.rho i else 0 := by
  unfold Req.rhoC Req.rho
  split_ifs <;> omega

/-- NB is the number of counted positions, all of which lie below 1,024. -/
theorem NB_eq_sum (y : Req) : (y.NB : ℤ) = ∑ i ∈ Finset.range nT, y.rhoC i := by
  have hsub : y.inst.cnt ⊆ Finset.range nT := fun i hi => by
    have h := y.mem_inst_cnt.1 hi
    rw [Finset.mem_range]
    unfold nT
    omega
  simp only [y.rhoC_inst]
  rw [Finset.sum_ite_mem, Finset.inter_eq_right.2 hsub, Finset.sum_const, y.inst.card_cnt,
    y.inst_NB, nsmul_eq_mul, mul_one]

/-- A request with 1,023 ≤ r has no counted position. -/
theorem rhoC_of_le {y : Req} (hr : 1023 ≤ y.r) (i : ℕ) : y.rhoC i = 0 := by
  unfold Req.rhoC
  rw [if_neg (by omega)]

/-- From r = 1,023 on no position is counted: the number of counted positions is 0. -/
theorem NB_of_le {y : Req} (hr : 1023 ≤ y.r) : y.NB = 0 := by
  unfold Req.NB
  omega

/-- No counted position below 1,024: none at all. -/
theorem rhoC_all {y : Req} (h0 : ∀ i < nT, y.rhoC i = 0) (i : ℕ) : y.rhoC i = 0 := by
  by_cases hi : i < nT
  · exact h0 i hi
  · unfold nT at hi
    rw [rhoC_eq, if_neg (by omega)]

/-! ## 2. Requests that the head cannot tell apart -/

/-- The two requests cover the same of the 1,024 positions and check the same token at each covered
position. -/
structure Alike (y y' : Req) : Prop where
  rho : ∀ i < nT, y.rho i = y'.rho i
  win : ∀ i < nT, y.rho i = 1 → y.win i = y'.win i

/-- A request is alike to itself. -/
theorem Alike.refl (y : Req) : Alike y y := ⟨fun _ _ => rfl, fun _ _ _ => rfl⟩

/-- Being alike goes both ways. -/
theorem Alike.symm {y y' : Req} (h : Alike y y') : Alike y' y :=
  ⟨fun i hi => (h.rho i hi).symm, fun i hi h1 => (h.win i hi ((h.rho i hi).trans h1)).symm⟩

/-- Alike requests count the same positions. -/
theorem Alike.rhoC {y y' : Req} (h : Alike y y') (i : ℕ) : y.rhoC i = y'.rhoC i := by
  rw [rhoC_eq y i, rhoC_eq y' i]
  by_cases hi : i < 1023
  · rw [if_pos hi, if_pos hi, h.rho i (by unfold nT; omega)]
  · rw [if_neg hi, if_neg hi]

/-- The same as an equation of functions. -/
theorem Alike.rhoC_fun {y y' : Req} (h : Alike y y') : y.rhoC = y'.rhoC := funext h.rhoC

/-- Alike requests have the same number of counted positions. -/
theorem Alike.NB {y y' : Req} (h : Alike y y') : y.NB = y'.NB := by
  have e : (y.NB : ℤ) = (y'.NB : ℤ) := by
    rw [NB_eq_sum y, NB_eq_sum y']
    exact Finset.sum_congr rfl fun i _ => h.rhoC i
  exact_mod_cast e

/-- The same r and e, and the same checked token at every covered position below 1,024. -/
theorem alike_of_fields {y y' : Req} (hr : y.r = y'.r) (he : y.e = y'.e)
    (hw : ∀ i < nT, y.r ≤ i → i < y.e → y.win i = y'.win i) : Alike y y' :=
  ⟨fun i _ => by unfold Req.rho; rw [hr, he],
    fun i hi h1 => hw i hi (rho_one h1).1 (rho_one h1).2⟩

/-- The two terms at which the library's theorems read an instance are alike, whatever the
policy. -/
theorem alike_reqOf_of (pol : AcceptancePolicy) (x : Instance ppref) : Alike (Cm.reqOf x) (Req.of pol x) :=
  alike_of_fields rfl rfl fun _ _ _ _ => rfl

/-- A record with the instance's r and e whose tokens are the instance's at the covered positions
(and anything elsewhere, 0 for one) is like "Cm.reqOf x". -/
theorem alike_reqOf (x : Instance ppref) (win : ℕ → ℕ) (pol : AcceptancePolicy)
    (hw : ∀ i < nT, x.r ≤ i → i < x.e → win i = x.w i) : Alike ⟨x.r, x.e, win, pol⟩ (Cm.reqOf x) :=
  alike_of_fields rfl rfl hw

/-! ## 3. The keys and the four clauses at alike requests -/

section Req
variable {K : Type} [CommRing K] (np : NormPar) (t : Cells K) (H : ℕ → ℕ → K) {y y' : Req}

/-- The margin with the ledger is the plain margin plus the counted positions' term. -/
theorem mg_split (y : Req) (v i : ℕ) :
    Head.mg t H y v i =
      Cm.Plain.mg t H y v i + (y.rhoC i : K) * (hidC t i + 2 ^ 37 * hidB t i) := rfl

/-- At a position that is not counted the two margins are one. -/
theorem mg_plain {i : ℕ} (h0 : y.rhoC i = 0) (v : ℕ) :
    Head.mg t H y v i = Cm.Plain.mg t H y v i := by
  rw [mg_split, h0, Int.cast_zero, zero_mul, add_zero]

/-- The middle digit of a margin reads the request through rho alone. -/
theorem K1_req (h : Alike y y') (v : ℕ) {i : ℕ} (hi : i < nT) : K1 t y v i = K1 t y' v i := by
  unfold K1
  rw [h.rho i hi]

/-- The low digit of a margin reads the request through rho alone. -/
theorem K2_req (h : Alike y y') (v : ℕ) {i : ℕ} (hi : i < nT) : K2 t y v i = K2 t y' v i := by
  unfold K2
  rw [h.rho i hi]

/-- The margin of the plain head is the same for requests that are alike. -/
theorem plainMg_req (h : Alike y y') (v : ℕ) {i : ℕ} (hi : i < nT) :
    Cm.Plain.mg t H y v i = Cm.Plain.mg t H y' v i := by
  unfold Cm.Plain.mg
  rcases y.rho_01 i with h0 | h1
  · rw [← h.rho i hi, h0]
    simp only [Int.cast_zero, zero_mul]
  · rw [← h.rho i hi, ← h.win i hi h1]

/-- The margin of the head with the ledger is the same for requests that are alike. -/
theorem mg_req (h : Alike y y') (v : ℕ) {i : ℕ} (hi : i < nT) :
    Head.mg t H y v i = Head.mg t H y' v i := by
  rw [mg_split, mg_split, plainMg_req t H h v hi, h.rhoC i]

/-- **Alike requests have the same keys of the plain head**, at every position below 1,024 and every
entry. -/
theorem plainKey_req (h : Alike y y') (s : Cm.Plain.Fam) (x : ℕ) {i : ℕ} (hi : i < nT) :
    Cm.Plain.TP.key np t H y s x i = Cm.Plain.TP.key np t H y' s x i := by
  have hm := fun v => plainMg_req t H h v hi
  have h1 := fun v => K1_req t h v hi
  have h2 := fun v => K2_req t h v hi
  cases s <;> simp only [Cm.Plain.TP.key, hm, h1, h2]

/-- **Alike requests have the same keys of the head with the ledger.** -/
theorem ledgerKey_req (h : Alike y y') (s : Fam) (x : ℕ) {i : ℕ} (hi : i < nT) :
    Policy.LedgerHead.key np t H y s x i = Policy.LedgerHead.key np t H y' s x i := by
  have hm := fun v => mg_req t H h v hi
  have h1 := fun v => K1_req t h v hi
  have h2 := fun v => K2_req t h v hi
  cases s <;> simp only [Policy.LedgerHead.key, hm, h1, h2]

/-- The clause (B4) reads the counted positions and the policy's clip. -/
theorem dB4_req (h : Alike y y') (hC : y.pol.C = y'.pol.C) (i : ℕ) : dB4 t y i = dB4 t y' i := by
  unfold dB4
  rw [h.rhoC i, hC]

/-- The clause (Z) reads the counted positions alone. -/
theorem dZ_req (h : Alike y y') (i : ℕ) : dZ t y i = dZ t y' i := by
  unfold dZ
  rw [h.rhoC i]

/-- The clause (B2) reads the counted positions, the clip and the bound on the mean. -/
theorem sB2_req (h : Alike y y') (hC : y.pol.C = y'.pol.C) (hθ : y.pol.theta = y'.pol.theta) :
    sB2 t y = sB2 t y' := by
  unfold sB2
  rw [h.rhoC_fun, h.NB, hC, hθ]

/-- The clause (B3) reads the counted positions and the policy's third word. -/
theorem sB3_req (h : Alike y y') (hc : y.pol.cap = y'.pol.cap) : sB3 t y = sB3 t y' := by
  unfold sB3
  rw [h.rhoC_fun, h.NB, hc]

end Req

section RelReq
variable {F : Type} [CommRing F] {np : NormPar} {H : ℕ → ℕ → F} {y y' : Req} {t : Cells ℤ}

/-- One direction of plainRF_req. -/
theorem plainRF_of_alike (h : Alike y y') (r : Cm.Plain.TP.RF np H y t) :
    Cm.Plain.TP.RF np H y' t :=
  ⟨r.small,
    fun s x i hx hi => by
      rw [← plainKey_req np (t.cast F) H h s x hi]
      exact r.keys s x i hx hi,
    r.idns⟩

/-- **The plain head's relation does not tell alike requests apart.** -/
theorem plainRF_req (h : Alike y y') : Cm.Plain.TP.RF np H y t ↔ Cm.Plain.TP.RF np H y' t :=
  ⟨plainRF_of_alike h, plainRF_of_alike h.symm⟩

/-- One direction of ledgerRF_req. -/
theorem ledgerRF_of_alike (h : Alike y y') (hp : y.pol = y'.pol)
    (r : Policy.LedgerHead.RF np H y t) : Policy.LedgerHead.RF np H y' t where
  small := r.small
  keys := fun s x i hx hi => by
    rw [← ledgerKey_req np (t.cast F) H h s x hi]
    exact r.keys s x i hx hi
  idns := r.idns
  jc := fun i hi => by
    rw [← dB4_req (t.cast F) h (congrArg AcceptancePolicy.C hp) i, ← dZ_req (t.cast F) h i]
    exact r.jc i hi
  sums := by
    rw [← sB2_req (t.cast F) h (congrArg AcceptancePolicy.C hp) (congrArg AcceptancePolicy.theta hp),
      ← sB3_req (t.cast F) h (congrArg AcceptancePolicy.cap hp)]
    exact r.sums

/-- **The relation with the ledger does not tell alike requests with one policy apart.** -/
theorem ledgerRF_req (h : Alike y y') (hp : y.pol = y'.pol) :
    Policy.LedgerHead.RF np H y t ↔ Policy.LedgerHead.RF np H y' t :=
  ⟨ledgerRF_of_alike h hp, ledgerRF_of_alike h.symm hp.symm⟩

end RelReq

/-! ## 4. The keys at two matrices that agree on the entries of an output matrix -/

section Mat
variable {K : Type} [CommRing K] (np : NormPar) (t : Cells K) {H H' : ℕ → ℕ → K} {y : Req}

/-- A logit reads the matrix at the channels below nD and at its own token alone. -/
theorem lg_mat (hH : ∀ j < nD, ∀ v < nV, H j v = H' j v) (i : ℕ) {v : ℕ} (hv : v < nV) :
    Head.lg t H i v = Head.lg t H' i v := by
  unfold Head.lg
  exact Finset.sum_congr rfl fun j hj => by rw [hH j (Finset.mem_range.1 hj) v hv]

/-- The margin of the plain head, for two matrices that agree within the sizes. -/
theorem plainMg_mat (hH : ∀ j < nD, ∀ v < nV, H j v = H' j v) {i : ℕ}
    (hw : y.rho i = 1 → y.win i < nV) {v : ℕ} (hv : v < nV) :
    Cm.Plain.mg t H y v i = Cm.Plain.mg t H' y v i := by
  unfold Cm.Plain.mg
  rcases y.rho_01 i with h0 | h1
  · rw [h0]
    simp only [Int.cast_zero, zero_mul]
  · rw [lg_mat t hH i (hw h1), lg_mat t hH i hv]

/-- The margin of the head with the ledger, for two matrices that agree within the sizes. -/
theorem mg_mat (hH : ∀ j < nD, ∀ v < nV, H j v = H' j v) {i : ℕ}
    (hw : y.rho i = 1 → y.win i < nV) {v : ℕ} (hv : v < nV) :
    Head.mg t H y v i = Head.mg t H' y v i := by
  rw [mg_split, mg_split, plainMg_mat t hH hw hv]

/-- **The plain head's keys read the matrix at j < 5,120, v < 202,048 alone**, if the token that a
covered position checks lies below 202,048. -/
theorem plainKey_mat (hH : ∀ j < nD, ∀ v < nV, H j v = H' j v) {i : ℕ}
    (hw : y.rho i = 1 → y.win i < nV) (s : Cm.Plain.Fam) {x : ℕ} (hx : x < Cm.Plain.len s) :
    Cm.Plain.TP.key np t H y s x i = Cm.Plain.TP.key np t H' y s x i := by
  cases s
  case HD0 => simp only [Cm.Plain.TP.key, plainMg_mat t hH hw (show x < nV from hx)]
  all_goals rfl

/-- **The same for the head with the ledger.** -/
theorem ledgerKey_mat (hH : ∀ j < nD, ∀ v < nV, H j v = H' j v) {i : ℕ}
    (hw : y.rho i = 1 → y.win i < nV) (s : Fam) {x : ℕ} (hx : x < len s) :
    Policy.LedgerHead.key np t H y s x i = Policy.LedgerHead.key np t H' y s x i := by
  cases s
  case HD0 => simp only [Policy.LedgerHead.key, mg_mat t hH hw (show x < nV from hx)]
  all_goals rfl

end Mat

section RelMat
variable {F : Type} [CommRing F] {np : NormPar} {H H' : ℕ → ℕ → F} {y : Req} {t : Cells ℤ}

/-- One direction of plainRF_mat. -/
theorem plainRF_of_mat (hH : ∀ j < nD, ∀ v < nV, H j v = H' j v)
    (hw : ∀ i < nT, y.rho i = 1 → y.win i < nV) (r : Cm.Plain.TP.RF np H y t) :
    Cm.Plain.TP.RF np H' y t :=
  ⟨r.small,
    fun s x i hx hi => by
      rw [← plainKey_mat np (t.cast F) hH (hw i hi) s hx]
      exact r.keys s x i hx hi,
    r.idns⟩

/-- **The plain head's relation at two matrices that agree on the entries of an output matrix.** -/
theorem plainRF_mat (hH : ∀ j < nD, ∀ v < nV, H j v = H' j v)
    (hw : ∀ i < nT, y.rho i = 1 → y.win i < nV) :
    Cm.Plain.TP.RF np H y t ↔ Cm.Plain.TP.RF np H' y t :=
  ⟨plainRF_of_mat hH hw, plainRF_of_mat (fun j hj v hv => (hH j hj v hv).symm) hw⟩

/-- The relation of the head with the ledger, for two matrices that agree within the sizes. -/
theorem ledgerRF_of_mat (hH : ∀ j < nD, ∀ v < nV, H j v = H' j v)
    (hw : ∀ i < nT, y.rho i = 1 → y.win i < nV) (r : Policy.LedgerHead.RF np H y t) :
    Policy.LedgerHead.RF np H' y t :=
  ⟨r.small,
    fun s x i hx hi => by
      rw [← ledgerKey_mat np (t.cast F) hH (hw i hi) s hx]
      exact r.keys s x i hx hi,
    r.idns, r.jc, r.sums⟩

end RelMat

/-- The output matrix that the layout reads from an integer matrix W, carried into a ring, is the
two-byte reading "Head.Hof" of W carried into that ring: at the entries of an output matrix. -/
theorem cast_H_eq_Hof {K : Type} [CommRing K] (W : Mat) {j v : ℕ} (hj : j < nD) (hv : v < nV) :
    (((Layout.weightsOf ppref Layout.kRef W).H j v : ℤ) : K) =
      Hof (fun r c => ((W r c : ℤ) : K)) j v := by
  rw [Hof_weightsOf W hj hv]
  simp only [Hof, Int.cast_add, Int.cast_mul, Int.cast_ofNat]

/-- **The two ways to read the output matrix from an index can be exchanged** in the plain head's
relation modulo p. -/
theorem plainRF_Hof (p : ℕ) {np : NormPar} (W : Mat) {y : Req} {t : Cells ℤ}
    (hw : ∀ i < nT, y.rho i = 1 → y.win i < nV) :
    Cm.Plain.TP.RF (F := ZMod p) np (Cm.TP.castH p W) y t ↔
      Cm.Plain.TP.RF (F := ZMod p) np (Hof (Cm.TP.castW p W)) y t :=
  plainRF_mat (fun _ hj _ hv => cast_H_eq_Hof W hj hv) hw

/-! ## 5. Where no position is counted -/

/-- the family of the head with the ledger that bears the name of a family of the plain head -/
def up : Cm.Plain.Fam → Fam
  | .NF => .NF | .NFH => .NFH | .HD0 => .HD0 | .HD1 => .HD1 | .ROW => .ROW | .HD2 => .HD2
  | .CNF => .CNF

/-- A family of the plain head has at most as many entries as its family with the ledger. -/
theorem len_up (s : Cm.Plain.Fam) : Cm.Plain.len s ≤ len (up s) := by
  cases s <;> first | exact le_refl _ | decide

/-- A family of the plain head looks up in the table of its family with the ledger. -/
theorem tableOf_up (s : Cm.Plain.Fam) :
    Policy.LedgerHead.tableOf (up s) = Cm.Plain.TP.tableOf s := by
  cases s <;> rfl

/-- At a position that is not counted the seven families have the same keys in both heads. -/
theorem key_up {K : Type} [CommRing K] (np : NormPar) (t : Cells K) (H : ℕ → ℕ → K) {y : Req}
    {i : ℕ} (h0 : y.rhoC i = 0) (s : Cm.Plain.Fam) (x : ℕ) :
    Policy.LedgerHead.key np t H y (up s) x i = Cm.Plain.TP.key np t H y s x i := by
  cases s
  case HD0 => simp only [up, Policy.LedgerHead.key, Cm.Plain.TP.key, mg_plain t H h0]
  all_goals rfl

/-- The 17 identities are one text in both heads. -/
theorem idn_eq {K : Type} [CommRing K] (np : NormPar) (t : Cells K) (i k : ℕ) :
    N.idn np t i k = Cm.Plain.idn np t i k := rfl

/-- The bound on all cells bounds the cells that the plain head reads. -/
theorem small_of_ledger {t : Cells ℤ} (h : Head.Small t) : Cm.Plain.Small (2 ^ 18) t :=
  fun i hi =>
    ⟨fun φ hφ => (h i hi).1 φ (lt_of_lt_of_le hφ (by decide)), (h i hi).2.1,
      fun φ hφ => (h i hi).2.2.1 φ (lt_of_lt_of_le hφ (by decide)), (h i hi).2.2.2⟩

/-- **Where no position is counted, the relation with the ledger gives the plain head's.** -/
theorem plain_of_ledger {F : Type} [CommRing F] {np : NormPar} {H : ℕ → ℕ → F} {y : Req}
    {t : Cells ℤ} (h0 : ∀ i < nT, y.rhoC i = 0) (h : Policy.LedgerHead.RF np H y t) :
    Cm.Plain.TP.RF np H y t where
  small := small_of_ledger h.small
  keys := fun s x i hx hi => by
    have e := h.keys (up s) x i (lt_of_lt_of_le hx (len_up s)) hi
    rw [tableOf_up, key_up np (t.cast F) H (h0 i hi)] at e
    exact e
  idns := h.idns

/-- **Where no position is counted, the four clauses on the hidden numbers hold whatever the cells
and the policy.** -/
theorem ledger_free {K : Type} [CommRing K] (t : Cells K) {y : Req}
    (h0 : ∀ i < nT, y.rhoC i = 0) :
    (∀ i, dB4 t y i = 0 ∧ dZ t y i = 0) ∧ sB2 t y = 0 ∧ sB3 t y = 0 := by
  have hall := rhoC_all h0
  have hNB : y.NB = 0 := y.NB_of_rhoC hall
  refine ⟨fun i => ⟨?_, ?_⟩, ?_, ?_⟩
  · unfold dB4
    rw [hall i, Int.cast_zero, zero_mul]
  · unfold dZ
    rw [hall i, Int.cast_zero, zero_mul]
  · unfold sB2
    rw [hNB, Nat.cast_zero, mul_zero, sub_zero]
    exact Finset.sum_eq_zero fun i _ => by rw [hall i, Int.cast_zero, zero_mul]
  · unfold sB3
    rw [if_neg (by omega), sub_zero]
    exact Finset.sum_eq_zero fun i _ => by rw [hall i, Int.cast_zero, zero_mul]

/-- **The request "the next token"** (r = 1,023, e = 1,024; e is not read here): no position is
counted, NB = 0, and the four clauses hold whatever the cells. -/
theorem next_free {K : Type} [CommRing K] (t : Cells K) {y : Req} (hr : y.r = 1023) :
    (∀ i, y.rhoC i = 0) ∧ y.NB = 0 ∧
      (∀ i, dB4 t y i = 0 ∧ dZ t y i = 0) ∧ sB2 t y = 0 ∧ sB3 t y = 0 :=
  ⟨rhoC_of_le (le_of_eq hr.symm), NB_of_le (le_of_eq hr.symm),
    ledger_free t fun i _ => rhoC_of_le (le_of_eq hr.symm) i⟩

end OnBytes.Road.HeadReq

#print axioms OnBytes.Road.HeadReq.NB_eq_sum
#print axioms OnBytes.Road.HeadReq.plainRF_req
#print axioms OnBytes.Road.HeadReq.ledgerRF_req
#print axioms OnBytes.Road.HeadReq.plainRF_Hof
#print axioms OnBytes.Road.HeadReq.ledgerRF_of_mat
#print axioms OnBytes.Road.HeadReq.plain_of_ledger
#print axioms OnBytes.Road.HeadReq.next_free
