-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Policy/Rel/LedgerHeadInt.lean

The field relation of the head with the cost ledger (Policy/Rel/LedgerHead.lean), modulo p, as
congruences between integers. Policy/Rel/LedgerHeadNoWrap.lean (on wrap-around) and
Policy/Rel/LedgerHeadHonest.lean (on the honest cells) work on these congruences; the relation is
formed in a ring.

* `RFz p np H y t`: `RF` with every equation in `ZMod p` written as a congruence modulo p.
* `map_key`: a ring homomorphism commutes with the keys.
* `rfz_of_rf`, `rf_of_rfz`: `RF` over `ZMod p`, at the output matrix H modulo p, holds if and only
  if `RFz p` holds, for every natural number p.

That a ring homomorphism commutes with the arrays, the identities and the four clauses of the ledger
is taken from Inst/Model/Head/NoWrapProgram.lean and Inst/Model/Head/NoWrapProgramN.lean.

Limits: this file says nothing on what the relation forces or admits.
-/
import Inst.Model.Head.NoWrapProgramN
import Policy.Rel.LedgerHead

set_option autoImplicit false

/- The next line removes the default table of scales (the instance `Scl.ref`) in this file.
Whatever reads a table here says which table. -/
attribute [-instance] Inst.Model.Scl.ref

namespace Policy.LedgerHead

open Inst.Model Inst.Model.Head

/-- The field relation of the head, as congruences between integers. -/
structure RFz (p : ℕ) (np : NormPar) (H : Mat) (y : Req) (t : Cells ℤ) : Prop where
  small : Head.Small t
  keys : ∀ s x i, x < len s → i < nT →
    ∃ u < (tableOf s).rows, key np t H y s x i ≡ (tableOf s).row u [ZMOD (p : ℤ)]
  idns : ∀ i < nT, ∀ k < 17, N.idn np t i k ≡ 0 [ZMOD (p : ℤ)]
  jc : ∀ i < nT, dB4 t y i ≡ 0 [ZMOD (p : ℤ)] ∧ dZ t y i ≡ 0 [ZMOD (p : ℤ)]
  sums : sB2 t y ≡ 0 [ZMOD (p : ℤ)] ∧ sB3 t y ≡ 0 [ZMOD (p : ℤ)]

section Map
variable {K K' : Type} [CommRing K] [CommRing K'] (f : K →+* K') (np : NormPar) (t : Cells K)
  (H : ℕ → ℕ → K) (y : Req)

/-- A ring homomorphism commutes with the keys. -/
theorem map_key (s : Fam) (x i : ℕ) :
    f (key np t H y s x i) = key np (t.map f) (fun j v => f (H j v)) y s x i := by
  cases s
  · simp only [key, map_sub, map_add, map_mul, map_pow, map_ofNat, map_xv, map_nw,
      map_rn, Ledger.map_R, map_Dv]
  · simp only [key, map_mul, map_natCast, map_rn]
  · simp only [key, map_sub, map_mul, map_pow, map_ofNat, map_mg, map_K1, map_K2]
  · exact map_K1 f t y x i
  · simp only [key, map_mul, map_intCast, map_Dv]
  · exact map_K2 f t y x i
  · simp only [key, map_add, map_mul, map_pow, map_ofNat, map_K1, map_ex]
  · simp only [key, map_add, map_mul, map_pow, map_ofNat, map_K1, map_ex]
  · simp only [key, map_add, map_mul, map_pow, map_ofNat, map_nw, map_nrm]

end Map

theorem cast_zero_iff (p : ℕ) (a : ℤ) : ((a : ℤ) : ZMod p) = 0 ↔ a ≡ 0 [ZMOD (p : ℤ)] := by
  have h := ZMod.intCast_eq_intCast_iff a 0 p
  rwa [Int.cast_zero] at h

variable {p : ℕ} {np : NormPar}

/-- From the relation over `ZMod p` to the congruences. -/
theorem rfz_of_rf {H : Mat} {y : Req} {t : Cells ℤ}
    (h : RF (F := ZMod p) np (fun j v => (H j v : ZMod p)) y t) : RFz p np H y t where
  small := h.small
  keys := fun s x i hx hi => by
    obtain ⟨u, hu, e⟩ := h.keys s x i hx hi
    refine ⟨u, hu, ?_⟩
    have e1 := map_key (Int.castRingHom (ZMod p)) np t H y s x i
    refine (ZMod.intCast_eq_intCast_iff _ _ _).1 ?_
    exact e1.trans e
  idns := fun i hi k hk =>
    (cast_zero_iff p _).1
      ((N.map_idn' (Int.castRingHom (ZMod p)) np t i k).trans (h.idns i hi k hk))
  jc := fun i hi =>
    ⟨(cast_zero_iff p _).1 ((map_dB4 (Int.castRingHom (ZMod p)) t y i).trans (h.jc i hi).1),
      (cast_zero_iff p _).1 ((map_dZ (Int.castRingHom (ZMod p)) t y i).trans (h.jc i hi).2)⟩
  sums := ⟨(cast_zero_iff p _).1 ((map_sB2 (Int.castRingHom (ZMod p)) t y).trans h.sums.1),
    (cast_zero_iff p _).1 ((map_sB3 (Int.castRingHom (ZMod p)) t y).trans h.sums.2)⟩

/-- From the congruences to the relation over `ZMod p`. -/
theorem rf_of_rfz {H : Mat} {y : Req} {t : Cells ℤ} (h : RFz p np H y t) :
    RF (F := ZMod p) np (fun j v => (H j v : ZMod p)) y t where
  small := h.small
  keys := fun s x i hx hi => by
    obtain ⟨u, hu, e⟩ := h.keys s x i hx hi
    refine ⟨u, hu, ?_⟩
    exact (map_key (Int.castRingHom (ZMod p)) np t H y s x i).symm.trans
      ((ZMod.intCast_eq_intCast_iff _ _ _).2 e)
  idns := fun i hi k hk =>
    (N.map_idn' (Int.castRingHom (ZMod p)) np t i k).symm.trans
      ((cast_zero_iff p _).2 (h.idns i hi k hk))
  jc := fun i hi =>
    ⟨(map_dB4 (Int.castRingHom (ZMod p)) t y i).symm.trans ((cast_zero_iff p _).2 (h.jc i hi).1),
      (map_dZ (Int.castRingHom (ZMod p)) t y i).symm.trans ((cast_zero_iff p _).2 (h.jc i hi).2)⟩
  sums := ⟨(map_sB2 (Int.castRingHom (ZMod p)) t y).symm.trans ((cast_zero_iff p _).2 h.sums.1),
    (map_sB3 (Int.castRingHom (ZMod p)) t y).symm.trans ((cast_zero_iff p _).2 h.sums.2)⟩

end Policy.LedgerHead
