-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Tie/Pv/Lookup/Rider/Model/Zt.lean: the last lt places of the first part of the key point of
the lookup of a sub-proof.

A definition, statements and proofs. The lists `outZx` and `outZk` off forB's output statement are
those of OnBytes/Tie/Pv/Lookup/Rider/ForBCalls.lean.
Main names:
  `outZt h lt b`: the last lt places of `outZx h b`. It is read as a point by `Blocks.ofList`; place
    0 belongs to the top bit. `outZt_at`, `outZt_pt`: its places as places of `outZx`, and of the
    point pt of the claim on the keys.
  `outZt_zk`: the last lt places of the key point of any call are the same: place iota + h.dT - lt +
    j of `outZk h iota b` is place j of `outZt h lt b`, for j < lt.
  `selIn_last`: these places are a lawful choice (`SelIn`, Cb/G6/Rider/UsesK.lean), for every member
    of any family on cubes of lt variables.
Limits: plain facts on lists. Nothing on which test of the programs reads these places.
-/
import OnBytes.Tie.Pv.Lookup.Rider.ForBCalls

set_option autoImplicit false

namespace Cb.Rider
open Cb Blocks Cb.LdLkp Cb.LdLkp.Kn Cb.Fo

section Arrays
variable {E St J : Type} [Field E]

/-- The last lt places of the first part of the key point. -/
def outZt (h : Sh) (lt : ℕ) (b : TX St E J) : List E := (outZx h b).drop (h.dT - lt)

theorem outZt_at (h : Sh) (lt : ℕ) (b : TX St E J) (t : ℕ) :
    ofList (outZt h lt b) t = (outZx h b).getD (h.dT - lt + t) 0 :=
  drop_at 0 (h.dT - lt) (outZx h b) t

theorem outZt_pt (h : Sh) {lt : ℕ} (hlt : lt ≤ h.dT) (b : TX St E J) {t : ℕ} (ht : t < lt) :
    b.2.1.pt (h.dT - lt + t) = ofList (outZt h lt b) t := by
  rw [outZt_at, outZx_at h b (j := h.dT - lt + t) (by omega)]

/-- The last lt places of a call's key point are the last lt places of the first part. -/
theorem outZt_zk (h : Sh) (hv : 1 ≤ h.v) (b : TX St E J) {iota lt j : ℕ} (hi : iota ≤ h.rK)
    (hlt : lt ≤ h.dT) (hj : j < lt) :
    (outZk h iota b).getD (iota + h.dT - lt + j) 0 = ofList (outZt h lt b) j := by
  rw [← outZt_pt h hlt b hj, outZk_at h hv b hi (j := iota + h.dT - lt + j) (by omega)]
  congr 1
  unfold keyIx
  rw [if_neg (by omega)]
  omega

end Arrays

/-- The last lt places of the first part of the key point are a lawful choice, for every member of
any family on cubes of lt variables. -/
theorem selIn_last {ι : Type} (h : Sh) {lt : ℕ} (hlt : lt ≤ h.dT) :
    SelIn (FoNums.v' h) (fun _ : ι => lt) fun _ t => h.dT - lt + t :=
  fun _ => ⟨fun t _ t' _ (e : h.dT - lt + t = h.dT - lt + t') => by omega,
    fun t (ht : t < lt) => by
      show h.dT - lt + t ≤ FoNums.v' h
      have h2 := sh_dT_le h
      omega⟩

end Cb.Rider

#print axioms Cb.Rider.outZt_pt
#print axioms Cb.Rider.outZt_zk
#print axioms Cb.Rider.selIn_last
