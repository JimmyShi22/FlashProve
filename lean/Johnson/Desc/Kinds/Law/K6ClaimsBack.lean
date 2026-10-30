--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Kinds/Law/K6ClaimsBack.lean: THE WAY BACK OF Law/K6Claims.lean's k6Out_of_claims: FROM
K6Out (Law/RowPins.lean: what the output head's own sub-protocol opens, at given components of a
witness) TO "THE SEAT's CLAIMS ARE WORTH 0 IN THE WITNESS's WORLD". STATED AND PROVED: MIRRORS OF
THAT FILE's PROOFS: no new mathematics.
WHAT IT CANNOT GIVE, FIRST. It stands at given components d and a given world Wd: that any witness
has these components is not said. Nothing on the items "planes" and "small" of the table's row:
K6Out does not read them. No example. Nothing on soundness or on hiding.
Why it goes through. Every link of the way there is an iff (Came.k6Out_iff) or an equation of worths
(joinForm_two; K6Exchange.keys), but one: K6Exchange.forms gives to each form at the reads in truth
a seat's form of that worth, not the other way round. Its payer, Law/AlikeWorth.lean's zero_claims,
is general in the two fillings of the reads and in the two worlds: it is called here with the roles
swapped.
  EntriesAlike.symm    the premise on the entries, mirrored: its three fields are equations.
  seat_zero_of_true    where all 35 forms at the reads in truth are worth 0 in W₂, all 35 at the
                       seat's reads are worth 0 in W₁.
  **claims_of_k6Out**  K6Out W t d gives: WeightAt · the seat's 35 forms are worth 0 in Wd · the
                       form of "join" at the seat's key vectors is worth 0 in Wd. Premises: the
                       letters' three equations at the state t; the exchange (for the keys); the
                       step from the forms in truth to the seat's (hZ: seat_zero_of_true pays it);
                       the lookup's last claim is worth the same in the two worlds.

-/
import Johnson.Desc.Kinds.Law.K6Claims

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E zeroE)
open OnBytes.Model (Fork Aff Reading World)
open VerifiableInference.Desc.First (S HeadOwn)
open Norm (lt ls d lPd T S2)

section All

variable [Sizes] [Policy] [Request] [Token] [FinalNorm.In] [In] [Norm.Heard] [FinalNorm.Heard]
  [Heard]

/-- The premise on the entries, mirrored. -/
theorem EntriesAlike.symm {W W' : World K} {N N' : FinalNorm.Reads} {R R' : Reads}
    (A : EntriesAlike W W' N N' R R') : EntriesAlike W' W N' N R' R :=
  ⟨fun r i h => (A.norm r i h).symm, fun i h => (A.wide i h).symm,
    fun r i h => (A.head r i h).symm⟩

end All

/-- **Where the 35 forms at the reads in truth are worth 0, so are the seat's.** -/
theorem seat_zero_of_true (g : Given) (H : HeardAll) (x : FinalNorm.Reads × Reads) (c : NCells)
    (W₁ W₂ : World K) (hs : ∀ j, W₁.slot j = W₂.slot j) :
    letI : Norm.Heard := H.1
    letI : FinalNorm.Heard := H.2.1
    letI : Heard := H.2.2
    EntriesAlike W₁ W₂ x.1 (normReadsAtCells c) x.2 (readsAt c.toCells) → HeardBare → S2 ∣ d →
    (∀ name fs', (claimsTrue g H c).lookup name = some fs' → ∀ f', f' ∈ fs' → vW W₂ f' = 0) →
    ∀ name fs, (claimsSeat (g, ⟨H.1, H.2.1, H.2.2⟩, ⟨x.1, x.2⟩)).lookup name = some fs →
      ∀ f, f ∈ fs → vW W₁ f = 0 := by
  letI : Norm.Heard := H.1
  letI : FinalNorm.Heard := H.2.1
  letI : Heard := H.2.2
  intro A B hd h0 name fs hl f hf
  exact zero_claims W₂ W₁ (fun j => (hs j).symm) (normReadsAtCells c) x.1 (readsAt c.toCells) x.2
    A.symm B hd h0 name fs hl f hf

/-- **FROM K6Out TO THE SEAT's CLAIMS WORTH 0.** t: the state behind the head's own step. -/
theorem claims_of_k6Out (W : OnBytes.Model.Verify.Public) (t : S) (d : Pinned) (g : Given)
    (H : HeardAll) (x : FinalNorm.Reads × Reads) (gk : OnBytes.Model.Forest.Heard) (Wd : World K)
    (hg : given (parOf W.hS (workOf W)) (seatAt W.hS (readsOf W)) t = .ok g)
    (hH : (seatAt W.hS (readsOf W)).heard t = some H) (hgk : t.lookHeard? = some gk)
    (hS : K6Exchange g H x d.1 Wd (worldE ((seatAt W.hS (readsOf W)).ledger t) d.2 noEnt))
    (hZ : (∀ name fs', (claimsTrue g H d.1).lookup name = some fs' → ∀ f', f' ∈ fs' →
        vW (worldE ((seatAt W.hS (readsOf W)).ledger t) d.2 noEnt) f' = 0) →
      ∀ name fs, (claimsSeat (g, ⟨H.1, H.2.1, H.2.2⟩, ⟨x.1, x.2⟩)).lookup name = some fs →
        ∀ f, f ∈ fs → vW Wd f = 0)
    (hc : vW Wd gk.cEnd = vW (worldE ((seatAt W.hS (readsOf W)).ledger t) d.2 noEnt) gk.cEnd)
    (hO : K6Out W t d) :
    WeightAt W t d.1.toCells d.2 ∧
      (∀ name fs, (claimsSeat (g, ⟨H.1, H.2.1, H.2.2⟩, ⟨x.1, x.2⟩)).lookup name = some fs →
        ∀ f, f ∈ fs → vW Wd f = 0) ∧
      vW Wd (Came.joinForm gk (keyVectorsAt (g, ⟨H.1, H.2.1, H.2.2⟩, ⟨x.1, x.2⟩))) = 0 := by
  obtain ⟨hWt, ⟨g2, H2, hg2, hH2, h35⟩, gk2, hgk2, g3, H3, hg3, hH3, hj⟩ :=
    (Came.k6Out_iff W t d).1 hO
  obtain rfl : g = g2 := Except.ok.inj (hg.symm.trans hg2)
  obtain rfl : H = H2 := Option.some.inj (hH.symm.trans hH2)
  obtain rfl : g = g3 := Except.ok.inj (hg.symm.trans hg3)
  obtain rfl : H = H3 := Option.some.inj (hH.symm.trans hH3)
  obtain rfl : gk = gk2 := Option.some.inj (hgk.symm.trans hgk2)
  refine ⟨hWt, hZ fun name fs' hl f' hf' => ?_, ?_⟩
  · rw [← rd_atWorld, h35 name fs' hl f' hf']
    exact rd_zero
  · rw [joinForm_two Wd _ gk (keyVectorsAt (g, ⟨H.1, H.2.1, H.2.2⟩, ⟨x.1, x.2⟩))
      (keysAt g H d.1) (by simp [keyVectorsAt, keysAt]) (fun c hc' => hS.keys c (by
        simpa [keyVectorsAt] using hc')) hc]
    exact hj

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.EntriesAlike.symm
#print axioms VerifiableInference.Desc.Kinds.Head.Law.seat_zero_of_true
#print axioms VerifiableInference.Desc.Kinds.Head.Law.claims_of_k6Out
