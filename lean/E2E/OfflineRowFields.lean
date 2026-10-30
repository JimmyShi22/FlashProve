-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/OfflineRowFields.lean: two general steps for the rows of the offline file whose parts own no coin.

  `good_of_row`   `Good` at letters that are false, from the three fields: the form that the muted rows
                  ask: `plays` and `acc` are vacuous
  `spent_none`    no part spends a run of a part that owns none of the written book's entries

Nothing on any property.
-/
import E2E.OfflineSides
import Johnson.Desc.ProofFile.Honest.Small.Field

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtPublicFiles.OfflineRows
open ProofFile.Honest
open VerifiableInference.Desc (Place)
open ProofFile.Honest.Small (ExactMember FreshMember exactAt_of_exact)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub of_atFull)

section Fields
variable {S Cl V W Y Pb : Type}

/-- **`Good` at letters that are false**, from the three fields. `plays` and `acc` are vacuous: the
form that the muted rows ask; it says nothing on a run. -/
theorem good_of_row {pre : List (Nat × Nat × List Fmt.DeclaredRound)} {φ : Face V W Pb}
    {σ : Side S Cl V W Y Pb} {Bk : ProverCoinCounts} {ord : List Place} {chain firstTree : Nat}
    {On : (u : Member V W Y Pb) → CsAll u.part.carries → Mid W Y → Before → Prop}
    {bud : Nat → List Fmt.Drawn → List (List (List Nat)) → Prop} (hf : σ.fits = true)
    (he : ∀ u ∈ σ.members, ExactMember φ σ chain firstTree On bud u)
    (hr : ∀ u ∈ σ.members, FreshMember φ σ Bk ord bud u) :
    Good pre φ σ Bk ord chain firstTree (fun _ _ _ _ => False) (fun _ _ _ _ => False) On bud :=
  ⟨hf, fun _ _ _ _ _ h => h.elim, fun _ _ _ _ _ h => h.elim,
    fun u hu => exactAt_of_exact pre (he u hu), hr⟩

/-- No part spends a run of a part that owns none of the written book's entries. -/
theorem spent_none {K₀ : KeyPub} (hK : fullPub = some K₀) {a : Addr} (ha : a ∉ bookOwners)
    (p : Addr) : (keyBook K₀).spentBy a p = [] := by
  unfold ProverCoinCounts.spentBy
  rw [List.filter_eq_nil_iff]
  intro e he hc
  have h := List.contains_iff_mem.1 (List.all_eq_true.1 (of_atFull owners_full hK) e he)
  simp only [Bool.and_eq_true, beq_iff_eq] at hc
  exact ha (hc.1.1 ▸ h)

end Fields

end AtPublicFiles.OfflineRows

#print axioms AtPublicFiles.OfflineRows.good_of_row
#print axioms AtPublicFiles.OfflineRows.spent_none
