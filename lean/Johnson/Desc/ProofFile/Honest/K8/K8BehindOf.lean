-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K8/K8BehindOf.lean: THE SMALLNESS TEST: THE SENTENCE `K8Behind` OF THE
ITEM "totalB" (Johnson/Desc/ProofFile/Honest/K9/TotalFront.lean, another house's file: the kind's
last run behind the batching returns outside the kind's own share of the fall) AT THE KIND's OWN
SHARE (`k8Share nU`, Johnson/Desc/ProofFile/Honest/K8/Share.lean): UNDER ONE NAMED PREMISE: at a
stand every other guard of the verifier's three tests holds. Under the same premise it is also the
share's "where it is silent the run returns"; OF THE BARE SHARE THAT SENTENCE IS NOT TRUE: the
silence of seven tests does not give sixteen guards. A joining of
Johnson/Desc/ProofFile/Honest/K8/TestsSplit.lean with
Johnson/Desc/ProofFile/Honest/K8/ShareLaid.lean. None of the library's goals.

  `k8Tests_of_tests`   the library's move `K9L.k8Tests` returns where the three tests return at the
                   state's own data and ledger
  `RestAtStand …`   THE NAMED PREMISE: at a stand, where the share is silent, at every state z₂ as
                   `K8Behind` has it (it goes on from what is fixed · it is good · its ledger is the
                   one behind the batching · its data are those behind the batching with the kept
                   slots laid): `K8Rest nU` at z₂'s data and ledger. It hands its payer every
                   premise of `K8Behind`
  **`k8Behind_of_rest`**   RestAtStand … → K8Behind Lk p φ Ok nU T b (k8Share nU)
Limits. AN IMPLICATION: IT MOVES THE DEBT AND PAYS NONE: `RestAtStand` HOLDS EVERY GUARD THAT IS NOT
AMONG THE SHARE's SEVEN: guards on public numbers, and five on values that ask "two computations
agree" or "nothing has turned": THAT AN HONEST STAND MEETS THEM, AT EVERY CHALLENGE, IS NOT
SHOWN. NOTHING ON HOW OFTEN THE SHARE SPEAKS: two of its seven tests hold equalities besides, which
must be shown never to fail; and at a real plan its first test reads weights on a vector of reads on
which this kind's own list lays nothing: so its count is not this kind's alone. It concludes at
other house's z₂: whether that is the state of which a fall's own law speaks is not held here.
Nothing is claimed on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K8.TestsSplit
import Johnson.Desc.ProofFile.Honest.K8.ShareLaid
import Johnson.Desc.ProofFile.Honest.K9.TotalFront

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K8
open OnBytes OnBytes.Model
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.First.TailClaims (testsP)
open ProofFile.Honest.K9 (BatStand K8Behind LsLaid)

/-- The library's move returns where the three tests return. -/
theorem k8Tests_of_tests {nU : Array Nat} {z : S} {tl : HTailF2} {F Fc : Fork}
    (hF : z.fork? = some F) (ht : z.tl? = some tl) (h : testsP nU tl F = .ok Fc) :
    ∃ t, K9L.k8Tests nU z = .ok t := by
  refine ⟨(z.putTl tl).putFork Fc, ?_⟩
  simp only [K9L.k8Tests, hF, ht, h, Desc.K9.there, bind, Except.bind, pure, Except.pure]

section
variable {α : Type} (Lk : Link S Claim) (p : Desc.K9.Where) (φ : S → α)
  (Ok : α × Option K9L.Pub9 → Prop) (nU : Array ℕ)
  {V W X Pb : Type} {Bk : ProverCoinCounts} (T : Thread Bk S Claim V W X Pb) (b : ℕ)

/-- **The named premise**: at a stand every other guard holds. -/
def RestAtStand : Prop :=
  ∀ κ s m En ds y cols s' x z G, BatStand Lk p T b κ s m En ds y cols s' x z G →
    Lk.tests s' = .ok () → k8Share nU s' = none → ∀ z₂, K9L.Fx9 φ Ok (K9L.fixed9 φ s) z₂ →
      K9L.good9 z₂ → z₂.fork? = s'.fork? → LsLaid s' z₂ →
        ∀ tl F, z₂.tl? = some tl → z₂.fork? = some F → K8Rest nU tl F

/-- **The kind's last run returns outside the kind's own share.** -/
theorem k8Behind_of_rest (hR : RestAtStand Lk p φ Ok nU T b) :
    K8Behind Lk p φ Ok nU T b (k8Share nU) := by
  intro κ s m En ds y cols s' x z G hS hT hsh z₂ hFx hg hf hL
  obtain ⟨F, tl, hF', ht', hz⟩ := hL
  have hzF : z₂.fork? = some F := hf.trans hF'
  have hn : (k8First { tl with lsTail := F.LS.extract tl.slotA tl.slotB } nU F).or
      (k8Second { tl with lsTail := F.LS.extract tl.slotA tl.slotB } F) = none := by
    rw [← share_at nU hz hzF, share_slot nU ht' hF' hz hzF, hsh]
  have hRest :=
    hR κ s m En ds y cols s' x z G hS hT hsh z₂ hFx hg hf ⟨F, tl, hF', ht', hz⟩ _ F hz hzF
  cases h1 : k8First { tl with lsTail := F.LS.extract tl.slotA tl.slotB } nU F with
  | some a =>
    rw [h1] at hn
    exact nomatch hn
  | none =>
    rw [h1] at hn
    obtain ⟨Fc, hc⟩ := tests_of_share h1 hn hRest
    exact k8Tests_of_tests hzF hz hc

end

end ProofFile.Honest.K8

#print axioms ProofFile.Honest.K8.k8Tests_of_tests
#print axioms ProofFile.Honest.K8.k8Behind_of_rest
