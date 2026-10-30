-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K8/RestJoin.lean: THE SMALLNESS TEST: THE JOIN: THE ONE NAMED PREMISE
OF Johnson/Desc/ProofFile/Honest/K8/K8BehindOf.lean (`RestAtStand`: at a stand of the batching every
guard of the verifier's three tests that is not among the kind's share holds) FROM A LIGHTER ONE
(`LeftAtStand`), WITH WHAT HAS A PAYER PAID INSIDE: `k8Rest_of`
(Johnson/Desc/ProofFile/Honest/K8/RestOf.lean) is called at a stand; its premise on the kept slots
is what the other house's `LsLaid` says; its heaviest premise, on the data's vectors of powers, is
`powered_laid` (Johnson/Desc/ProofFile/Honest/K8/PoweredAtStand.lean). So the other house's sentence
`K8Behind` at the kind's own share stands under `LeftAtStand`. None of the library's goals.

  `K8Left nU tl F`   WHAT IS LEFT, at the test's data and the ledger: eight facts on the plan and
                   the ledger (the window ends inside the ledger's coefficients · the data's blocks
                   are the loop's, one or two · the digits' array has its two last virtual rows ·
                   two facts that keep other arrays apart from it) AND THE TEN CLAUSES AND SIX
                   CONJUNCTS OF `K8Rest` THAT HAVE NO PAYER, as the verifier's text has them
  `LeftAtStand …`   the named premise: `K8Left` at every state z₂ as `K8Behind` has it
  **`restAtStand_of`**   K8At · ThetaAt at the order · the order's split · PowOn behind
                   "K8.equations" · LeftAtStand ⊢ RestAtStand
  **`k8Behind_of_left`**   the same premises ⊢ K8Behind Lk p φ Ok nU T b (k8Share nU)
Limits. AN IMPLICATION STILL: `LeftAtStand` IS NOT PAID: IT IS NOT SHOWN THAT AN HONEST STAND
MEETS IT. `K8At`, `ThetaAt` at the order and `PowOn` behind "K8.equations" are premises: the last
two are paid at each sort of link but for the sort's ties and one sentence at the lookups' entries
(Johnson/Desc/K8/Honest/ThetaRunAt.lean, Johnson/Desc/K8/Honest/PowBehind.lean). Nothing on how
often the share speaks.
Nothing is claimed on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K8.K8BehindOf
import Johnson.Desc.ProofFile.Honest.K8.RestOf
import Johnson.Desc.ProofFile.Honest.K8.PoweredAtStand

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K8
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open Fo (HasRow)
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.First.TailClaims (coefBody)
open VerifiableInference.Desc.First.K8.Honest (ThetaAt)
open VerifiableInference.Desc.LinkJoin (PowOn)
open ProofFile.Honest.K9 (BatStand K8Behind LsLaid k8Entry)

/-- What is left of `K8Rest`, with the facts that come in for what is paid. -/
def K8Left (nU : Array Nat) (tl : HTailF2) (F : Fork) : Prop :=
  tl.slotB ≤ F.LS.size ∧ t2BL tl.tau = .ok tl.blocks ∧ tl.blocks.size ≠ 0 ∧
  tl.blocks.size ≤ 2 ∧ HasRow F tl.ix.ZZ tl.zzRowReads ∧ HasRow F tl.ix.ZZ tl.zzRowTies ∧
  tl.ix.BZ ≠ tl.ix.ZZ ∧ (∀ mu, mu < tl.NM → tl.gtTree.getD mu 0 ≠ tl.ix.ZZ) ∧
  (nU == tl.nUF) = true ∧
  ∃ (g : Forest.Heard) (jo : Nat) (nbW : Nat) (W : List Want),
    tl.heard = some g ∧ tl.joinObj9 = some jo ∧ tl.wants = some (nbW, W) ∧
    (((coefBody tl g F).trees.getD tl.ix.ZZ {}).rows.size == 2 * nbW + 2 && tl.forestHeld g &&
      [0, 1].all (tl.callHeld g nbW)) = true ∧
    tl.piecesTile (coefBody tl g F) W = true ∧ tl.pointsHeld g = true ∧
    ((((coefBody tl g F).trees.getD tl.ix.ZZ {}).rows.getD (2 * nbW + 1) {}).L.size ==
        2 * tl.mz &&
      tl.gamX.size == tl.NM && tl.gamV.size == tl.NM &&
      (List.range tl.NM).all (tl.tieShapeHeld (coefBody tl g F)) &&
      tl.shp.foldl (fun n s => n + s.m) 0 == tl.mz &&
      tl.planesShapeHeld (coefBody tl g F) g) = true ∧
    tl.planesWeightsHeld (coefBody tl g F) g jo = true ∧
    tl.readShapeHeld
      (((coefBody tl g F).trees.getD tl.ix.ZZ {}).rows.getD (2 * nbW) {}).L = true ∧
    tl.readWeightsHeld (coefBody tl g F)
      (((coefBody tl g F).trees.getD tl.ix.ZZ {}).rows.getD (2 * nbW) {}).L = true

section
variable {α : Type} (Lk : Link S Claim) (p : Desc.K9.Where) (φ : S → α)
  (Ok : α × Option K9L.Pub9 → Prop) (nU : Array ℕ)
  {V W X Pb : Type} {Bk : ProverCoinCounts} (T : Thread Bk S Claim V W X Pb) (b : ℕ)

/-- **The named premise**: at a stand what is left holds. -/
def LeftAtStand : Prop :=
  ∀ κ s m En ds y cols s' x z G, BatStand Lk p T b κ s m En ds y cols s' x z G →
    Lk.tests s' = .ok () → k8Share nU s' = none → ∀ z₂, K9L.Fx9 φ Ok (K9L.fixed9 φ s) z₂ →
      K9L.good9 z₂ → z₂.fork? = s'.fork? → LsLaid s' z₂ →
        ∀ tl F, z₂.tl? = some tl → z₂.fork? = some F → K8Left nU tl F

variable {Lk p φ Ok nU T b}

/-- **The join.** -/
theorem restAtStand_of {k : Desc.K9.SegSort} {pW : K8.ParW} (hK : K8At Lk k pW)
    (hTh : ThetaAt Lk Lk.order) {pre post : List (ℕ × String)}
    (hsp : Lk.order = pre ++ k8Entry k :: post) (hPw : PowOn Lk post)
    (hLeft : LeftAtStand Lk p φ Ok nU T b) : RestAtStand Lk p φ Ok nU T b := by
  intro κ s m En ds y cols s' x z G hS hT hsh z₂ hFx hg hf hL tl₂ F hz hzF
  have hK8 := hLeft κ s m En ds y cols s' x z G hS hT hsh z₂ hFx hg hf hL tl₂ F hz hzF
  obtain ⟨F', tl, hF', ht', hz'⟩ := hL
  obtain rfl : F = F' := Option.some.inj (hzF.symm.trans (hf.trans hF'))
  obtain rfl : tl₂ = { tl with lsTail := F.LS.extract tl.slotA tl.slotB } :=
    Option.some.inj (hz.symm.trans hz')
  obtain ⟨hG, hx, hP⟩ := powered_at_stand hK hTh hsp hPw hS
  obtain rfl : G = F := Option.some.inj (hG.symm.trans hF')
  have hPow := powered_laid ⟨hx, hP⟩ ht' (G.LS.extract tl.slotA tl.slotB)
  obtain ⟨hin, hb, b1, b2, hR, hT', hB, hm, r1, g, jo, nbW, W', hg', hjo, hW, r4, r5, r6, r7, r9,
    r10, r11⟩ := hK8
  exact k8Rest_of rfl hin hb b1 b2 hPow hR hT' hB hm r1 hg' hjo hW r4 r5 r6 r7 r9 r10 r11

/-- **So the kind's last run returns outside the kind's own share.** -/
theorem k8Behind_of_left {k : Desc.K9.SegSort} {pW : K8.ParW} (hK : K8At Lk k pW)
    (hTh : ThetaAt Lk Lk.order) {pre post : List (ℕ × String)}
    (hsp : Lk.order = pre ++ k8Entry k :: post) (hPw : PowOn Lk post)
    (hLeft : LeftAtStand Lk p φ Ok nU T b) : K8Behind Lk p φ Ok nU T b (k8Share nU) :=
  k8Behind_of_rest Lk p φ Ok nU T b (restAtStand_of hK hTh hsp hPw hLeft)

end

end ProofFile.Honest.K8

#print axioms ProofFile.Honest.K8.restAtStand_of
#print axioms ProofFile.Honest.K8.k8Behind_of_left
