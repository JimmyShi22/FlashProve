-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K10/Pay/XchFreshSent.lean: the closing of a segment (K10): what a sending lays at the message
that is a fold's fresh mask, in the sending's own coins. For the field fresh of `CarryOwed` (Honest/K10/Xch/CarryTop.lean).

The text is the code switch's `rowsAll` (Honest/K2/Sending.lean), at the table `freshTable` (Honest/K2/AtPlan.lean).

  `eAt_stretch`      a coin that is read by number is the coin of that number
  `fresh_mask_at`    `fresh_message_mask` (Pay/XchFreshCoins.lean) with "it is a fresh mask" as an equation
  **`sent_fresh_mask`**  where `rowsAll` returns V and message number n is the fresh mask of a fold with fv row variables: inside
                   the mask table, (V n).mask is `K1.Ride.lay` of coins c₀, and c₀ t, for t below 2 fv + 1, is the sending's
                   own coin number (the coins of the messages in front) + `fromE` + t

Limits. That `rowsAll` returns is a premise. Nothing is said of a witness, a book or a run.
-/
import Johnson.Desc.ProofFile.Honest.K10.Pay.XchFreshCoins
import Johnson.Desc.ProofFile.Honest.K2.Law.MaskCoin
import Johnson.Desc.ProofFile.Honest.K12.CutOfBook

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10
open OnBytes.Slice (GE)
open Johnson.Prover.Send (Rows)
open VerifiableInference.Desc.K2.Honest (zeroG)
open ProofFile.Honest.K2 (Stretch messageRows freshTable fromE inMaskOf rowsAll foldAt dueBefore messageDue sendingDue)

/-- A coin that is read by number is the coin of that number. -/
theorem eAt_stretch {d : Due} (c : Cs d) {i : Nat} {v : Cb.Gl.E} (h : c.eAt i = .ok v) :
    i < d.e ∧ (K12.stretchOf c).e i = v := by
  unfold Cs.eAt at h
  split at h
  · rename_i hi
    refine ⟨hi, ?_⟩
    unfold K12.stretchOf
    show (if h : i < d.e then c.e ⟨i, h⟩ else 0) = v
    rw [dif_pos hi]
    exact Except.ok.inj h
  · cases h

/-- What the shared text lays at a fold's fresh mask, with "it is a fresh mask" as an equation. -/
theorem fresh_mask_at {codes : OnBytes.Codes} {s : OnBytes.OracleShape} {fold : Option Nat} {fv : Nat}
    (hf : fold = some fv) {data : Nat → Nat → Cb.Gl.E} {k : Stretch} {Rr : Rows}
    (h : messageRows freshTable codes s fold data k = .ok Rr) :
    ∃ cM : Array Cb.Gl.E, (∀ t, t < 2 * fv + 1 → k.coins.eAt (fromE codes s + t) = .ok (cM.getD t zeroG)) ∧
      ∀ r i, r < s.maskRows → i < (codes.mask.getD s.maskCode default).ell →
        Rr.mask r i = (⟨fv, OnBytes.ceilLog2 s.maskRows⟩ : K1.Ride).lay (cM.getD · zeroG) r i := by
  subst hf
  obtain ⟨cM, hM, hR⟩ := fresh_message_mask h
  exact ⟨cM, fun t ht => fresh_message_coin hM ht, hR⟩

/-- **What a sending lays at the message that is a fold's fresh mask, in the sending's own coins.** -/
theorem sent_fresh_mask {codes : OnBytes.Codes} {sent : Array OnBytes.OracleNotice} {fresh : Option (Nat × Nat)}
    {data : Nat → Nat → Nat → Cb.Gl.E} {c : Cs (sendingDue codes sent fresh)} {V : Nat → Rows}
    (h : rowsAll freshTable codes sent fresh data c = .ok V) {n fv : Nat} (hn : n < sent.size)
    (hf : foldAt fresh n = some fv) :
    ∃ c₀ : Nat → GE,
      (∀ t, t < 2 * fv + 1 → c₀ t =
        (K12.stretchOf c).e ((dueBefore codes sent fresh n).e + (fromE codes (sent.getD n default).shape + t))) ∧
      ∀ r i, r < (sent.getD n default).shape.maskRows →
        i < (codes.mask.getD (sent.getD n default).shape.maskCode default).ell →
        (V n).mask r i =
          (⟨fv, OnBytes.ceilLog2 (sent.getD n default).shape.maskRows⟩ : K1.Ride).lay c₀ r i := by
  obtain ⟨c', hc', hm⟩ := K2.rowsAll_at h hn
  obtain ⟨cM, hM, hR⟩ := fresh_mask_at hf hm
  refine ⟨(cM.getD · zeroG), fun t ht => ?_, hR⟩
  obtain ⟨hlt, hv⟩ := eAt_stretch c' (hM t ht)
  show cM.getD t zeroG = _
  rw [← hv]
  exact K12.Light.cut_at c _ _ c' hc' _ hlt

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.eAt_stretch
#print axioms ProofFile.Honest.K10.fresh_mask_at
#print axioms ProofFile.Honest.K10.sent_fresh_mask
