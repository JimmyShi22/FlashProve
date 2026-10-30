-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K13/WTextAtEnd.lean: kind K13 (the members' batching): from "each main entry of a message
is the datum of W's job" to "the entries at the places of W's vector are the text's": the vector
`wVec` (Johnson/Desc/ProofFile/Honest/K13/WData.lean) at the index's reader and at the row weights
`wG` that the filling `pileAnyK3` makes of the challenges. The full size, and the hash function
`OnBytes.secondHashFunction`, alone. One statement with its proof; no definition.

Main name. `k13_wText_of_word`: m: any words; n: any number of a message; hd: any list of
challenges; u: what the job's reader makes of an input. From hword (each main entry of m at n is the
job's datum at u and hd) the entries at the places that W's layout gives the vector are `wVec`'s, at
`wG` of the first `wHeard` challenges of hd.

Limits. hword IS A PREMISE: kind K1's law on its sender's words pays it. Nothing here names a
thread, a state or a witness.

What is not claimed. It is none of the library's goals. Nothing on soundness, completeness or
hiding.
-/
import AtFullSide.K13.WitnessHasWAt356

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K13
open OnBytes
open ProofFile.Honest ProofFile.Honest.K13
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.K13.Law (wMsgFull)
open P5J (AtMgA TS)
open ProofFile.Honest.K1 (PlaceIn)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh)

include h in
/-- hword is a premise. **From "each main entry is the job's datum" to "the vector's entries are
`wVec`'s".** u: what the job's reader makes of the input. hd: the challenges that the job is handed.
m: the words. n: W's number. -/
theorem k13_wText_of_word {X' : Type} (G : ProofFile.Ground) (first : ℕ) (own₀ : X')
    (u : PlaceIn ProofFile.Inst) (hd : List Fmt.Drawn) (m : OnBytes.Means.Words OnBytes.Slice.GE) (n : ℕ)
    (hword : ∀ r j,
      r < (Johnson.Prover.Send.shapeAt
        (K1.wJobAt (X := X') Zp.first (K1.wGp Zp) 4 wMsgFull first
          (wDataAt pileAnyK3 Zp G)).P 0).mainRows →
      j < ((K1.wJobAt (X := X') Zp.first (K1.wGp Zp) 4 wMsgFull first
        (wDataAt pileAnyK3 Zp G)).P.codes.base.getD (Johnson.Prover.Send.shapeAt
          (K1.wJobAt (X := X') Zp.first (K1.wGp Zp) 4 wMsgFull first
            (wDataAt pileAnyK3 Zp G)).P 0).code default).ell →
      m n .main (r + 2 ^ Johnson.Pack.k1 (Johnson.Prover.Send.shapeAt
        (K1.wJobAt (X := X') Zp.first (K1.wGp Zp) 4 wMsgFull first
          (wDataAt pileAnyK3 Zp G)).P 0) * j) =
        match (K1.wJobAt (X := X') Zp.first (K1.wGp Zp) 4 wMsgFull first
          (wDataAt pileAnyK3 Zp G)).data u { heard := hd, own := own₀, seen := .bare [] } 0 r j with
        | some (.inr x) => x
        | some (.inl x) => algebraMap OnBytes.Slice.GF OnBytes.Slice.GE x
        | none => 0) :
    ∀ e < 2 ^ Zp.first.lin.kCol,
      m n .main ((linLayW Zp.first.codes Zp.first.lin).index e) =
        wVec Zp.first.lin u.R.weights
          (wG Zp.first.lin (wHeard Zp) (pileAnyK3 Zp G) u.x (hd.take (wHeard Zp))) e := by
  intro e he
  obtain ⟨Bs, base₀, O⟩ := h.laid.opened
  have hmsg := K1.msg_w_head h O
  obtain ⟨hl, hno⟩ := k13_wLays_at_head h pileAnyK3 G u.x he
  obtain ⟨hr, hj⟩ := wPair_lays_in_shape pileAnyK3 Zp G _ hmsg hl
  have hsh : Johnson.Prover.Send.shapeAt
      (K1.wJobAt (X := X') Zp.first (K1.wGp Zp) 4 wMsgFull first (wDataAt pileAnyK3 Zp G)).P 0 =
      Zp.first.lin.w := K1.w_shape_zero Zp.first (K1.wGp Zp) 4 wMsgFull hmsg
  have W := hword _ _ hr hj
  have hidx : (linLayW Zp.first.codes Zp.first.lin).index e %
        2 ^ (linLayW Zp.first.codes Zp.first.lin).rowBits +
      2 ^ Johnson.Pack.k1 (Johnson.Prover.Send.shapeAt
        (K1.wJobAt (X := X') Zp.first (K1.wGp Zp) 4 wMsgFull first
          (wDataAt pileAnyK3 Zp G)).P 0) *
        ((linLayW Zp.first.codes Zp.first.lin).index e /
          2 ^ (linLayW Zp.first.codes Zp.first.lin).rowBits) =
      (linLayW Zp.first.codes Zp.first.lin).index e := by
    rw [hsh]
    exact Nat.mod_add_div _ _
  rw [hidx] at W
  refine W.trans ?_
  rw [wPair_data pileAnyK3 Zp G wMsgFull first u _ 0 _ _, if_pos ⟨rfl, hl⟩]
  show wVec Zp.first.lin u.R.weights
    (wG Zp.first.lin (wHeard Zp) (pileAnyK3 Zp G) u.x (hd.take (wHeard Zp))) _ = _
  rw [hno]

end AtFullSide.K13

#print axioms AtFullSide.K13.k13_wText_of_word
