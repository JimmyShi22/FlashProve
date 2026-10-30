-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/Law/LotAtReads.lean: THE SHARED "SENDING" (the kind K1) IN THE
FRAME FOR THE HONEST SIDE: WHAT THE LOT's DATA (lotData,
Johnson/Desc/ProofFile/Honest/K1/LotData.lean) ANSWERS AT A SEAT OF "U3", AT THE ROW AND PLACE AT
WHICH THE LAYOUT LAYS AN ARRAY's ELEMENT: THE VALUE OF "U3"'s ARRAYS THERE. Two statements and their
proofs. No definition.

  u3_at_laid       read through the one call RowData.at_, u3RowsOf Z G x is laidRows G (u3Seats Z G)
                   (u3ValsOf Z G x): by their texts
  lot_val_reads    at a seat s of "U3", under the public test apartOk, at the row and place at which
                   the layout lays element (i, c) of an array a of segment l: lotData answers
                   u3ValsOf's value of a's name at (i, c)

THREE CALLS: data_reads (Johnson/Desc/ProofFile/Honest/K1/LotData.lean: at a seat of "U3", under
apartOk, lotData hands "U3"'s data) · u3_at_laid · laidData_at
(Johnson/Desc/ProofFile/Honest/K5/Law/WayBackFill.lean). u3Rows (Johnson/HonestTrace/U3Rows.lean) is
laidRows with a turned field "ready": RowData.at_ reads heardAt, lays and entry alone.

WHAT LIES BENEATH, among other files: WayBackFill.lean
and WayBack.lean: CONDITIONAL ON THE PROGRAMS' PUBLIC TEST
reqLayoutOk; ONE DIRECTION · U3Rows.lean, with RowOfArray.lean and SeatOf.lean.

Limits. Every premise is asked and none is proved here: apartOk and "s is a seat of U3" (public) and
laidData_at's own. What u3ValsOf's value is, is not said here. Nothing on soundness, on completeness
or on any other property.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.K1.LotData
import Johnson.Desc.ProofFile.Honest.K5.Law.WayBackFill

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open OnBytes VerifiableInference.Desc
open OnBytes.Params (ReqArray)
open OnBytes.HonestTrace (pairOf laidRows)
open OnBytes.HonestTrace.U3 (u3Seats u3ValsOf u3RowsOf)
open ProofFile.Honest.K5 (laidData_at)

/-- Read through the one call, "U3"'s data is its values laid at its seats. -/
theorem u3_at_laid (Z : Pub) (G : Ground) (x : ProofFile.Inst) (R : Readers) (hd : List Fmt.Drawn)
    (a : MsgAddr) (r j : ℕ) :
    (u3RowsOf Z G x).at_ R hd a r j =
      (laidRows G (u3Seats Z G) (u3ValsOf Z G x)).at_ R hd a r j := rfl

/-- **At a seat of "U3", at the layout's place, the lot's data answers the value of "U3"'s
arrays.** -/
theorem lot_val_reads (S : OnBytes.HonestTrace.Sz) (Z : Pub) (G : Ground) (x : ProofFile.Inst)
    (hap : apartOk Z G = true) {s : OnBytes.HonestTrace.Seat} (hs : s ∈ u3Seats Z G)
    (ok : reqLayoutOk G.first.codes G.first.shape G.first.layout = true) {l : ℕ} {nm : String}
    {a : ReqArray} (ha : arrayOf G.first.layout l nm = some a) {i c : ℕ} {rp : ℕ × ℕ}
    (hrp : laidAt a i c = some rp) {M : Params.ReqMessage}
    (hM : Meaning.messageAt G.first.shape l a.message = some M) (hans : M.shape.answers ≠ 0)
    (hA : pairOf (u3Seats Z G) s.addr = some (l, a.message)) {z : ℕ × ℕ}
    (hz : (u3ValsOf Z G x).size l a.name = some z) (hi : i < z.1) (hc : c < z.2) (R : Readers)
    (hd : List Fmt.Drawn) :
    (lotData S Z G x).at_ R hd s.addr rp.1 rp.2 =
      some ((u3ValsOf Z G x).val R (hd.take (OnBytes.HonestTrace.heardOf (u3Seats Z G) s.addr)) l
        a.name i c) := by
  rw [data_reads S Z G x R hd s rp.1 rp.2 hap hs, u3_at_laid]
  exact laidData_at ok ha hrp hM hans _ hA hz hi hc R hd

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.u3_at_laid
#print axioms ProofFile.Honest.K1.lot_val_reads
