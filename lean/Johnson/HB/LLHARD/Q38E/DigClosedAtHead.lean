-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/HB/LLHARD/Q38E/DigClosedAtHead.lean: the closed side of `DigAheadOk`
(Johnson/Desc/First/Look/K3DigitsAhead.lean) under the one head, joined: for every witness and every
cell of the digits' array in the condition's range there is one seat at which four of the
condition's six clauses hold, in its own letters: the cell has that seat; the seat lies in its
table; the first member of the table's list at the seat has the list's shape; and what the witness's
messages hold at the cell is the caller's reading there.

Row or tool. A joining of Johnson/HB/LLHARD/Q38E/ClosedOfOk.lean, TiesAtHead.lean and
MemAtHead.lean. For the law on the digits of the sub-protocol K8: the condition `DigAheadOk` at the
state behind the draw of the approximate range proof.

What it spends. Rows are those of the proof file's entry tests, `LPFD.lawsAsk`
(Johnson/Desc/Laid/ProofAsks.lean), counted from 1: row 1 holds the
declared rounds to the written ones, row 9 the made plan (`madeRow`), row 11 is the lookups' digits'
row (`digEntry`). `digClosed_at_head`: row 11 (through `digOK_at_head`), and the head's fields
`pubOne` (through `cols_at_head`) and `k3` (through `memAt_at_head`); h6 is a premise.
`e_digClosed_at_head`: rows 1, 9 and 11: it pays h6 by `oneShape_at_head`.

What is here (namespace Q38).
  `digClosed_at_head`: under `h6 : oneShapeB (At.ms Zp Z.lay) = true`.
  `e_digClosed_at_head`: the same with that premise paid: no premise beside the head, the segment's
    number and the reader's answer.

Limits. The other two clauses, on what is still ahead, speak of a state of the verifier and are not
touched here; they must be shown at this seat. Nothing on soundness.


-/
import Johnson.HB.LLHARD.Q38E.ClosedOfOk
import Johnson.HB.LLHARD.Q38E.TiesAtHead
import Johnson.HB.LLHARD.Q38E.MemAtHead
import Johnson.Desc.First.Look.K3DigitsAhead

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace Q38
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Chain Wit)
open VerifiableInference.Desc.Sound (MsgT msgsOf)
open VerifiableInference.Desc.First.Look
open VerifiableInference.Desc.First.Att.P (MemAt)
open VerifiableInference.OnPublicFiles (oneShapeB digMu)
open P5J (AtMgA)

variable {Z : VerifierAndGoals.PublicFiles} {D₀ : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl} {x₀ : Place}

set_option maxRecDepth 40000 in
/-- **The closed side, joined: one seat for four clauses.** -/
theorem digClosed_at_head (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀) {l : ℕ} (hl : l ≤ 24)
    {x : Place} {tl : HTailF2} (hx : digAt (P5J.At.X Zp) l = some (x, tl))
    (h6 : oneShapeB (P5J.At.ms Zp Z.lay) = true) :
    ∀ (w : Wit (P5J.CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT),
      ∀ μ, μ < tl.NM → ∀ u, u < tl.tau → ∀ i, i < (tl.mats.getD μ {}).m → ∀ b, b < 2 →
      ∃ z : Seat,
        seatOf h.𝔇.sent x.link (.cell tl.ix.ZZ u ((tl.zzCol μ b 0).getD 0 + i)) = some z ∧
        z.Fits h.𝔇.sent.codes (digList x h.𝔇.sent h.𝔇.l3.rad) ∧
        (∀ hk : z.msg < (digList x h.𝔇.sent h.𝔇.l3.rad).length,
          MemAt h.𝔇.ms (digList x h.𝔇.sent h.𝔇.l3.rad)
            (fun j => h.𝔇.l3.seat x.link true j.1) ⟨z.msg, hk⟩) ∧
        digVal x h.𝔇.sent h.𝔇.l3.rad
            (msgsOf h.𝔇.sent.codes (digList x h.𝔇.sent h.𝔇.l3.rad)
              (fun j => h.𝔇.l3.seat x.link true j.1) h.𝔇.l3.arr w)
            (.cell tl.ix.ZZ u ((tl.zzCol μ b 0).getD 0 + i)) =
          some (digMu x h.𝔇.sent h.𝔇.l3.rad (fun j => h.𝔇.l3.seat x.link true j.1) h.𝔇.l3.arr w
            (enOf x.arrays (tl.ix.ZZ, u, (tl.zzCol μ b 0).getD 0 + i))) := by
  intro w μ hμ u hu i hi b hb
  obtain ⟨z, h1, h2, h3⟩ :=
    closed_of_ok (digOK_at_head h hl hx) (cols_at_head h hx) hμ hu hi hb
  exact ⟨z, h1, h2, fun hk => memAt_at_head h hl hx h6 ⟨z.msg, hk⟩, h3 _⟩

/-- The same, with "one seat, one shape" paid at the head. -/
theorem e_digClosed_at_head (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀) {l : ℕ} (hl : l ≤ 24)
    {x : Place} {tl : HTailF2} (hx : digAt (P5J.At.X Zp) l = some (x, tl)) :
    ∀ (w : Wit (P5J.CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT),
      ∀ μ, μ < tl.NM → ∀ u, u < tl.tau → ∀ i, i < (tl.mats.getD μ {}).m → ∀ b, b < 2 →
      ∃ z : Seat,
        seatOf h.𝔇.sent x.link (.cell tl.ix.ZZ u ((tl.zzCol μ b 0).getD 0 + i)) = some z ∧
        z.Fits h.𝔇.sent.codes (digList x h.𝔇.sent h.𝔇.l3.rad) ∧
        (∀ hk : z.msg < (digList x h.𝔇.sent h.𝔇.l3.rad).length,
          MemAt h.𝔇.ms (digList x h.𝔇.sent h.𝔇.l3.rad)
            (fun j => h.𝔇.l3.seat x.link true j.1) ⟨z.msg, hk⟩) ∧
        digVal x h.𝔇.sent h.𝔇.l3.rad
            (msgsOf h.𝔇.sent.codes (digList x h.𝔇.sent h.𝔇.l3.rad)
              (fun j => h.𝔇.l3.seat x.link true j.1) h.𝔇.l3.arr w)
            (.cell tl.ix.ZZ u ((tl.zzCol μ b 0).getD 0 + i)) =
          some (digMu x h.𝔇.sent h.𝔇.l3.rad (fun j => h.𝔇.l3.seat x.link true j.1) h.𝔇.l3.arr w
            (enOf x.arrays (tl.ix.ZZ, u, (tl.zzCol μ b 0).getD 0 + i))) :=
  digClosed_at_head h hl hx (oneShape_at_head h)

end Q38


#print axioms Q38.digClosed_at_head
#print axioms Q38.e_digClosed_at_head
