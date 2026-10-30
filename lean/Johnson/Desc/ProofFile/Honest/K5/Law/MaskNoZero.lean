-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/MaskNoZero.lean: NUMBERS OF A PUBLIC PLAN: CONDITIONAL, under
the library's hypothesis h on the public input (`P5J.AtMgA`): K5's NUMBER OF THE MESSAGE THAT HOLDS
THE MASK ROW OF ATTENTION SEGMENT 2 g + 1 (`maskNo5`) IS THE PLAN's NUMBER OF (that segment, its own
message 0): `P5J.At.num Zp (2 * g + 1) 0`. It is our half of the tie between a code switch's message
and K5's own name of it. No run, no input, no book. No definition; four theorems.

Main names:
  `P6T.keptN_congr`: `keptN` reads its record at the shape alone.
  `P6T.mask_first_written`: A CLOSED FACT; Lean's kernel evaluates it: at the library's written
    shape, at each g < 12, `maskMsg` names the member right behind the kept ones: the first own
    message of segment 2 g + 1 has a mask row.
  `maskNo5_is_num_at`: `maskNo5_is_num` (MaskNos.lean in this folder) WITH ONE CONJUNCT MORE: kM =
    `keptN` + mi: the equation that its proof has and its statement drops. The elder law stands as
    it is; this one gives it.
  `maskNo5_at_head`: h; hg: g < 12; hx: the place's link is 2 g + 1; hm: `maskMsg` names kM: the
    number.

How `maskNo5_at_head` goes. The sharper law: kM = `keptN` at the head's record + mi. Under h the
plan's shape is the written one (`shape_written`); `maskMsg` and `keptN` read the shape alone
(`P6T.maskMsg_congr`, `P6T.keptN_congr`); so by the closed fact kM = `keptN` at the written record:
mi = 0.

Limits. CONDITIONAL. THE TIE IS NOT MET HERE: this file has K5's side alone: that a code switch's
message number 3 bears that same number of the plan is not said and not called here. hx, the place's
link, is a premise of `maskNo5_at_head`: where the place is a return of `lookAt`, the sealed
`VerifiableInference.OnPublicFiles.lookAt_link` (Johnson/Desc/First/Look/K3CallsAddress.lean) has it: not
called here. That a lot with that number stands in the frame's list is not said here.
`maskNo5_is_num_at`'s proof is `maskNo5_is_num`'s, line for line, but for one term: two texts of one
proof in one house: the elder could be one call of the sharper. The closed fact is an evaluation by
Lean's kernel of the library's written shape: it says what that term comes to. At the earlier hash
`OnBytes.secondHashFunction` alone.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.MaskNos

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P6T
open P5T
open VerifiableInference.Desc.First.Look (Sent keptAt bornAt messagesAt)
open VerifiableInference.Desc.First.Att.P (maskMsg)

/-- `keptN` reads D at its shape alone. -/
theorem keptN_congr {D D' : Sent} (e : D.shape = D'.shape) : keptN D = keptN D' := by
  funext i
  unfold keptN keptAt
  rw [e]

/-- **At the written shape the first own message of each attention segment has a mask row**:
`maskMsg` names the member right behind the kept ones. By evaluation in Lean's kernel. -/
theorem mask_first_written : ∀ g, g < 12 →
    maskMsg sentShape (2 * g + 1) = some (keptN sentShape (2 * g + 1)) := by
  decide +kernel

end P6T

namespace ProofFile.Honest.K5
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.First.Look (sigListCalls)
open VerifiableInference.Desc.First.Att.P (maskMsg)
open P5J (AtMgA TS)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)

/-- **`maskNo5_is_num`, with the equation between kM and mi kept.** CONDITIONAL: under the
hypothesis h; `maskMsg` names member kM. -/
theorem maskNo5_is_num_at {x₁ : VerifiableInference.Desc.First.Look.Place} {kM : ℕ}
    {hk : kM < (sigListCalls h.𝔇.sent h.𝔇.l3.rad x₁.link).length}
    (hm : maskMsg h.𝔇.sent x₁.link = some kM) :
    ∃ (Lk : OnBytes.Params.ReqLink) (mi : ℕ), Zp.first.shape.link[x₁.link]? = some Lk ∧
      mi < Lk.messages.length ∧ kM = P6T.keptN (P5J.At.sentAt Zp) x₁.link + mi ∧
      maskNo5 h x₁ kM hk = P5J.At.num Zp x₁.link mi := by
  have hm' : maskMsg (P5J.At.sentAt Zp) x₁.link = some kM := hm
  obtain ⟨Lk, mi, hl, hmi, rfl⟩ := P6T.maskMsg_some hm'
  obtain ⟨p, p₀, hc, hf, hk0⟩ := P6T.maskSeats_gives (maskSeats_head h)
    (List.getElem?_eq_some_iff.1 hl).1 hm'
  have key := P6T.key_of_call hc (Nat.le_add_right _ _)
  rw [Nat.add_sub_cancel_left] at key
  refine ⟨Lk, mi, hl, hmi, rfl, ?_⟩
  have es : P6T.seatCallsT (P5J.At.pseats Zp) (P5J.At.sentAt Zp) x₁.link
      (P6T.keptN (P5J.At.sentAt Zp) x₁.link + mi) = (p.j, p.t) := by
    unfold P6T.seatCallsT
    rw [hc]
    rfl
  show P5J.At.arr Zp (P6T.seatCallsT (P5J.At.pseats Zp) (P5J.At.sentAt Zp) x₁.link
      (P6T.keptN (P5J.At.sentAt Zp) x₁.link + mi)).1
    (P6T.seatCallsT (P5J.At.pseats Zp) (P5J.At.sentAt Zp) x₁.link
      (P6T.keptN (P5J.At.sentAt Zp) x₁.link + mi)).2 = _
  rw [es]
  exact P5T.arrOf_is_num _ p.j p.t x₁.link mi p₀ hf (hk0.trans key)

/-- **K5's NUMBER OF THE MESSAGE WITH SEGMENT 2 g + 1's MASK ROW IS THE PLAN's NUMBER OF (that
segment, own message 0).** CONDITIONAL: under the hypothesis h; hg; hx: the place's link; hm:
`maskMsg` names member kM. -/
theorem maskNo5_at_head {x₁ : VerifiableInference.Desc.First.Look.Place} {kM : ℕ}
    {hk : kM < (sigListCalls h.𝔇.sent h.𝔇.l3.rad x₁.link).length} {g : ℕ} (hg : g < 12)
    (hx : x₁.link = 2 * g + 1) (hm : maskMsg h.𝔇.sent x₁.link = some kM) :
    maskNo5 h x₁ kM hk = P5J.At.num Zp (2 * g + 1) 0 := by
  obtain ⟨Lk, mi, -, -, ek, en⟩ := maskNo5_is_num_at h (hk := hk) hm
  have e3 : (P5J.At.sentAt Zp).shape = P6T.sentShape.shape := h.toAtMg.shape_written
  have hm' : maskMsg (P5J.At.sentAt Zp) x₁.link = some kM := hm
  rw [P6T.maskMsg_congr e3, hx, P6T.mask_first_written g hg] at hm'
  have e0 : P6T.keptN P6T.sentShape (2 * g + 1) = kM := Option.some.inj hm'
  rw [P6T.keptN_congr e3, hx] at ek
  have e1 : mi = 0 := by omega
  subst e1
  rw [en, hx]

end ProofFile.Honest.K5

#print axioms P6T.keptN_congr
#print axioms P6T.mask_first_written
#print axioms ProofFile.Honest.K5.maskNo5_is_num_at
#print axioms ProofFile.Honest.K5.maskNo5_at_head
