-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/Door/Law/K5LeftFitsE.lean: kind K5: LEAVES OF "WHAT IS LEFT OF THE KIND's LAW AT THE TABLE" (the structure K5Owes, Door/Law/K5AtMgPaid.lean) THAT FOLLOW FROM WHAT LIES: each theorem concludes a leaf's own text.
  hRd_plus: the composed data's readers at the segment ARE the readers of the link, with the two holes holesAt (readersAt_some; both in Johnson/Desc/First/Batch/ReadersAt.lean) · silent_none: away from the output head's segment the second hole is silent · forms_is_run: so there whatever the readers give at a name other than
    "K8.equations" is what the run's own reader gives.
  attAt_plus: attAt (Johnson/Desc/First/Look/K3AttInst.lean) at the segment returns the place, the plan's shape and the plan's parameters of the smallness test · pieceAt_plus: the lookup on the calls stands at number 2 inside the segment.
  notHead_plus: an attention segment is not the output head's · attOK_plus · callsFit_plus: from the guard's yes and the plan · planOk_plus · claimsOk_plus: from the seated sub-protocol's own test on its parameters.
PREMISES THAT STAY: equations on the composed meaning's letters (D.Rd = readersAt lk X mH · D.mH = headLink Wv, the latter written out), by its make; the plan's and the guard's public facts.
IS IT EMPTY HERE? Implications.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.Door.Law.K5LeftFitsD
import Johnson.Desc.First.Batch.ReadersAt
import Johnson.Desc.First.Look.K3AttInst
import Johnson.Desc.First.Att.K05LawGuard

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace H2K5.Door
open Cb Cb.Fo Cb.LdLkp OnBytes OnBytes.Model OnBytes.Model.Road OnBytes.Maker Johnson.Pack
open VerifiableInference.Desc VerifiableInference.Desc.First VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First.Look (Sent attSg JAtt enMask lookAt placeAt k3SortAt)
open VerifiableInference.Desc.First.FillK4 (isLay)
open VerifiableInference.Desc.K9 (RunOf readerOf)
open VerifiableInference.Desc.K13.Law (DataK13 fillK13)
open VerifiableInference.OnPublicFiles (k3LeftItemAt k3LeftOnItemAt)
open VerifiableInference.Desc.First.Att.P
open VerifiableInference.Desc.K12.Door (Laid)
open VerifiableInference.Desc.First.Look (AttOK attAt)
open VerifiableInference.Desc.K9 (Readers statesOfLink readersOfLink LinkHoles readersAt holesAt readersAt_some)

/-! ## The readers -/

theorem hRd_plus {D : PubData} {lk : ℕ → Option (Link S Claim)} {X : Verify.Public} {mH : ℕ} (hDR : D.Rd = readersAt lk X mH) {m : ℕ}
    {Lk : Link S Claim} (hl : lk m = some Lk) : D.Rd m = readersOfLink (holesAt X mH m Lk) Lk := by
  rw [hDR]
  exact readersAt_some lk X mH m Lk hl

/-- Away from the output head's segment the second hole is silent. -/
theorem silent_none (X : Verify.Public) {mH m : ℕ} (h : (m == mH) = false) (Lk : Link S Claim) :
    (holesAt X mH m Lk).silent = fun _ _ _ => none := by
  unfold holesAt
  simp only [h]
  rfl

/-- **So there the readers give nothing but the run's own reader's answer.** -/
theorem forms_is_run (X : Verify.Public) {mH m : ℕ} (h : (m == mH) = false) (Lk : Link S Claim) (b : ℕ) (name : String)
    (hn : (name == "K8.equations") = false) (s : S) :
    (readersOfLink (holesAt X mH m Lk) Lk).forms b name s = readerOf (statesOfLink Lk) b name s := by
  show (if name == "K8.equations" then (holesAt X mH m Lk).small s
    else match readerOf (statesOfLink Lk) b name s with
      | some R => some R
      | Option.none => (holesAt X mH m Lk).silent b name s) = _
  rw [hn, silent_none X h Lk]
  cases readerOf (statesOfLink Lk) b name s <;> rfl

/-! ## The place -/

section
variable {Wv : Verify.Public} {g : ℕ} {a : Attention.Plan} {x : Look.Place}

theorem attAt_plus (hP : PlanIs Wv) (h4 : Wv.p4 = true) (ha : Wv.A[g]? = some a) (hx : lookAt Wv (2 * g + 1) false = some x) :
    attAt Wv (2 * g + 1) = some (x, a.S, a.seam.tl) := by
  have e1 := (guard_theorems hP h4 ha hx (Params.settingOf Wv.P.frame)).1
  unfold attAt
  rw [if_pos ⟨h4, by omega⟩, hx]
  have hd : (2 * g + 1) / 2 = g := by omega
  simp only [Option.bind_some, hd, ha, e1, Option.map_some]

theorem pieceAt_plus (h4 : Wv.p4 = true) : K3.pieceAt Wv (2 * g + 1) false = 2 := by
  unfold K3.pieceAt
  rw [notHead h4 g]
  rfl

/-- hmH's right side is headLink Wv, written out (Johnson/Desc/First/Look/K3HeadStated.lean: not imported). -/
theorem notHead_plus {D : PubData} (hmH : D.mH = (if Wv.p4 then 2 else 1) * Wv.NGr) (h4 : Wv.p4 = true) : (2 * g + 1 == D.mH) = false := by
  rw [hmH]
  exact beq_eq_false_iff_ne.2 (odd_facts (W := Wv) (g := g) h4).1

variable (before : List (ℕ × ℕ)) (Dn : Sent) (rad : OracleShape → Nat)

theorem attOK_plus (hP : PlanIs Wv) (h4 : Wv.p4 = true) (ha : Wv.A[g]? = some a) (hx : lookAt Wv (2 * g + 1) false = some x)
    (hG : k5GuardN Wv (2 * g + 1) g = true) (hb : planOk (parO Wv (2 * g + 1) a before) = true) (hc : claimsOkAtO a = true) :
    AttOK (Params.settingOf Wv.P.frame) x a.S a.seam.tl Dn rad := by
  obtain ⟨x', A0, hx', ⟨pf, e⟩, Pb⟩ := guard_gives_written hP h4 g before Dn rad ha hG hb hc
  obtain rfl : x' = x := Option.some.inj (hx'.symm.trans hx)
  have eS : a.S = A0.S := by rw [e]
  exact eS ▸ Pb.att

theorem callsFit_plus (hP : PlanIs Wv) (h4 : Wv.p4 = true) (ha : Wv.A[g]? = some a) (hx : lookAt Wv (2 * g + 1) false = some x)
    (hG : k5GuardN Wv (2 * g + 1) g = true) : OnBytes.Road.L5.CallsFit a.S x.fs := by
  unfold k5GuardN k5ListN at hG
  rw [ha, hx] at hG
  dsimp only at hG
  obtain ⟨_, _, gc, _⟩ := guardList_gives hG
  rw [(guard_theorems hP h4 ha hx (Params.settingOf Wv.P.frame)).2.2.1]
  exact gc

theorem planOk_plus {blk : Block S Claim} (h : k5AtN Wv (2 * g + 1) g before = some blk) (hok : blk.planOk = true)
    (ha : Wv.A[g]? = some a) : planOk (parO Wv (2 * g + 1) a before) = true := (planOk_of_blk h hok ha).1

theorem claimsOk_plus {blk : Block S Claim} (h : k5AtN Wv (2 * g + 1) g before = some blk) (hok : blk.planOk = true)
    (ha : Wv.A[g]? = some a) : claimsOkAtO a = true := (planOk_of_blk h hok ha).2

end

end H2K5.Door

#print axioms H2K5.Door.hRd_plus
#print axioms H2K5.Door.silent_none
#print axioms H2K5.Door.forms_is_run
#print axioms H2K5.Door.attAt_plus
#print axioms H2K5.Door.pieceAt_plus
#print axioms H2K5.Door.notHead_plus
#print axioms H2K5.Door.attOK_plus
#print axioms H2K5.Door.callsFit_plus
#print axioms H2K5.Door.planOk_plus
#print axioms H2K5.Door.claimsOk_plus
