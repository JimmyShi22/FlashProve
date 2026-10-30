-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoBaseTotal.lean: the attention sub-proof's lookup inside the one
equation, for EVERY pair of lists with the base property. The statements and the proof follow those
of OnBytes/Tie/Pv/Lookup/Ends/FoAddsAttV.lean.

claims_addedL and att_look_total (OnBytes/Tie/Pv/Lookup/Ends/FoAddsAttV.lean) begin "there are lists
A, B such that …". Two statements of that form need not speak of the same lists. Here what
claims_addedL says of its lists has a name, and what att_look_total says is shown of every pair of
lists with that property.

 - AttBase P h A B: claims_addedL's clause on A and B, to the letter: every run of Attention.claims
   P h that returns, from a state with one coefficient for each slot and of the right sizes, has
   added the lookup's rows, A, the lookup's join, B, and then runs Forest.planeLins; A and B have
   the counted lengths.
 - attBase_ex: there are such lists (claims_addedL).
 - AttTotalIs P h A B: att_look_total's clause on A and B, to the letter.
 - att_look_totalB: AttBase P h A B gives AttTotalIs P h A B. The proof is att_look_total's, which
   only hands A and B on.

Limits: attention alone. The equation keeps the total and the number of claims of the state in which
Attention.claims began (F.total, F.nClaim): that they are 0 there is not drawn here.
Not claimed: anything on soundness, completeness or hiding. Nor is it claimed that a run returns.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoAddsAttV

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Fo
open TwV OnBytes OnBytes.Model OnBytes.PscRun OnBytes.Attention Cb.Fo

/-- What claims_addedL says of its two lists. -/
def AttBase (P : Plan) (h : Attention.Heard)
    (A B : (ℕ → ℕ) → List Cl) : Prop :=
      ∀ (F G : Fork) (c c' : Ctx), Attention.claims P h F c = .ok (((), G), c') →
        F.LS.size = F.ns → Sized F →
        (A (colsOf F)).length = cnt3 h + cnt4 h + cnt5 h ∧
        (B (colsOf F)).length = cnt6 h + cnt7 h + cnt8 h ∧
        ∃ (Fp : Fork) (cp : Ctx),
          Added F Fp ((h.g.rows.toList.map fun f => (f, #[])) ++ A (colsOf F) ++
            [(joinForm h.g (joinsA h P.NC).kf, #[])] ++ B (colsOf F)) ∧
          colsOf Fp = colsOf F ∧ Later F Fp ∧ Sized Fp ∧
          Forest.planeLins h.g h.S.cf.lmb
            (fun e col => u3at h (if e == 0 then h.t.tBit0 else h.t.tBit1) col)
            (fun col => u3at h h.t.tPin col) Fp cp = .ok (((), G), c')

theorem attBase_ex (P : Plan) (h : Attention.Heard) : ∃ A B, AttBase P h A B :=
  claims_addedL P h

/-- What att_look_total says of its two lists. -/
def AttTotalIs (P : Plan) (h : Attention.Heard)
    (A B : (ℕ → ℕ) → List Cl) : Prop :=
      ∀ (F G : Fork) (c c' : Ctx), Attention.claims P h F c = .ok (((), G), c') →
        F.LS.size = F.ns → Sized F →
        (A (colsOf F)).length = cnt3 h + cnt4 h + cnt5 h ∧
        (B (colsOf F)).length = cnt6 h + cnt7 h + cnt8 h ∧
        ∀ (K : Type) [CommRing K] (ρ : Reading K) (F0 : Fork) (jLK : ℕ) (rsK : Rounds K),
          HeardIs ρ h.g F0 (endsOf h.g.shape h.S.cf.lmb jLK rsK) → Later F0 F →
          FoNums.ok h.g.shape = true → P.NC = h.g.shape.NC →
          ∀ (H : Fork), Later G H → ∀ (ν : Pl → K) (entry : ℕ → ℕ → ℕ → K),
            ReadsLaw h.g.shape h.S.cf.lmb (endsOf h.g.shape h.S.cf.lmb jLK rsK).zb0
              (endsOf h.g.shape h.S.cf.lmb jLK rsK).zb1 ν entry h.iU3 (colsOf F h.iU3) h.t.tBit0
              h.t.tBit1 h.t.tPin →
            G.total ρ (H.worldOf ρ (fun j => ν (.mask j)) entry) =
              F.total ρ (H.worldOf ρ (fun j => ν (.mask j)) entry) +
                powSum (ρ.val F.theta) F.nClaim
                  ((endsOf h.g.shape h.S.cf.lmb jLK rsK).rows.map (rowRes ν)) +
                clsValue ρ (H.worldOf ρ (fun j => ν (.mask j)) entry) (ρ.val F.theta)
                  (F.nClaim + h.g.rows.size) (A (colsOf F)) +
                ρ.val F.theta ^ (F.nClaim + h.g.rows.size + (cnt3 h + cnt4 h + cnt5 h)) *
                  claimJoin h.g.shape h.S.cf.lmb jLK rsK ν
                    (fun q => (kfA h q).value ρ (H.worldOf ρ (fun j => ν (.mask j)) entry)) +
                clsValue ρ (H.worldOf ρ (fun j => ν (.mask j)) entry) (ρ.val F.theta)
                  (F.nClaim + h.g.rows.size + (cnt3 h + cnt4 h + cnt5 h) + 1) (B (colsOf F)) +
                powSum (ρ.val F.theta)
                  (F.nClaim + h.g.rows.size + (cnt3 h + cnt4 h + cnt5 h) + 1 +
                    (cnt6 h + cnt7 h + cnt8 h))
                  [claimLeaves h.g.shape h.S.cf.lmb jLK rsK ν
                      (colsK h.g.shape h.S.cf.lmb (endsOf h.g.shape h.S.cf.lmb jLK rsK).zb0 ν),
                    claimBits h.g.shape h.S.cf.lmb jLK rsK ν
                      (colsK h.g.shape h.S.cf.lmb (endsOf h.g.shape h.S.cf.lmb jLK rsK).zb1 ν),
                    Pin.countK h.g.shape h.S.cf.lmb (Pin.pinColK h.S.cf.lmb ν)]

/-- The lookup inside the one equation, for every pair of lists with the base property. -/
theorem att_look_totalB (P : Plan) (h : Attention.Heard)
    (A B : (ℕ → ℕ) → List Cl)
    (hb : AttBase P h A B) : AttTotalIs P h A B := by
  have HH : AttBase P h A B := hb
  intro F G c c' hr hs hF
  obtain ⟨hA, hB, Fp, cp, pre, kp, lp, zp, hpl⟩ := HH F G c c' hr hs hF
  refine ⟨hA, hB, fun K _ ρ F0 jLK rsK hI h0 hok hNC H hH ν entry Lw => ?_⟩
  have R := readsAt_attention h Fp cp
  rw [congrFun kp h.iU3] at R
  obtain ⟨lq, _, _, hg⟩ := planeLins_reads ρ h.g h.S.cf.lmb jLK rsK (bitAtt h) (pinAtt h) F0 Fp G
    cp c' R hpl hI (h0.trans lp) hok pre.sized zp
  obtain ⟨t1, _, _⟩ := hg H hH ν entry Lw
  have hsz : (joinsA h P.NC).kf.size = h.g.shape.NC := (kf_size h P.NC).trans hNC
  have lH : Later F0 H := ((h0.trans lp).trans lq).trans hH
  have eR := PlaneClaims.rows_claim ρ h.g h.S.cf.lmb jLK rsK F0 hI H lH ν entry
  have eJ : (joinForm h.g (joinsA h P.NC).kf).value ρ (H.worldOf ρ (fun j => ν (.mask j)) entry) =
      claimJoin h.g.shape h.S.cf.lmb jLK rsK ν
        (fun q => (kfA h q).value ρ (H.worldOf ρ (fun j => ν (.mask j)) entry)) := by
    rw [joinForm_claim ρ h.g h.S.cf.lmb jLK rsK F0 hI hok _ hsz H lH ν entry]
    refine claimJoin_congr _ _ _ _ _ _ _ fun q hq => ?_
    rw [kf_at h P.NC q (by rw [hNC]; exact hq)]
  rw [t1, pre.total, pre.theta, pre.nClaim]
  simp only [clsValue_append, clsValue_forms, claimsValue_powSum, List.length_append,
    List.length_map, Array.length_toList, List.length_cons, List.length_nil, hA, hB]
  rw [eR]
  have e1 : clsValue ρ (H.worldOf ρ (fun j => ν (.mask j)) entry) (ρ.val F.theta)
      (F.nClaim + (h.g.rows.size + (cnt3 h + cnt4 h + cnt5 h)))
      [(joinForm h.g (joinsA h P.NC).kf, #[])] =
      ρ.val F.theta ^ (F.nClaim + h.g.rows.size + (cnt3 h + cnt4 h + cnt5 h)) *
        (joinForm h.g (joinsA h P.NC).kf).value ρ
          (H.worldOf ρ (fun j => ν (.mask j)) entry) := by
    simp [clsValue, sumFrom, value_form, Nat.add_assoc]
  rw [e1, eJ]
  simp only [Nat.add_assoc, Nat.zero_add]
  ring

end Fo
