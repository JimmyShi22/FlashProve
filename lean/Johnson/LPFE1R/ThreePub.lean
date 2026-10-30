-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/LPFE1R/ThreePub.lean: THE TWO CLOSED FACTS P2 · P3 OF
three_of_leftOn (LPFE1R/ThreeOfLeftOn.lean) FROM THE DIGITS' LOOKUP's PLAN (DigOK: LeftRest's own
field dig). Statements and proofs.

  three_pub         the library's test on the smallness test's record (DgP.shapeTest2) gives: 5 ≤ kT
                    + cK (the first call's table has 2 ^ 10 rows: PortOK.wide; kOf ≤ kT: Port.OK) ·
                    both calls are there (TailOK.nc) · each call's n is the structure's own
                    (PortOK.call)
  three_of_dig      LeftRest's field three from: OkCore out of Ok · DigOK at tlD · K3LeftOn at the
                    shape tlD.f9 at the state in front

Limits. AN IMPLICATION: K3LeftOn at tlD.f9 at the states in front of the batching is shown in
Johnson/P5J/K09LeftD.lean (P5J.leftD_at) at the states that meet the condition in front of the
batching, from the standing hypotheses (P5J.AtMgA) at OnBytes.secondHashFunction, m < 25 and digAt (At.X Zp) m =
some (xx, tlD). No soundness statement.

-/
import Johnson.LPFE1R.ThreeOfLeftOn
import Johnson.Desc.First.Look.K3Caller

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Look (DigOK Sent)
open VerifiableInference.Desc.PhiAll

/-- **P2 and P3, from the library's test on the smallness test's record.** -/
theorem three_pub {tl : HTailF2} {pp : ℕ} (hs : DgP.shapeTest2 tl pp = true) :
    5 ≤ tl.f9.kT + tl.f9.cK ∧ ∀ q < 2, q < tl.f9.NC ∧
      ((tl.f9.calls[q]?).map (·.n)).getD 0 = (tl.zOf q).call.n := by
  obtain ⟨_, hT, hP⟩ := DgP.shape2_parts hs
  have h0 : 0 < tl.f9.NC := by
    rw [hT.nc]
    omega
  have hk := (hT.port.2.2.2.2.2 0 h0).1
  rw [hP.wide.1] at hk
  have h10 : 10 ≤ tl.f9.kT := hk
  refine ⟨by omega, fun q hq => ?_⟩
  have hq' : q < tl.f9.NC := by
    rw [hT.nc]
    exact hq
  exact ⟨hq', (hP.call q hq').1⟩

variable {β : Type}

/-- **LeftRest's FIELD three, from the plan and the lookups' promise on the state in front.** -/
theorem three_of_dig (u : HTailF2) (ψ : S → β) (Ok : Q β → Prop) (nU : Array ℕ) (tlD : HTailF2)
    (hc : ∀ q, Ok q → OkCore nU tlD q) {set : Params.Setting} {x : First.Look.Place} {D : Sent}
    {rad : OracleShape → ℕ} {pp : ℕ} (dg : DigOK set x tlD D rad pp) (s : S) {lm first : ℕ}
    {Qf : Fork → Prop}
    (L : K3LeftOn S.fork? (fun s : S => s.tl?.bind (·.heard)) tlD.f9 lm first Qf s) :
    ∀ (e : S) (tl : HTailF2) (g : Forest.Heard), e.tl? = some tl → tl.heard = some g →
      Fx9 (phiAll u ψ) Ok (fixed9 (phiAll u ψ) s) e →
      tl.f9 = g.shape ∧ 5 ≤ g.shape.kT + g.shape.cK ∧
        ∀ q < 2, (g.zk.getD q #[]).size = (tl.zOf q).call.n :=
  three_of_leftOn u ψ Ok nU tlD hc (three_pub dg.tail).1 (three_pub dg.tail).2 s L

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.three_pub
#print axioms VerifiableInference.Desc.LinkJoin.three_of_dig
