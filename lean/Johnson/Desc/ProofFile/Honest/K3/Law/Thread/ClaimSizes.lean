-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Thread/ClaimSizes.lean: the kind "lookup" (K3): the sizes of
the claim on the weights that the step behind the lookup on the head's digits lays (the library's
`weightsClaim`, Johnson/Desc/First/Look/LookQuiet.lean); and one test with code on public data,
`layoutOk`, that covers the public points at which that routine can refuse. One definition and
theorems.

Terms. Honest/K3/GLOSSARY.md.

What is shown.
  `avStep_size`, `avFold_size`, `avOf_size`: the factor on the vocabulary has the vocabulary's size.
  `facKK_sizes`: the factor on the channels. The size of its field HV depends on the size of the
    heard array rs: it is min o (2 ^ (min lamS rs.size - z)).
  `claim_sizes`: the unit's number, and the three sizes of each factor, of what the routine returns.
  `layoutOk`: the public test, with code. It asks: the call HD0 is there; so is its segment HD0; the
    layout's last unit is of the sort 13; that unit's groups are two, named "x" and "kk", in this
    order.
  `layoutOk_groups`: where the test accepts, the three hypotheses of `claim_sizes` on the layout
    hold.

Hypotheses that remain.
  `h`: (in `claim_sizes`) the routine returns; (in `layoutOk_groups`) the public test `layoutOk`
    accepts.
  `hg`, `hx`, `hkk`: (in `claim_sizes`) three facts on the public layout: the last unit's groups are
    two; the first is named "x"; the second is named "kk".

How the proof goes. By the library's closed form of the return (`weightsClaim_is`,
Johnson/Top/H0/K11Caller/HeadClaim.lean) and its `eqTab_size` (Johnson/Road/FormsKeysEq.lean). The
file is written over the library's own files alone: no declaration on shapes is named in it.

The last unit is spelt in two ways. The routine asks the sort of `lay.U.back?` and walks the groups
of `lay.U.getD (lay.U.size - 1) default`; the test follows it to the letter. On an array that is not
empty the two are one unit; on an empty one `back?` is none and the test rejects.

Users. `claim_sizes` is called in Honest/K3/Law/Thread/CarriesHeadDigits.lean; `layoutOk_groups`
there and in Honest/K3/Law/Thread/ClaimReturns.lean.

Limits. `claim_sizes` goes in one direction: from the routine's return. That the routine returns
where the test accepts is not shown here; `weightsClaim_returns`
(Honest/K3/Law/Thread/ClaimReturns.lean) shows it under one further hypothesis, on what the head
heard. The test is narrower than the routine's public refusals: it accepts only where the last
unit's groups are exactly "x", then "kk", while the routine refuses only at a group that bears
neither name. `layoutOk` is not evaluated at any layout in this file. It is evaluated in
Honest/K3/Law/Thread/CarriesGuardsHead.lean [not in this library]: it accepts at one of three small
synthetic public parts and rejects at the two
others. No instance of these hypotheses is exhibited in this file.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Top.H0.K11Caller.HeadClaim
import Johnson.Road.FormsKeysEq

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law.AtThr
open OnBytes (E)
open OnBytes.Model (WsLay WsClaim WsGrp WsFac eqTab eqLow)
open OnBytes.Road.Hd (facKK avOf avFold avStep)
open VerifiableInference.Desc.First.K11Caller (weightsClaim_is avFold_succ)

theorem avStep_size (on : Array Bool) (win : Array Nat) (wx : E) (eH AV : Array E) (t : Nat) :
    (avStep on win wx eH AV t).size = AV.size := by
  unfold avStep
  split
  · exact Array.size_modify
  · rfl

theorem avFold_size (on : Array Bool) (win : Array Nat) (wx : E) (eH A0 : Array E) :
    ∀ n, (avFold on win wx eH A0 n).size = A0.size
  | 0 => rfl
  | n + 1 => by rw [avFold_succ, avStep_size, avFold_size on win wx eH A0 n]

/-- **The factor on the vocabulary has the vocabulary's size.** -/
theorem avOf_size (R : OnBytes.Model.Head.Run) (ew : Array E) : (avOf R ew).size = R.h.V := by
  unfold avOf
  rw [avFold_size]
  simp

/-- **The factor on the channels.** The size of HV depends on the size of rs. -/
theorem facKK_sizes (rs : Array E) (z o lamS : Nat) :
    (facKK rs z o lamS).HV.size = min o (2 ^ (min lamS rs.size - z)) ∧
      (facKK rs z o lamS).pt.size = z ∧ (facKK rs z o lamS).AV.size = 0 := by
  refine ⟨?_, ?_, rfl⟩
  · show ((eqLow rs z lamS).extract 0 o).size = _
    unfold eqLow
    rw [Array.size_extract, OnBytes.Road.eqTab_size, Array.size_reverse, Array.size_extract,
      Nat.sub_zero]
  · show ((Array.range z).map _).size = z
    simp

/-- **The unit's number and the sizes of each factor of what the routine returns.** Conditional on
its return and three facts on the public layout. -/
theorem claim_sizes {R : OnBytes.Model.Head.Run} {lay : WsLay} {cl : WsClaim}
    (h : VerifiableInference.Desc.First.Look.weightsClaim R lay = .ok cl) {gx gk : WsGrp}
    (hg : (lay.U.getD (lay.U.size - 1) default).g = [gx, gk]) (hx : gx.name = "x")
    (hkk : gk.name = "kk") :
    cl.ui = lay.U.size - 1 ∧ cl.f.map (fun x => (x.HV.size, x.pt.size, x.AV.size)) =
      [(0, 0, R.h.V), (min gk.o (2 ^ (min R.hp.lamS R.x.rs.size - gk.z)), gk.z, 0)] := by
  obtain ⟨q, g, _, _, rfl, _⟩ := weightsClaim_is h hg hx hkk
  obtain ⟨e1, e2, e3⟩ := facKK_sizes R.x.rs gk.z gk.o R.hp.lamS
  refine ⟨rfl, ?_⟩
  show [((#[] : Array E).size, (#[] : Array E).size, (avOf R _).size),
    ((facKK R.x.rs gk.z gk.o R.hp.lamS).HV.size, (facKK R.x.rs gk.z gk.o R.hp.lamS).pt.size,
      (facKK R.x.rs gk.z gk.o R.hp.lamS).AV.size)] = _
  rw [avOf_size, e1, e2, e3]
  rfl

/-- **One test with code that covers the public points at which the routine can refuse.** It is
narrower than these refusals: it asks that the last unit's groups are exactly "x", then "kk". -/
def layoutOk (L : OnBytes.Model.Head.HL) (lay : WsLay) : Bool :=
  ((OnBytes.Model.Head.callNo L "HD0").any fun q =>
      ((L.calls.getD q default).seg? "HD0").isSome) &&
    ((lay.U.back?.map (·.X)) == some 13) &&
    (match (lay.U.getD (lay.U.size - 1) default).g with
      | [gx, gk] => gx.name == "x" && gk.name == "kk"
      | _ => false)

/-- Where the test accepts: the three hypotheses of `claim_sizes` on the layout. -/
theorem layoutOk_groups {L : OnBytes.Model.Head.HL} {lay : WsLay} (h : layoutOk L lay = true) :
    ∃ gx gk, (lay.U.getD (lay.U.size - 1) default).g = [gx, gk] ∧ gx.name = "x" ∧
      gk.name = "kk" := by
  unfold layoutOk at h
  rw [Bool.and_eq_true] at h
  have h3 := h.2
  match hm : (lay.U.getD (lay.U.size - 1) default).g with
  | [gx, gk] =>
    rw [hm] at h3
    have h4 : (gx.name == "x" && gk.name == "kk") = true := h3
    rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at h4
    exact ⟨gx, gk, rfl, h4.1, h4.2⟩
  | [] =>
    rw [hm] at h3
    exact nomatch h3
  | [_] =>
    rw [hm] at h3
    exact nomatch h3
  | _ :: _ :: _ :: _ =>
    rw [hm] at h3
    exact nomatch h3

end ProofFile.Honest.K3.Law.AtThr

#print axioms ProofFile.Honest.K3.Law.AtThr.avStep_size
#print axioms ProofFile.Honest.K3.Law.AtThr.avFold_size
#print axioms ProofFile.Honest.K3.Law.AtThr.avOf_size
#print axioms ProofFile.Honest.K3.Law.AtThr.facKK_sizes
#print axioms ProofFile.Honest.K3.Law.AtThr.claim_sizes
#print axioms ProofFile.Honest.K3.Law.AtThr.layoutOk_groups
