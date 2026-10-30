-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/- Johnson/P1K8R/DigThereAll.lean: THE DIGITS' LOOKUP's PLACE AND THE SMALLNESS TEST's PUBLIC VALUE
ARE THERE AT EACH OF THE 25 LINKS: `First.Look.digAt Z.p.X l` answers, in scope, at an opening's
letters and under the description's own test on the plan. It is the closed premise hx of
`k08_digits_of_ahead` (Johnson/P1K8R/DigitsAtDraw.lean). Johnson/K11R/DigThere.lean has the same at
link 24 alone; its three lemmas on the lookups' maker are called here, and its last proof is
repeated with l as a letter.
  `digThere_all`: in scope, at an opening, under `F.planOk = true`, at every l ≤ 24.
  `digThere_at_head`: **under the head `P5J.AtMgA`**: at `P5J.At.X Zp`.
How. `IM.k3_of`: at each link the digits' lookup's sub-protocol is the lookups' own, alone, at the
address with piece 7 (at the output head's link: 8); it stands in the flat list, so it passes its
test on the plan; `K11Live.theStated_parts`: so the maker has looked up a place, a count and a
shape; the piece says that it is the lookup on the digits, not the one on the calls (2 | 3).
Limits. A member of the head is proved at `storedPublicFiles` and `zGap` alone (at secondHashFunction; side library
AtFullSide/Top/). At `OnBytes.secondHashFunction` alone. Nothing on soundness or
on hiding.

-/
import Johnson.K11R.DigThere
import Johnson.P5J.MgAtAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace P1K8T

open OnBytes OnBytes.Model OnBytes.Maker
open VerifiableInference.Desc (Block Chain Link FileDescription Place KindName Claim blocksOk)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Look (placeAt laidAt lookAt tlAt digAt)
open ProofFile (Cl)
open P5J (AtMgA)

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **At all 25 links.** -/
theorem digThere_all (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true) {l : ℕ}
    (hl : l ≤ 24) : ∃ xd tl, digAt Z.p.X l = some (xd, tl) := by
  have hd := O.desc
  subst hd
  obtain ⟨Lk, b, b', e1, e2, e3, hla⟩ := IM.k3_of hS hR O l (Nat.lt_succ_of_le hl) true
  have eF : c.blocksInOrder[14 * l + IM.k3Ix l true + 2]? = some b := by
    have h := IM.hear_at_flat e1 e2
    rwa [IM.flatIx_scope hS hR O hl (IM.k3Ix l true)] at h
  have hb : blocksOk c.blocksInOrder = true := by
    cases hb : blocksOk (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s)
        (ProofFile.startS Z) c).first.blocksInOrder with
    | true => exact hb
    | false => simp [FileDescription.planOk, FileDescription.planOkCore, hb] at hOk
  have hbp : b.planOk = true := by
    have h1 := List.all_eq_true.1 hb b (List.mem_of_getElem? eF)
    simp only [Bool.and_eq_true] at h1
    exact h1.1
  rw [IM.alone_planOk hla] at hbp
  rw [O.W] at e3
  obtain ⟨i, digits, p, laid, hi, hpc, hp1, hl1, hsh⟩ :=
    K11Live.theStated_parts _ _ _ _ _ _ e3 hbp
  obtain rfl : l = i := Option.some.inj hi
  have hdg : digits = true := by
    have hpc' : IM.k3Ix l true + 1 = VerifiableInference.Desc.K3.pieceAt Z.p.X l digits := hpc
    unfold VerifiableInference.Desc.K3.pieceAt at hpc'
    cases digits with
    | true => rfl
    | false =>
      exfalso
      have h6 : 7 ≤ IM.k3Ix l true + 1 := by
        show 7 ≤ ((if true = true then 6 else 1) + (if l = 24 then 1 else 0)) + 1
        rw [if_pos rfl]
        omega
      split at hpc' <;> simp at hpc' <;> omega
  subst hdg
  unfold placeAt at hp1
  obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.1 hp1
  have hl2 : (tlAt Z.p.X l).bind VerifiableInference.Desc.First.Look.laidDigits = some laid := hl1
  obtain ⟨tl, htl, _⟩ := Option.bind_eq_some_iff.1 hl2
  obtain ⟨h, hh⟩ := Option.isSome_iff_exists.1 hsh
  refine ⟨x, { tl with f9 := h }, ?_⟩
  unfold digAt
  rw [hx, htl]
  show ((VerifiableInference.Desc.First.Look.P.ofPlace (Params.settingOf Z.p.X.P.frame) true
    x).shape.map fun h => (x, { tl with f9 := h })) = _
  rw [hh]
  rfl

end

/-- **Under the head.** -/
theorem digThere_at_head {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
    {Np : H2U.Places4} {cF : Chain S Cl} {x : VerifiableInference.Desc.First.Look.Place}
    (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {l : ℕ} (hl : l ≤ 24) :
    ∃ xd tl, digAt (P5J.At.X Zp) l = some (xd, tl) := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  exact digThere_all h.scope h.reads O h.laid.planOk hl

end P1K8T

#print axioms P1K8T.digThere_all
#print axioms P1K8T.digThere_at_head
