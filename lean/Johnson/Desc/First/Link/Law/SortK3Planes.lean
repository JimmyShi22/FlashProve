-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/SortK3Planes.lean: WHAT IS LEFT OF A LINK's LAW (K9): THE FIELDS k3p,
k3s, k3sL OF `SortRest` (SortRest.lean) AT THE ENTRY "planes": PAID, IN THE GOALS'
SCOPE, WHERE THE CALLING KIND's READERS ARE THERE. Theorems: calls. IT PAYS NO LAW OF ITS OWN. THE
FIELD k3 (RunOk) AT "planes" IS NOT HERE: it hangs on the caller's clauses.

  at_planes_is    At L (IM.k3Ix m false, "planes") run ⊢ there is the place's p with
                  run = K3.planesRun (seatCalls K3Lot.ofForm) p.lm r: THE TIE, AN EQUATION OF
                  FUNCTIONS (`k03_planes_raw`, Johnson/Desc/First/Look/K03StatesRaw.lean)
  k3p_planes · k3s_planes · k3sL_planes   the three fields' own texts at that entry, by
                  planes_puts | planes_core (Johnson/Top/H/Keep/RunsPutFork.lean)
  planes_entry_low (m ≠ 24: (1, "planes")) · planes_entry_head ((2, "planes"))

PREMISES: hS hR O · m < 25 · hL : c.links[m]? = some L · hr : K3Lot.readersAt Bs.G₀.W m = some r.
Limits. That the readers are there at an attention link and at the head's is not shown here. NO
MEMBER. Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.SortK3Objects

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.OnPublicFiles
open OnBytes OnBytes.Model
open OnBytes.PscRun (Sized)
open VerifiableInference.Desc (Block Chain Link FileDescription)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K3 (seatCalls)
open VerifiableInference.Desc.LinkJoin (At HasFork)

section
variable {Pf : VerifierAndGoals.PublicFiles} {pp₀ : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)} {c : Chain S ProofFile.Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
  (hS : VerifierAndGoals.InScope Pf = true) (hR : VerifierAndGoals.readFiles Pf = .ok pp₀)
  (O : IM.Open OnBytes.secondHashFunction Pf.pol lay Pf.KL F Z Bs base c A B) {m : ℕ} (hm : m < 25)
  {L : Link S ProofFile.Cl} (hL : c.links[m]? = some L) {r : Desc.K3.Readers S}
  (hr : K3Lot.readersAt Bs.G₀.W m = some r)
include hS hR O hm hL hr

/-- **What the link states under "planes" at the calls' lookup's block is the kind's own run.** -/
theorem at_planes_is {run : ℕ → S → Except String (List ProofFile.Cl × S)}
    (h : At L (IM.k3Ix m false, "planes") run) :
    ∃ p : Desc.First.Look.P, Desc.First.Look.placeAt Bs.G₀.W m false = some p ∧
      run = Desc.K3.planesRun (seatCalls K3Lot.ofForm) p.lm r := by
  obtain ⟨Lk, p, h1, hp, h2⟩ := k03_planes_raw hS hR O m hm r hr
  obtain rfl : Lk = L := Option.some.inj (h1.symm.trans hL)
  obtain ⟨b, hb, hl⟩ := Option.bind_eq_some_iff.1 h
  have hb' : Lk.hear[IM.k3Ix m false]? = some b := hb
  have hl' : b.claims.lookup "planes" = some run := hl
  obtain ⟨x, hx, hx2⟩ := Desc.LinkJoin.find_of_lookup "planes" b.claims run hl'
  have e : Desc.K9.statesOfLink Lk (IM.k3Ix m false) = b.claims := by
    unfold Desc.K9.statesOfLink
    rw [hb']
    rfl
  rw [e, hx] at h2
  refine ⟨p, hp, ?_⟩
  rw [← hx2]
  exact congrArg Prod.snd (Option.some.inj h2)

/-- **k3p at "planes".** -/
theorem k3p_planes (run : ℕ → S → Except String (List ProofFile.Cl × S))
    (h : At L (IM.k3Ix m false, "planes") run) :
    ∀ n e cl e₁, run n e = .ok (cl, e₁) → ∃ G, e₁ = e.putFork G := by
  obtain ⟨p, _, rfl⟩ := at_planes_is hS hR O hm hL hr h
  exact planes_puts _ k03_atS2_calls p.lm r

/-- **k3s at "planes".** -/
theorem k3s_planes (run : ℕ → S → Except String (List ProofFile.Cl × S))
    (h : At L (IM.k3Ix m false, "planes") run) :
    ∀ n e cl e₁, run n e = .ok (cl, e₁) → HasFork Sized e → HasFork Sized e₁ := by
  obtain ⟨p, _, rfl⟩ := at_planes_is hS hR O hm hL hr h
  rintro n e cl e₁ hq ⟨G₀, hF, hz⟩
  obtain ⟨G, rfl, _, _, hG⟩ := planes_core _ k03_atS2_calls p.lm r n e cl e₁ G₀ hF hz hq
  exact ⟨G, Desc.LinkJoin.fork_putFork e G₀ hF G, hG⟩

/-- **k3sL at "planes".** -/
theorem k3sL_planes (run : ℕ → S → Except String (List ProofFile.Cl × S))
    (h : At L (IM.k3Ix m false, "planes") run) :
    ∀ n e cl e₁, run n e = .ok (cl, e₁) → HasFork (fun F => Sized F ∧ F.LS.size = F.ns) e →
      HasFork (fun F => Sized F ∧ F.LS.size = F.ns) e₁ := by
  obtain ⟨p, _, rfl⟩ := at_planes_is hS hR O hm hL hr h
  rintro n e cl e₁ hq ⟨G₀, hF, hz, hn⟩
  obtain ⟨G, rfl, e1, e2, hG⟩ := planes_core _ k03_atS2_calls p.lm r n e cl e₁ G₀ hF hz hq
  exact ⟨G, Desc.LinkJoin.fork_putFork e G₀ hF G, hG, by rw [e1, e2]; exact hn⟩

end

theorem planes_entry_low {m : ℕ} (hm : m ≠ 24) :
    ((1 : ℕ), "planes") = (IM.k3Ix m false, "planes") := by simp [IM.k3Ix, hm]

theorem planes_entry_head : ((2 : ℕ), "planes") = (IM.k3Ix 24 false, "planes") := rfl

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.at_planes_is
#print axioms VerifiableInference.OnPublicFiles.k3p_planes
#print axioms VerifiableInference.OnPublicFiles.k3s_planes
#print axioms VerifiableInference.OnPublicFiles.k3sL_planes
#print axioms VerifiableInference.OnPublicFiles.planes_entry_low
#print axioms VerifiableInference.OnPublicFiles.planes_entry_head
