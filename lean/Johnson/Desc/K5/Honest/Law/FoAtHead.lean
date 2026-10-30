-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K5/Honest/Law/FoAtHead.lean: CONDITIONAL, under the library's hypothesis on the public
input (`P5J.AtMgA`): THREE PUBLIC FACTS ON THE LOOKUP ON THE CALLS OF AN ATTENTION SEGMENT, IN THE
STORED PLAN's OWN LETTERS: the library's test on the lookup's numbers says yes; the lookup has four
calls; the ledger's first free slot in front of the segment's own rounds is the number of the
lookup's hidden values. Each is drawn inside a proof of
Johnson/Desc/K5/Honest/Law/JoinMeetsAtHead.lean already; here they stand as statements, so that
others can call them.

  `fo_at_head`      CONDITIONAL: `FoNums.ok` a.fs = true, and a.fs.NC = 4
  `first_at_head`   CONDITIONAL: the filling's `first?` at the segment is `Forest.elems` a.fs

Limits. Public numbers alone. h is a hypothesis of every statement that names it. At the library's
full size and the format's second hash function alone.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.K5.Honest.Law.JoinMeetsAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace H2K5.Honest
open Cb Cb.LdLkp OnBytes OnBytes.Model OnBytes.Model.Road OnBytes.Maker
open VerifiableInference.Desc VerifiableInference.Desc.First VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First.Look (lookAt)
open P5J (AtMgA mgAtAll TS)
open H2K5.Door

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : Look.Place} (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
include h

/-- **The library's test on the lookup's numbers says yes, and the lookup has four calls.**
CONDITIONAL: under the hypothesis h; g is below 12; ea: the group's plan; hx: the place of the
segment's lookup on the calls. -/
theorem fo_at_head {g : ℕ} (hg : g < 12) {a : Attention.Plan} {x₁ : Look.Place}
    (ea : (P5J.At.X Zp).A[g]? = some a)
    (hx : lookAt (P5J.At.X Zp) (2 * g + 1) false = some x₁) :
    FoNums.ok a.fs = true ∧ a.fs.NC = 4 := by
  obtain ⟨h4, _, _⟩ := scope_all h
  have hP := planIs_all h
  obtain ⟨_, _, _, hfs⟩ := Att.P.place_calls h4 ea hx
  obtain ⟨blk, hat⟩ := seated_all h hg
  obtain ⟨hok, hG⟩ := seatedOk_guard_all h hg hat
  have pOk := planOk_plus (beforeAll Zp g) hat hok ea
  have cOk := claimsOk_plus (beforeAll Zp g) hat hok ea
  have AO := attOK_plus (beforeAll Zp g) h.𝔇.sent h.𝔇.l3.rad hP h4 ea hx hG pOk cOk
  rw [← hfs]
  exact ⟨VerifiableInference.OnPublicFiles.foOk_of_shape AO.shape, AO.four⟩

/-- **The ledger's first free slot in front of the segment's own rounds, as the filling has it.**
CONDITIONAL: as `fo_at_head`, but that no bound on g is asked. -/
theorem first_at_head {g : ℕ} {a : Attention.Plan} {x₁ : Look.Place}
    (ea : (P5J.At.X Zp).A[g]? = some a)
    (hx : lookAt (P5J.At.X Zp) (2 * g + 1) false = some x₁) :
    h.𝔇.pubD.d5.first? (2 * g + 1) = some (Forest.elems a.fs) := by
  obtain ⟨h4, _, _⟩ := scope_all h
  have hP := planIs_all h
  have T := dataIs_all h (2 * g + 1)
  exact first_at h.𝔇.pubD.d5 (by rw [T.d5W]; exact hP) (by rw [T.d5W]; exact h4)
    (by rw [T.d5W]; exact ea) (by rw [T.d5W]; exact hx)

end

end H2K5.Honest

#print axioms H2K5.Honest.fo_at_head
#print axioms H2K5.Honest.first_at_head
