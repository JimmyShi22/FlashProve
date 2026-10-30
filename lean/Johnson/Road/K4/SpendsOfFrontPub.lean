-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/SpendsOfFrontPub.lean: WHAT K4's SHARE OF THE BRIDGE SPENDS AT A GROUP's TWO
BORDERS, OUT OF THE BORDER IN FRONT, WITH A CONDITION ON THE PUBLIC PART BESIDE "REACHED". Two
statements with their proofs. No new argument: `spends_of_front`
(SpendsOfFront.lean) typed anew at the narrower condition, over the lemmas BENEATH the two that it
calls.

WHY. `spends_of_front` takes its three premises at EVERY state that the IOP's run reaches in front
of K4. The condition beside the promise at which the kinds' laws are counted is narrower: "reached,
and Pp of the public part" (`RchPub`, Johnson/Top/H0/Walk/ReachPub.lean).
Premises at plain "reached" are dearer than needed, and a payer that ends at typed instances does
not fit them. That lemma cannot be called with premises at the narrower condition; but its proof
goes state by state: a state reached behind K4 comes of one reached in front BY AN ACCEPTING RUN OF
K4's SUB-PROTOCOL, WITH THE SAME PUBLIC PART (`kept_rchAt`).

  `spends_of_front_pub`: in the goals' scope, at an opening, g < 12, Pp a letter: W0, R0, L7 at
    every state with `RchPub (descAt Z A B c) Pp (28 * g + 4)` and no mark ⟹ `K4Spends Dm E j a.1`
    at j = 28 g + 4 and 28 g + 5, at every state with `RchPub … Pp j` and no mark.
  `sp_of_front_pub`: the same under "∀ g < 12".

Limits. IT PAYS NOTHING: W0, R0, L7 are premises; NO MEMBER OF THEM IS SHOWN. What `K4Spends` serves
speaks at a wider meaning, one side of a bridge. K04_law IS NOT PROVED BY THIS. Nothing is said of
Pp. The second hash function alone. Nothing on soundness.
-/
import Johnson.Road.K4.SpendsOfFront
import Johnson.Top.H0.Walk.ReachPub

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4

open OnBytes OnBytes.Model
open OnBytes.Desc.First.K4 (Rest)
open OnBytes.Road.K4.Riders (roomIsB_kept)
open VerifiableInference.Desc (Block FileDescription)
open VerifiableInference.Desc.First (S LayOwn)
open VerifiableInference.Desc.First.K8.Ready (lay7B)
open VerifiableInference.Desc.Sound (MgData WideData WideFacts moreW_base)
open Johnson.Desc.First.Walk.Tied (RchAt RchPub roomIsB)

variable {Pb : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {ly : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}
  {c : VerifiableInference.Desc.Chain S ProofFile.Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **What K4's share of the bridge spends at a group's two borders, out of the border in front, at
"reached, and Pp of the public part"**, under hS hR O hg W0 R0 L7. -/
theorem spends_of_front_pub {Xi Tok : Type} {rows cols nR : ℕ} {X : Verify.Public}
    (Dm : MgData Xi ProofFile.InstPub Tok rows cols nR X) (E : WideData ProofFile.InstPub)
    (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pb.pol ly Pb.KL F Z Bs base c A B) {g : ℕ} (hg : g < 12)
    (Pp : (descAt Z A B c).XiPub → Prop) {Str : Type}
    (W0 : ∀ a : ((descAt Z A B c).XiPub × (descAt Z A B c).S₁) × Str,
      RchPub (descAt Z A B c) Pp (28 * g + 4) a → a.1.2.failed = none → WideFacts Dm E a.1)
    (R0 : ∀ a : ((descAt Z A B c).XiPub × (descAt Z A B c).S₁) × Str,
      RchPub (descAt Z A B c) Pp (28 * g + 4) a → a.1.2.failed = none →
        roomIsB E.dP.free0 E.dP.fvs (2 * g) a.1.2 = true)
    (L7 : ∀ a : ((descAt Z A B c).XiPub × (descAt Z A B c).S₁) × Str,
      RchPub (descAt Z A B c) Pp (28 * g + 4) a → a.1.2.failed = none →
        ((E.dP.tl (2 * g)).any fun tlP => lay7B tlP a.1.2) = true) :
    ∀ j, j = 28 * g + 4 ∨ j = 28 * g + 4 + 1 →
      ∀ a : ((descAt Z A B c).XiPub × (descAt Z A B c).S₁) × Str,
        RchPub (descAt Z A B c) Pp j a → a.1.2.failed = none → K4Spends Dm E j a.1 := by
  intro j hj a h hu
  obtain ⟨a1, a2⟩ := room_of_fit (atK4_full g hg) room_open_wide
  rcases hj with rfl | rfl
  · have K := hK_front Dm E (atK4_full g hg) (L7 a h hu)
    refine ⟨W0 a h hu, fun m' hm => ?_, fun m hm => (K m).1 hm, fun m hm => (K m).2.1 hm,
      fun m hm => (K m).2.2 hm⟩
    rw [moreW_base] at hm
    rw [a1 m' hm]
    exact R0 a h hu
  · have h5 : RchAt (descAt Z A B c) (28 * g + 5) a := h.1
    obtain ⟨s, p, hr, Kp⟩ := kept_rchAt hS hR O hg h5
    obtain ⟨a₀, _, _, _, ha₀, _, _, _, _, _, _, _, hRest, _⟩ := Kp
    have hu' : s.failed = none := by
      rw [← hRest.failed]
      exact hu
    have hr' : RchPub (descAt Z A B c) Pp (28 * g + 4) ((a.1.1, s), a.2) := ⟨hr, h.2⟩
    have hl := L7 _ hr' hu'
    have hl' : ((E.dP.tl (2 * g)).any fun tlP => lay7B tlP a.1.2) = true := by
      unfold lay7B at hl ⊢
      rw [hRest.tl]
      exact hl
    have K := hK_behind Dm E (atK4_full g hg) hl' (funsThird_rchAt hS hR O hg h5)
    refine ⟨wide_rest hRest ha₀ (W0 _ hr' hu'), fun m' hm => ?_, fun m hm => (K m).1 hm,
      fun m hm => (K m).2.1 hm, fun m hm => (K m).2.2 hm⟩
    rw [moreW_base] at hm
    rw [a2 m' hm, roomIsB_kept hRest]
    exact R0 _ hr' hu'

/-- **The premise Sp of k04_law_R, to the letter, out of the twelve borders in front.** -/
theorem sp_of_front_pub {Xi Tok : Type} {rows cols nR : ℕ} {X : Verify.Public}
    (Dm : MgData Xi ProofFile.InstPub Tok rows cols nR X) (E : WideData ProofFile.InstPub)
    (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pb.pol ly Pb.KL F Z Bs base c A B)
    (Pp : (descAt Z A B c).XiPub → Prop) {Str : Type}
    (W0 : ∀ g, g < 12 → ∀ a : ((descAt Z A B c).XiPub × (descAt Z A B c).S₁) × Str,
      RchPub (descAt Z A B c) Pp (28 * g + 4) a → a.1.2.failed = none → WideFacts Dm E a.1)
    (R0 : ∀ g, g < 12 → ∀ a : ((descAt Z A B c).XiPub × (descAt Z A B c).S₁) × Str,
      RchPub (descAt Z A B c) Pp (28 * g + 4) a → a.1.2.failed = none →
        roomIsB E.dP.free0 E.dP.fvs (2 * g) a.1.2 = true)
    (L7 : ∀ g, g < 12 → ∀ a : ((descAt Z A B c).XiPub × (descAt Z A B c).S₁) × Str,
      RchPub (descAt Z A B c) Pp (28 * g + 4) a → a.1.2.failed = none →
        ((E.dP.tl (2 * g)).any fun tlP => lay7B tlP a.1.2) = true) :
    ∀ g, g < 12 → ∀ j, j = 28 * g + 4 ∨ j = 28 * g + 4 + 1 →
      ∀ a : ((descAt Z A B c).XiPub × (descAt Z A B c).S₁) × Str,
        RchPub (descAt Z A B c) Pp j a → a.1.2.failed = none → K4Spends Dm E j a.1 :=
  fun g hg => spends_of_front_pub Dm E hS hR O hg Pp (W0 g hg) (R0 g hg) (L7 g hg)

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.spends_of_front_pub
#print axioms OnBytes.Road.K4.sp_of_front_pub
