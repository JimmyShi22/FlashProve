-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
NOT TRIED FOR EMPTINESS: no place of a stored set is known at which all premises hold together.
Johnson/Desc/First/Look/K3DigitsHeadAlike.lean: the lookup on the digits of the output head's
segment's approximate range proof: WHAT THE OUTPUT HEAD's KIND's OWN RUNS READ OF THE STATE IS THE
SAME ON BOTH SIDES OF AN ACCEPT OF THE WHOLE SEATED SUB-PROTOCOL: another house's relation Alike
(Johnson/Desc/Kinds/Law/RunsFixed.lean). IT CROSSES THE STEP WITHOUT A ROUND:
Johnson/Top/H/Keep/HeadOwnSame.lean has the one fact that was lacking («the state of the squares'
level's sumcheck stays») across the lookup's own rounds alone. Joinings. NO RESULT ON THE PROTOCOL.

Main names.
  squares_putFork: laying a ledger leaves that state.
  k3_digits_step_squares: it stays across the whole seated sub-protocol: k3_digits_squares, then the
    step without a round, which at the output head's segment lays the claim on the weights alone
    (quietHead_ok), elsewhere a ledger (quietDigits_ok).
  k3_digits_step_alike: Alike s s₂, by alike_of_pass with k3_digits_step_samePlanes
    (K3DigitsCallersStay.lean).
OBJECT. Desc.K3.theStated's value at the digits' address; two states of the verifier.
USER. Nobody yet. Meant: own_formsIn_pass_seat, join_formsIn_pass_seat
(Johnson/Top/H/Keep/HeadOwnAtSeat.lean) at the whole seated accept.
LETTERS. Those of K3DigitsCallersStay.lean; o.
IS IT EMPTY? The premises are an .ok of the seated sub-protocol's decide, «the output head's segment
is open in front» and a K3Pass: shown together at no state.





Limits. General in the type of a claim.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Top.H.Keep.HeadOwnSame
import Johnson.Desc.First.Look.K3DigitsCallersStay

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop IOR Cb Cb.Fo Cb.Fo.NumsEq Cb.LdLkp Cb.Lkp Cb.Rider TWhole TwV Tw
open OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Model OnBytes.Maker Run Fo Fo.Peel TwRound
open VerifiableInference.Desc.First.Look VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Kinds.Head.Law (SamePlanes Alike)

/-- Laying a ledger leaves the state of the squares' level's sumcheck. -/
theorem squares_putFork (s : Desc.First.S) (G : Fork) {o : Desc.First.HeadOwn}
    (ho : s.here = .head o) :
    ∀ o', (s.putFork G).here = .head o' → o'.squaresP = o.squaresP := by
  intro o' h'
  by_cases hc : o.opened = true
  · have e : s.putFork G = { s with here := .head { o with F := G } } := by
      simp [Desc.First.S.putFork, ho, hc]
    rw [e] at h'
    have e2 : ({ o with F := G } : Desc.First.HeadOwn) = o' := Desc.First.Here.head.inj h'
    rw [← e2]
  · have e : s.putFork G = s := by simp [Desc.First.S.putFork, ho, hc]
    rw [e, ho] at h'
    rw [← Desc.First.Here.head.inj h']

section
variable {Cl : Type}

/-- **It stays across the whole seated sub-protocol.** -/
theorem k3_digits_step_squares (claim : Aff → Cl)
    (readers : ℕ → Option (Desc.K3.Readers Desc.First.S)) (X : Verify.Public) (codes : Codes)
    (shape : Params.ReqShape) (a : Desc.Place) (B : Desc.Block Desc.First.S Cl)
    (h : Desc.K3.theStated claim readers X codes shape a = some B) (hOk : B.planOk = true)
    (i : ℕ) (hi : a.link = some i) (hpc : a.piece = Desc.K3.pieceAt X i true)
    (s s₂ : Desc.First.S) (rs : List Fmt.RoundView) (gs : List (List (ℕ × List UInt64)))
    (hd : B.decide s rs gs = .ok s₂) {o : Desc.First.HeadOwn} (ho : s.here = .head o) :
    ∀ o', s₂.here = .head o' → o'.squaresP = o.squaresP := by
  obtain ⟨P', sent, laid, n, gs', s', -, hyes, hstep⟩ :=
    theStated_yes_digits claim readers X codes shape a B h hOk i hi hpc s s₂ rs gs hd
  have H0 := k3_digits_squares claim a.piece laid sent _ [] s s' _ gs' hyes ho
  rcases hstep with e | ⟨f, hf, hfs⟩
  · rw [e]
    exact H0
  · obtain ⟨o1, ho1, -⟩ :=
      (k3_digits_samePlanes claim a.piece laid sent _ [] s s' _ gs' hyes).head o ho
    unfold Desc.K3.quietAt at hf
    simp only [if_true] at hf
    split at hf
    · obtain rfl := Option.some.inj hf
      obtain ⟨ah, c, ha, -, e⟩ := Desc.K3.quietHead_ok X s' s₂ hfs
      intro o' h'
      rw [e] at h'
      have e2 : ({ ah with claim := some c } : Desc.First.HeadOwn) = o' :=
        Desc.First.Here.head.inj h'
      rw [← e2]
      exact H0 ah ha
    · split at hf <;> split at hf <;>
        (obtain ⟨_, -, rfl⟩ := Option.map_eq_some_iff.1 hf
         obtain ⟨F, -, -, e⟩ := Desc.K3.quietDigits_ok _ _ s' s₂ hfs
         intro o' h'
         rw [e] at h'
         exact (squares_putFork s' _ ho1 o' h').trans (H0 o1 ho1))

/-- **Alike AT THE WHOLE SEATED ACCEPT.** -/
theorem k3_digits_step_alike (claim : Aff → Cl)
    (readers : ℕ → Option (Desc.K3.Readers Desc.First.S)) (X : Verify.Public) (codes : Codes)
    (shape : Params.ReqShape) (a : Desc.Place) (B : Desc.Block Desc.First.S Cl)
    (h : Desc.K3.theStated claim readers X codes shape a = some B) (hOk : B.planOk = true)
    (i : ℕ) (hi : a.link = some i) (hpc : a.piece = Desc.K3.pieceAt X i true)
    (s s₂ : Desc.First.S) (rs : List Fmt.RoundView) (gs : List (List (ℕ × List UInt64)))
    (hd : B.decide s rs gs = .ok s₂) {o : Desc.First.HeadOwn} (ho : s.here = .head o)
    {F G : Fork} (Q : K3Pass s s₂ F G) : Alike s s₂ :=
  alike_of_pass
    (k3_digits_step_samePlanes claim readers X codes shape a B h hOk i hi hpc s s₂ rs gs hd) Q ho
    (k3_digits_step_squares claim readers X codes shape a B h hOk i hi hpc s s₂ rs gs hd ho)

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.squares_putFork
#print axioms VerifiableInference.OnPublicFiles.k3_digits_step_squares
#print axioms VerifiableInference.OnPublicFiles.k3_digits_step_alike
