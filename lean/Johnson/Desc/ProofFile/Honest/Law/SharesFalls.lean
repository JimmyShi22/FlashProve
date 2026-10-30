-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/SharesFalls.lean: THE FALLS' SHARES: THE FORM IS THE GATE. At each
fixed input and each fixed run's coins: the typed verifier's messages at which the honest run meets
a fall (`fallAt`, Honest/Fall.lean) have at most the sum of the numbers of three lists of gates that
COVER them (`covered_le`, Honest/Law/SharesFile.lean). And the messages at which the run returns
with the second chain's end lacking are among those at which it meets a fall or a part stops: so
their measure is at most the two bounds' sum.

WHY GATES. A fall's test at its own member, over that member's own challenges (`Fall.HeldOn`), does
not bear every fall: one that is seated at a member without a round has its chance at the member in
front, through the state that this member's step returns; one whose chance runs over two rounds is
held only where an event at the earlier round is counted first, though the verifier refuses nothing
there (a mark). Both are gates. Shown to us by another thread of this project.

WHAT THIS IS. Definitions, and conditional lemmas on our own fold and the library's own measure
(`Iop.prRho`), at one input and one run's coins. None of the library's goals.

MET FOR NOTHING. WHOEVER WRITES THE FALLS OWES THE COVER: a gate that always speaks covers
everything and is held by 1 alone. At numbers that add up to 1 or more nothing is said.
`refused_sub` takes the premises of the rule for acceptance (`ThreadsC`) at this input and coin: at
falls that speak wherever a member's own step refuses it says that a run which is refused is
refused.

  1  `Fall.HeldOn`   the special case: a fall at a member with rounds
  2  `falls_held`   the law
  3  `refused_sub`, `refused_held`   where the run returns and is refused

Limits. No cover is shown here. THE FALLS' LAWS STAND AT ONE INPUT AND ONE RUN's COINS k. The
library's own forms of completeness (`Honest.Acc`, Iop/InteractiveOracleProof.lean; `BatchProtocol.Complete`, Iop/Batch.lean)
ask acceptance AT EVERY COIN outside a set of verifier's messages that no coin enters. A bound at
each k does not bound {ρ | at SOME k the run meets a fall}: so these numbers have no seat in these
two forms. Where they can land: in a form that takes a fall's set at each fixed coin and asks ONE
NUMBER FOR ALL COINS (the library's `HonFit`, Johnson/Prover/All/OfHonest.lean: by its authors'
word, held by no lemma of ours); and in a share over the message and the coins together
(Honest/Law/SharesMean.lean). The laws end in sums of the gates' numbers, which are letters: NO
STATED SHARE OF A FALL IS IN THEM. THE KIT C OF VERIFIER's MESSAGES IS A LETTER: how a measure over
its typed challenges comes from a count of what they show hangs on the kit, and is not here. Among
the hypotheses that the prose above does not name: `Draws.due` (the challenges are such as the
description's rounds can draw; the first chain's last challenge is the empty one): `refused_sub`;
`FileDescription.planOk` (the library's executable test): `refused_sub`, `refused_held`; `ready … = .ok`
(`ready` returns at these coins): `refused_sub`, `refused_held`; `FileDescription.okStart` (the library's
executable test, at the instance): `refused_sub`, `refused_held`. This file proves nothing about
soundness, completeness, hiding or any other property of the protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.SharesFile
import Johnson.Desc.ProofFile.Honest.Law.ThreadStratC

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open Prob
open scoped ENNReal
open VerifiableInference.Desc
open OnBytes.Maker (RDT WholeD uLT drawnT chainsOf)
open _root_.Run.PQ (CK)

variable {Xi W₀ Rc Ky Tr X₀ X TF TJ T3 S : Type}

/-! ## 1 The special case -/

/-- **A fall's share is held at its own member's rounds**, at every state in front that the letter P
lets in. It bears a fall at a member with rounds whose test can be bounded at each such state. At P
:= False it is met for nothing. Spent by `fallDebt_of_heldOn` (Honest/Law/CoverSeat.lean). A
definition: a premise's form. -/
def Fall.HeldOn (f : Fall S) (C : CK) (ds : List RDT) (P : S → Prop) : Prop :=
  ∀ s, P s → Held C ds (fun own => (f.test s own).isSome) f.share

/-! ## 2 The law -/

section
variable (C : CK) (D : WholeD) (tF : TF) (tJ : TJ) (t3 : T3) {F : FileDescription Xi} {Bk : ProverCoinCounts}
  (G : Sides F Bk W₀ Rc Ky Tr X₀ X) (H : Prover W₀ Rc Xi Ky Tr X₀ X) (w₀ : W₀) (rc : Rc) (x : Xi)
  (k : Coins Bk)

/-- **THE FALLS' SHARES**, at one input and one run's coins. cover: wherever the run meets a fall
some gate has spoken. -/
theorem falls_held (gs₁ gs₂ gs₃ : List Gate) (e₁ : gs₁.flatMap (·.ds) = D.ds₁)
    (e₂ : gs₂.flatMap (·.ds) = D.ds₂) (e₃ : gs₃.flatMap (·.ds) = D.ds₃)
    (fr₃ : List Fmt.Drawn → List Fmt.Drawn → List Fmt.Drawn)
    (cover : ∀ ρ : Iop.Rho (chainsOf C D tF tJ t3).sh,
      (fallAt G H w₀ rc x k (drawsAt C D tF tJ t3 ρ)).isSome = true →
      spoken gs₁ [] (drawnT C D.ds₁ ((chainsOf C D tF tJ t3).rho₁ ρ)) = true ∨
      spoken gs₂ [] (drawnT C D.ds₂ ((chainsOf C D tF tJ t3).rho₂ ρ)) = true ∨
      spoken gs₃ (fr₃ (drawnT C D.ds₁ ((chainsOf C D tF tJ t3).rho₁ ρ))
        (drawnT C D.ds₂ ((chainsOf C D tF tJ t3).rho₂ ρ)))
        (drawnT C D.ds₃ ((chainsOf C D tF tJ t3).rho₃ ρ)) = true)
    (h₁ : GatesHeld C gs₁ []) (h₂ : GatesHeld C gs₂ [])
    (h₃ : ∀ (a : Iop.Rho (uLT C D.ds₁)) (b : Iop.Rho (uLT C D.ds₂)),
      spoken gs₁ [] (drawnT C D.ds₁ a) = false → spoken gs₂ [] (drawnT C D.ds₂ b) = false →
      GatesHeld C gs₃ (fr₃ (drawnT C D.ds₁ a) (drawnT C D.ds₂ b))) :
    Iop.prRho {ρ : Iop.Rho (chainsOf C D tF tJ t3).sh |
        (fallAt G H w₀ rc x k (drawsAt C D tF tJ t3 ρ)).isSome = true} ≤
      (gs₁.map (·.p)).sum + ((gs₂.map (·.p)).sum + (gs₃.map (·.p)).sum) :=
  covered_le C D tF tJ t3 gs₁ gs₂ gs₃ e₁ e₂ e₃ fr₃ _ cover h₁ h₂ h₃

/-! ## 3 Where the run returns and is refused -/

/-- **A run that returns with the second chain's end lacking has met a fall, or stands at a list at
which a part stops.** T: the premises of the rule for acceptance, at the rows' own falls. -/
theorem refused_sub {R : Ready W₀ Rc Xi Ky Tr X₀ X}
    (hR : ready F Bk (G.prover H) w₀ rc x k = .ok R) (hp : F.planOk = true)
    (hx : F.okStart x = true) (T : ThreadsC F Bk (G.prover H) w₀ rc x k R)
    (hf : T.f₁ = G.falls₁ ∧ T.f₂ = G.falls₂ ∧ T.f₃ = G.falls₃) {δ : Draws} (hδ : δ.due F = true)
    {r : RunC F} (h : runC F Bk (G.prover H) w₀ rc x k δ = .ok r) (hn : r.ends.2.2 = none) :
    (fallAt G H w₀ rc x k δ).isSome = true ∨ (silentAt F (G.prover H) w₀ rc x δ).isSome = true := by
  cases hs : silentAt F (G.prover H) w₀ rc x δ with
  | some _ => exact Or.inr rfl
  | none =>
    left
    unfold fallAt
    rw [h]
    show (viewsFall F G.falls₁ G.falls₂ G.falls₃ x r.run.views).isSome = true
    cases hv : viewsFall F G.falls₁ G.falls₂ G.falls₃ x r.run.views with
    | some _ => rfl
    | none =>
      obtain ⟨q1, q2, q3⟩ := hf
      rw [← q1, ← q2, ← q3] at hv
      obtain ⟨⟨e₁, e₂, e₃, he⟩, -⟩ := runC_accepts_views h hR hp hx hδ hs T.I₁ T.I₂ T.I₃ T.f₁ T.f₂
        T.f₃ T.h₁ T.h₂ T.h₃ T.y₁ T.y₂ T.y₃ T.a₁ T.a₂ T.a₃ T.fin hv
      rw [he] at hn
      cases hn

/-- **And so its measure is at most the two bounds' sum.** zF: a bound on the messages at which the
run meets a fall; zS: on those at which a part stops. -/
theorem refused_held {R : Ready W₀ Rc Xi Ky Tr X₀ X}
    (hR : ready F Bk (G.prover H) w₀ rc x k = .ok R) (hp : F.planOk = true)
    (hx : F.okStart x = true) (T : ThreadsC F Bk (G.prover H) w₀ rc x k R)
    (hf : T.f₁ = G.falls₁ ∧ T.f₂ = G.falls₂ ∧ T.f₃ = G.falls₃)
    (hdue : ∀ ρ, (drawsAt C D tF tJ t3 ρ).due F = true) (zF zS : ℝ≥0∞)
    (hF : Iop.prRho {ρ : Iop.Rho (chainsOf C D tF tJ t3).sh |
      (fallAt G H w₀ rc x k (drawsAt C D tF tJ t3 ρ)).isSome = true} ≤ zF)
    (hS : Iop.prRho {ρ : Iop.Rho (chainsOf C D tF tJ t3).sh |
      (silentAt F (G.prover H) w₀ rc x (drawsAt C D tF tJ t3 ρ)).isSome = true} ≤ zS) :
    Iop.prRho {ρ : Iop.Rho (chainsOf C D tF tJ t3).sh | ∃ r,
      runC F Bk (G.prover H) w₀ rc x k (drawsAt C D tF tJ t3 ρ) = .ok r ∧ r.ends.2.2 = none} ≤
      zF + zS := by
  refine le_trans (pr_mono _ ?_) (le_trans (pr_union_le _ _ _) (add_le_add hF hS))
  rintro ρ ⟨r, h, hn⟩
  exact refused_sub G H w₀ rc x k hR hp hx T hf (hdue ρ) h hn

end

end ProofFile.Honest

#print axioms ProofFile.Honest.falls_held
#print axioms ProofFile.Honest.refused_sub
#print axioms ProofFile.Honest.refused_held
