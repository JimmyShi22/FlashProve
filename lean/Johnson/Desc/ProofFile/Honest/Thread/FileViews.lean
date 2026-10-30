-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Thread/FileViews.lean: THE FILE's RULE FOR ACCEPTANCE
(Honest/Thread/FileYes.lean, `file_accepts`) WITH THE FRAME's OWN TEST ON THE VIEWS AS ITS PREMISE:
the falls are three lists of `Fall` (Honest/Side.lean); a fall that is not seated at a member's
place is never asked; "no fall speaks along the run" is `viewsFall F f₁ f₂ f₃ x r.run.views = none`
(Honest/Fall.lean): one equation with code, which reads the run's views and `F.pub x` alone.

WHAT THIS IS. A COROLLARY OF A CONDITIONAL LEMMA ON OUR OWN DEFINITIONS, pointwise. IT IS NONE OF
THE LIBRARY's GOALS, and it bears no milestone's name. Its premises are shown here of no
description. IT IS IDLE WHERE A THREAD CANNOT BE ENTERED.

FOUR WAYS IN WHICH THE RULE IS MET FOR NOTHING. (1) A THREAD THAT CANNOT BE ENTERED: as said. (2)
THE LETTERS FOR THE FALLS ARE FREE. A fall that always speaks: `Yes` holds for nothing, and "no
fall speaks" fails. WORSE: a fall that speaks just where its member's own step refuses: `Yes` holds
for nothing there, and "no fall speaks" then IS "that member's own step says yes along the run": A
PREMISE THAT HOLDS PART OF THE CONCLUSION. At a member without a round that is easily laid: its
step reads the state alone, as a fall's test does; and a description's members without a round may
bear real tests. (3) A PROVER THAT STOPS AT EVERY LIST: `silentAt` is never `none`. (4) A BOOK AT
WHICH `ready` REFUSES AT EVERY COIN. WHAT PAYS: THE SHARE: a fall's stated share (`Fall.share`,
Honest/Side.lean), which nothing here holds against its test, and the stops' measure. Each fall's
test is to NAME the verifier's own Bools that it holds; whatever else its member can refuse at is
`Accepted`'s to show (Honest/Thread/Pays.lean says the same of that debt).

How. `fallFree_of_views` (Honest/Law/FallFree.lean) and `file_accepts`. The yes at a member is
asked outside `fallsBy fᵢ ‹the chain's flat list›`: by the member's number, the falls that are
seated at its place.

Limits. As Honest/Thread/FileYes.lean's. Among the hypotheses that the prose above does not name:
`Draws.due` (the challenges are such as the description's rounds can draw; the first chain's last
challenge is the empty one): `file_accepts_views`; `FileDescription.planOk` (the library's executable
test): `file_accepts_views`; `FileDescription.okStart` (the library's executable test, at the instance):
`file_accepts_views`; `runC … = .ok` (`runC` returns at these coins and challenges):
`file_accepts_views`. This file proves nothing about soundness, completeness, hiding or any other
property of the protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.FileYes
import Johnson.Desc.ProofFile.Honest.Law.FallFree

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc

variable {W₀ Rc Xi Ky Tr X₀ X : Type} {Bk : ProverCoinCounts}

/-- **THE FILE's RULE FOR ACCEPTANCE, WHERE THE FRAME's OWN TEST ON THE VIEWS MEETS NO FALL.** A
conditional lemma on our own definitions. It is none of the library's goals, and it bears no
milestone's name. It is met for nothing in four
ways, which the head names: a thread that cannot be entered is one; a fall laid at will another. -/
theorem file_accepts_views {F : FileDescription Xi} {H : Prover W₀ Rc Xi Ky Tr X₀ X}
    {T₁ : Thread Bk F.S₁ F.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi}
    {T₂ : Thread Bk F.S₂ F.Cl Empty (Common W₀ Rc Ky) X₀ Ky}
    {T₃ : Thread Bk F.S₃ F.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi}
    {f₁ : List (Fall F.S₁)} {f₂ : List (Fall F.S₂)} {f₃ : List (Fall F.S₃)}
    {w₀ : W₀} {rc : Rc} {x : Xi} {k : Coins Bk} {ρ : Draws} {R : Ready W₀ Rc Xi Ky Tr X₀ X}
    {r : RunC F}
    (hS : Sits F H T₁ T₂ T₃) (hp : F.planOk = true) (hx : F.okStart x = true)
    (o₁ : Owes T₁) (o₂ : Owes T₂) (o₃ : Owes T₃)
    (y₁ : Yes T₁ (fallsBy f₁ F.first.blocksInOrder)) (y₂ : Yes T₂ (fallsBy f₂ F.shared.blocksInOrder))
    (y₃ : Yes T₃ (fallsBy f₃ F.second.blocksInOrder))
    (hR : ready F Bk H w₀ rc x k = .ok R) (hρ : ρ.due F = true)
    (hsil : silentAt F H w₀ rc x ρ = none)
    (a₁ : Enters₁ F H T₁ w₀ rc x k R) (a₂ : Enters₂ F H T₂ w₀ rc x k R)
    (a₃ : DoorBehind F H T₁ T₂ T₃ x k R) (door : DoorYes F T₁ T₂ x k)
    (fin : FinYes F T₁ T₂ T₃ x k)
    (h : runC F Bk H w₀ rc x k ρ = .ok r)
    (hv : viewsFall F f₁ f₂ f₃ x r.run.views = none) :
    (∃ e₁ e₂ e₃, r.ends = (some e₁, some e₂, some e₃)) ∧
      F.run x r.run.views.1 r.run.views.2.1 r.run.views.2.2 = true := by
  obtain ⟨n₁, n₂, n₃⟩ := fallFree_of_views h f₁ f₂ f₃ hv
  exact file_accepts hS hp hx o₁ o₂ o₃ y₁ y₂ y₃ hR hρ hsil a₁ a₂ a₃ door fin h n₁ n₂ n₃

end ProofFile.Honest

#print axioms ProofFile.Honest.file_accepts_views
