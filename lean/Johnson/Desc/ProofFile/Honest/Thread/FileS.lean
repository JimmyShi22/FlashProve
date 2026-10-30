-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Thread/FileS.lean: THE FILE's RULE FOR ACCEPTANCE, WITH THE MEMBERS'
DEBTS ASKED FROM THE PAIR OF THE THREAD AND WHAT IS SAID (Honest/Thread/PaysS.lean): `file_runs`,
`file_accepts` and `file_accepts_views` (Honest/Thread/File.lean, FileYes.lean, FileViews.lean)
with `OwesS` and `YesS` in the stead of `Owes` and `Yes`: WEAKER PREMISES; beside them `SaidNext`
at every member and the letter at the three starts. The premises at the chains' starts and ends
stay asked from the threads alone. Calls alone: the fold's own rules in letters
(Honest/Law/RunsFile.lean, AcceptC.lean, FallFree.lean) at the three families `ThrS T₁ S₁`, `ThrS
T₂ S₂`, `ThrS T₃ S₃`.

  `file_runsS`, `file_acceptsS`, `file_accepts_viewsS`

WHAT THESE ARE. CONDITIONAL LEMMAS ON OUR OWN DEFINITIONS, pointwise. NONE IS ONE OF THE LIBRARY's
GOALS; they bear no milestone's name; their premises are shown here of no description. THEIR END IS
`FileDescription.run`'s YES ON THE VIEWS OF `runC`'s RUN: one of the nine tests of the reduction's verdict:
not a verifier's accept. THEY ARE MET FOR NOTHING in the four ways that File.lean's head names; THEY
ARE IDLE where the letter cannot be entered (Said := False: the premises on the letter at the starts
cannot then be met).

Limits. Nothing on how likely a stop or a fall is. The letter at the three starts is asked at the
states as `ChainProgress.start` lays them (the field `opened`: `some []`, `some []`, and, where the two ends'
fields hold columns, these joined). `Enters₁`, `Enters₂` stand at the states that `ready` gives, and
serve there because `Thr` does not read the field. `SaidNext` asks the letter at the state that has
taken the sub-protocol's columns (`Mid.took`). The members' debts are asked at every state that
`ThrS` allows, at every value of the field `opened` too: where a member has a part that reads the
columns and errs at `none` (its duty: Honest/Frame.lean, `Seen.opened`), `PlaysS`
(Honest/Thread/PaysS.lean) at a letter that lets `none` through before it is met only vacuously.
Among the hypotheses that the prose above does not name: `Draws.due` (the challenges are such as
the description's rounds can draw; the first chain's last challenge is the empty one):
`file_runsS`, `file_acceptsS`, `file_accepts_viewsS`;
`FileDescription.planOk` (the library's executable test): `file_runsS`, `file_acceptsS`,
`file_accepts_viewsS`; `sealPlain` (the first chain's last declared round declares no item except
roots, and no root): `file_runsS`; `ready … = .ok` (`ready` returns at these coins): `file_runsS`,
`file_acceptsS`, `file_accepts_viewsS`; `silentAt … = none` (the honest side does not stop at these
challenges, or the request has no trace): `file_runsS`, `file_acceptsS`, `file_accepts_viewsS`;
`PlanServes` (Honest/Law/RunsFile.lean): `file_runsS`; `FileDescription.okStart` (the library's executable
test, at the instance): `file_acceptsS`, `file_accepts_viewsS`. This file proves nothing about
soundness, completeness, hiding or any other property of the protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.PaysS
import Johnson.Desc.ProofFile.Honest.Thread.FileViews

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc

variable {W₀ Rc Xi Ky Tr X₀ X : Type} {Bk : ProverCoinCounts}

section
variable {F : FileDescription Xi} {H : Prover W₀ Rc Xi Ky Tr X₀ X}
  {T₁ : Thread Bk F.S₁ F.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi}
  {T₂ : Thread Bk F.S₂ F.Cl Empty (Common W₀ Rc Ky) X₀ Ky}
  {T₃ : Thread Bk F.S₃ F.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi}
  {S₁ : Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr) X → Prop}
  {S₂ : Nat → Coins Bk → Mid (Common W₀ Rc Ky) X₀ → Prop}
  {S₃ : Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr) X → Prop}
  {w₀ : W₀} {rc : Rc} {x : Xi} {k : Coins Bk} {ρ : Draws} {R : Ready W₀ Rc Xi Ky Tr X₀ X}

/-- **THE RUN RETURNS**, with the debts asked from the pair. A conditional lemma on our own
definitions. It is none of the library's goals, and it bears no milestone's name. -/
theorem file_runsS (hS : Sits F H T₁ T₂ T₃) (hp : F.planOk = true)
    (o₁ : OwesS T₁ S₁) (o₂ : OwesS T₂ S₂) (o₃ : OwesS T₃ S₃)
    (n₁ : ∀ b, SaidNext T₁ S₁ b) (n₂ : ∀ b, SaidNext T₂ S₂ b) (n₃ : ∀ b, SaidNext T₃ S₃ b)
    (hR : ready F Bk H w₀ rc x k = .ok R) (hq : sealPlain F = true) (hρ : ρ.due F = true)
    (hsil : silentAt F H w₀ rc x ρ = none) (hP : PlanServes H w₀ rc R)
    (a₁ : Enters₁ F H T₁ w₀ rc x k R) (a₂ : Enters₂ F H T₂ w₀ rc x k R)
    (a₃ : DoorBehind F H T₁ T₂ T₃ x k R)
    (e₁ : S₁ 0 k { R.start₁ H with opened := some [] })
    (e₂ : S₂ 0 k { R.start₂ H with opened := some [] })
    (e₃ : ∀ m₁ m₂ o₁ o₂, S₁ F.first.blocksInOrder.length k m₁ → S₂ F.shared.blocksInOrder.length k m₂ →
      m₁.opened = some o₁ → m₂.opened = some o₂ →
      S₃ 0 k { R.start₃ H m₁ m₂ with opened := some (o₁ ++ o₂) }) :
    ∃ r, runC F Bk H w₀ rc x k ρ = .ok r := by
  obtain ⟨⟨p1, c1, f1, b1, h1⟩, ⟨p2, c2, f2, b2, h2⟩, ⟨p3, c3, f3, b3, h3⟩, t1, t2, t3⟩ := hS
  obtain ⟨s1, s2, s3⟩ := planOk_all hp
  have q₁ := playsOn_of_owesS T₁ S₁ (by rw [b1]; exact t1) (by rw [b1]; exact s1) o₁ n₁
  have q₂ := playsOn_of_owesS T₂ S₂ (by rw [b2]; exact t2) (by rw [b2]; exact s2) o₂ n₂
  have q₃ := playsOn_of_owesS T₃ S₃ (by rw [b3]; exact t3) (by rw [b3]; exact s3) o₃ n₃
  rw [p1, c1, f1, b1, h1] at q₁
  rw [p2, c2, f2, b2, h2] at q₂
  rw [p3, c3, f3, b3, h3] at q₃
  exact runC_returns hR hq hρ hsil hP (ThrS T₁ S₁) (ThrS T₂ S₂) (ThrS T₃ S₃) q₁ q₂ q₃ ⟨a₁, e₁⟩
    ⟨a₂, e₂⟩ fun v₁ m₁ E₁ v₂ m₂ E₂ s₃ o₁ o₂ u₁ u₂ hs g₁ g₂ =>
      ⟨a₃ v₁ m₁ E₁ v₂ m₂ E₂ s₃ u₁.1 u₂.1 hs, e₃ m₁ m₂ o₁ o₂ u₁.2 u₂.2 g₁ g₂⟩

/-- **THE FILE's RULE FOR ACCEPTANCE**, with the debts asked from the pair. A conditional lemma on
our own definitions. It is none of the library's goals, and it bears no milestone's name. -/
theorem file_acceptsS {fl₁ : Nat → F.S₁ → List Fmt.Drawn → Option String}
    {fl₂ : Nat → F.S₂ → List Fmt.Drawn → Option String}
    {fl₃ : Nat → F.S₃ → List Fmt.Drawn → Option String} {r : RunC F}
    (hS : Sits F H T₁ T₂ T₃) (hp : F.planOk = true) (hx : F.okStart x = true)
    (o₁ : OwesS T₁ S₁) (o₂ : OwesS T₂ S₂) (o₃ : OwesS T₃ S₃)
    (n₁ : ∀ b, SaidNext T₁ S₁ b) (n₂ : ∀ b, SaidNext T₂ S₂ b) (n₃ : ∀ b, SaidNext T₃ S₃ b)
    (y₁ : YesS T₁ S₁ fl₁) (y₂ : YesS T₂ S₂ fl₂) (y₃ : YesS T₃ S₃ fl₃)
    (hR : ready F Bk H w₀ rc x k = .ok R) (hρ : ρ.due F = true)
    (hsil : silentAt F H w₀ rc x ρ = none)
    (a₁ : Enters₁ F H T₁ w₀ rc x k R) (a₂ : Enters₂ F H T₂ w₀ rc x k R)
    (a₃ : DoorBehind F H T₁ T₂ T₃ x k R) (door : DoorYes F T₁ T₂ x k)
    (fin : FinYes F T₁ T₂ T₃ x k)
    (e₁ : S₁ 0 k { R.start₁ H with opened := some [] })
    (e₂ : S₂ 0 k { R.start₂ H with opened := some [] })
    (e₃ : ∀ m₁ m₂ o₁ o₂, S₁ F.first.blocksInOrder.length k m₁ → S₂ F.shared.blocksInOrder.length k m₂ →
      m₁.opened = some o₁ → m₂.opened = some o₂ →
      S₃ 0 k { R.start₃ H m₁ m₂ with opened := some (o₁ ++ o₂) })
    (h : runC F Bk H w₀ rc x k ρ = .ok r)
    (g₁ : fallFree 0 F.first.blocksInOrder fl₁ (F.start₁ (F.pub x)) (withEmptySealRound r.run.views.1).rounds
      r.run.views.1.opened)
    (g₂ : fallFree 0 F.shared.blocksInOrder fl₂ (F.start₂ (F.pub x)) r.run.views.2.1.rounds
      r.run.views.2.1.opened)
    (g₃ : ∀ v₁ v₂ s₃, r.ends.1 = some v₁ → r.ends.2.1 = some v₂ →
      F.start₃ (F.pub x) v₁ v₂ = .ok s₃ →
      fallFree F.lastChainFirstTreeNumber F.second.blocksInOrder fl₃ s₃ r.run.views.2.2.rounds r.run.views.2.2.opened) :
    (∃ v₁ v₂ v₃, r.ends = (some v₁, some v₂, some v₃)) ∧
      F.run x r.run.views.1 r.run.views.2.1 r.run.views.2.2 = true := by
  obtain ⟨⟨p1, c1, f1, b1, h1⟩, ⟨p2, c2, f2, b2, h2⟩, ⟨p3, c3, f3, b3, h3⟩, t1, t2, t3⟩ := hS
  obtain ⟨s1, s2, s3⟩ := planOk_all hp
  have q₁ := playsOn_of_owesS T₁ S₁ (by rw [b1]; exact t1) (by rw [b1]; exact s1) o₁ n₁
  have q₂ := playsOn_of_owesS T₂ S₂ (by rw [b2]; exact t2) (by rw [b2]; exact s2) o₂ n₂
  have q₃ := playsOn_of_owesS T₃ S₃ (by rw [b3]; exact t3) (by rw [b3]; exact s3) o₃ n₃
  have z₁ := saysYes_of_yesS T₁ S₁ y₁
  have z₂ := saysYes_of_yesS T₂ S₂ y₂
  have z₃ := saysYes_of_yesS T₃ S₃ y₃
  rw [p1, c1, f1, b1, h1] at q₁ z₁
  rw [p2, c2, f2, b2, h2] at q₂ z₂
  rw [p3, c3, f3, b3, h3] at q₃ z₃
  exact runC_accepts h hR hp hx hρ hsil (ThrS T₁ S₁) (ThrS T₂ S₂) (ThrS T₃ S₃) fl₁ fl₂ fl₃ q₁ q₂ q₃
    z₁ z₂ z₃ ⟨a₁, e₁⟩ ⟨a₂, e₂⟩
    (fun v₁ m₁ E₁ v₂ m₂ E₂ o₁ o₂ u₁ u₂ j₁ j₂ => by
      obtain ⟨s₃, hs⟩ := door v₁ m₁ E₁ v₂ m₂ E₂ u₁.1 u₂.1
      exact ⟨s₃, hs, a₃ v₁ m₁ E₁ v₂ m₂ E₂ s₃ u₁.1 u₂.1 hs, e₃ m₁ m₂ o₁ o₂ u₁.2 u₂.2 j₁ j₂⟩)
    (fun v₁ m₁ E₁ v₂ m₂ E₂ v₃ m₃ E₃ u₁ u₂ u₃ => fin v₁ m₁ E₁ v₂ m₂ E₂ v₃ m₃ E₃ u₁.1 u₂.1 u₃.1)
    g₁ g₂ g₃

/-- **THE SAME, WITH "NO FALL SPEAKS" AS ONE TEST ON THE VIEWS.** -/
theorem file_accepts_viewsS {f₁ : List (Fall F.S₁)} {f₂ : List (Fall F.S₂)}
    {f₃ : List (Fall F.S₃)} {r : RunC F}
    (hS : Sits F H T₁ T₂ T₃) (hp : F.planOk = true) (hx : F.okStart x = true)
    (o₁ : OwesS T₁ S₁) (o₂ : OwesS T₂ S₂) (o₃ : OwesS T₃ S₃)
    (n₁ : ∀ b, SaidNext T₁ S₁ b) (n₂ : ∀ b, SaidNext T₂ S₂ b) (n₃ : ∀ b, SaidNext T₃ S₃ b)
    (y₁ : YesS T₁ S₁ (fallsBy f₁ F.first.blocksInOrder)) (y₂ : YesS T₂ S₂ (fallsBy f₂ F.shared.blocksInOrder))
    (y₃ : YesS T₃ S₃ (fallsBy f₃ F.second.blocksInOrder))
    (hR : ready F Bk H w₀ rc x k = .ok R) (hρ : ρ.due F = true)
    (hsil : silentAt F H w₀ rc x ρ = none)
    (a₁ : Enters₁ F H T₁ w₀ rc x k R) (a₂ : Enters₂ F H T₂ w₀ rc x k R)
    (a₃ : DoorBehind F H T₁ T₂ T₃ x k R) (door : DoorYes F T₁ T₂ x k)
    (fin : FinYes F T₁ T₂ T₃ x k)
    (e₁ : S₁ 0 k { R.start₁ H with opened := some [] })
    (e₂ : S₂ 0 k { R.start₂ H with opened := some [] })
    (e₃ : ∀ m₁ m₂ o₁ o₂, S₁ F.first.blocksInOrder.length k m₁ → S₂ F.shared.blocksInOrder.length k m₂ →
      m₁.opened = some o₁ → m₂.opened = some o₂ →
      S₃ 0 k { R.start₃ H m₁ m₂ with opened := some (o₁ ++ o₂) })
    (h : runC F Bk H w₀ rc x k ρ = .ok r)
    (hv : viewsFall F f₁ f₂ f₃ x r.run.views = none) :
    (∃ v₁ v₂ v₃, r.ends = (some v₁, some v₂, some v₃)) ∧
      F.run x r.run.views.1 r.run.views.2.1 r.run.views.2.2 = true := by
  obtain ⟨g₁, g₂, g₃⟩ := fallFree_of_views h f₁ f₂ f₃ hv
  exact file_acceptsS hS hp hx o₁ o₂ o₃ n₁ n₂ n₃ y₁ y₂ y₃ hR hρ hsil a₁ a₂ a₃ door fin e₁ e₂ e₃ h
    g₁ g₂ g₃

end

end ProofFile.Honest

#print axioms ProofFile.Honest.file_runsS
#print axioms ProofFile.Honest.file_acceptsS
#print axioms ProofFile.Honest.file_accepts_viewsS
