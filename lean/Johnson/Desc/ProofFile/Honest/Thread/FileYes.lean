-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Thread/FileYes.lean: the rule for a file, its second half: acceptance.
From the hypotheses at every sub-protocol of the three chains' flat lists, the acceptance among them
(Honest/Thread/Pays.lean), and the conditions where the chains begin and meet
(Honest/Thread/File.lean): where `runC` (Honest/Walk.lean) has returned a run along which no fall
fires, no chain has rejected, and the description accepts that run's views.

What this is. A conditional lemma on this folder's own definitions, pointwise: at one input, one
run's coins and one list of challenges. It is none of the library's goals and proves none of them,
and no goal follows from it without its hypotheses. Its hypotheses are proved here of no
description. It says nothing where an invariant cannot be entered: an invariant that is false
everywhere satisfies `Owes` and `Yes` vacuously; if it is the first or the shared chain's it fails
`Enters₁` or `Enters₂`, and if it is the second chain's, `DoorBehind` cannot be proved unless it
holds vacuously.

Five ways in which the rule holds vacuously or trivially.
  * An invariant that cannot be entered: as said.
  * The parameters for the falls are free. With a fall that always fires, `Yes` holds vacuously, and
    "no fall fires" fails. Worse, with a fall that fires exactly where its sub-protocol's own step
    rejects, `Yes` holds trivially there, and "no fall fires" then is "that sub-protocol's own step
    accepts along the run": a hypothesis that contains part of the conclusion. At a sub-protocol
    without a round that is easily arranged: its step reads the state alone, as a fall's test does;
    and a description's sub-protocols without a round may have real tests.
  * A prover that stops at every list of challenges: `silentAt` is never `none`.
  * A book at which `ready` returns an error at every coin.
  * A prover with a part that reads the field `opened` and errs at `none` (its duty:
    Honest/Frame.lean, `Seen.opened`): `Owes` takes `Thr` alone, so it holds there only if the
    invariant before that part's sub-protocol is never met where it could play; the other hypotheses
    carry the invariant there: the rule says nothing at such a prover, whatever the `Thread`s
    (Limits; the road: Honest/Thread/FileS.lean).
What this costs is the share: a fall's stated share (`Fall.share`, Honest/Side.lean), which nothing
here compares with its test, and the stops' measure. Each fall's test is to name the verifier's own
Bools that it covers; whatever else its sub-protocol can reject at has to be proved in `Accepted`
(Honest/Thread/Pays.lean says the same of that hypothesis).

How. By calls alone: `playsOn_of_owes`, `saysYes_of_yes` (Honest/Thread/File.lean), and the general
rule `runC_accepts` (Honest/Law/AcceptC.lean), at the three families of conditions `Thr T₁`,
`Thr T₂`, `Thr T₃`. That rule asks the invariants at the starts at the states as `ChainProgress.start` lays
them; `Enters₁`, `Enters₂` and `DoorBehind` stand at the states that `ready` gives, and serve there
because `Thr` does not read the field `opened`.

Every hypothesis, and what it is. Those of `file_runs`, but for `sealPlain` and `PlanServes` (the
run is given). `F.okStart x`: an executable test on the instance. `Yes`: the acceptance at every
sub-protocol, outside the parameters fl₁, fl₂, fl₃. `DoorYes`, `FinYes`: the second chain's start
and the last test accept at the invariants' ends. No fall fires: `fallFree`
(Honest/Law/AcceptC.lean) at these parameters, along the verifier's own steps on the run's own
views; the third from the second chain's start at the run's first two ends, which are the ends of
the verifier's steps on these views (`runC_ends`, Honest/Law/RunC.lean).

Limits.
  * Nothing on how likely a stop or a fall is: no probability is in it.
  * It speaks of `FileDescription.run` on the views of the run of `runC`: not of a typed transcript, a
    strategy, a nonce or a compiled verifier.
  * Among the hypotheses that the prose above does not name: `Draws.due` (the challenges are such as
    the description's rounds can draw; the first chain's last challenge is the empty one):
    `file_accepts`; `FileDescription.planOk` (the library's executable test): `file_accepts`.
  * The hypotheses of Honest/Thread/Pays.lean take `Thr` alone, which does not read the state's
    field `opened`: they are asked at every value of the field, `none` too. At a sub-protocol with a
    part that errs where no columns are handed, `Plays` is met in that form only vacuously
    (Honest/Thread/ThrField.lean, Limits); the road from `ThrS` is Honest/Thread/FileS.lean.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.File
import Johnson.Desc.ProofFile.Honest.Law.AcceptC

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc

variable {W₀ Rc Xi Ky Tr X₀ X : Type} {Bk : ProverCoinCounts}

/-- **The rule for a file, acceptance: where no fall fires along the run, the description accepts
its views.** A conditional lemma on this folder's own definitions. It is none of the library's
goals. It holds vacuously or trivially in five ways, which the head names: an invariant that cannot
be entered is one; a fall chosen at will another. -/
theorem file_accepts {F : FileDescription Xi} {H : Prover W₀ Rc Xi Ky Tr X₀ X}
    {T₁ : Thread Bk F.S₁ F.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi}
    {T₂ : Thread Bk F.S₂ F.Cl Empty (Common W₀ Rc Ky) X₀ Ky}
    {T₃ : Thread Bk F.S₃ F.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi}
    {fl₁ : Nat → F.S₁ → List Fmt.Drawn → Option String}
    {fl₂ : Nat → F.S₂ → List Fmt.Drawn → Option String}
    {fl₃ : Nat → F.S₃ → List Fmt.Drawn → Option String}
    {w₀ : W₀} {rc : Rc} {x : Xi} {k : Coins Bk} {ρ : Draws} {R : Ready W₀ Rc Xi Ky Tr X₀ X}
    {r : RunC F}
    (hS : Sits F H T₁ T₂ T₃) (hp : F.planOk = true) (hx : F.okStart x = true)
    (o₁ : Owes T₁) (o₂ : Owes T₂) (o₃ : Owes T₃)
    (y₁ : Yes T₁ fl₁) (y₂ : Yes T₂ fl₂) (y₃ : Yes T₃ fl₃)
    (hR : ready F Bk H w₀ rc x k = .ok R) (hρ : ρ.due F = true)
    (hsil : silentAt F H w₀ rc x ρ = none)
    (a₁ : Enters₁ F H T₁ w₀ rc x k R) (a₂ : Enters₂ F H T₂ w₀ rc x k R)
    (a₃ : DoorBehind F H T₁ T₂ T₃ x k R) (door : DoorYes F T₁ T₂ x k)
    (fin : FinYes F T₁ T₂ T₃ x k)
    (h : runC F Bk H w₀ rc x k ρ = .ok r)
    (n₁ : fallFree 0 F.first.blocksInOrder fl₁ (F.start₁ (F.pub x)) (withEmptySealRound r.run.views.1).rounds
      r.run.views.1.opened)
    (n₂ : fallFree 0 F.shared.blocksInOrder fl₂ (F.start₂ (F.pub x)) r.run.views.2.1.rounds
      r.run.views.2.1.opened)
    (n₃ : ∀ e₁ e₂ s₃, r.ends.1 = some e₁ → r.ends.2.1 = some e₂ →
      F.start₃ (F.pub x) e₁ e₂ = .ok s₃ →
      fallFree F.lastChainFirstTreeNumber F.second.blocksInOrder fl₃ s₃ r.run.views.2.2.rounds r.run.views.2.2.opened) :
    (∃ e₁ e₂ e₃, r.ends = (some e₁, some e₂, some e₃)) ∧
      F.run x r.run.views.1 r.run.views.2.1 r.run.views.2.2 = true := by
  obtain ⟨⟨p1, c1, f1, b1, h1⟩, ⟨p2, c2, f2, b2, h2⟩, ⟨p3, c3, f3, b3, h3⟩, t1, t2, t3⟩ := hS
  obtain ⟨s1, s2, s3⟩ := planOk_all hp
  have q₁ := playsOn_of_owes T₁ (by rw [b1]; exact t1) (by rw [b1]; exact s1) o₁
  have q₂ := playsOn_of_owes T₂ (by rw [b2]; exact t2) (by rw [b2]; exact s2) o₂
  have q₃ := playsOn_of_owes T₃ (by rw [b3]; exact t3) (by rw [b3]; exact s3) o₃
  have z₁ := saysYes_of_yes T₁ y₁
  have z₂ := saysYes_of_yes T₂ y₂
  have z₃ := saysYes_of_yes T₃ y₃
  rw [p1, c1, f1, b1, h1] at q₁ z₁
  rw [p2, c2, f2, b2, h2] at q₂ z₂
  rw [p3, c3, f3, b3, h3] at q₃ z₃
  exact runC_accepts h hR hp hx hρ hsil (Thr T₁) (Thr T₂) (Thr T₃) fl₁ fl₂ fl₃ q₁ q₂ q₃ z₁ z₂ z₃
    a₁ a₂
    (fun e₁ m₁ E₁ e₂ m₂ E₂ _ _ u₁ u₂ _ _ => by
      obtain ⟨s₃, hs⟩ := door e₁ m₁ E₁ e₂ m₂ E₂ u₁ u₂
      exact ⟨s₃, hs, a₃ e₁ m₁ E₁ e₂ m₂ E₂ s₃ u₁ u₂ hs⟩)
    fin n₁ n₂ n₃

end ProofFile.Honest

#print axioms ProofFile.Honest.file_accepts
