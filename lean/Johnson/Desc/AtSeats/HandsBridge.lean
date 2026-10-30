--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/AtSeats/HandsBridge.lean: `IM.Hands` AT A WIDER FURTHER
TEST IS `IM.HandsR` (HandsFence.lean: another house's light file: `Hands` with a fence Fk) AT THE
NARROWER ONE. Statements with their proofs; free of any kind of sub-protocol. Why. Our terms of
`Hands` at kind K13's batching, at W's commitment and at the first segment's opening rest on
structures on the table's letters that name public items which have left the door: they have
members at a WIDER filling alone. The half of the promise that reads the verifier's state is asked
at the narrower filling, with the facts on the state in hand as a fence. This is the like, for
that half, of the bridge for ties (Johnson/Desc/Sound/PlusDoor.lean). `handsR_of_wider`: **THE
  BRIDGE**: from `IM.Hands N links ps E' ft k b`: `IM.HandsR Fk N links ps E ft k b`,
    WHERE: under the fence, at a state without a mark, the narrower test with the four tests on the
    book-keeping gives the wider test at border k (up); the wider test gives the narrower at border
    k + 1 (down).
  `eAt_down`, `eAt_up`: "down" and "up" at the promise's public test (`EAt`)
  of two fillings Mg and `widen Mg M pub' io'`, from the test on the two
    doors (`doorsFitB`) and "outside the class the wider tests are Mg's"
    (Johnson/Desc/Sound/PlusDoorA.lean); up asks of the fence that each item of the class that is
    open at M passes the wider test.
  `handsR_of_widen`: so at these two.
What is not claimed. That the fence gives the facts. Nothing on soundness.

-/
import Johnson.IMR.HandsFence
import Johnson.Desc.AtSeats.HandsAtE
import Johnson.Desc.Sound.PlusDoorA

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace HashBuild
open VerifiableInference.Desc (Block Place)
open VerifiableInference.Desc.First (S ModelPart Numbers More Pub Meaning)
open VerifiableInference.Desc.Sound (widen doorsFitB doorsFitB_parts)
open VerifiableInference.Desc
open ProofFile (Cl)

/-- The four tests on the book-keeping do not read the further test. -/
theorem xk_swap {N : Numbers} {links : List ModelPart} {ps : List Place} {E E' : ℕ → S → Bool} {k : ℕ}
    {s : S} (hx : IM.XK N links ps E k s = true) (he : E' k s = true) :
    IM.XK N links ps E' k s = true := by
  unfold IM.XK at hx ⊢
  rw [Bool.and_eq_true] at hx ⊢
  exact ⟨hx.1, he⟩

/-- **THE BRIDGE.** -/
theorem handsR_of_wider {Fk : ℕ → S → Prop} {N : Numbers} {links : List ModelPart} {ps : List Place}
    {E E' : ℕ → S → Bool} {ft k : ℕ} {b : Block S Cl}
    (hup : ∀ s, Fk k s → s.failed = none → IM.XK N links ps E k s = true → E' k s = true)
    (hdown : ∀ s, E' (k + 1) s = true → E (k + 1) s = true)
    (H : IM.Hands N links ps E' ft k b) : IM.HandsR Fk N links ps E ft k b where
  mark := fun s s' _ hy => H.mark s s' hy
  shape := fun s s' f hy h0 h1 hx => H.shape s s' hy h0 h1 (xk_swap hx (hup s f h0 hx))
  rows := fun s s' f hy h0 h1 hx => H.rows s s' hy h0 h1 (xk_swap hx (hup s f h0 hx))
  members := fun s s' f hy h0 h1 hx => H.members s s' hy h0 h1 (xk_swap hx (hup s f h0 hx))
  book := fun s s' f hy h0 h1 hx => H.book s s' hy h0 h1 (xk_swap hx (hup s f h0 hx))
  more := fun s s' f hy h0 h1 hx => hdown s' (H.more s s' hy h0 h1 (xk_swap hx (hup s f h0 hx)))

section
variable {Pp W : Type} (z : Pp) (Mg : Meaning Pp W) (M : More) (pub' : Pub → Pp × S → Bool)
  (io' : Pp × S → Bool) (cA : Pub → Bool) (links : List ModelPart) (ps : List Place)

/-- From the wider filling's public test to the narrower's. -/
theorem eAt_down (k : ℕ) (s : S) (hhand : ∀ q, cA q = false → ∀ x, pub' q x = Mg.pub q x)
    (hD : doorsFitB Mg.more M cA links ps k = true)
    (h : EAt z (widen Mg M pub' io') links ps k s = true) : EAt z Mg links ps k s = true := by
  obtain ⟨d1, _, d3⟩ := doorsFitB_parts hD
  obtain ⟨h2, h3⟩ := eAt_parts h
  refine eAt_of (fun q hq => ?_) fun q hq => ?_
  · rw [← hhand q (d1 q hq).2]
    exact h2 q (d1 q hq).1
  · rw [← hhand q (d3 q hq)]
    exact h3 q hq

/-- From the narrower to the wider, where each item of the class that is open at M passes. -/
theorem eAt_up (k : ℕ) (s : S) (hhand : ∀ q, cA q = false → ∀ x, pub' q x = Mg.pub q x)
    (hD : doorsFitB Mg.more M cA links ps k = true)
    (hF : ∀ q ∈ (First.pubSets M links ps)[k]?.getD [], cA q = true → pub' q (z, s) = true)
    (h : EAt z Mg links ps k s = true) : EAt z (widen Mg M pub' io') links ps k s = true := by
  obtain ⟨_, d2, d3⟩ := doorsFitB_parts hD
  obtain ⟨h2, h3⟩ := eAt_parts h
  refine eAt_of (fun q hq => ?_) fun q hq => ?_
  · show pub' q (z, s) = true
    cases hc : cA q with
    | true => exact hF q hq hc
    | false =>
      rw [hhand q hc]
      refine h2 q ((d2 q hq).resolve_left ?_)
      rw [hc]
      exact Bool.false_ne_true
  · show pub' q (z, s) = true
    rw [hhand q (d3 q hq)]
    exact h3 q hq

/-- **The bridge at the promise's public test of two fillings.** -/
theorem handsR_of_widen {Fk : ℕ → S → Prop} {N : Numbers} {ft k : ℕ} {b : Block S Cl}
    (hhand : ∀ q, cA q = false → ∀ x, pub' q x = Mg.pub q x)
    (hD : doorsFitB Mg.more M cA links ps k = true)
    (hD' : doorsFitB Mg.more M cA links ps (k + 1) = true)
    (hF : ∀ s, Fk k s → s.failed = none → ∀ q ∈ (First.pubSets M links ps)[k]?.getD [],
      cA q = true → pub' q (z, s) = true)
    (H : IM.Hands N links ps (EAt z (widen Mg M pub' io') links ps) ft k b) :
    IM.HandsR Fk N links ps (EAt z Mg links ps) ft k b :=
  handsR_of_wider
    (fun s f h0 hx => eAt_up z Mg M pub' io' cA links ps k s hhand hD (hF s f h0)
      (IM.xk_parts hx).2.2.2.2)
    (fun s h => eAt_down z Mg M pub' io' cA links ps (k + 1) s hhand hD' h) H

end

end HashBuild
