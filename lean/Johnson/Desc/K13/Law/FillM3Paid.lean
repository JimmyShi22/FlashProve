-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Law/FillM3Paid.lean: WHAT KIND K13's TIE ASKS OF THE TABLE's LETTERS (`FillM3`,
Johnson/Desc/K13/Law/AtTable.lean), WITH EVERY LEMMA THAT HAS BEEN COMPILED CALLED BY NAME. A
definition and statements with their proofs: calls alone.
What is called. `fillM3_at`, `mgK13_of_fills` (MgK13.lean, MgK13OfFills.lean) · `seed3`
(SigHeld.lean) for `OwedSeed3` · `pinsStay` (SigPins.lean)
for `OwedPinsStay` · `below_of_plan` (PlanTestsM3.lean) for the fifth test on the plan.
Main names:
  `weightsItem`: the public item "K13.weightsOk".
  `planK13_of`: the five tests on the plan in the form of PlanTestsM3.lean give `PlanK13`.
  `rider3_keeps`: a public item whose Bool is a test wB on the record that rides over the block's
    step (`OwedKeeps wB`, OwedSig.lean), and whose `pubP` says nothing, is a rider.
  `fillM3_paid`: **`FillM3` at any list Q of riders**, under NINE NAMED PREMISES:
    (1) hF: what the letters of Mg say (`FillsK13`: the composed meaning's files' to pay);
    (2) hW, hWP: what Mg says at "K13.weightsOk"; (3) hPl: five tests on the plan (`PlanM3`);
    (4) hIn: the proximity test's three items are in Q; (5) hQ: Q holds these three,
    "K13.pileMasks" and "K13.weightsOk" and no other; (6) hK: `OwedKeeps wB` (proved at
    wB := `First.weightsB`: `weightsKeeps`, RidersWeights.lean, which this file does not import);
    (7) hsmp: `SmpReads smp`; (8) hdec: `DecBlind decT`; (9) hrest: what other layers say of "in
    order" rides over the block's step.
What is not claimed. Any of the nine. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.K13.Law.MgK13OfFills
import Johnson.Desc.K13.Law.PlanTestsM3
import Johnson.Desc.K13.Law.SigHeld
import Johnson.Desc.K13.Law.SigPins

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open OnBytes OnBytes.Model OnBytes.Slice OnBytes.Maker
open Johnson.Pack (sigOf)
open VerifiableInference.Desc.First (S Pub Meaning Numbers)
open VerifiableInference.Desc.Sound (MsgT Sending Mem)

/-- The public item "K13.weightsOk". -/
def weightsItem : Pub := First.moreItem (none, "K13.weightsOk")

/-- The five tests on the plan, in the form in which they are tests with code. -/
theorem planK13_of {Pp : Type} {N : Numbers} {cs : Codes} {ms : List Mem} {M : List OracleShape}
    {L : K12.Door.Laid} (h : PlanM3 L M ms cs N) : PlanK13 Pp N cs ms M L where
  seat := h.hL
  shape := h.hshape
  code := h.hcode
  lengths := h.hlen
  below := below_of_plan h.hbelow

/-- A public item whose Bool is a test on the record that rides, and whose `pubP` says nothing. -/
theorem rider3_keeps {Pp W Cl : Type} {P : Where} {Mg : Meaning Pp W} {q : Pub} {wB : S → Bool}
    (hK : OwedKeeps wB) (hW : ∀ x, Mg.pub q x = wB x.2) (hWP : ∀ x, Mg.pubP q x) :
    Rider3 Cl P Mg q := fun x x' h =>
  ⟨fun h0 => by
    rw [hW] at h0 ⊢
    exact hK.1 P x x' h h0, fun _ => hWP x'⟩

/-- **`FillM3`, with what is through Lean called by name.** -/
theorem fillM3_paid {Pp Cl Xi Cells Tok : Type} {nR : ℕ} {P : Where} {N : Numbers}
    {Mg : Meaning Pp (Desc.Wit Cells Tok MsgT)} {cs : Codes} {sh : Params.ReqShape}
    {ly : Params.ReqLayout} {rest : Pp × S → Bool} {arr : ℕ → ℕ → ℕ}
    {mat : Cells → Fin nR → (Fin P.lin.kCol → Bool) → GE} {G : FileDescription Xi}
    {smp : Pp × S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp}
    {ms : List Mem} {decT : (ℕ → Option (ℕ × List UInt64)) → Pp × S → Option Cells}
    {M : List OracleShape} {L : K12.Door.Laid} {wB : S → Bool} (Q : List Pub)
    (hF : FillsK13 P N Mg cs sh ly rest arr mat G smp ms decT M L)
    (hW : ∀ x, Mg.pub weightsItem x = wB x.2) (hWP : ∀ x, Mg.pubP weightsItem x)
    (hPl : PlanM3 L M ms cs N)
    (hIn : bookItem ∈ Q ∧ seatsItem ∈ Q ∧ shapesItem ∈ Q)
    (hQ : ∀ q ∈ Q, q ∈ knownK13 ∨ q = weightsItem)
    (hK : OwedKeeps wB) (hsmp : SmpReads smp) (hdec : DecBlind decT)
    (hrest : ∀ x x', StepM3 Cl P x x' → rest x = true → rest x' = true) :
    FillM3 Cl P N Mg (rwBook arr mat) Q :=
  fillM3_at Q (mgK13_of_fills hF) (planK13_of hPl) hIn.1 hIn.2.1 hIn.2.2 seed3 pinsStay hsmp hdec
    hrest fun q hq hk => by
      rcases hQ q hq with h | rfl
      · exact absurd h hk
      · exact rider3_keeps hK hW hWP

end VerifiableInference.Desc.K13.Law
