-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Law/FillM3Paid6.lean: `fillM3_paid5` (Johnson/Desc/K13/Law/RidersMore.lean) WITH
ITS ONE OWED PREMISE CALLED BY NAME: over a yes of kind K13's block "K13.pileWithin" goes on:
`withinM3` (WithinM3.lean) at `ledgersC` and `ledgersKept` (LedgersC.lean,
LedgersKept.lean). A statement with its proof: a call alone.
  `withinM3_paid`: `OwedWithinM3`, with no premise.
  `fillM3_paid6`: **`FillM3` at any list Q of riders** as in `fillM3_paid5`: NO LAW ON A BLOCK IS
  LEFT AMONG ITS PREMISES: what the letters of Mg say (`FillsK13`; Mg at "K13.weightsOk" and at
  "K12.bookFits") · five tests on the plan (`PlanM3`) · which items are in Q · `SmpReads smp` ·
  `DecBlind decT` · what other layers say of "in order" rides (its payer: `rest_M3`, RestAtM3.lean).
What is not claimed. The premises. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.K13.Law.RidersMore
import Johnson.Desc.K13.Law.WithinM3
import Johnson.Desc.K13.Law.LedgersKept

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open OnBytes OnBytes.Model OnBytes.Slice OnBytes.Maker
open Johnson.Pack (sigOf)
open VerifiableInference.Desc.First (S Pub Meaning Numbers)
open VerifiableInference.Desc.Sound (MsgT Sending Mem)

/-- Over a yes of kind K13's block "K13.pileWithin" goes on. -/
theorem withinM3_paid : OwedWithinM3 := withinM3 ledgersC ledgersKept

/-- **`FillM3`, with every law on a block called by name.** -/
theorem fillM3_paid6 {Pp Cl Xi Cells Tok : Type} {nR : ℕ} {P : Where} {N : Numbers}
    {Mg : Meaning Pp (Desc.Wit Cells Tok MsgT)} {cs : Codes} {sh : Params.ReqShape}
    {ly : Params.ReqLayout} {rest : Pp × S → Bool} {arr : ℕ → ℕ → ℕ}
    {mat : Cells → Fin nR → (Fin P.lin.kCol → Bool) → GE} {G : FileDescription Xi}
    {smp : Pp × S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp}
    {ms : List Mem} {decT : (ℕ → Option (ℕ × List UInt64)) → Pp × S → Option Cells}
    {M : List OracleShape} {L : K12.Door.Laid} (Q : List Pub)
    (hF : FillsK13 P N Mg cs sh ly rest arr mat G smp ms decT M L)
    (hW : ∀ x, Mg.pub weightsItem x = First.weightsB x.2) (hWP : ∀ x, Mg.pubP weightsItem x)
    (hB : ∀ x, Mg.pub bookFitsItem x = Sound.bookFitsB x.2.book)
    (hBP : ∀ x, Mg.pubP bookFitsItem x) (hPl : PlanM3 L M ms cs N)
    (hIn : bookItem ∈ Q ∧ seatsItem ∈ Q ∧ shapesItem ∈ Q)
    (hQ : ∀ q ∈ Q, q ∈ knownK13 ∨ q = weightsItem ∨ q = pileWithinItem ∨ q = oneRowItem ∨
      q = bookFitsItem)
    (hsmp : SmpReads smp) (hdec : DecBlind decT)
    (hrest : ∀ x x', StepM3 Cl P x x' → rest x = true → rest x' = true) :
    FillM3 Cl P N Mg (rwBook arr mat) Q :=
  fillM3_paid5 Q hF hW hWP hB hBP hPl hIn hQ withinM3_paid hsmp hdec hrest

end VerifiableInference.Desc.K13.Law
