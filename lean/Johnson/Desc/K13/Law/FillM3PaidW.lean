-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Law/FillM3PaidW.lean: `fillM3_paid` (Johnson/Desc/K13/Law/FillM3Paid.lean) WITH ITS
SIXTH PREMISE CALLED BY NAME: "K13.weightsOk" rides over kind K13's block: `weightsKeeps`
(Johnson/Desc/K13/Law/RidersWeights.lean). A statement with its proof: a call
alone.
  `fillM3_paidW`: **`FillM3` at any list Q of riders**, under EIGHT NAMED PREMISES: (1) hF: what the
  letters of Mg say (`FillsK13`); (2) hW, hWP: Mg at "K13.weightsOk" says `First.weightsB` and
  nothing beside; (3) hPl: five tests on the plan (`PlanM3`); (4) hIn, (5) hQ: which items are in Q;
  (6) hsmp: `SmpReads smp`; (7) hdec: `DecBlind decT`; (8) hrest: what other layers say of "in
  order" rides over the block's step. NO LAW ON A BLOCK IS LEFT AMONG THEM.
What is not claimed. Any of the eight. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.K13.Law.FillM3Paid
import Johnson.Desc.K13.Law.RidersWeights

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open OnBytes OnBytes.Model OnBytes.Slice OnBytes.Maker
open Johnson.Pack (sigOf)
open VerifiableInference.Desc.First (S Pub Meaning Numbers)
open VerifiableInference.Desc.Sound (MsgT Sending Mem)

/-- **`FillM3`, with every law on a block called by name.** -/
theorem fillM3_paidW {Pp Cl Xi Cells Tok : Type} {nR : ℕ} {P : Where} {N : Numbers}
    {Mg : Meaning Pp (Desc.Wit Cells Tok MsgT)} {cs : Codes} {sh : Params.ReqShape}
    {ly : Params.ReqLayout} {rest : Pp × S → Bool} {arr : ℕ → ℕ → ℕ}
    {mat : Cells → Fin nR → (Fin P.lin.kCol → Bool) → GE} {G : FileDescription Xi}
    {smp : Pp × S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp}
    {ms : List Mem} {decT : (ℕ → Option (ℕ × List UInt64)) → Pp × S → Option Cells}
    {M : List OracleShape} {L : K12.Door.Laid} (Q : List Pub)
    (hF : FillsK13 P N Mg cs sh ly rest arr mat G smp ms decT M L)
    (hW : ∀ x, Mg.pub weightsItem x = First.weightsB x.2) (hWP : ∀ x, Mg.pubP weightsItem x)
    (hPl : PlanM3 L M ms cs N)
    (hIn : bookItem ∈ Q ∧ seatsItem ∈ Q ∧ shapesItem ∈ Q)
    (hQ : ∀ q ∈ Q, q ∈ knownK13 ∨ q = weightsItem)
    (hsmp : SmpReads smp) (hdec : DecBlind decT)
    (hrest : ∀ x x', StepM3 Cl P x x' → rest x = true → rest x' = true) :
    FillM3 Cl P N Mg (rwBook arr mat) Q :=
  fillM3_paid Q hF hW hWP hPl hIn hQ weightsKeeps hsmp hdec hrest

end VerifiableInference.Desc.K13.Law
