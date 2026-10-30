-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Law/FillM4Paid5.lean: `fillM4_paid4` (Johnson/Desc/K13/Law/FillM4Paid4.lean) WITH
ITS ONE OWED PREMISE CALLED BY NAME: over a yes of W's commitment "K13.pileWithin" goes on:
`withinM4` (WithinM4.lean) at `ledgersC` and `ledgersKept` (LedgersC.lean,
LedgersKept.lean). A statement with its proof: a call alone.
  `withinM4_paid`: `OwedWithinM4`, with no premise.
  `fillM4_paid5`: **`FillM4` at any list Q of riders** as in `fillM4_paid4`: NO LAW ON A BLOCK IS
  LEFT AMONG ITS PREMISES: what the letters of Mg say (`FillsK13`; Mg at "K13.weightsOk") · tests on
  the plan (`PlanM3`, `PlanM4`, the joined block's `planOk`) · which items are in Q · `SmpOld N p ms
  smp` · `DecBlind decT` · what other layers say of "in order" rides (its payer: `rest_M4`,
  RestAtM4.lean [not in this library]).
What is not claimed. The premises. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.K13.Law.FillM4Paid4
import Johnson.Desc.K13.Law.WithinM4
import Johnson.Desc.K13.Law.LedgersC
import Johnson.Desc.K13.Law.LedgersKept

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open OnBytes OnBytes.Model OnBytes.Slice OnBytes.Maker
open Johnson.Pack (sigOf)
open VerifiableInference.Desc.First (S Pub Meaning Numbers)
open VerifiableInference.Desc.Sound (MsgT Sending Mem Frame)

/-- Over a yes of W's commitment "K13.pileWithin" goes on. -/
theorem withinM4_paid : OwedWithinM4 := withinM4 ledgersC ledgersKept

/-- **`FillM4`, with every law on a block called by name.** -/
theorem fillM4_paid5 {Pp Cl Xi Cells Tok : Type} {nR : ℕ} {F : Frame} (y₀ : F.E.Str) {P : Where}
    {P' : K1.Par} {N : Numbers} {Mg : Meaning Pp (Desc.Wit Cells Tok MsgT)}
    {sh : Params.ReqShape} {ly : Params.ReqLayout} {rest : Pp × S → Bool} {arr : ℕ → ℕ → ℕ}
    {mat : Cells → Fin nR → (Fin P.lin.kCol → Bool) → GE} {G : FileDescription Xi}
    {smp : Pp × S → (s : Sending) → (i : Fin s.l.length) →
      Option ((sigOf P'.codes s.l).om i).Smp}
    {ms : List Mem} {decT : (ℕ → Option (ℕ × List UInt64)) → Pp × S → Option Cells}
    {M : List OracleShape} {L : K12.Door.Laid} (Q : List Pub) (p : Option Place)
    (hF : FillsK13 P N Mg P'.codes sh ly rest arr mat G smp ms decT M L)
    (hW : ∀ x, Mg.pub weightsItem x = First.weightsB x.2) (hWP : ∀ x, Mg.pubP weightsItem x)
    (hPl : PlanM3 L M ms P'.codes N) (h4 : PlanM4 0 L M N p P')
    (hplan : (atM4 (Cl := Cl) P (K1.sendAtS P')).planOk = true)
    (hQ : ∀ q ∈ Q, q ∈ knownK13 ∨ q = .frontOk ∨ q = weightsItem ∨ q = pileWithinItem ∨
      q = oneRowItem)
    (hIn : ∀ q ∈ knownK13, q ∈ Q) (hsmp : SmpOld N p ms smp) (hdec : DecBlind decT)
    (hrest : ∀ x x', StepM4 Cl P P' x x' → rest x = true → rest x' = true) :
    FillM4 Cl P P' N Mg Q p :=
  fillM4_paid4 y₀ Q p hF hW hWP hPl h4 hplan hQ hIn withinM4_paid hsmp hdec hrest

end VerifiableInference.Desc.K13.Law

#print axioms VerifiableInference.Desc.K13.Law.withinM4_paid
#print axioms VerifiableInference.Desc.K13.Law.fillM4_paid5
