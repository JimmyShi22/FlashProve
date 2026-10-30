-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Law/FillM3Paid4.lean: WHAT KIND K13's TIE ASKS OF THE TABLE's LETTERS (`FillM3`),
AT THE FORM OF THE LAYER OF FillK13.lean WHOSE DOOR HAS TWO ITEMS MORE THAT RIDE PAST THE BLOCK
("K13.pileWithin", "K13.oneRow"). A statement with its proof: calls alone.
  `fillM3_paid4`: **`FillM3` at any list Q of riders** that holds the proximity test's three, and
  beside the four of `knownK13` at most "K13.weightsOk", "K13.pileWithin", "K13.oneRow". ITS
  PREMISES ARE `fillM3_paidW`'s (Johnson/Desc/K13/Law/FillM3PaidW.lean) AND ONE THAT IS OWED:
  `OwedWithinM3` (OwedWithin.lean). What Mg says at the two new items, and that `pubP` says nothing
  there, are fields of `FillsK13`.
What is not claimed. The premises. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.K13.Law.FillM3PaidW
import Johnson.Desc.K13.Law.PileWithin

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open OnBytes OnBytes.Model OnBytes.Slice OnBytes.Maker
open Johnson.Pack (sigOf)
open VerifiableInference.Desc.First (S Pub Meaning Numbers)
open VerifiableInference.Desc.Sound (MsgT Sending Mem)

/-- **`FillM3` at the door with the two items more ("K13.pileWithin", "K13.oneRow").** -/
theorem fillM3_paid4 {Pp Cl Xi Cells Tok : Type} {nR : ℕ} {P : Where} {N : Numbers}
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
    (hQ : ∀ q ∈ Q, q ∈ knownK13 ∨ q = weightsItem ∨ q = pileWithinItem ∨ q = oneRowItem)
    (hO : OwedWithinM3) (hsmp : SmpReads smp) (hdec : DecBlind decT)
    (hrest : ∀ x x', StepM3 Cl P x x' → rest x = true → rest x' = true) :
    FillM3 Cl P N Mg (rwBook arr mat) Q :=
  fillM3_at Q (mgK13_of_fills hF) (planK13_of hPl) hIn.1 hIn.2.1 hIn.2.2 seed3 pinsStay hsmp hdec
    hrest fun q hq hk => by
      rcases hQ q hq with h | rfl | rfl | rfl
      · exact absurd h hk
      · exact rider3_keeps weightsKeeps hW hWP
      · exact rider3_pileWithin hO hF.within (hF.quiet _ (by simp [quietK13]))
      · exact rider3_oneRow hF.oneRow (hF.quiet _ (by simp [quietK13]))

end VerifiableInference.Desc.K13.Law
