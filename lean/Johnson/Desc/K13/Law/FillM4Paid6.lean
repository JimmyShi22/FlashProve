-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Law/FillM4Paid6.lean: THE CALL AT W's COMMITMENT, AT A DOOR THAT HAS
"K12.bookFits" TOO. A statement with its proof: calls alone. It stands apart from the first
segment's opening's files.
  `fillM4_paid6`: **`FillM4` at any list Q of riders** that holds the four of `knownK13`, and beside
  them at most `frontOk`, "K13.weightsOk", "K13.pileWithin", "K13.oneRow", "K12.bookFits". NO LAW ON
  A SUB-PROTOCOL IS LEFT AMONG ITS PREMISES. New against `fillM4_paid5` (FillM4Paid5.lean):
  `rider4_fits` (BookFitsRides.lean) is called; two binders on what Mg says at the item; one binder
  hfB: the item's test says what the laws' word `BookFits` says: proved in another file
  (`bookFitsB_iff`, Johnson/Desc/Sound/BookTestsLaw.lean), which this file does not import.
What is not claimed. The premises. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.K13.Law.FillM4Paid5
import Johnson.Desc.K13.Law.RidersMore
import Johnson.Desc.K13.Law.BookFitsRides

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open OnBytes OnBytes.Params OnBytes.Model OnBytes.Slice OnBytes.Maker
open Desc.Plain
open Johnson.Pack (sigOf)
open Johnson.Desc.First.Walk (LayPar)
open VerifiableInference.Desc.First (S Pub Meaning Numbers)
open VerifiableInference.Desc.Sound (MsgT Sending Mem Frame bookStepB)
open VerifiableInference.Desc.K12.Door (toTree)
open VerifiableInference.Desc.Book (BookFits)

/-- **`FillM4` at a door that has "K12.bookFits" too.** -/
theorem fillM4_paid6 {Pp Cl Xi Cells Tok : Type} {nR : ℕ} {F : Frame} (y₀ : F.E.Str) {P : Where}
    {P' : K1.Par} {N : Numbers} {Mg : Meaning Pp (Desc.Wit Cells Tok MsgT)}
    {sh : Params.ReqShape} {ly : Params.ReqLayout} {rest : Pp × S → Bool} {arr : ℕ → ℕ → ℕ}
    {mat : Cells → Fin nR → (Fin P.lin.kCol → Bool) → GE} {G : FileDescription Xi}
    {smp : Pp × S → (s : Sending) → (i : Fin s.l.length) →
      Option ((sigOf P'.codes s.l).om i).Smp}
    {ms : List Mem} {decT : (ℕ → Option (ℕ × List UInt64)) → Pp × S → Option Cells}
    {M : List OracleShape} {L : K12.Door.Laid} (Q : List Pub) (p : Option Place)
    (hF : FillsK13 P N Mg P'.codes sh ly rest arr mat G smp ms decT M L)
    (hW : ∀ x, Mg.pub weightsItem x = First.weightsB x.2) (hWP : ∀ x, Mg.pubP weightsItem x)
    (hB : ∀ x, Mg.pub bookFitsItem x = Sound.bookFitsB x.2.book)
    (hBP : ∀ x, Mg.pubP bookFitsItem x) (hfB : ∀ B, Sound.bookFitsB B = true ↔ BookFits B)
    (hPl : PlanM3 L M ms P'.codes N) (h4 : PlanM4 0 L M N p P')
    (hplan : (atM4 (Cl := Cl) P (K1.sendAtS P')).planOk = true)
    (hQ : ∀ q ∈ Q, q ∈ knownK13 ∨ q = .frontOk ∨ q = weightsItem ∨ q = pileWithinItem ∨
      q = oneRowItem ∨ q = bookFitsItem)
    (hIn : ∀ q ∈ knownK13, q ∈ Q) (hsmp : SmpOld N p ms smp) (hdec : DecBlind decT)
    (hrest : ∀ x x', StepM4 Cl P P' x x' → rest x = true → rest x' = true) :
    FillM4 Cl P P' N Mg Q p := by
  have hMg := mgK13_of_fills hF
  have hBk : ∀ x, Mg.pub bookItem x = bookStepB P'.gp.firstTree x.2.book x.2.roots := fun x =>
    (hMg.book x).trans (congrArg (fun ft => bookStepB ft x.2.book x.2.roots) h4.hft)
  refine fillM4_of Q p hMg.ours
    (others4_at_sig P P' arr mat N Mg Q p P'.codes G smp ms decT L hMg.sig
      (hIn _ (by simp [knownK13])) (hIn _ (by simp [knownK13])) hMg.masks hMg.seats
      (fun x h => by rw [hMg.ours.indexThere] at h; exact h) (planK13_of hPl).below hsmp hdec)
    hrest hplan fun q hq => ?_
  rcases hQ q hq with hk | rfl | rfl | rfl | rfl | rfl
  · have hP := hMg.quiet q hk
    simp only [knownK13, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl
    · exact rider4_book hq hBk hP
    · exact rider4_seats (L := toTree L) hq hMg.seats hP h4.hp h4.hs
    · exact rider4_shapes hq hMg.shapes hP h4.hx
    · exact rider4_pileMasks hq hMg.masks hP
  · exact rider4_frontOk y₀ hMg.ours hq
  · exact rider4_kept hq weightsKeeps hW hWP
  · exact rider4_pileWithin withinM4_paid hq hF.within (hF.quiet _ (by simp [quietK13]))
  · exact rider4_oneRow hq hF.oneRow (hF.quiet _ (by simp [quietK13]))
  · exact rider4_fits Sound.bookFitsB hfB hq hB hBP

end VerifiableInference.Desc.K13.Law
