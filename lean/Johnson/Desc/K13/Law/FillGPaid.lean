-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Law/FillGPaid.lean: WHAT THE TIE AT THE FIRST SEGMENT's OPENING ASKS OF THE TABLE's
LETTERS (`FillG`, Johnson/Desc/K13/Law/AtTableFirst.lean), WITH EVERY RIDER CALLED BY NAME.
What comes at the opening is a letter mk, as in `fillG_at`. A statement with its
proof: a call alone.
  `fillG_paid`: **`FillG` at the list mk of items that come**: `fillG_at` (FillGAt.lean) at
  `mgK13_of_fills`, at the four equations on the list of rounds' side out of ONE Lean structure with
  code (`PlanGSeats`, PlanTestsM4.lean), and with its premise on the foreign riders paid by
  `ridersG_paid` (RidersGPaid.lean). WHAT IS LEFT: what the letters of Mg say (`FillsK13`, `MgG`, Mg
  at "unheard", "K13.weightsOk", "K12.bookFits") · tests with code (`PlanG`, `PlanGSeats`, the
  joined sub-protocol's `planOk`, first tree 0) · which items are in Q · `DecBlind decT` · what
  other layers say of "in order" rides · hconstr: the constraints' sentence goes back over the
  opening (another layer's sentence: owed) · hmore: the making of whatever comes beyond `madeSix`
  (other layers' items: owed) · hfB (proved: `bookFitsB_iff`, Johnson/Desc/Sound/BookTestsLaw.lean).
What is not claimed. The premises. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.K13.Law.RidersGPaid
import Johnson.Desc.K13.Law.PlanTestsM4
import Johnson.Desc.K13.Law.MgK13OfFills

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open OnBytes OnBytes.Params OnBytes.Model OnBytes.Slice OnBytes.Maker
open Desc.Plain
open Johnson.Pack (sigOf)
open Johnson.Desc.First.Walk (LayPar)
open VerifiableInference.Desc.First (S Pub Meaning Numbers unheardB)
open VerifiableInference.Desc.Sound (MsgT Sending Mem Frame bookStepB)
open VerifiableInference.Desc.K12.Door (toTree)
open VerifiableInference.Desc.Book (BookFits)
open VerifiableInference.Desc.First.Look (K3Data)

/-- **`FillG`, with every rider called by name.** -/
theorem fillG_paid {Pp Cl Xi Cells Tok : Type} {nR : ℕ} {P : Where} {N : Numbers}
    {Mg : Meaning Pp (Desc.Wit Cells Tok MsgT)} {cs : Codes} {sh : Params.ReqShape}
    {ly : Params.ReqLayout} {rest : Pp × S → Bool} {arr : ℕ → ℕ → ℕ}
    {mat : Cells → Fin nR → (Fin P.lin.kCol → Bool) → GE} {G : FileDescription Xi}
    {smp : Pp × S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp}
    {ms : List Mem} {decT : (ℕ → Option (ℕ × List UInt64)) → Pp × S → Option Cells}
    {M : List OracleShape} {L : K12.Door.Laid} {q : Params.First} {gp : GPar} {nm : String}
    {X : LayPar} {fvs : List Bool} {kCol : ℕ} {nsOf : ℕ → Option ℕ} {d : K3Data} {dg : Bool}
    (Q : List Pub) (p : Option Place) (mk : List Pub)
    (hF : FillsK13 P N Mg cs sh ly rest arr mat G smp ms decT M L) (hG : MgG N Mg nsOf d dg)
    (hU : ∀ x, Mg.pub .unheard x = unheardB x.2) (hUP : ∀ x, Mg.pubP .unheard x)
    (hPl : PlanG X nsOf d dg sh ly) (hm : Pub.noneSent ∈ Q)
    (hplan : (K1.openingZero q gp nm X fvs kCol : Block S Cl).planOk = true)
    (hS : PlanGSeats L M N p (K1.firstPar q gp))
    (hft : (K1.firstPar q gp).gp.firstTree = 0)
    (hdec : DecBlind decT)
    (hrest : ∀ x x', StepG Cl q gp nm X fvs kCol x x' → rest x = true → rest x' = true)
    (hconstr : ∀ x x' y y' w m c, StepG Cl q gp nm X fvs kCol x x' →
      (∀ q' ∈ Q, Mg.pub q' x = true) → First.bookAt N p x.2 = true → y'.cell = y.cell →
      Mg.constr m c x' y' w → Mg.constr m c x y w)
    (hmore : ∀ x x' i, StepG Cl q gp nm X fvs kCol x x' → (∀ q' ∈ Q, Mg.pub q' x = true) →
      First.bookAt N p x.2 = true → Mg.inOrder x = true → i ∈ mk → i ∉ madeSix →
      Mg.pub i x' = true ∧ Mg.pubP i x')
    (hW : ∀ x, Mg.pub weightsItem x = First.weightsB x.2) (hWP : ∀ x, Mg.pubP weightsItem x)
    (hB : ∀ x, Mg.pub bookFitsItem x = Sound.bookFitsB x.2.book)
    (hBP : ∀ x, Mg.pubP bookFitsItem x) (hfB : ∀ B, Sound.bookFitsB B = true ↔ BookFits B)
    (hQ : ∀ i ∈ Q, i = .noneSent ∨ i ∈ knownG ∨ i = weightsItem ∨ i = pileWithinItem ∨
      i = oneRowItem ∨ i = bookFitsItem) :
    FillG Cl q gp nm X fvs kCol N Mg Q p mk :=
  fillG_at Q p mk (mgK13_of_fills hF) hG hU hUP hPl hm hplan hS.hidx hft hS.hp hS.hs hS.hx hdec
    hrest hconstr hmore
    (ridersG_paid hm hG.noneSent hW hWP hB hBP hfB hF.within (hF.quiet _ (by simp [quietK13]))
      hF.oneRow (hF.quiet _ (by simp [quietK13])) hQ)

end VerifiableInference.Desc.K13.Law
