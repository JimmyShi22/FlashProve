-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Shape/LinkGuardHead.lean: THE CODE SWITCH AT THE FIRST PLACE OF LINKS 1 TO 23: THE
TABLE's OWN GUARD (linkGd, SwitchReturns.lean) ACCEPTS AT EVERY STATE THAT IS REACHED THERE, WHOEVER
PLAYS, UNDER THE HEAD P5J.AtMgA ALONE. LinkGuardWhole.lean has it at an opening O and where the
plan's numbers at the place return (hP, hn): here these three are paid. A joining of laws.

  **linkGd_at_base**: IN THE LETTERS OF switch_link_returns (SwitchReturns.lean): at the Bs that the
    maker's own ProofFile.baseOf returns at the public part, and at whatever prepOf and numsAt return
    there: the opening is the head's (h.laid.opened), and its base is that Bs (O.made). It holds at
    every place a and name nm: switch_link_returns has the member at l := m + 1 under a := { chain
    := 1, link := some l, piece := 1, kind := .K2 } and nm := "", at the n that numsAt returns:
    since prepOf and numsAt are functions, that n is this.
  **linkGd_under_head**: there are such Bs, Pp, n (t3_nums_link, Johnson/P1K2R/TieThreeConst.lean),
    and the guard accepts at them.

Limits. LinkGuardWhole.lean's, but for O, hP, hn. "Reached" is over the list of the wrapped
sub-protocols. The links' places alone. THE GUARD ALONE: what the guarded step does behind it, and
the cells' test on values, are LinkGuardCell.lean's. The full size alone. Of a reached state: that
anything is reached is not said. That the head has a member is shown in scope, where the reader
returns and `protocolDataWellFormed` accepts (`head_of_live`, Johnson/P5J/HeadOfLive.lean); that these three hold
together, at two named sets of public files, in a side library. At the format's second hash
function. Nothing on soundness, completeness or hiding.
-/
import Johnson.AtFull.Shape.LinkGuardWhole
import Johnson.P1K2R.TieThreeConst

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Johnson.AtFull.Shape
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Chain Place)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Shape
open VerifiableInference.Desc.Sound (below)
open Johnson.Desc.First.Walk.Tied (Reach)
open P1K2 (Prep Nums numsAt prepOf)
open IM (k2P)
open OnBytes.Maker (WholeD)
open P5J (AtMgA)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r₀ : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place} {Bs : ProofFile.PureBase}
  {z : ProofFile.InstPub}

/-- **In the table's own letters.** -/
theorem linkGd_at_base (h : AtMgA OnBytes.secondHashFunction Z D r₀ Zp Np cF x)
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs)
    {m : Nat} (h23 : m < 23) {Pp : Prep} {n : Nums} (hP : prepOf Zp Bs.G₀ = some Pp)
    (hn : numsAt Pp (some (m + 1)) = some n) {s : S}
    (hr : Reach 0 (cF.blocksInOrder.map below) (ProofFile.startS Zp) (14 * (m + 1) + 2) (z, s))
    (a : Place) (nm : String) :
    linkGd (k2P Zp a nm .link n) (chainF s) = true := by
  obtain ⟨Bs', base, O⟩ := h.laid.opened
  obtain rfl : Bs' = Bs := Except.ok.inj (O.made.symm.trans hB)
  exact linkGd_reached_whole h O h23 hP hn hr a nm

/-- **Under the head alone.** -/
theorem linkGd_under_head (h : AtMgA OnBytes.secondHashFunction Z D r₀ Zp Np cF x)
    {m : Nat} (h23 : m < 23) {s : S}
    (hr : Reach 0 (cF.blocksInOrder.map below) (ProofFile.startS Zp) (14 * (m + 1) + 2) (z, s))
    (a : Place) (nm : String) :
    ∃ (Bs : ProofFile.PureBase) (Pp : Prep) (n : Nums),
      ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs ∧ prepOf Zp Bs.G₀ = some Pp ∧
      numsAt Pp (some (m + 1)) = some n ∧ linkGd (k2P Zp a nm .link n) (chainF s) = true := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨Pp, n, hP, hn⟩ := VerifiableInference.Desc.First.K2Caller.t3_nums_link h.scope h.reads O
    h.laid.planOk (l := m + 1) (by omega) (by omega)
  exact ⟨Bs, Pp, n, O.made, hP, hn, linkGd_reached_whole h O h23 hP hn hr a nm⟩

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.linkGd_at_base
#print axioms Johnson.AtFull.Shape.linkGd_under_head
