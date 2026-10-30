-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/LPFK9R/SortRunAtMg.lean: THE FIELD hAt OF WHAT IS LEFT OF A LINK's LAW (`CoreRest2`,
Johnson/Desc/First/Link/Law/LinkRestAtSort2.lean; `CoreLeft`): "the run run stands at
the entry o of the link's order", AT THE CHOSEN o (the smallness test's equations: (4,
"K8.equations"); at the head's link (5, "K8.equations")): THERE IS SUCH A RUN, AT THE SEAT AND AT
THE CLOSED CONSTANT. Theorems: calls.

Why. The ties (K8Ties.lean) say of EVERY run that stands at that entry that it stands under the
smallness test's run; they do not say that one stands there. The letter run of the list stands
under "there are": so the field is met by an existence.

By: chain_hear_alone (Johnson/IMR/LaidFirst.lean: the hearing block at
that number is a lot's block, alone) · lot_of_kind · k8_member (K8Ties.lean: that lot's blocks are
the kind's whole block) · claims_lookup (Johnson/IMR/SeatForm.lean: what is looked up in the seated
block is the guard around what is looked up in the lot's) · k8_equations_under (the whole block
states a run of that name).

What is said.
  `k8_at_seat`: at a seated link, at the number i of a hearing block of the kind K8: there are the
    link and a run with At Lk (i, "K8.equations") run.
  `hAt_layers_mg`, `hAt_att_mg`, `hAt_head_mg`: **the field, at the link that the constant's data
    name**: ∃ run, At L (4, "K8.equations") run (at the head's link: 5).

PREMISES at the constant: h : AtMgA OnBytes.secondHashFunction .. · O : IM.Open .. (AtMg's own field gives it)
· m < 25 · the sort · h.𝔇.lk m = some L.

Limits. WHICH run is not named beyond its being the guard around the lot's. secondHashFunction alone at the
constant. Nothing on any state. Nothing on soundness.

-/
import Johnson.LPFK9R.SortTiesAtMg

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace LPFK9
open VerifiableInference.Desc (Block Chain Link Place KindName FileDescription)
open VerifiableInference.Desc.First (S ModelPart kindsBeforeBatching)
open VerifiableInference.Desc.LinkJoin (At)
open VerifiableInference.Desc.K9L (k8_equations_under)
open OnBytes.Maker (WholeD)
open ProofFile (Cl)
open IM (Open subAt)
open P5J (AtMgA)

/-- **A RUN STANDS AT THE SMALLNESS TEST's ENTRY, AT THE SEAT.** -/
theorem k8_at_seat {o : ProofFile.SecondHashFunctionArgument} {Z : ProofFile.Pub} {B : ProofFile.PureBase}
    {base : List (Block S Cl)} {c : Chain S Cl}
    (hB : ProofFile.baseOf Z (ProofFile.pureSeat o Z) = .ok B)
    (hb : (ProofFile.partsAt (ProofFile.pureSeat o Z) B).base = .ok base)
    (hc : ProofFile.chainBy Z base (ProofFile.partsAt (ProofFile.pureSeat o Z) B).frames
      (ProofFile.partsAt (ProofFile.pureSeat o Z) B).road = .ok c) (l : ℕ) (sub : ModelPart)
    (hl : (ProofFile.subsOf Z)[l]? = some sub) (i : ℕ)
    (hk : (kindsBeforeBatching sub (l == 0))[i]? = some KindName.K8) (hi : 2 ≤ i + 1 ∧ i + 1 ≤ 9) :
    ∃ Lk, c.links[l]? = some Lk ∧ ∃ run, At Lk (i, "K8.equations") run := by
  obtain ⟨Lk, b, e1, e2, sp, _, L, hL, b', hb', _, ep, ha⟩ :=
    IM.chain_hear_alone hB hb hc l sub hl i .K8 hk (by decide) (by decide) hi
  obtain rfl : L = ProofFile.P1K8.lot Z := IM.lot_of_kind hL hb' (by rw [ep]; rfl)
  obtain ⟨X, l', _, rfl⟩ := k8_member hb'
  obtain ⟨r, h2, _⟩ := k8_equations_under (ProofFile.k8ParW Z B.G₀ X l')
  refine ⟨Lk, e1, IM.guardRun ProofFile.sameReply r, ?_⟩
  show ((Lk.hear[i]?).bind fun x => x.claims.lookup "K8.equations") = some _
  rw [e2]
  show b.claims.lookup "K8.equations" = some _
  rw [IM.claims_lookup ha, h2]
  rfl

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S Cl} {x : VerifiableInference.Desc.First.Look.Place} {F : FileDescription ProofFile.Inst}
  {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {A₂ : ProofFile.SharedSeat} {B₂ : ProofFile.SecondSeat}

/-- **hAt AT A LAYERS' LINK OF THE CONSTANT.** -/
theorem hAt_layers_mg (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL F Zp Bs base cF A₂ B₂) (m : ℕ) (hm : m < 25)
    (hs : subAt m = .layers) (L : Link S Cl) (hlk : h.𝔇.lk m = some L) :
    ∃ run, At L (4, "K8.equations") run := by
  have hl := IM.subs_scope h.toAtMg.scope h.toAtMg.reads O m hm
  rw [hs] at hl
  obtain ⟨Lk, e, run, hr⟩ := k8_at_seat O.made O.places O.chain m .layers hl 4
    (kinds_at (m == 0)).2.1 (by omega)
  obtain rfl : Lk = L := Option.some.inj (e.symm.trans (link_of_lk h O m L hlk))
  exact ⟨run, hr⟩

/-- **hAt AT AN ATTENTION LINK OF THE CONSTANT.** -/
theorem hAt_att_mg (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL F Zp Bs base cF A₂ B₂) (m : ℕ) (hm : m < 25)
    (hs : subAt m = .attention) (L : Link S Cl) (hlk : h.𝔇.lk m = some L) :
    ∃ run, At L (4, "K8.equations") run := by
  have hl := IM.subs_scope h.toAtMg.scope h.toAtMg.reads O m hm
  rw [hs] at hl
  obtain ⟨Lk, e, run, hr⟩ := k8_at_seat O.made O.places O.chain m .attention hl 4
    (kinds_at (m == 0)).2.2.2.1 (by omega)
  obtain rfl : Lk = L := Option.some.inj (e.symm.trans (link_of_lk h O m L hlk))
  exact ⟨run, hr⟩

/-- **hAt AT THE HEAD's LINK OF THE CONSTANT.** -/
theorem hAt_head_mg (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL F Zp Bs base cF A₂ B₂) (m : ℕ) (hm : m < 25)
    (hs : subAt m = .head) (L : Link S Cl) (hlk : h.𝔇.lk m = some L) :
    ∃ run, At L (5, "K8.equations") run := by
  have hl := IM.subs_scope h.toAtMg.scope h.toAtMg.reads O m hm
  rw [hs] at hl
  obtain ⟨Lk, e, run, hr⟩ := k8_at_seat O.made O.places O.chain m .head hl 5
    (kinds_at (m == 0)).2.2.2.2.2.1 (by omega)
  obtain rfl : Lk = L := Option.some.inj (e.symm.trans (link_of_lk h O m L hlk))
  exact ⟨run, hr⟩

end LPFK9

#print axioms LPFK9.k8_at_seat
#print axioms LPFK9.hAt_layers_mg
#print axioms LPFK9.hAt_att_mg
#print axioms LPFK9.hAt_head_mg
