-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/MarksData.lean: CONDITIONAL: on the library's head on the
public input (`P5J.AtMgA`), or, in the forms without it, on what stands in its stead (two structures
of facts on public numbers; the goals' scope, the files read and an opening of the description): AT
THE OWN ROUNDS OF AN ATTENTION SEGMENT: (i) WHATEVER DATA FIT THE MEMBER's DECLARED ROUNDS BEAR, AT
EACH ROUND THAT THE FIRST MARK LISTS, THE ENTRY OF A MASKED SUMCHECK's ROUND AND A KIND THAT IS
NEITHER THAT OF SEEDS NOR THE SEALED ONE; (ii) NO OTHER MEMBER OF THE FIRST CHAIN HAS THAT MEMBER's
PLACE. Lemmas on data and on places. NO BOUND FOR A MARK IS SHOWN HERE.

What it is for. The frame's law on the first chain asks an owner's bound for a mark (`MarkDebt`,
Johnson/Desc/ProofFile/Honest/Law/CoverJoin.lean) at every list of data dsb with
`List.Forall₂ KindFits dsb b.rounds` (`KindFits`, Johnson/Desc/ProofFile/Honest/Law/Due.lean), b the
member of the chain at the mark's place (`FirstAsks`, its field hM,
Johnson/Desc/ProofFile/Honest/Law/CoverAsks.lean). A count over the listed rounds takes the data's
entries and kinds there as a premise. (i) makes that premise from the frame's; (ii) says which
member b is.

Main names:
  `reads_data`: (i) at the kind's own declared rounds. Conditional: two structures of facts on
    public numbers; the fit.
  `reads_data_head`: **(i) under the head, at the member at number 14 (2 g + 1) + 4.**
  `own_member_only`: **(ii)**, in the letters of an opening. `own_member_only_head`: under the head.
  `k5Marks_member_is`: (ii) in the form that a caller of the frame's law holds: a member of the
    chain whose place is that of a mark of the list `k5Marks` (MarksList.lean one folder up): which
    member it is, and which mark. `k5Marks_member_is_head`: under the head, with the plan at the
    look-up that `reads_data_head` takes.

How. `rounds_at_head` (MarksOwn.lean in this folder); `public_at_head`
(Johnson/Desc/K5/Honest/Law/PublicAtHead.lean); `read_round_plan` (ReadEntries.lean there): the
declared round at a listed number, as a term; `read_kind` (MarkForm.lean there); `K5Law.forall₂_at`
(Johnson/Desc/First/Att/Claims/KeysTabs.lean): two lists related member by member are related at
each number. For (ii): `LPFK9.places_nodup` (Johnson/LPFK9R/ToldInScope.lean): in scope no place
stands twice in the first chain's flat list; and `IM.k5_of`, `IM.hear_at_flat`, `IM.flatIx_scope`,
`IM.alone_place` (Johnson/IMR/). Kin of the first step in the frame: `kindFits_get`
(Johnson/Desc/ProofFile/Honest/Law/CoverFitAt.lean), in another form, over more files.

Limits. That any list of data fits the declared rounds is not shown here: the frame has it where a
description's data are made (`kinds_of_data`, Johnson/Desc/ProofFile/Honest/Law/DataKinds.lean) and
cuts it to one member (`kindFits_at`, CoverFitAt.lean); these are not called here. The first mark's
rounds alone: of the second mark's nothing is said. No measure, no number. At the function
`OnBytes.secondHashFunction`; under the head at the library's full size alone. h (`P5J.AtMgA`,
Johnson/P5J/MgAtAll.lean) is a hypothesis of every statement that names it. It can be met: at the
goals' two named sets of full-size public files, as Lean's written copies spell them, the head has a
member with no premise (the side library's `AtFullSide.Top.headMember_zFull`; at the second set
`AtFullSide.Top.headMember_zGap`, and at either set `AtFullSide.Top.headMember_named`
(AtFullSide/Top/HeadMemberAtGap.lean)). Of the files on this kind's honest side only those under
AtFullSide/K5/ call these; this one does not. At other public files in scope the library's
`P5J.head_exists_at_name` gives a member under premises on the files, of which the fourth follows
from the third (`P5J.owed_of_live`).
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.MarksOwn
import Johnson.Desc.ProofFile.Honest.K5.Law.MarksListLaw
import Johnson.Desc.ProofFile.Honest.Law.Due
import Johnson.LPFK9R.ToldInScope
import Johnson.Desc.First.Att.Claims.KeysTabs
import Johnson.IMR.K5Seat
import Johnson.IMR.FlatScope

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K5
open OnBytes OnBytes.Model OnBytes.Maker
open VerifiableInference.Desc VerifiableInference.Desc.First
open H2K5.Honest (readRounds read_round_plan read_kind public_at_head)
open P5J (AtMgA TS)

/-- **The data at the rounds that the first mark lists, at the kind's own declared rounds.** S': the
segment's shape: the kind's parameters p hold none; it feeds the numbers as the claims read them and
the two structures. Conditional: H, Pl: two structures of facts on public numbers; hk: the data fit
the declared rounds. -/
theorem reads_data (p : Att.P.Par) (S' : OnBytes.Attention.Shape)
    (H : H2K5.Honest.Sized ⟨S', p.own⟩) (Pl : H2K5.Honest.Planned ⟨S', p.own⟩) {dsb : List RDT}
    (hk : List.Forall₂ KindFits dsb (Att.P.rounds p)) :
    ∀ i d, dsb[i]? = some d → i ∈ readRounds p.own (H2K5.Honest.Pub5.g ⟨S', p.own⟩) →
      d.entry = { Part.MaskedSum.entry "PSC round" 3 1 0 with work := p.work } ∧ d.kind ≠ .seeds ∧
        d.kind ≠ .sealed := by
  intro i d hi hL
  obtain ⟨e1, e2⟩ := K5Law.forall₂_at hk hi (read_round_plan p S' H Pl i hL)
  have e3 : Fmt.kindOf "PSC round" = some d.kind := e2
  rw [read_kind] at e3
  obtain e4 : Fmt.Kind.elems = d.kind := Option.some.inj e3
  refine ⟨e1, ?_, ?_⟩
  · rw [← e4]
    exact fun c => nomatch c
  · rw [← e4]
    exact fun c => nomatch c

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : Look.Place}

/-- **THE SAME UNDER THE HEAD, AT THE MEMBER.** Conditional: h: the head; hg; ea: the group's plan;
f4: which member; hk: the data fit its declared rounds. -/
theorem reads_data_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {g : ℕ} (hg : g < 12)
    {a : Attention.Plan} (ea : (P5J.At.X Zp).A[g]? = some a) {b4 : Block S ProofFile.Cl}
    (f4 : cF.blocksInOrder[14 * (2 * g + 1) + 4]? = some b4) {dsb : List RDT}
    (hk : List.Forall₂ KindFits dsb b4.rounds) :
    ∀ i d, dsb[i]? = some d → i ∈ readRounds a.own (Att.P.parCOf a).geo →
      d.entry = { Part.MaskedSum.entry "PSC round" 3 1 0 with work := (parAt Zp g a).work } ∧
        d.kind ≠ .seeds ∧ d.kind ≠ .sealed := by
  have Pu := public_at_head h hg ea
  rw [rounds_at_head h hg ea f4] at hk
  exact reads_data (parAt Zp g a) a.S Pu.sized Pu.planned hk

end

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)} {c : Chain S ProofFile.Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **A member of the first chain at the place of an attention segment's own rounds is the member at
number 14 (2 g + 1) + 4.** Conditional: the scope; the files read; an opening; hg; hb; hp. -/
theorem own_member_only (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {g : ℕ} (hg : g < 12)
    {b : Block S ProofFile.Cl} (hb : b ∈ c.blocksInOrder) (hp : b.place = ⟨1, some (2 * g + 1), 3, .K5⟩) :
    c.blocksInOrder[14 * (2 * g + 1) + 4]? = some b := by
  obtain ⟨Lk, b₀, b', a', e1, e2, _, hla, _⟩ := IM.k5_of hS hR O g hg
  have hfl := IM.hear_at_flat e1 e2
  rw [IM.flatIx_scope hS hR O (l := 2 * g + 1) (by omega) 2,
    show 14 * (2 * g + 1) + 2 + 2 = 14 * (2 * g + 1) + 4 by omega] at hfl
  have hp₀ : b₀.place = ⟨1, some (2 * g + 1), 3, .K5⟩ := IM.alone_place hla
  have hn : (c.blocksInOrder.map (·.place)).Nodup := LPFK9.places_nodup hS hR O
  obtain rfl : b₀ = b :=
    List.inj_on_of_nodup_map hn (List.mem_of_getElem? hfl) hb (hp₀.trans hp.symm)
  exact hfl

/-- **A MEMBER OF THE FIRST CHAIN AT THE PLACE OF A MARK OF THE LIST: WHICH MEMBER IT IS, AND WHICH
MARK.** There is a group g below 12 with a plan a such that b is the member at number
14 (2 g + 1) + 4 and mk is one of the two marks at 2 g + 1 and a. Conditional: the scope; the files
read; an opening; hm; hb; hp: the two places are one. -/
theorem k5Marks_member_is (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {mk : Mark}
    (hm : mk ∈ k5Marks Z Bs.G₀) {b : Block S ProofFile.Cl} (hb : b ∈ c.blocksInOrder)
    (hp : mk.place = b.place) :
    ∃ g < 12, ∃ a, Bs.G₀.W.A[g]? = some a ∧ c.blocksInOrder[14 * (2 * g + 1) + 4]? = some b ∧
      (mk = mkReads (2 * g + 1) a.own (Att.P.parCOf a).geo ∨ mk = mkLive (2 * g + 1) a.own) := by
  obtain ⟨y, hy, a, ha, hk⟩ := mem_k5Marks.1 hm
  rw [H2K5.Row.k5Places_scope hS hR O.pub O.blank] at hy
  obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hy
  have hg' : g < 12 := List.mem_range.1 hg
  have hq : b.place = ⟨1, some (2 * g + 1), 3, .K5⟩ := by
    rw [← hp]
    rcases hk with rfl | rfl <;> rfl
  exact ⟨g, hg', a, ha, own_member_only hS hR O hg' hb hq, hk⟩

end

/-- The same under the head. Conditional: h: the head; hg; hb; hp. -/
theorem own_member_only_head {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
    {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : Look.Place}
    (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {g : ℕ} (hg : g < 12) {b : Block S ProofFile.Cl}
    (hb : b ∈ cF.blocksInOrder) (hp : b.place = ⟨1, some (2 * g + 1), 3, .K5⟩) :
    cF.blocksInOrder[14 * (2 * g + 1) + 4]? = some b := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  exact own_member_only h.scope h.reads O hg hb hp

/-- **`k5Marks_member_is` under the head**, with the plan at the look-up that `reads_data_head` and
the laws on the two marks take. Conditional: h: the head; hB: the base's return; hm; hb; hp. -/
theorem k5Marks_member_is_head {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
    {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : Look.Place}
    (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bs : ProofFile.PureBase}
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs) {mk : Mark}
    (hm : mk ∈ k5Marks Zp Bs.G₀) {b : Block S ProofFile.Cl} (hb : b ∈ cF.blocksInOrder)
    (hp : mk.place = b.place) :
    ∃ g < 12, ∃ a, (P5J.At.X Zp).A[g]? = some a ∧ cF.blocksInOrder[14 * (2 * g + 1) + 4]? = some b ∧
      (mk = mkReads (2 * g + 1) a.own (Att.P.parCOf a).geo ∨ mk = mkLive (2 * g + 1) a.own) := by
  obtain ⟨Bs', base, O⟩ := h.laid.opened
  obtain rfl : Bs' = Bs := Except.ok.inj (O.made.symm.trans hB)
  obtain ⟨g, hg, a, ea, hf, hk⟩ := k5Marks_member_is h.scope h.reads O hm hb hp
  rw [O.W] at ea
  exact ⟨g, hg, a, ea, hf, hk⟩

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.reads_data
#print axioms ProofFile.Honest.K5.reads_data_head
#print axioms ProofFile.Honest.K5.own_member_only
#print axioms ProofFile.Honest.K5.k5Marks_member_is
#print axioms ProofFile.Honest.K5.own_member_only_head
#print axioms ProofFile.Honest.K5.k5Marks_member_is_head
