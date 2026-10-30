-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/K6BuiltAtConst.lean: THREE FACTS ON THE BUILT SEGMENT 24 OF THE PROOF FILE'S
DESCRIPTION'S OWN PLANNER, UNDER THE HEAD AtMg (Johnson/P5J/AtMg.lean), GENERAL IN THE
LETTER o FOR THE SECOND HASH FUNCTION: they are three fields of K6LeftMg (Law/K6DueSplit.lean) at
the closed term.

Main names (namespace VerifiableInference.Desc.Kinds.Head.Law.AtTable).
  built_plain: under AtMg the public part's built segments are buildLinksH's value at the
      description's own list of segments (ProofFile.Plain.linksPlain) and at the public part's own chains.
  built_24: so segment 24 is there, with the head's plan's ledger and number of slots.
  ns_at_const, trees_at_const: the fields ns and treesB.
  room_at_const: the field roomC.

How. madeOf_planned and pubBy_made
(Johnson/Desc/ProofFile/Law/MakerPublic.lean) give "the description's planner returns the public
part's record"; its text (Johnson/Desc/ProofFile/PlanPlain.lean) is opened by its own bind_ok;
Meaning.links_alternate (Johnson/Goal/Meaning/PlanShapes.lean), which is stated for every
caller of listLinksH and buildLinksH, gives segment 24. room_at_const follows
reads_room_of_public (Law/ReadsRoomInScope.lean) line by line at the description's list in the place
of the library's: its stones reads_named_of_built, public_third and public_array are called; that
theorem itself cannot be: it is stated at the library's builtOf.
Nearest relatives: Law/K6LooksInScope.lean [not in this library]
(built_head, looks_in_scope: the same two
facts at the LIBRARY'S planner, whose record parts from the description's in the digest and in the
field run).
What it does not say. Nothing on the other segments. Nothing on soundness.
-/
import Johnson.Desc.Kinds.Law.DAtConst
import Johnson.Desc.Kinds.Law.ReadsRoomInScope
import Johnson.Desc.ProofFile.Law.MakerPublic
import Johnson.Goal.Meaning.PlanShapes
import Johnson.Desc.First.SentTerms

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.Kinds.Head.Law.AtTable

open OnBytes OnBytes.Model
open OnBytes.Model.Stages (LinkH LinksH listLinksH buildLinksH)
open VerifiableInference.Desc.First.FillSent (treesAt looksOf)
open P5J (At.X At.layout)

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {Dw : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl}

/-- **The built segments are buildLinksH's value at the description's own list.** -/
theorem built_plain (h : P5J.AtMg o Z Dw r Zp Np cF) :
    ∃ l₀, ProofFile.Plain.linksPlain (At.X Zp) = .ok l₀ ∧
      buildLinksH l₀ (At.X Zp).NGr (At.X Zp).p4 (At.X Zp).layers.wsLay
        Zp.made.p.chains.proof.first = .ok Zp.made.p.built := by
  have hp : ProofFile.Plain.planned o Z.pol Z.KL (some Z.lay) = .ok Zp.made.p :=
    ProofFile.Law.madeOf_planned (ProofFile.Law.pubBy_made h.laid.pub)
  unfold ProofFile.Plain.planned at hp
  obtain ⟨X, _, hp⟩ := ProofFile.Law.bind_ok hp
  obtain ⟨c, _, hp⟩ := ProofFile.Law.bind_ok hp
  obtain ⟨b, hb, hp⟩ := ProofFile.Law.bind_ok hp
  have e := Except.ok.inj hp
  have eX : X = At.X Zp := congrArg Verify.Planned.X e
  have ec : c = Zp.made.p.chains := congrArg Verify.Planned.chains e
  have eb : b = Zp.made.p.built := congrArg Verify.Planned.built e
  subst eX
  subst ec
  subst eb
  unfold ProofFile.Plain.builtOf at hb
  obtain ⟨l₀, h0, hb⟩ := ProofFile.Law.bind_ok hb
  exact ⟨l₀, h0, hb⟩

/-- **Segment 24 is there, with the head's plan's ledger and number of slots.** -/
theorem built_24 (h : P5J.AtMg o Z Dw r Zp Np cF) :
    ∃ b, Zp.made.p.built.links[24]? = some b ∧ b.Fp = (At.X Zp).H.Fp ∧
      b.ns = (At.X Zp).H.ns := by
  obtain ⟨l₀, h0, hB⟩ := built_plain h
  obtain ⟨p4, ng, -⟩ := _root_.Meaning.scope_plans h.scope h.reads h.pubOne
  unfold ProofFile.Plain.linksPlain at h0
  rw [p4, ng] at h0 hB
  obtain ⟨-, -, l, h24, L⟩ := _root_.Meaning.links_alternate h0 hB h0
  unfold OnBytes.L5.LinksOrder.zipped at h24
  rw [Array.getElem?_zipWith] at h24
  cases hb : Zp.made.p.built.links[24]? with
  | none =>
    rw [hb] at h24
    cases h24
  | some b =>
    rw [hb] at h24
    cases hx : l₀[24]? with
    | none =>
      rw [hx] at h24
      cases h24
    | some y =>
      rw [hx] at h24
      obtain rfl := Option.some.inj h24
      exact ⟨b, rfl, L.Fp, L.ns⟩

variable {x : First.Look.Place}

/-- **The field ns at the closed term.** -/
theorem ns_at_const (h : P5J.AtMgA o Z Dw r Zp Np cF x) :
    (dAt h).pubD.nsOf 24 = some (At.X Zp).H.ns := by
  obtain ⟨b, hb, -, hn⟩ := built_24 h.toAtMg
  show (Zp.made.p.built.links[24]?).map (·.ns) = _
  rw [hb]
  show some b.ns = _
  rw [hn]

/-- **The field treesB at the closed term.** -/
theorem trees_at_const (h : P5J.AtMgA o Z Dw r Zp Np cF x) :
    treesAt (dAt h).built 24 = looksOf (At.X Zp).H.Fp := by
  obtain ⟨b, hb, hF, -⟩ := built_24 h.toAtMg
  show treesAt Zp.made.p.built.links 24 = _
  unfold treesAt
  rw [hb]
  show looksOf b.Fp = _
  rw [hF]

/-- **The field roomC at the closed term.** -/
theorem room_at_const (h : P5J.AtMgA o Z Dw r Zp Np cF x) :
    readsRoomC (At.X Zp) (At.layout Zp) ((dAt h).sent.arrayOf.getD 24 #[]) = true := by
  obtain ⟨l₀, hl, hb⟩ := built_plain h.toAtMg
  obtain ⟨p4, ng, -⟩ := _root_.Meaning.scope_plans h.scope h.reads h.pubOne
  unfold ProofFile.Plain.linksPlain at hl
  rw [p4] at hl
  obtain ⟨_, _, z, _, e⟩ := OnBytes.L5.LinksOrder.listLinksH_with _ _ _ _ _ hl
  have T : (At.X Zp).H.tl.ix.U.getD 2 none = some 0 := ReadsNamed.public_third h.pubOne
  obtain ⟨c1, tr, A, c2, c3, c4, c5⟩ := Built.reads_named_of_built hb z e (t := 0) T
  obtain ⟨p0, pK, pR, _⟩ := ReadsArray.public_array h.pubOne
  have c2' : (At.X Zp).H.Fp.trees[0]? = some tr := c2
  have etr : (At.X Zp).H.Fp.trees.getD 0 {} = tr := by
    rw [Array.getD_eq_getD_getElem?, c2']
    rfl
  rw [etr] at pK pR
  have e0 : readsOf (At.X Zp) = 0 := by
    unfold readsOf
    rw [T]
    rfl
  rw [ng] at c1 c3
  show readsRoomC (At.X Zp) Zp.made.p.chains.proof.first.layout
    ((Zp.made.p.built.links.map (·.arrayOf)).getD 24 #[]) = true
  unfold readsRoomC
  rw [e0, c1]
  show ((reqArray Zp.made.p.chains.proof.first.layout (2 * 12) "U3").any fun A =>
    Decidable.decide (0 < A.sizeI) && Decidable.decide ((At.X Zp).H.nU.getD 2 0 ≤ A.sizeC)) = true
  rw [c3]
  show (Decidable.decide (0 < A.sizeI) &&
    Decidable.decide ((At.X Zp).H.nU.getD 2 0 ≤ A.sizeC)) = true
  rw [c4, c5, pR, pK]
  simp

end VerifiableInference.Desc.Kinds.Head.Law.AtTable

#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.built_plain
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.built_24
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.ns_at_const
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.trees_at_const
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.room_at_const
