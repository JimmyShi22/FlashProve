-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/PlanOkGives.lean: what the test on the plan of a lookup's
sub-protocol yields, at the lot's sub-protocol and at the description's own member. Conditional on a
test on the plan that accepts. Two definitions of propositions, and theorems.

Terms. Honest/K3/GLOSSARY.md ("address", "lot", "member", "plan", "site", "sub-protocol").

What is shown.
  `PlanGives`: what is said of a sub-protocol at an address: the place's parameters; their shape;
    the plan's entries are, but for the work bits, those that the hearing at the shape's face goes
    by (`entriesFit`); several calls; room for the lookup's scalars in the link's count; the
    sub-protocol's rounds are the parameters'; no round has an oracle message.
  `theOwn_plan`, `theWhole_plan`, `theStated_plan`: conditional on `b.planOk = true`: it holds of
    the value of `K3.theOwn`, `K3.theWhole`, `K3.theStated`.
  `member_planOk`: the member's test on the plan gives that of the lot's sub-protocol, where the
    sub-protocol is wrapped alone (by the wrapping's text: `IM.seatedAs`, Johnson/IMR/SeatForm.lean,
    keeps the field).
  `MemberPlan`, `memberPlan`: the statement and its proof: what a caller that uses "the seated row
    plays" needs of the member.

Hypotheses that remain. A test on the plan that accepts (`hp`; of the member `hm`), and, in the
three at the library's texts, `h`: the text returns the sub-protocol at the address. In
`member_planOk`: `hy`, `hl`: m is the flat list's form of y; y is b wrapped alone (`IM.LaidAlone`).
Of the member: the library has it of every member of the first chain where the description's own
test on the plan accepts (`planOk_blocks`, Johnson/Desc/PlanPasses.lean).

Users. This file is imported by Honest/K3/Law/MemberSite.lean, Honest/K3/Law/Keep/SitesAtDesc.lean
[not in this library], Honest/K3/Law/Thread/SiteThereHead.lean and
Johnson/AtFull/Shape/SitesAtHead.lean.

Limits. What is not yielded: that the face passes the hearing's own test on its numbers (`Face.ok`):
no clause of the sub-protocol's test on the plan is that test; `siteTests` (Honest/K3/Lot.lean)
evaluates it, and Honest/K3/Law/FaceOk.lean leads to it from two tests on the shape. The room is
stated at the program's count (`Forest.elems`), not at `Face.slots`: that the two are one number is
shown in Honest/K3/Law/SlotsElems.lean.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.MemberAtSite
import Johnson.Desc.ProofFile.Honest.K3.Law.Statements

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law
open VerifiableInference.Desc (Block Chain FileDescription KindName Place OpenedColumn Oracle)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Look (placeAt)
open VerifiableInference.Desc.K3 (pieceAt theOwn theWhole theStated faceOf entriesFit)
open ProofFile.Honest.AtPlace (AsFlat member_alone alone_gives)

/-- What the test on the plan yields of a sub-protocol at the address a. -/
def PlanGives {Cl : Type} (X : OnBytes.Model.Verify.Public) (a : Place) (b : Block S Cl) : Prop :=
  ∃ i d p h, a.link = some i ∧ a.piece = pieceAt X i d ∧ placeAt X i d = some p ∧
    p.shape = some h ∧ entriesFit (faceOf h) (p.entries.getD []) = true ∧ 1 < h.NC ∧
    p.first + OnBytes.Model.Forest.elems h ≤ p.ns ∧ b.rounds = p.rounds ∧
    b.oracles = b.rounds.map fun _ => []

theorem theOwn_plan {Cl : Type} (claim : OnBytes.Model.Aff → Cl) (runs : Bool)
    (X : OnBytes.Model.Verify.Public) (codes : OnBytes.Codes) (shape : OnBytes.Params.ReqShape)
    (a : Place) (b : Block S Cl) (h : theOwn claim runs X codes shape a = some b)
    (hp : b.planOk = true) : PlanGives X a b := by
  unfold theOwn at h
  split at h
  · exact nomatch h
  · obtain ⟨i, hi, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨digits, _, h⟩ := List.exists_of_findSome?_eq_some h
    split at h
    · exact nomatch h
    · rename_i hpc
      obtain ⟨p, hpl, h⟩ := Option.bind_eq_some_iff.1 h
      obtain ⟨sent, _, h⟩ := Option.bind_eq_some_iff.1 h
      obtain ⟨laid, _, h⟩ := Option.bind_eq_some_iff.1 h
      obtain ⟨key, _, rfl⟩ := Option.map_eq_some_iff.1 h
      have hp' : ((VerifiableInference.Desc.K3.planOk p laid
          ([] : List (VerifiableInference.Desc.First.Look.Guest S Cl)) &&
          VerifiableInference.Desc.K3.Law.fitsVia p) && key) = true := by
        cases runs <;> exact hp
      simp only [Bool.and_eq_true] at hp'
      obtain ⟨⟨hk3, hfv⟩, _⟩ := hp'
      unfold VerifiableInference.Desc.K3.planOk at hk3
      simp only [Bool.and_eq_true] at hk3
      have hpp := hk3.1
      unfold VerifiableInference.Desc.First.Look.P.planOk at hpp
      unfold VerifiableInference.Desc.K3.Law.fitsVia at hfv
      cases hsh : p.shape with
      | none => simp [hsh] at hfv
      | some hS =>
        simp only [hsh, Bool.and_eq_true, decide_eq_true_eq] at hpp hfv
        obtain ⟨⟨⟨⟨⟨_, _⟩, hNC⟩, hroom⟩, _⟩, _⟩ := hpp
        refine ⟨i, digits, p, hS, hi, by simpa using hpc, hpl, hsh, hfv.1, hNC, hroom, ?_, ?_⟩
        · cases runs <;> rfl
        · cases runs <;> rfl

theorem theWhole_plan {Cl : Type} (claim : OnBytes.Model.Aff → Cl) (runs : Bool)
    (X : OnBytes.Model.Verify.Public) (codes : OnBytes.Codes) (shape : OnBytes.Params.ReqShape)
    (a : Place) (b : Block S Cl) (h : theWhole claim runs X codes shape a = some b)
    (hp : b.planOk = true) : PlanGives X a b := by
  unfold theWhole at h
  obtain ⟨b₀, hb, rfl⟩ := Option.map_eq_some_iff.1 h
  split at hp
  · have hp₀ : (b₀.planOk && true) = true := hp
    obtain ⟨i, d, p, hS, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ :=
      theOwn_plan claim runs X codes shape a b₀ hb (by simpa using hp₀)
    refine ⟨i, d, p, hS, h1, h2, h3, h4, h5, h6, h7, ?_, ?_⟩
    · show b₀.rounds ++ [] = p.rounds
      rw [List.append_nil, h8]
    · show b₀.oracles ++ [] = (b₀.rounds ++ []).map fun _ => []
      rw [List.append_nil, List.append_nil, h9]
  · obtain ⟨i, d, p, hS, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ :=
      theOwn_plan claim runs X codes shape a b₀ hb hp
    exact ⟨i, d, p, hS, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem theStated_plan {Cl : Type} (claim : OnBytes.Model.Aff → Cl)
    (readers : Nat → Option (VerifiableInference.Desc.K3.Readers S))
    (X : OnBytes.Model.Verify.Public) (codes : OnBytes.Codes) (shape : OnBytes.Params.ReqShape)
    (a : Place) (b : Block S Cl) (h : theStated claim readers X codes shape a = some b)
    (hp : b.planOk = true) : PlanGives X a b := by
  unfold theStated at h
  obtain ⟨b₀, hb, h⟩ := Option.bind_eq_some_iff.1 h
  split at h
  · obtain rfl := Option.some.inj h
    exact theWhole_plan claim true X codes shape a _ hb hp
  · split at h
    · obtain rfl := Option.some.inj h
      exact theWhole_plan claim true X codes shape a _ hb hp
    · split at h
      · obtain rfl := Option.some.inj h
        exact theWhole_plan claim true X codes shape a _ hb hp
      · obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.1 h
        exact theWhole_plan claim true X codes shape a b₀ hb hp

/-- The member's test on the plan gives that of the lot's sub-protocol, where the sub-protocol is
wrapped alone. -/
theorem member_planOk {same : S → S → Bool} {y m b : Block S Cl} {name : String} {a : Place}
    (hy : AsFlat y m) (hl : IM.LaidAlone same y b name a) (hm : m.planOk = true) :
    b.planOk = true := by
  have hyp : y.planOk = true := by
    rcases hy with rfl | rfl
    · exact hm
    · have : (y.planOk && y.hasNoClaimsAndNothingAfter) = true := hm
      simp only [Bool.and_eq_true] at this
      exact this.1
  rw [hl] at hyp
  exact hyp

theorem zip_map_nil {α β : Type} : ∀ l : List α,
    l.zip (l.map fun _ => ([] : List β)) = l.map fun r => (r, ([] : List β))
  | [] => rfl
  | _ :: l => by rw [List.map_cons, List.zip_cons_cons, zip_map_nil l, List.map_cons]

/-- **What the member's test on the plan gives a caller that uses "the seated row plays".** Wherever
the description returns (`IM.Open`): for a sub-protocol b of the lookups' lot, a member m of the
first chain's flat list at b's place whose test on the plan accepts, and a site s made at the
address at which b stands: there is a list of entries es which the hearing at the site's face goes
by (`entriesFit`), and m's rounds, each with its oracle messages, are these entries, each as a
declared round that opens nothing, with no oracle message. Conditional on `m.planOk = true`.
A lemma's statement, none of the library's goals. -/
def MemberPlan : Prop :=
  ∀ (o : SecondHashFunctionArgument) (pol lay KL : ByteArray) (F : FileDescription Inst) (Z : Pub) (Bs : PureBase)
    (base : List (Block S Cl)) (c : Chain S Cl) (A : SharedSeat) (B : SecondSeat),
    IM.Open o pol lay KL F Z Bs base c A B →
    ∀ b ∈ (K3Lot.lot Z).blocks Bs.G₀, ∀ m ∈ c.blocksInOrder, m.place = b.place → m.planOk = true →
    ∀ (ps : List Spot) (x : Nat × Bool × Place) (s : Site), x ∈ K3Lot.addresses Z →
      x.2.2 = b.place → siteAt Z.p.X ps x = some s →
      ∃ es : List Fmt.Entry, entriesFit s.at_.face es = true ∧
        m.rounds.zip m.oracles = es.map fun e => (declOf e, ([] : List Oracle))

/-- **The proof of `MemberPlan`.** -/
theorem memberPlan : MemberPlan := by
  intro o pol lay KL F Z Bs base c A B O b hb m hm hp hpl ps x s hx hxb hs
  have hb' : b ∈ K3Lot.hear Z := by rw [← lot_blocks Z Bs.G₀]; exact hb
  unfold K3Lot.hear at hb'
  obtain ⟨x', hx', hst⟩ := List.mem_filterMap.1 hb'
  have hpx' := theStated_place _ _ _ _ _ _ b hst
  obtain ⟨hk, hal⟩ := k3_alone Z x' hx'
  have hL : K3Lot.lot Z ∈ onlineFirstChainBlockTables Z := by simp [onlineFirstChainBlockTables]
  obtain ⟨y, hy, hlaid⟩ := member_alone o pol lay KL F Z Bs base c A B O (K3Lot.lot Z) hL b hb
    (by rw [hpx', hk]; decide) (by rw [hpx']; exact hal) m hm hp
  obtain ⟨_, _, g3, g4, _, _, _⟩ := alone_gives sameReply y m b m.name b.place hy hlaid
  obtain ⟨i, d, p, hS, h1, h2, h3, h4, h5, _, _, h8, h9⟩ :=
    theStated_plan _ _ _ _ _ _ b hst (member_planOk hy hlaid hpl)
  rw [← hpx', ← hxb] at h1 h2
  unfold K3Lot.addresses at hx
  obtain ⟨j, _, hx⟩ := List.mem_flatMap.1 hx
  obtain ⟨e, _, rfl⟩ := List.mem_map.1 hx
  obtain rfl : j = i := Option.some.inj h1
  obtain rfl : e = d := pieceAt_inj _ _ _ _ h2
  unfold siteAt at hs
  obtain ⟨p', hp', hs⟩ := Option.bind_eq_some_iff.1 hs
  obtain rfl : p = p' := Option.some.inj (h3.symm.trans hp')
  obtain ⟨hS', hS'', hs⟩ := Option.bind_eq_some_iff.1 hs
  obtain rfl : hS = hS' := Option.some.inj (h4.symm.trans hS'')
  obtain ⟨_, _, hs⟩ := Option.bind_eq_some_iff.1 hs
  have hface : s.at_.face = faceOf hS := by
    dsimp only at hs
    split at hs
    · obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.1 hs
      rfl
    · obtain rfl := Option.some.inj hs
      rfl
  refine ⟨p.entries.getD [], by rw [hface]; exact h5, ?_⟩
  rw [g4, h9, g3, zip_map_nil, h8]
  show ((p.entries.getD []).map fun e => ({ entry := e } : Fmt.DeclaredRound)).map
    (fun r => (r, ([] : List Oracle))) = _
  rw [List.map_map]
  rfl

end ProofFile.Honest.K3.Law

#print axioms ProofFile.Honest.K3.Law.theStated_plan
#print axioms ProofFile.Honest.K3.Law.member_planOk
#print axioms ProofFile.Honest.K3.Law.memberPlan
#print axioms ProofFile.Honest.K3.Law.theOwn_plan
#print axioms ProofFile.Honest.K3.Law.theWhole_plan
#print axioms ProofFile.Honest.K3.Law.zip_map_nil
