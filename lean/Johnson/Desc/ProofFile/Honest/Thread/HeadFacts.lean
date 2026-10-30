-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Thread/HeadFacts.lean: CLOSED FACTS ON THE LIBRARY's WRITTEN LIST OF
PLACES (P5J.At.ps), AND THREE FACTS UNDER THE LIBRARY's HEAD ON THE FIRST CHAIN's MEMBERS AND THE
GROUND. No lot, no filling, no prover. One definition with code; eight statements with their proofs.

  ps_338 · ps_346 · ps_355   the written list's places number 338, 346 and 355: closed facts
  k1FrontB            A CLOSED TEST WITH CODE on the first 324 places of the written list: each is
                      of another kind than K1, or the first segment's opening, or the reads or the
                      digits of one of the segments 0 to 22; its two letters shut an arm each
  k1FrontW · k1Front_arms   the test accepts; neither arm of it is idle: closed facts
  place_of_member     CONDITIONAL: a member's place stands at the member's number in the written
                      list
  built_25            CONDITIONAL: the ground that is made of the head's public part has 25 built
                      segments
  numbers_head        CONDITIONAL: each of the segments 0 to 23 is built, and linkNumbers names the
                      pieces 4 and 6 at it

The premises. h: the library's head (P5J.AtMgA, Johnson/P5J/MgAtAll.lean) · hG: G is the ground that
the maker makes of the head's public part · hb: blk is the member number b · hl: l is below 24.

Called, of the library: IM.ground_gets, IM.ground_named (Johnson/IMR/PureJoin.lean) ·
P5J.At.places_paid (Johnson/P5J/PlacesPaid.lean).

Whose. By the authors of the attention sub-protocol's (K5's) own rounds.

Limits. The closed facts are decided by Lean's kernel by evaluation at the library's written list as
it stands (the depth of recursion is raised for them); the library has ps_355's fact already
(H2K12.place_355, Johnson/Loose/H2K12/Hands354AtSeat.lean): it is decided anew here to spare that
import. k1Front_arms says that the list holds a place of each form: it is no trial of anything else.
That there is a ground G with hG under h is not said here. At the library's full size and the
format's second hash function alone. No property of a prover or a protocol is claimed.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K1.PlaceJob
import Johnson.P5J.MgAtAll
import Johnson.P5J.PlacesPaid
import Johnson.IMR.PureJoin

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.FirstFill
open VerifiableInference.Desc (Place KindName Chain Block)
open OnBytes.Maker (WholeD)
open OnBytes.Model.Stages (LinkH)
open P5J (AtMgA TS)

/-! ## 1 Closed facts on the written list of places -/

set_option maxRecDepth 1000000 in
/-- The written list's place number 338. A closed fact. -/
theorem ps_338 : P5J.At.ps[338]? = some ⟨1, some 24, 1, .K7⟩ := by decide +kernel

set_option maxRecDepth 1000000 in
/-- The written list's place number 346. A closed fact. -/
theorem ps_346 : P5J.At.ps[346]? = some ⟨1, some 24, 9, .K11⟩ := by decide +kernel

set_option maxRecDepth 1000000 in
/-- The written list's place number 355. A closed fact. -/
theorem ps_355 : P5J.At.ps[355]? = some ⟨1, none, 3, .K13⟩ := by decide +kernel

/-- **A closed test on the first 324 places of the written list**: each is of another kind than K1,
or (where first is set) the first segment's opening, or (where later is set) the reads or the digits
of one of the segments 0 to 22. -/
def k1FrontB (first later : Bool) : Bool :=
  (P5J.At.ps.take 324).all fun p =>
    p.kind != .K1 || (first && p == ⟨1, some 0, 1, .K1⟩) ||
      (later && (List.range 23).any fun l =>
        p == ⟨1, some l, 4, .K1⟩ || p == ⟨1, some l, 6, .K1⟩)

set_option maxRecDepth 1000000 in
/-- The test accepts. A closed fact. -/
theorem k1FrontW : k1FrontB true true = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- **Neither arm of the test is idle**: with either arm shut the test says no: so among the first
324 written places one is the opening, and one is a segment's reads or digits. A closed fact on the
written list as it stands: it shows no more than that. -/
theorem k1Front_arms : k1FrontB false true = false ∧ k1FrontB true false = false := by
  decide +kernel

/-! ## 2 Under the library's head -/

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)

include h in
/-- **A member's place stands at the member's number in the written list.** CONDITIONAL: under the
hypothesis h; blk is the member number b of the first chain's flat list. -/
theorem place_of_member {b : Nat} {blk : Block TS ProofFile.Cl} (hb : cF.blocksInOrder[b]? = some blk) :
    P5J.At.ps[b]? = some blk.place := by
  rw [← P5J.At.places_paid h.scope h.reads h.laid]
  unfold VerifiableInference.Desc.First.blockPlaces
  rw [List.getElem?_map, hb]
  rfl

include h in
/-- **The ground that is made of the head's public part has 25 built segments.** CONDITIONAL: under
the hypothesis h; G is that ground. -/
theorem built_25 {G : Ground} (hG : blankBy pureRoad.links Zp = some G) : G.built.size = 25 :=
  (IM.ground_gets h.scope h.reads h.laid.pub hG).1

include h in
/-- **Under the head each of the segments 0 to 23 is built, and linkNumbers names the pieces 4 and 6
at it.** CONDITIONAL: under the hypothesis h; G is the ground that is made of the head's public
part; l is below 24. -/
theorem numbers_head {G : Ground} (hG : blankBy pureRoad.links Zp = some G) {l : Nat}
    (hl : l < 24) : ∃ (Y : LinkH) (rd dg : Option (List Nat)), G.built[l]? = some Y ∧
      VerifiableInference.Desc.K1.linkNumbers G Y = some (4, 6, rd, dg) := by
  obtain ⟨nam, -⟩ := IM.ground_named h.scope h.reads h.laid.pub hG
  have hs := ((IM.ground_gets h.scope h.reads h.laid.pub hG).2 l (by omega)).2
  obtain ⟨Y, Y', a, ka, ga, -, a', ka', ga', -⟩ := nam (l / 2) (by omega)
  unfold Meaning.getsOf at hs
  rw [if_neg (by omega)] at hs
  rcases Nat.mod_two_eq_zero_or_one l with e | e
  · rw [if_pos e] at hs
    rw [show 2 * (l / 2) = l by omega] at a
    cases hq : G.W.G[l / 2]? with
    | none =>
      rw [hq] at hs
      cases hs
    | some hp =>
      refine ⟨Y, (hp.tl.ix.U.getD 2 none).map ([·]), some [hp.tl.ix.ZZ, hp.tl.ix.BZ], a, ?_⟩
      unfold VerifiableInference.Desc.K1.linkNumbers
      rw [if_pos (by rw [ka]; rfl), ga, hq]
      rfl
  · rw [if_neg (by omega)] at hs
    rw [show 2 * (l / 2) + 1 = l by omega] at a'
    cases hq : G.W.A[l / 2]? with
    | none =>
      rw [hq] at hs
      cases hs
    | some p =>
      refine ⟨Y', some [p.iU3], some [p.seam.tl.ix.ZZ, p.seam.tl.ix.BZ], a', ?_⟩
      unfold VerifiableInference.Desc.K1.linkNumbers
      rw [if_neg (by rw [ka']; decide), if_pos (by rw [ka']; rfl), ga', hq]
      rfl

end ProofFile.Honest.FirstFill

#print axioms ProofFile.Honest.FirstFill.ps_338
#print axioms ProofFile.Honest.FirstFill.ps_346
#print axioms ProofFile.Honest.FirstFill.ps_355
#print axioms ProofFile.Honest.FirstFill.k1FrontW
#print axioms ProofFile.Honest.FirstFill.k1Front_arms
#print axioms ProofFile.Honest.FirstFill.place_of_member
#print axioms ProofFile.Honest.FirstFill.built_25
#print axioms ProofFile.Honest.FirstFill.numbers_head
