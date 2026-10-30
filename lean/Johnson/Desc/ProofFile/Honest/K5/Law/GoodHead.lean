-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/GoodHead.lean: UNDER THE LIBRARY's HEAD (P5J.AtMgA,
Johnson/P5J/MgAtAll.lean): Good (Honest/Side.lean) AT THE ROW OF AN ATTENTION SEGMENT's OWN ROUNDS
(kind K5: the label of that sub-protocol in the description) BESIDE THE DESCRIPTION's OWN MEMBER:
the side that Side.seated makes of the first chain's flat list at the kind's place of group g. Two
premises of k5_good_paid (Honest/K5/Law/GoodPaid.lean) are shown there: K5Block, and the test on the
calls' shapes. Statements with their proofs.

  found_is_member   whichever member of the flat list find? finds at the kind's place of group g is
                 the member at the border borderOf g
  k5Block_head   **K5Block at that member**, at the plan's numbers
  shapes_head    the verifier's test on a call's shape says yes at every call of the row
  seated_head    Side.seated makes a side there: k5_good_head is not met for nothing on that score
  k5_good_head   **Good at the side that Side.seated makes there**, at whatever falls

THE PREMISES THAT STAY, BY NAME. h: the head: A HYPOTHESIS · g is below 12 · a is the plan of group
g · the seat's two facts: its segment is 2 g + 1; its public data are the plan's · σ₀ is the side
that Side.seated makes (there is one: seated_head) · hk: no entry of the book names a part of this
place as owner (fresh alone spends it).

WHAT k5_good_head SAYS, AND WHAT NOT: as k5_good_paid: AT A := B := THE EMPTY SENTENCE (False):
plays AND acc ARE MET FOR NOTHING. fits is shown. fresh is shown, AND IS EMPTY: the row has no coin
of its own. exact is had, member by member, from the three theorems on the frame's own parts, their
premises on the declared rounds and on the calls' shapes AT THE DESCRIPTION's OWN MEMBER's ROUNDS.

Every part of K5's row has takes = ⟨0, 0⟩; that no entry of the book names one as owner is the
premise hk. exact speaks, AT EACH MEMBER BY ITSELF, of the runs that it spends AS UNIFORM AND
INDEPENDENT of each other and of all that is fixed in the equation. That they are so in a run is not
stated here: it needs AT THE LEAST fresh at the part that owns them, the book's lending of just
these runs, and that no two of them share a coin. Of what stands in front the row's jobs read the
challenges alone.

NEVER LEFT OFF, as the theorem on the masked sumcheck's part has it (Honest/SumLaw/SumExact.lean):
the spender's half alone · the owners' sentences are typed by no file of this folder, and none is
called here · one part at a time, all else fixed before the coins · it holds at every job, right or
wrong, so it says nothing on whether the job is the protocol's · nothing on hiding. ("This folder"
is said here of Honest/K5/ and K5/Honest/.)

WHOEVER CARRIES A RUN BEHIND ITS SPENDER, as the theorem on the round of n scalars has it
(Honest/Small/Scalars.lean): the frame lets any part behind the spender carry it, and c to t + c is
one to one: what this part shows, together with the run, gives t at every coin: so such a carrier
has to meet its own exact at each fixed carried run, beside a simulator that is not handed it.
At K5 the runs are entries of the segment's mask row: PAID BY NOBODY HERE.

THE CALLER's CONDITION, AND K5 IS THE CALLER. In these theorems a job may read the rounds shown in
front of the part: they are fixed before the coins there; where an item that a job reads was sent
under an entry which is spent here, that is not so in a run, and the theorems say nothing. THAT AT
K5's ROW NO MOVE OF A MEMBER OF THE SIDE READS ANYTHING OF WHAT HAS BEEN SEEN IS k5_members_noneSeen
(Honest/K5/Law/NoneSeen5.lean), WHICH THIS FILE DOES NOT IMPORT.
By the jobs' texts and types: what is handed on is Unit; there is no
point; of the input the trace alone is read. What was heard is handed on whole, a digest that stands
in a challenge too, and the seat's reader of the key points is a free field. ONE SLOT OF A JOB IS
HANDED COINS: the summand at Y is handed the run of the end values that the same job spends: the
frame's own letter, at every job.

Limits. The library's full size alone; twelve places. No property is claimed.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.GoodPaid
import Johnson.Desc.ProofFile.Honest.K5.Law.Member
import Johnson.Desc.First.Att.Door.Law.K05KindR
import Johnson.P5J.PlacesPaid

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K5
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Block Chain Place)
open VerifiableInference.Desc.Part.MaskedSum (shapeOk)
open H2K5.Honest (shapes)
open P5J (AtMgA TS)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
include h

/-- **Whichever member find? finds at the kind's place of group g is the member at the border.**
CONDITIONAL: the head. By the library's two facts: the flat list's places are the written list; in
that list the places of the kind are just the twelve. -/
theorem found_is_member {g : Nat} {b : Block TS ProofFile.Cl}
    (hf : cF.blocksInOrder.find? (fun b => b.place == (⟨1, some (2 * g + 1), 3, .K5⟩ : Place)) = some b) :
    cF.blocksInOrder[borderOf g]? = some b := by
  have hp : b.place = ⟨1, some (2 * g + 1), 3, .K5⟩ :=
    eq_of_beq (List.find?_some
      (p := fun b : Block TS ProofFile.Cl => b.place == (⟨1, some (2 * g + 1), 3, .K5⟩ : Place)) hf)
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 (List.mem_of_find?_eq_some hf)
  have e : cF.blocksInOrder.map (·.place) = P5J.At.ps := P5J.At.places_paid h.scope h.reads h.laid
  have hpi : P5J.At.ps[i]? = some b.place := by
    rw [← e, List.getElem?_map, hi]
    rfl
  obtain ⟨g', -, rfl, e2⟩ := H2K5.Door.k5_places_full i b.place hpi (by rw [hp])
  have e3 : some (2 * g + 1) = some (2 * g' + 1) := by
    have := congrArg (·.link) (hp.symm.trans e2)
    exact this
  have e4 : g' = g := by
    have := Option.some.inj e3
    omega
  rw [e4] at hi
  exact hi

/-- **K5Block at the description's own member.** CONDITIONAL: the head; g is below 12; a is the plan
of group g; blk is the member at the border; the seat's two facts. -/
theorem k5Block_head {g : Nat} (hg : g < 12) {a : OnBytes.Attention.Plan}
    (ha : (P5J.At.X Zp).A[g]? = some a) {blk : Block TS ProofFile.Cl}
    (hb : cF.blocksInOrder[borderOf g]? = some blk) {Z5 : Seat5} (hl : Z5.link = 2 * g + 1)
    (hP : Z5.P = ⟨a.S, a.own⟩) : K5Block blk Z5 (parAt Zp g a) := by
  obtain ⟨blk', a', hfl, Pl, Dc⟩ := k5_member h hg
  obtain rfl : blk' = blk := Option.some.inj (hfl.symm.trans hb)
  obtain rfl : a' = a := Option.some.inj (Pl.plan.symm.trans ha)
  refine ⟨?_, Dc.rounds, Dc.oracles, ?_⟩
  · rw [Dc.place]
    show (⟨1, some (2 * g + 1), 3, .K5⟩ : Place) = ⟨1, some Z5.link, 3, .K5⟩
    rw [hl]
  · rw [hP]
    rfl

/-- **The test on a call's shape says yes at every call of the row.** CONDITIONAL: as k5Block_head,
less the member. -/
theorem shapes_head {g : Nat} (hg : g < 12) {a : OnBytes.Attention.Plan}
    (ha : (P5J.At.X Zp).A[g]? = some a) {Z5 : Seat5} (hP : Z5.P = ⟨a.S, a.own⟩) :
    ((shapes Z5.P.x).all fun s =>
      match s with
      | .sum k => shapeOk k
      | .one _ => true) = true := by
  obtain ⟨_, a', -, Pl, Dc⟩ := k5_member h hg
  obtain rfl : a' = a := Option.some.inj (Pl.plan.symm.trans ha)
  have e := shapes_plan Dc.plan
  rw [hP]
  exact e

/-- **Side.seated makes a side at the kind's place of group g.** CONDITIONAL: the head; g is below
12; the seat's segment is 2 g + 1. -/
theorem seated_head {W₀ Rc Xi Tr X Pb : Type} {g : Nat} (hg : g < 12) (cells : Tr → Cells)
    {Z5 : Seat5} (hl : Z5.link = 2 * g + 1) (fs₀ : List (Fall TS)) :
    ∃ σ₀ : Side TS ProofFile.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb,
      Side.seated cF.blocksInOrder Z5.place (k5Pairs cells Z5) fs₀ = some σ₀ := by
  obtain ⟨blk, _, hb, -, Dc⟩ := k5_member h hg
  have hp : blk.place = Z5.place := by
    rw [Dc.place]
    show (⟨1, some (2 * g + 1), 3, .K5⟩ : Place) = ⟨1, some Z5.link, 3, .K5⟩
    rw [hl]
  have hs : (cF.blocksInOrder.find? fun b => b.place == Z5.place).isSome = true :=
    List.find?_isSome.2 ⟨blk, List.mem_of_getElem? hb, beq_iff_eq.2 hp⟩
  obtain ⟨b, hb'⟩ := Option.isSome_iff_exists.1 hs
  exact ⟨_, by
    unfold Side.seated
    rw [hb']
    rfl⟩

/-- **Good at K5's row beside the description's own member, AT A := B := THE EMPTY SENTENCE (False):
SO ITS FIELDS plays AND acc ARE MET FOR NOTHING: IT SAYS fits, exact AND fresh, AND NOTHING ON THE
PLAYING OR ON THE VERIFIER's YES; fresh IS EMPTY.** CONDITIONAL: see the head. pre is tied to no
description, not to this one either; at each pre this says of exact no more than msForm_paid,
loneForm_paid and quietForm_paid (Honest/K5/Law/GoodPaid.lean).
No move of this kind reads what it is handed as seen (Honest/K5/Law/NoneSeen5.lean, with that file's
limits; what is seen holds the opened columns too: Seen, Honest/Frame.lean). The simulators that
simsOf lays beside the parts (sumSim, quietSim, scalarsSim) read none of the opened columns that the
front holds: a reading of their code, with theorems for parts of it (tells_scalars; tell_toSim). The
rest is a reading of the frame's text: play and shows reach these columns through a move's say
alone; in Good they stand besides only in premises that tie the state to the front or test
positions, and in the fields plays and acc, which are empty here, and in On, which is True here. So,
as a reading, this theorem's statement says the same at every value of the opened columns. -/
theorem k5_good_head {W₀ Rc Xi Tr X Pb : Type} {g : Nat} (hg : g < 12)
    {a : OnBytes.Attention.Plan} (ha : (P5J.At.X Zp).A[g]? = some a) {cells : Tr → Cells}
    {Z5 : Seat5} (hl : Z5.link = 2 * g + 1) (hP : Z5.P = ⟨a.S, a.own⟩)
    (pre : List (Nat × Nat × List Fmt.DeclaredRound))
    (φ : Face (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) Pb) (Bk : ProverCoinCounts) (ord : List Place)
    (chain firstTree : Nat) (fs₀ : List (Fall TS))
    {σ₀ : Side TS ProofFile.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb}
    (hσ : Side.seated cF.blocksInOrder Z5.place (k5Pairs cells Z5) fs₀ = some σ₀)
    (hk : ∀ e ∈ Bk.ahead, e.owner.place ≠ Z5.place) :
    Good pre φ σ₀ Bk ord chain firstTree (fun _ _ _ _ => False) (fun _ _ _ _ => False)
      (fun _ _ _ _ => True) k5Bud := by
  obtain ⟨b, hf, rfl⟩ := Option.map_eq_some_iff.1 hσ
  have hf' : cF.blocksInOrder.find? (fun b => b.place == (⟨1, some (2 * g + 1), 3, .K5⟩ : Place)) =
      some b := by
    rw [← hl]
    exact hf
  exact k5_good_paid pre φ Bk ord chain firstTree
    (k5Block_head h hg ha (found_is_member h hf') hl hP) rfl (shapes_head h hg ha hP) hk

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.found_is_member
#print axioms ProofFile.Honest.K5.k5Block_head
#print axioms ProofFile.Honest.K5.shapes_head
#print axioms ProofFile.Honest.K5.seated_head
#print axioms ProofFile.Honest.K5.k5_good_head
