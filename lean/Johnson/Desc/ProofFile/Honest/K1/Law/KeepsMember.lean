-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/Law/KeepsMember.lean: the kind K1's clauses of the letter keeps AT
A MEMBER AS A CHAIN SEATS IT: with "no mark behind" inside, and shown from the seated member's own
accepting step (StepYes, Johnson/Top/H0/Walk/Reach.lean). Three definitions of propositions,
statements and proofs, over Johnson/Desc/ProofFile/Honest/K1/Law/Keeps.lean,
Johnson/Desc/ProofFile/Honest/K1/Law/KeepsReads.lean and
Johnson/Desc/ProofFile/Honest/K1/Law/KeepsFirstOut.lean, none of which turns, and over the library's
laws on how a lot's sub-protocol stands in the first chain (Johnson/IMR/SeatForm.lean,
Johnson/IMR/K1Seat.lean, Johnson/IMR/BackSeat.lean, Johnson/IMR/MemberPath.lean).

TWO LAYERS. K1CommitKeeps and K1ReadsKeeps say what a return of the kind's own decision leaves: it
leaves the mark as it was. The guard that a chain lays around a lot's sub-protocol accepts only
without a mark: so at the seated member the clause is the decision's AND "no mark behind".

  K1CommitKeepsM, K1ReadsKeepsM: the two clauses with s'.failed = none.
  K1KeepsAt p: BY THE PLACE: at a place of the first chain, of the kind K1, inside a link: pieces 4
    and 5: the reads' member; pieces 6 and 7: the digits' member. AT EVERY OTHER PLACE IT IS False:
    at another kind's or another chain's place, and at the two places where the kind's text is only
    the first HALF of a member (the first segment's opening, piece 1 of link 0; W's sending behind
    the links, piece 4). False HAS TWO FACES: a law that ENDS in the clause cannot be shown there; a
    law that TAKES the clause as a premise holds there for nothing.
  k1_commit_member, k1_reads_member: where b is the digits' (the reads') sub-protocol of the lot,
    seated alone (IM.LaidAlone): an accepting step of b gives the clause.
  k1_member_hear: THE SAME BY THE LETTERS OF THE ARM "hear" OF THE LIBRARY's TEN FORMS OF A MEMBER
    (IM.FlatCase, Johnson/IMR/FlatCases.lean) at the kind K1: a sub-protocol b' of a lot of the
    description at ⟨1, some l, i + 1, K1⟩, 1 ≤ i, and b seated alone over it: an accepting step of b
    gives K1KeepsAt at that place. No premise on the public files.
  k1_member_later: AT THE DESCRIPTION's OWN CHAIN: wherever the description of the proof file is
    made (IM.Open, Johnson/IMR/SeatOpen.lean; by IM.k1_later, Johnson/IMR/K1Seat.lean): at every
    link and every index behind its first at which the link's list of kinds has K1 the chain has a
    member, and its accepting steps give K1KeepsAt at its place: so the premise on the seat of the
    two lemmas above (IM.LaidAlone) is met there.
  k1_first_half: the arm "first" at link 0: an accepting step of the lot's own sub-protocol at ⟨1,
    some 0, 1, K1⟩ gives K1FirstKeeps and K1Out. No clause on the mark: the second half is joined
    behind.
  k1_send_half: the arm "back" at ⟨1, none, 4, K1⟩: a return of the lot's sub-protocol there is a
    return of K1's sending, which gives K1SendKeeps, and then a return of the kind K13's step behind
    it (K13.rowsB, Johnson/Desc/K13/Kind.lean), which is handed on as it is.

Not shown here. ONE WAY, FROM AN ACCEPTING STEP: that a member accepts anywhere is not said. Which
member of a chain's flat list has which form (IM.flat_cases says it for files in scope). Nothing on
the step that is joined behind the opening, nor on K13's step behind W's sending. The three are
definitions: nothing is claimed of them. Nothing on soundness, on completeness or on any other
property.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.ProofFile.Honest.K1.Law.KeepsReads
import Johnson.Desc.ProofFile.Honest.K1.Law.KeepsFirstOut
import Johnson.IMR.BackSeat
import Johnson.IMR.MemberPath
import Johnson.Top.H0.Walk.ReachInv

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Place KindName)
open VerifiableInference.Desc.First (S)
open OnBytes.Model.Stages (LinkH)
open Johnson.Desc.First.Walk.Tied (StepYes stepYes_decide)

/-- **The digits' member's clause**: what the commitment's decision leaves, and no mark behind. A
definition: a premise's form. -/
def K1CommitKeepsM (s s' : S) : Prop := K1CommitKeeps s s' ∧ s'.failed = none

/-- **The reads' member's clause**: what the whole member's decision leaves, and no mark behind. A
definition: a premise's form. -/
def K1ReadsKeepsM (s s' : S) : Prop := K1ReadsKeeps s s' ∧ s'.failed = none

/-- **The kind's clause by the place**, at the places where a whole member is the kind's own. At
every other place it is False: a law that ends in it cannot be shown there; a law that takes it as a
premise holds there for nothing. A definition: a premise's form. -/
def K1KeepsAt (p : Place) (s s' : S) : Prop :=
  match p.chain, p.kind, p.link, p.piece with
  | 1, .K1, some _, 4 | 1, .K1, some _, 5 => K1ReadsKeepsM s s'
  | 1, .K1, some _, 6 | 1, .K1, some _, 7 => K1CommitKeepsM s s'
  | _, _, _, _ => False

/-- **An accepting step of the seated digits' member gives its clause.** -/
theorem k1_commit_member {same : S → S → Bool} {b : Block S ProofFile.Cl} {q : Params.First}
    {gp : _root_.Desc.Plain.GPar} {l pc m : Nat} {arrays : Option (List Nat)} {name : String}
    {a : Place}
    (h : IM.LaidAlone same b
      (VerifiableInference.Desc.K1.laterAt q gp l pc m arrays : Block S Unit).retype name a)
    {ft : Nat} {s s' : S} (y : StepYes ft b s s') : K1CommitKeepsM s s' := by
  obtain ⟨rs, gs, d⟩ := stepYes_decide y
  obtain ⟨d', hm⟩ := IM.alone_noMark h d
  have d'' : (VerifiableInference.Desc.K1.laterAt q gp l pc m arrays : Block S Unit).decide s rs
      gs = .ok s' := d'
  exact ⟨k1_commit_keeps d'', hm⟩

/-- **An accepting step of the seated reads' member gives its clause.** -/
theorem k1_reads_member {same : S → S → Bool} {b : Block S ProofFile.Cl} {Z : ProofFile.Pub} {G : ProofFile.Ground}
    {l : Nat} {X : LinkH} {pr : Nat} {reads : Option (List Nat)} {name : String} {a : Place}
    (h : IM.LaidAlone same b (IM.k1Reads Z G l X pr reads).retype name a)
    {ft : Nat} {s s' : S} (y : StepYes ft b s s') : K1ReadsKeepsM s s' := by
  obtain ⟨rs, gs, d⟩ := stepYes_decide y
  obtain ⟨d', hm⟩ := IM.alone_noMark h d
  have d'' : (IM.k1Reads Z G l X pr reads).decide s rs gs = .ok s' := d'
  exact ⟨k1_reads_keeps d'', hm⟩

/-- **BY THE LETTERS OF THE ARM "hear" AT THE KIND K1**: an accepting step of the seated member
gives the kind's clause at its place. -/
theorem k1_member_hear {Z : ProofFile.Pub} {G₀ : ProofFile.Ground} {l i : Nat} {b b' : Block S ProofFile.Cl}
    {name : String} (lot : ∃ L ∈ ProofFile.onlineFirstChainBlockTables Z, b' ∈ L.blocks G₀)
    (hp : b'.place = { chain := 1, link := some l, piece := i + 1, kind := .K1 }) (hi : 1 ≤ i)
    (hla : IM.LaidAlone ProofFile.sameReply b b' name
      { chain := 1, link := some l, piece := i + 1, kind := .K1 })
    {ft : Nat} {s s' : S} (y : StepYes ft b s s') :
    K1KeepsAt { chain := 1, link := some l, piece := i + 1, kind := .K1 } s s' := by
  obtain ⟨L, hL, hb⟩ := lot
  obtain ⟨x, hx, rfl⟩ := IM.lot_K1 hL hb (by rw [hp]) (l := l) (by rw [hp])
  rcases IM.k1_mem hx with rfl | ⟨l', X, pr, pd, reads, digits, -, hn, rfl | rfl⟩
  · have e : (1 : Nat) = i + 1 := congrArg Place.piece hp
    omega
  · have e : pr = i + 1 := congrArg Place.piece hp
    have k := k1_reads_member hla y
    rcases IM.numbers_pieces hn with ⟨h4, -⟩ | ⟨h5, -⟩
    · obtain rfl : i = 3 := by omega
      exact k
    · obtain rfl : i = 4 := by omega
      exact k
  · have e : pd = i + 1 := congrArg Place.piece hp
    have k := k1_commit_member hla y
    rcases IM.numbers_pieces hn with ⟨-, h6⟩ | ⟨-, h7⟩
    · obtain rfl : i = 5 := by omega
      exact k
    · obtain rfl : i = 6 := by omega
      exact k

/-- **AT THE DESCRIPTION's OWN CHAIN**: wherever the description of the proof file is made (IM.Open,
Johnson/IMR/SeatOpen.lean), at every link l and every index i behind its first at which the link's
list of kinds has K1: the chain has a member there, and every accepting step of it gives the kind's
clause at its place. So the premise on the seat of k1_commit_member and k1_reads_member is met
there. -/
theorem k1_member_later {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray}
    {F : VerifiableInference.Desc.FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase}
    {base : List (Block S ProofFile.Cl)} {c : VerifiableInference.Desc.Chain S ProofFile.Cl}
    {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} (O : IM.Open o pol lay KL F Z Bs base c A B) (l : Nat)
    (sub : VerifiableInference.Desc.First.ModelPart) (hl : (ProofFile.subsOf Z)[l]? = some sub) (i : Nat)
    (hk : (VerifiableInference.Desc.First.kindsBeforeBatching sub (l == 0))[i]? = some KindName.K1)
    (hi : 2 ≤ i + 1 ∧ i + 1 ≤ 9) :
    ∃ Lk b, c.links[l]? = some Lk ∧ Lk.hear[i]? = some b ∧ ∀ ft s s', StepYes ft b s s' →
      K1KeepsAt { chain := 1, link := some l, piece := i + 1, kind := .K1 } s s' := by
  obtain ⟨Lk, b, Xl, pr, pd, reads, digits, e1, e2, -, hn, h⟩ := IM.k1_later O l sub hl i hk hi
  refine ⟨Lk, b, e1, e2, fun ft s s' y => ?_⟩
  rcases h with ⟨e, hla⟩ | ⟨e, hla⟩
  · have k := k1_reads_member hla y
    rcases IM.numbers_pieces hn with ⟨h4, -⟩ | ⟨h5, -⟩
    · obtain rfl : i = 3 := by omega
      exact k
    · obtain rfl : i = 4 := by omega
      exact k
  · have k := k1_commit_member hla y
    rcases IM.numbers_pieces hn with ⟨-, h6⟩ | ⟨-, h7⟩
    · obtain rfl : i = 5 := by omega
      exact k
    · obtain rfl : i = 6 := by omega
      exact k

/-- **THE ARM "first" AT LINK 0: THE KIND's HALF**: an accepting step of the lot's own sub-protocol
at the first segment's opening's place. -/
theorem k1_first_half {Z : ProofFile.Pub} {G₀ : ProofFile.Ground} {b' : Block S ProofFile.Cl}
    (lot : ∃ L ∈ ProofFile.onlineFirstChainBlockTables Z, b' ∈ L.blocks G₀)
    (hp : b'.place = { chain := 1, link := some 0, piece := 1, kind := .K1 })
    {ft : Nat} {s t : S} (y : StepYes ft b' s t) : K1FirstKeeps s t ∧ K1Out s t := by
  obtain ⟨rs, gs, d⟩ := stepYes_decide y
  obtain ⟨L, hL, hb⟩ := lot
  obtain ⟨x, hx, rfl⟩ := IM.lot_K1 hL hb (by rw [hp]) (l := 0) (by rw [hp])
  rcases IM.k1_mem hx with rfl | ⟨l', X, pr, pd, reads, digits, -, hn, rfl | rfl⟩
  · have d' : (VerifiableInference.Desc.K1.firstSegmentOpening G₀.first
        (VerifiableInference.Desc.K1.gpOf Z) : Block S Unit).decide s rs gs = .ok t := d
    exact ⟨k1_first_keeps d', k1_first_out d'⟩
  · have e : pr = 1 := congrArg Place.piece hp
    rcases IM.numbers_pieces hn with ⟨h4, -⟩ | ⟨h5, -⟩ <;> omega
  · have e : pd = 1 := congrArg Place.piece hp
    rcases IM.numbers_pieces hn with ⟨-, h6⟩ | ⟨-, h7⟩ <;> omega

/-- **THE ARM "back" AT W's PLACE: THE KIND's HALF**: a return of the lot's sub-protocol there is a
return of K1's sending, and then a return of K13's step behind it. -/
theorem k1_send_half {Z : ProofFile.Pub} {G₀ : ProofFile.Ground} {b' : Block S ProofFile.Cl}
    (lot : ∃ L ∈ ProofFile.onlineFirstChainBlockTables Z, b' ∈ L.blocks G₀)
    (hp : b'.place = { chain := 1, link := none, piece := 4, kind := .K1 })
    {s s' : S} {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (d : b'.decide s rs gs = .ok s') :
    ∃ m rs₂ gs₂, K1SendKeeps s m ∧
      (VerifiableInference.Desc.K13.rowsB VerifiableInference.Desc.K13.atS
        (VerifiableInference.Desc.K13.whereOf Z) : Block S Unit).decide m rs₂ gs₂ = .ok s' := by
  obtain ⟨L, hL, hb⟩ := lot
  obtain ⟨-, w, hw, rfl⟩ := IM.lot_M4 hL hb (by rw [hp]) (by rw [hp])
  unfold VerifiableInference.Desc.K13.wBlock VerifiableInference.Desc.K1.wAt at hw
  obtain ⟨msg, -, rfl⟩ := Option.map_eq_some_iff.1 hw
  obtain ⟨m, h1, h2⟩ := VerifiableInference.Desc.Keeps.ebind_ok d
  exact ⟨m, _, _, k1_send_keeps h1, h2⟩

end ProofFile.Honest.K1
