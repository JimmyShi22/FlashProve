-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Thread/K1LaterRels.lean: six relations between the verifier's state
before and after a sending of oracle messages at a later moment of a segment (kind K1), as one
definition, and lemmas that show them from an accepting step. The clause of `keeps` that the authors
of K1's lemmas have written (`K1KeepsAt`, Honest/K1/Law/KeepsMember.lean) does not contain these
six. The open items `row m c` and `pile` need them to pass over such a sub-protocol (RowForward.lean,
PileForward.lean, RowPileForwardKinds.lean). The file depends on the sealed library alone.

  1  `K1LaterRels`   the definition
  2  `newTrees_booked`   what the library's `K1.Booked` gives for the fifth relation
  3  `rels_commitAtS`, `rels_joined`, `rels_later`   an accepting decision on two rounds gives the
     six: for the sending alone, for the sending with a step without a round joined after it, and
     for the two sub-protocols of a segment's later places (`K1.Later`)
  4  `rels_commit_member`, `rels_reads_member`   the same from an accepting step (`StepYes`) of the
     sub-protocol as the first chain holds it (`IM.LaidAlone`)
  5  `rels_member_later`   wherever the description of the proof file is made (`IM.Open`): at every
     segment and every index after its first at which the segment's list of kinds has K1, the chain
     has a sub-protocol, and each of its accepting steps gives the six

Sources. Each relation is a lemma of the library for an accepting decision of the sending:
`K1.keepsOld_commitAtS` (Johnson/Desc/K1/Law/GoodSend5.lean), `K1.commitAtS_group` with
`K1.Joins.rowsKept` (GroupAtLater.lean, JoinsRows.lean), `K1.commitAtS_treesOlder`
(EarlierTreesUnchanged.lean), `K1.commitAtS_booked` (BookAtRecord.lean), `K1.commitAtS_rows`
(RowsAtCommit.lean). Three of the six are three of the four relations of the library's
`K1.LaterRows` (RowAtLater.lean). Parts 4 and 5 have the form of `k1_commit_member`,
`k1_reads_member` and `k1_member_later` (Honest/K1/Law/KeepsMember.lean).

Limits.
  * One direction: from an accepting step. That a sub-protocol accepts anywhere is not shown.
  * Nothing on K1's opening of the first segment or on the sending after the segments.
  * `K1LaterRels` is a definition. Nothing is claimed of it.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.K1.Law.RowAtLater
import Johnson.Desc.K1.Law.PileAtLater
import Johnson.Desc.K1.Law.TiedAtLater
import Johnson.Desc.K1.Law.BlocksAtLater
import Johnson.IMR.K1Seat
import Johnson.IMR.MemberPath

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Place KindName)
open VerifiableInference.Desc.First (S)
open OnBytes.Model.Stages (LinkH)
open Johnson.Desc.First.Walk.Tied (StepYes)

/-! ## 1 The definition -/

/-- What a sending at a later moment of a segment leaves, beside the kind's own clause: the older
messages stay; every group keeps its open rows; there is no new group; every tree that is there
stays; the place of a new message names a new tree; the pending rows stay. It is a definition: a
part of a clause of `keeps`. -/
def K1LaterRels (s s' : S) : Prop :=
  VerifiableInference.Desc.K1.OldMsgs s.st s'.st ∧
    (∀ (j : Nat) (G : OnBytes.Group), s.st.groups[j]? = some G →
      ∃ G' : OnBytes.Group, s'.st.groups[j]? = some G' ∧ G'.rows = G.rows) ∧
    s'.st.groups.size = s.st.groups.size ∧
    VerifiableInference.Desc.K1.TreesOlder s.book s'.book ∧
    (∀ o, s.book.place.size ≤ o → ∀ q, s'.book.place[o]? = some q → s.book.trees.size ≤ q.1) ∧
    s'.rows = s.rows

/-! ## 2 The fifth relation -/

/-- Where the library's `K1.Booked` holds, the place of a new message names a new tree. -/
theorem newTrees_booked {P : VerifiableInference.Desc.K1.Par} {bk bk' : OnBytes.TreeBook}
    {n n' : Nat} (hB : VerifiableInference.Desc.K1.Booked P bk n bk' n') :
    ∀ o, bk.place.size ≤ o → ∀ q, bk'.place[o]? = some q → bk.trees.size ≤ q.1 := by
  intro o ho q hq
  rw [hB.place, Array.getElem?_append_right ho, Array.getElem?_map] at hq
  obtain ⟨i, -, rfl⟩ := Option.map_eq_some_iff.1 hq
  exact Nat.le_add_right _ _

/-! ## 3 From an accepting decision on two rounds -/

section
variable {Cl : Type}

/-- The sending alone. -/
theorem rels_commitAtS (P : VerifiableInference.Desc.K1.Par) (link moment : Nat)
    (arrays : Option (List Nat)) {s s' : S} {r₁ r₂ : Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))}
    (h : (VerifiableInference.Desc.K1.commitAtS P link moment arrays : Block S Cl).decide s [r₁, r₂]
      gs = .ok s') : K1LaterRels s s' := by
  obtain ⟨L, -, hJ⟩ :=
    VerifiableInference.Desc.K1.commitAtS_group P link moment arrays s s' r₁ r₂ gs h
  exact ⟨VerifiableInference.Desc.K1.keepsOld_commitAtS P link moment arrays s s' _ gs h,
    hJ.rowsKept, hJ.size,
    VerifiableInference.Desc.K1.commitAtS_treesOlder P link moment arrays s s' r₁ r₂ gs h,
    newTrees_booked
      (VerifiableInference.Desc.K1.commitAtS_booked P link moment arrays s s' r₁ r₂ gs h),
    VerifiableInference.Desc.K1.commitAtS_rows P link moment arrays s s' _ gs h⟩

/-- The sending with a step joined after it that leaves the statement, the list of commitment trees
and the pending rows. -/
theorem rels_joined (P : VerifiableInference.Desc.K1.Par) (link moment : Nat)
    (arrays : Option (List Nat)) (nm : String) (q : Block S Cl)
    (hq : VerifiableInference.Desc.K1.QuietP q) {s s' : S} {r₁ r₂ : Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))}
    (h : (Block.andThen nm (VerifiableInference.Desc.K1.commitAtS P link moment arrays) q).decide s
      [r₁, r₂] gs = .ok s') : K1LaterRels s s' := by
  obtain ⟨s₁, gs₁, rs₂, gs₂, h1, h3⟩ :=
    VerifiableInference.Desc.K1.joined_yes P link moment arrays nm q s s' r₁ r₂ gs h
  obtain ⟨e1, e2, -, -, -, -, -, -, e9⟩ := hq _ _ _ _ h3
  unfold K1LaterRels
  rw [e1, e2, e9]
  exact rels_commitAtS P link moment arrays h1

end

/-- The two sub-protocols of a segment's later places. -/
theorem rels_later {B own : Block S Unit} (hB : VerifiableInference.Desc.K1.Later B own) {s s' : S}
    {r₁ r₂ : Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (h : B.decide s [r₁, r₂] gs = .ok s') : K1LaterRels s s' := by
  cases hB with
  | digits q gp l piece digits => exact rels_commitAtS _ l 2 digits h
  | reads Z G l X pr reads =>
    exact rels_joined _ l 1 reads _ _ (VerifiableInference.Desc.K1.quietP_orLoud _ _ _ G l X _) h

/-! ## 4 From an accepting step of the sub-protocol as the first chain holds it -/

/-- The sub-protocol of the digits. -/
theorem rels_commit_member {same : S → S → Bool} {b : Block S ProofFile.Cl} {q : Params.First}
    {gp : _root_.Desc.Plain.GPar} {l pc : Nat} {digits : Option (List Nat)} {name : String}
    {a : Place}
    (h : IM.LaidAlone same b
      (VerifiableInference.Desc.K1.laterAt q gp l pc 2 digits : Block S Unit).retype name a)
    {ft : Nat} {s s' : S} (y : StepYes ft b s s') : K1LaterRels s s' := by
  obtain ⟨R, c, -, e⟩ := y
  have hb : b = IM.seatedAs same
      (VerifiableInference.Desc.K1.laterAt q gp l pc 2 digits : Block S Unit).retype name a := h
  have hl : b.rounds.length = 2 := by
    rw [hb]
    rfl
  obtain ⟨r₁, r₂, gs, d⟩ := VerifiableInference.Desc.K1.yes_of_step b hl ft s s' R c c.length e
  obtain ⟨d', -⟩ := IM.alone_noMark h d
  have d'' : (VerifiableInference.Desc.K1.laterAt q gp l pc 2 digits : Block S Unit).decide s
      [r₁, r₂] gs = .ok s' := d'
  exact rels_later (.digits q gp l pc digits) d''

/-- The sub-protocol of the reads. -/
theorem rels_reads_member {same : S → S → Bool} {b : Block S ProofFile.Cl} {Z : ProofFile.Pub}
    {G : ProofFile.Ground} {l : Nat} {X : LinkH} {pr : Nat} {reads : Option (List Nat)} {name : String}
    {a : Place} (h : IM.LaidAlone same b (IM.k1Reads Z G l X pr reads).retype name a)
    {ft : Nat} {s s' : S} (y : StepYes ft b s s') : K1LaterRels s s' := by
  obtain ⟨R, c, -, e⟩ := y
  have hb : b = IM.seatedAs same (IM.k1Reads Z G l X pr reads).retype name a := h
  have hl : b.rounds.length = 2 := by
    rw [hb]
    exact VerifiableInference.Desc.K1.rounds_k1Reads Z G l X pr reads
  obtain ⟨r₁, r₂, gs, d⟩ := VerifiableInference.Desc.K1.yes_of_step b hl ft s s' R c c.length e
  obtain ⟨d', -⟩ := IM.alone_noMark h d
  have d'' : (IM.k1Reads Z G l X pr reads).decide s [r₁, r₂] gs = .ok s' := d'
  exact rels_later (.reads Z G l X pr reads) d''

/-! ## 5 At the description's own chain -/

/-- **Wherever the description of the proof file is made**: at every segment `l` and every index
`i` after its first at which the segment's list of kinds has K1, the chain has a sub-protocol, and
each of its accepting steps gives the six relations. -/
theorem rels_member_later {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray}
    {F : VerifiableInference.Desc.FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase}
    {base : List (Block S ProofFile.Cl)} {c : VerifiableInference.Desc.Chain S ProofFile.Cl}
    {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} (O : IM.Open o pol lay KL F Z Bs base c A B) (l : Nat)
    (sub : VerifiableInference.Desc.First.ModelPart) (hl : (ProofFile.subsOf Z)[l]? = some sub) (i : Nat)
    (hk : (VerifiableInference.Desc.First.kindsBeforeBatching sub (l == 0))[i]? = some KindName.K1)
    (hi : 2 ≤ i + 1 ∧ i + 1 ≤ 9) :
    ∃ Lk b, c.links[l]? = some Lk ∧ Lk.hear[i]? = some b ∧
      ∀ ft s s', StepYes ft b s s' → K1LaterRels s s' := by
  obtain ⟨Lk, b, Xl, pr, pd, reads, digits, e1, e2, -, -, h⟩ := IM.k1_later O l sub hl i hk hi
  refine ⟨Lk, b, e1, e2, fun ft s s' y => ?_⟩
  rcases h with ⟨-, hla⟩ | ⟨-, hla⟩
  · exact rels_reads_member hla y
  · exact rels_commit_member hla y

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.newTrees_booked
#print axioms ProofFile.Honest.FirstThread.rels_commitAtS
#print axioms ProofFile.Honest.FirstThread.rels_joined
#print axioms ProofFile.Honest.FirstThread.rels_later
#print axioms ProofFile.Honest.FirstThread.rels_commit_member
#print axioms ProofFile.Honest.FirstThread.rels_reads_member
#print axioms ProofFile.Honest.FirstThread.rels_member_later
