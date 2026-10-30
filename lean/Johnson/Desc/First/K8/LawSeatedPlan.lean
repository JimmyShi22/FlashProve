-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/K8/LawSeatedPlan.lean: THE SMALLNESS TEST: "FIXED BEFORE THE DRAW", AT THE BLOCK
AS A SEAT LAYS IT; AND ALL ITS PREMISES FROM ONE TEST WITH CODE.

A MEND. Johnson/Desc/First/K8/LawPlaced.lean states the laws at the plan of a block b with
`Like seat p b`, and `Like` asks, among four fields, that b's DECISION is the kind's. A seat may lay
the kind's block with a guard behind its decision (`Guards`, Johnson/Desc/First/K8/LawSeated.lean):
that block's decision is another, so `Like` is false of it, and these laws speak of a block that
such a seat does not lay. Their proofs never read the decision. Here they stand under less:
  `LikeP seat p b`: b has the kind's declared rounds, its field `before` and its test on the plan.
    `Like.toP`; `likeP_guarded`: a block that guards the kind's block and keeps these two fields has
    it.
  `beforeAt_likeP`, `file_facts_likeP`, `file_before_draw_P`, `file_answers_before_draw_P`: the
    laws of LawPlaced.lean under `LikeP`: the same conclusions.
  `named_below_P`, `seats_below_P`: those of Johnson/Desc/First/K8/LawSeats.lean.
  `named_seats_below_P`: that of Johnson/Desc/First/K8/LawNamed.lean.
  `before_at_entry`, `arrays_before_at_entry`: THE SAME AT AN ENTRY OF THE FLAT LIST, by its number:
    the draw's round; every named message in front of it; the answers between; and, under
    `Named.namedB`, every array that the matrix multiplies.
  `before_of_test`: **a yes of the one test with code `beforeB F seat p i`**
    (Johnson/Desc/First/K8/SeatedPlan.lean) **gives all premises**: every message that the place
    names is sent strictly in front of the round of the draw.
Definitions, statements and proofs.
Limits. Those of LawPlaced.lean and LawSeats.lean. `beforeB` is shown true at no description of the
protocol here. Nothing on what the named trees hold.

-/
import Johnson.Desc.First.K8.LawNamed
import Johnson.Desc.First.K8.LawSeated
import Johnson.Desc.First.K8.SeatedPlan

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8

/-- The block b has the kind's rounds, field `before` and test on the plan. -/
structure LikeP {S Cl : Type} (seat : Seat S) (p : Par) (b : Block S Cl) : Prop where
  rounds : b.rounds = (approximateRangeProofDrawKind (Cl := Cl) seat p).rounds
  before : b.before = (approximateRangeProofDrawKind (Cl := Cl) seat p).before
  planOk : b.planOk = (approximateRangeProofDrawKind (Cl := Cl) seat p).planOk

theorem Like.toP {S Cl : Type} {seat : Seat S} {p : Par} {b : Block S Cl} (h : Like seat p b) :
    LikeP seat p b := ⟨h.rounds, h.before, h.planOk⟩

/-- A block that guards the kind's block at the carried record and keeps the two other fields. -/
theorem likeP_guarded {Cl : Type} {p : Par} {c : Block S Cl} (g : Guards c (approximateRangeProofDrawKind atS p))
    (hb : c.before = (approximateRangeProofDrawKind (Cl := Cl) atS p).before)
    (hp : c.planOk = (approximateRangeProofDrawKind (Cl := Cl) atS p).planOk) : LikeP atS p c := ⟨g.1, hb, hp⟩

/-- The test on the order reads a block's rounds and its field `before` alone. -/
theorem beforeAt_likeP {S Cl : Type} {seat : Seat S} {p : Par} {b : Block S Cl}
    (h : LikeP seat p b) (D : List Fmt.DeclaredRound × List Fmt.DeclaredRound × List Fmt.DeclaredRound)
    (O : List Oracle × List Oracle × List Oracle) (c : Nat) (post : List (Block S Cl)) :
    ∀ (pre : List (Block S Cl)) (from' : Nat),
      beforeAt D O c from' (pre ++ b :: post) = beforeAt D O c from' (pre ++ approximateRangeProofDrawKind seat p :: post)
  | [], from' => by
    simp only [List.nil_append, beforeAt, h.rounds, h.before]
  | a :: pre, from' => by
    simp only [List.cons_append, beforeAt, beforeAt_likeP h D O c post pre]

section
variable {Xi : Type} (F : FileDescription Xi) {seat : Seat F.S₁} {p : Par} {b : Block F.S₁ F.Cl}
  (h : LikeP seat p b) (pre post : List (Block F.S₁ F.Cl))
  (hflat : F.first.blocksInOrder = pre ++ b :: post) (hF : F.planOk = true)

include h hflat hF in
/-- What the file's one test on the plan gives at such a block. -/
theorem file_facts_likeP :
    beforeAt F.roundsDeclaredByBlocks (oraclesOf F.first.blocksInOrder, oraclesOf F.shared.blocksInOrder, oraclesOf F.second.blocksInOrder) 0 0
        (pre ++ approximateRangeProofDrawKind seat p :: post) = true ∧
      (approximateRangeProofDrawKind (Cl := F.Cl) seat p).planOk = true ∧ F.roundsDeclaredByBlocks.1[roundsIn pre]? = some (round p) := by
  simp only [FileDescription.planOk, FileDescription.planOkCore, Bool.and_eq_true] at hF
  have hbo : F.beforeOk = true := by tauto
  have hbl : blocksOk F.first.blocksInOrder = true := by tauto
  simp only [FileDescription.beforeOk, Bool.and_eq_true] at hbo
  have hb := hbo.1.1
  refine ⟨?_, ?_, ?_⟩
  · rw [← beforeAt_likeP h, ← hflat]
    exact hb
  · rw [hflat] at hbl
    simp only [blocksOk, List.all_eq_true, Bool.and_eq_true] at hbl
    rw [← h.planOk]
    exact (hbl b (by simp)).1
  · show (F.first.blocksInOrder.flatMap (·.rounds))[roundsIn pre]? = _
    rw [hflat, flatMap_rounds_at, h.rounds]
    rfl

include h hflat hF in
/-- **Every message that the place names is sent strictly in front of the round of the draw.** -/
theorem file_before_draw_P (n : Nat) (hn : n ∈ p.matsIn ++ p.readsIn) :
    ∃ i, sendRound F.roundsDeclaredByBlocks.1 n = some i ∧ i < roundsIn pre := by
  obtain ⟨h1, h2, h3⟩ := file_facts_likeP F h pre post hflat hF
  exact before_draw seat p F.roundsDeclaredByBlocks _ pre post h1 h2 h3 n hn

include h hflat hF in
theorem file_answers_before_draw_P (n : Nat) (hn : n ∈ p.matsIn ++ p.readsIn)
    (hs : ((oraclesOf F.first.blocksInOrder)[n]?).any (fun o => o.tenants.any (·.sampled)) = true) :
    ∃ i j r, sendRound F.roundsDeclaredByBlocks.1 n = some i ∧ F.roundsDeclaredByBlocks.1[j]? = some r ∧ r.entry.answers ≠ 0 ∧ i < j ∧
      j < roundsIn pre := by
  obtain ⟨h1, h2, h3⟩ := file_facts_likeP F h pre post hflat hF
  exact answers_before_draw seat p F.roundsDeclaredByBlocks _ pre post h1 h2 h3 n hn hs

include h hflat hF in
theorem named_below_P (n : Nat) (hn : n ∈ p.matsIn ++ p.readsIn) :
    n < rootsIn (F.roundsDeclaredByBlocks.1.take (roundsIn pre)) := by
  obtain ⟨i, h1, h2⟩ := file_before_draw_P F h pre post hflat hF n hn
  exact lt_of_lt_of_le (sendRound_lt _ _ _ h1) (rootsIn_take_mono _ _ _ h2)

include h hflat hF in
theorem seats_below_P (l : List (OnBytes.OracleShape × ℕ)) (seat' : Fin l.length → ℕ × ℕ)
    (hnamed : ∀ i, (seat' i).1 ∈ p.matsIn ++ p.readsIn) (i : Fin l.length) :
    (seat' i).1 < rootsIn (F.roundsDeclaredByBlocks.1.take (roundsIn pre)) :=
  named_below_P F h pre post hflat hF _ (hnamed i)

include h hflat hF in
theorem named_seats_below_P (rad : OnBytes.OracleShape → Nat) (S : OnBytes.Statement)
    (book : OnBytes.TreeBook) (tl : OnBytes.Model.HTailF2) (L : OnBytes.Model.LinkCtx)
    (hN : Named.namedB p S book tl L = true) (i : Fin (Named.listOf rad S book tl L).length) :
    (Named.seatFn rad S book tl L i).1 < rootsIn (F.roundsDeclaredByBlocks.1.take (roundsIn pre)) :=
  seats_below_P F h pre post hflat hF _ _ (Named.named_of_test hN rad) i

end

/-- The cut of a list at an entry. -/
theorem cut_at {α : Type} {l : List α} {i : Nat} {b : α} (hb : l[i]? = some b) :
    l = l.take i ++ b :: l.drop (i + 1) := by
  obtain ⟨hi, e⟩ := List.getElem?_eq_some_iff.1 hb
  rw [← e, List.getElem_cons_drop, List.take_append_drop]

/-- **At an entry of the first chain's flat list with `LikeP`**: the draw's round stands behind the
rounds of the entries in front; every message that the place names is sent strictly in front of it;
and where such a message has a sampled tenant a round with answers stands between. -/
theorem before_at_entry {Xi : Type} (F : FileDescription Xi) {seat : Seat F.S₁} {p : Par}
    {b : Block F.S₁ F.Cl} (h : LikeP seat p b) (i : Nat) (hb : F.first.blocksInOrder[i]? = some b)
    (hF : F.planOk = true) :
    F.roundsDeclaredByBlocks.1[roundsIn (F.first.blocksInOrder.take i)]? = some (round p) ∧
      (∀ n ∈ p.matsIn ++ p.readsIn,
        ∃ j, sendRound F.roundsDeclaredByBlocks.1 n = some j ∧ j < roundsIn (F.first.blocksInOrder.take i)) ∧
      ∀ n ∈ p.matsIn ++ p.readsIn,
        ((oraclesOf F.first.blocksInOrder)[n]?).any (fun o => o.tenants.any (·.sampled)) = true →
        ∃ j j' r, sendRound F.roundsDeclaredByBlocks.1 n = some j ∧ F.roundsDeclaredByBlocks.1[j']? = some r ∧ r.entry.answers ≠ 0 ∧
          j < j' ∧ j' < roundsIn (F.first.blocksInOrder.take i) :=
  ⟨(file_facts_likeP F h _ _ (cut_at hb) hF).2.2,
    fun n hn => file_before_draw_P F h _ _ (cut_at hb) hF n hn,
    fun n hn hs => file_answers_before_draw_P F h _ _ (cut_at hb) hF n hn hs⟩

/-- **Every array that the matrix multiplies lies in a message that is sent strictly in front of the
round of the draw**: under the test `Named.namedB`. -/
theorem arrays_before_at_entry {Xi : Type} (F : FileDescription Xi) {seat : Seat F.S₁} {p : Par}
    {b : Block F.S₁ F.Cl} (h : LikeP seat p b) (i : Nat) (hb : F.first.blocksInOrder[i]? = some b)
    (hF : F.planOk = true) (S₀ : OnBytes.Statement) (book : OnBytes.TreeBook)
    (tl : OnBytes.Model.HTailF2) (L : OnBytes.Model.LinkCtx)
    (hN : Named.namedB p S₀ book tl L = true) (t : Nat) (ht : t ∈ Named.arrays tl) :
    ∃ o m j, Named.msgNow L t = some o ∧ Named.memberAt S₀ book o = some m ∧
      sendRound F.roundsDeclaredByBlocks.1 m.2.1 = some j ∧ j < roundsIn (F.first.blocksInOrder.take i) := by
  obtain ⟨o, m, h1, _, h3, _, h5⟩ := Named.arrays_in_named hN ht
  obtain ⟨j, e, hj⟩ := (before_at_entry F h i hb hF).2.1 _ h5
  exact ⟨o, m, j, h1, h3, e, hj⟩

/-- **A yes of that test gives all premises.** -/
theorem before_of_test {Xi : Type} (F : FileDescription Xi) (seat : Seat F.S₁) (p : Par) (i : Nat)
    (h : beforeB F seat p i = true) (n : Nat) (hn : n ∈ p.matsIn ++ p.readsIn) :
    ∃ j, sendRound F.roundsDeclaredByBlocks.1 n = some j ∧ j < roundsIn (F.first.blocksInOrder.take i) := by
  unfold beforeB at h
  obtain ⟨hF, h⟩ := Bool.and_eq_true_iff.1 h
  cases hb : F.first.blocksInOrder[i]? with
  | none => simp [hb] at h
  | some b =>
    simp only [hb, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    exact file_before_draw_P F ⟨h1, h2, h3⟩ _ _ (cut_at hb) hF n hn

end VerifiableInference.Desc.First.K8

#print axioms VerifiableInference.Desc.First.K8.likeP_guarded
#print axioms VerifiableInference.Desc.First.K8.file_before_draw_P
#print axioms VerifiableInference.Desc.First.K8.file_answers_before_draw_P
#print axioms VerifiableInference.Desc.First.K8.seats_below_P
#print axioms VerifiableInference.Desc.First.K8.named_seats_below_P
#print axioms VerifiableInference.Desc.First.K8.before_at_entry
#print axioms VerifiableInference.Desc.First.K8.arrays_before_at_entry
#print axioms VerifiableInference.Desc.First.K8.before_of_test
