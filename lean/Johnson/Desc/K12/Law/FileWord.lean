-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import Johnson.Desc.K12.Law.FirstNeBook
import Johnson.Desc.RunLaws
/-
Johnson/Desc/K12/Law/FileWord.lean: THE PLAN's HALF OF THE ROW masks_fixed_word, FROM THE FILE's ONE TEST ON THE PLAN: FileDescription.planOk. Statements and proofs. NO SOUNDNESS IS CLAIMED. NOTHING ON HIDING.
  WordSays3 p b D c at': seat_word3's conclusion (FirstNeBook.lean), five conjuncts, as one proposition.
  plan_gives (over FileDescription.planOk_ok, Johnson/Desc/RunLaws.lean, and BookPlan.ok_clause): F.planOk = true ⇒ beforeAt's yes at each of the three flat lists · inOrderIn at each chain's declared rounds. (That every block of the flat lists passes its own test, and that F.roundsDeclaredByBlocks is F.plans, is IN THE LIBRARY: Keeps.planOk_blocks, Johnson/Desc/PlanPasses.lean; Sound.decl_of_planOk, Johnson/Desc/Sound/ReadsOkProofs.lean; both are fields of FileDescription.PlanOk too.)
  flat_rounds: (pre ++ b :: post).flatMap rounds = pre's rounds ++ (b.rounds ++ post's rounds), and pre's rounds are roundsIn pre many.
  word_at_list: seat_word3 at a flat list whose rounds are the chain's declared rounds: hDs | hlen are paid; hfree is said of pre's own rounds.
  file_word_first | file_word_shared | file_word_second: F.planOk = true · the chain's flat list = pre ++ b :: post · Keeps b (proximityTestKind guardedProximityTestParts p) · (proximityTestKind guardedProximityTestParts p).planOk = true · p.place.chain = 1 | 2 | 3 · free = rootsOf (pre.flatMap rounds) ⇒ WordSays3 p b F.roundsDeclaredByBlocks 0 | 1 | 2 (0 + roundsIn pre).
PREMISES LEFT: hk (SeatKeeps | MasksWord2 pay it for the wrappers named there) · hp (a seat's planOk holds the kind's: seat_planOk, AccKAtCourseAll.lean, at a seat as Chain.blocksInOrder lays it) · hc (p.place.chain: F.placesOk says it of b.place; Keeps says nothing of the place, and a driver stamps it: at a place made by proximityTestParametersAt P x it is P's own chain: the seat's literal) · hfree: ASKED BY NO TEST ON A PLAN.
Limits: as MasksWord2.lean's: trees and declared rounds' numbers, not words; for a tree taken from an earlier chain: «is sent», no order between chains; THE ROW ITSELF STAYS OWED.

-/
set_option autoImplicit false
namespace H2K.Made
open VerifiableInference.Desc VerifiableInference.Desc.K12
open VerifiableInference.Desc.BookPlan (inOrderIn)
open H2K.FixedBefore (foldStart)
open Johnson.G.OfPlan (rootsOf)

def WordSays3 {S Cl : Type} (p : P12) (b : Block S Cl)
    (D : List Fmt.DeclaredRound × List Fmt.DeclaredRound × List Fmt.DeclaredRound) (c at' : ℕ) : Prop :=
    (∀ o ∈ p.nums.first,
      (∃ n, o.2 = .own n ∧ n < p.nums.free ∧
        ∃ i, sendRound (chainOf D (c + 1)) n = some i ∧ i < at') ∨
      (∃ c' n, o.2 = .taken c' n ∧ c' ≤ c ∧ ∃ i, sendRound (chainOf D (c' + 1)) n = some i ∧
        (c' = c → i < at'))) ∧
    (p.nums.ownMask = true →
      sendRound (chainOf D (c + 1)) p.nums.free = some (at' + 1)) ∧
    (∀ s : Fmt.M1.Stage, 0 + 1 < p.nums.stages.length → p.nums.stages[0]? = some s →
      ∀ r ∈ (b.rounds.drop (foldStart 1 p.nums.stages 0 + 1 + s.k)).take 2, ∀ o ∈ r.opens,
        SentBy D c (at')
          (at' + (foldStart 1 p.nums.stages 0 + 1)) o) ∧
    (∀ (j : ℕ) (s s' : Fmt.M1.Stage), p.nums.stages[j]? = some s →
      j + 1 + 1 < p.nums.stages.length → p.nums.stages[j + 1]? = some s' →
      ∀ r ∈ (b.rounds.drop (foldStart 1 p.nums.stages (j + 1) + 1 + s'.k)).take 2, ∀ o ∈ r.opens,
        SentBy D c (at')
          (at' + (foldStart 1 p.nums.stages j + (s.k + 2))) o) ∧
    (∀ (j : ℕ) (s : Fmt.M1.Stage), p.nums.stages[j]? = some s → j + 2 = p.nums.stages.length →
      ∀ r ∈ (b.rounds.drop (foldStart 1 p.nums.stages (j + 1))).take 2, ∀ o ∈ r.opens,
        SentBy D c (at')
          (at' + (foldStart 1 p.nums.stages j + (s.k + 2))) o)

theorem plan_gives {Xi : Type} (F : FileDescription Xi) (hF : F.planOk = true) :
    (beforeAt F.roundsDeclaredByBlocks (oraclesOf F.first.blocksInOrder, oraclesOf F.shared.blocksInOrder, oraclesOf F.second.blocksInOrder) 0 0
        F.first.blocksInOrder = true ∧
      beforeAt F.roundsDeclaredByBlocks (oraclesOf F.first.blocksInOrder, oraclesOf F.shared.blocksInOrder, oraclesOf F.second.blocksInOrder) 1 0
        F.shared.blocksInOrder = true ∧
      beforeAt F.roundsDeclaredByBlocks (oraclesOf F.first.blocksInOrder, oraclesOf F.shared.blocksInOrder, oraclesOf F.second.blocksInOrder) 2 0
        F.second.blocksInOrder = true) ∧
    (inOrderIn 0 F.roundsDeclaredByBlocks.1 = true ∧ inOrderIn 1 F.roundsDeclaredByBlocks.2.1 = true ∧ inOrderIn 2 F.roundsDeclaredByBlocks.2.2 = true) := by
  have hP := (F.planOk_ok).1 hF
  have hbo := hP.before
  simp only [FileDescription.beforeOk, Bool.and_eq_true] at hbo
  have hio : BookPlan.inOrder F.roundsDeclaredByBlocks = true :=
    BookPlan.ok_clause (x := ("inOrder", BookPlan.inOrder F.roundsDeclaredByBlocks)) hP.book (by simp [BookPlan.clauses])
  simp only [BookPlan.inOrder, Bool.and_eq_true] at hio
  exact ⟨⟨hbo.1.1, hbo.1.2, hbo.2⟩, hio.1.1, hio.1.2, hio.2⟩

theorem flat_rounds {S Cl : Type} (pre : List (Block S Cl)) (b : Block S Cl)
    (post : List (Block S Cl)) :
    (pre ++ b :: post).flatMap (·.rounds) =
      pre.flatMap (·.rounds) ++ (b.rounds ++ post.flatMap (·.rounds)) := by
  rw [List.flatMap_append, List.flatMap_cons]

theorem word_at_list {S Cl : Type} (p : P12)
    (hp : (proximityTestKind guardedProximityTestParts p : Block T12 Unit).planOk = true)
    (b : Block S Cl) (hk : Keeps b (proximityTestKind guardedProximityTestParts p : Block T12 Unit))
    (D : List Fmt.DeclaredRound × List Fmt.DeclaredRound × List Fmt.DeclaredRound)
    (O : List Oracle × List Oracle × List Oracle) (c : ℕ) (pre post : List (Block S Cl))
    (hc : p.place.chain = c + 1) (h : beforeAt D O c 0 (pre ++ b :: post) = true)
    (hin : inOrderIn c (chainOf D (c + 1)) = true)
    (hdecl : chainOf D (c + 1) = (pre ++ b :: post).flatMap (·.rounds))
    (hfree : p.nums.free = rootsOf (pre.flatMap (·.rounds))) :
    WordSays3 p b D c (0 + roundsIn pre) :=
  seat_word3 p hp b hk D O c 0 pre post hc h hin (pre.flatMap (·.rounds))
    (post.flatMap (·.rounds)) (hdecl.trans (flat_rounds pre b post))
    ((length_flatMap_rounds pre).trans (Nat.zero_add _).symm) hfree

theorem file_word_first {Xi : Type} (F : FileDescription Xi) (hF : F.planOk = true) (p : P12)
    (hp : (proximityTestKind guardedProximityTestParts p : Block T12 Unit).planOk = true) (pre post : List (Block F.S₁ F.Cl))
    (b : Block F.S₁ F.Cl) (hflat : F.first.blocksInOrder = pre ++ b :: post)
    (hk : Keeps b (proximityTestKind guardedProximityTestParts p : Block T12 Unit)) (hc : p.place.chain = 1)
    (hfree : p.nums.free = rootsOf (pre.flatMap (·.rounds))) :
    WordSays3 p b F.roundsDeclaredByBlocks 0 (0 + roundsIn pre) := by
  obtain ⟨⟨h1, _, _⟩, i1, _, _⟩ := plan_gives F hF
  rw [hflat] at h1
  exact word_at_list p hp b hk F.roundsDeclaredByBlocks _ 0 pre post hc h1 i1
    (show F.first.blocksInOrder.flatMap (·.rounds) = _ by rw [hflat]) hfree

theorem file_word_shared {Xi : Type} (F : FileDescription Xi) (hF : F.planOk = true) (p : P12)
    (hp : (proximityTestKind guardedProximityTestParts p : Block T12 Unit).planOk = true) (pre post : List (Block F.S₂ F.Cl))
    (b : Block F.S₂ F.Cl) (hflat : F.shared.blocksInOrder = pre ++ b :: post)
    (hk : Keeps b (proximityTestKind guardedProximityTestParts p : Block T12 Unit)) (hc : p.place.chain = 2)
    (hfree : p.nums.free = rootsOf (pre.flatMap (·.rounds))) :
    WordSays3 p b F.roundsDeclaredByBlocks 1 (0 + roundsIn pre) := by
  obtain ⟨⟨_, h2, _⟩, _, i2, _⟩ := plan_gives F hF
  rw [hflat] at h2
  exact word_at_list p hp b hk F.roundsDeclaredByBlocks _ 1 pre post hc h2 i2
    (show F.shared.blocksInOrder.flatMap (·.rounds) = _ by rw [hflat]) hfree

theorem file_word_second {Xi : Type} (F : FileDescription Xi) (hF : F.planOk = true) (p : P12)
    (hp : (proximityTestKind guardedProximityTestParts p : Block T12 Unit).planOk = true) (pre post : List (Block F.S₃ F.Cl))
    (b : Block F.S₃ F.Cl) (hflat : F.second.blocksInOrder = pre ++ b :: post)
    (hk : Keeps b (proximityTestKind guardedProximityTestParts p : Block T12 Unit)) (hc : p.place.chain = 3)
    (hfree : p.nums.free = rootsOf (pre.flatMap (·.rounds))) :
    WordSays3 p b F.roundsDeclaredByBlocks 2 (0 + roundsIn pre) := by
  obtain ⟨⟨_, _, h3⟩, _, _, i3⟩ := plan_gives F hF
  rw [hflat] at h3
  exact word_at_list p hp b hk F.roundsDeclaredByBlocks _ 2 pre post hc h3 i3
    (show F.second.blocksInOrder.flatMap (·.rounds) = _ by rw [hflat]) hfree

end H2K.Made

#print axioms H2K.Made.plan_gives
#print axioms H2K.Made.word_at_list
#print axioms H2K.Made.file_word_first
#print axioms H2K.Made.file_word_shared
#print axioms H2K.Made.file_word_second
