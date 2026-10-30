-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Tw/K2C/ThreeTogether.lean: code switching: THE THREE PREMISES OF THE THIRD TIE AT A
PLACE THAT COUNT TREES FOLLOW TOGETHER FROM ONE LIST OF PREMISES, AT ONE N, ONE PLACE, ONE STATE AND
ONE seatN := seatNew N m r: (1) hS, the premise of hAt's field «seats» (the tree's NUMBER,
p.firstTree + t.roots) · (2) the field «sent» of what is owed on the numbers (K2.LinkDebts |
K2.SwitchDebts: the tree's PLACE IN THE BOOK, t.book.trees.size) · (3) M (K2.MembersLike against
N.sent (m + 1) 0). THE FIND: they can be met together only where
t.book.trees.size = p.firstTree + t.roots. Theorems with their proofs. NO
SUB-PROTOCOL IMPORTS THIS FILE.
  len_of_tests     the two tests give r.l.length = sent.size - 1: so SentByPlace.lean's hl falls
  frontOf_of_at    K2.frontAt p s = some x gives K2.FrontOf p s x (the converse of
                   K2.frontAt_of, Tw/K2C/HeldAtYes.lean): so hF here and the first two clauses of
                   K2.Fence are one sentence
  three_together   the three, at every front under the table of joints' promise, Rch and «no mark»,
                   with the front's layout in hand; (2) at n := the notices' count less one, at
                   n := 1 + kept + own and, where p stands at the finish, at n := 1 + kept: one
                   number, whichever of the three a payer of the debts lays
FROM: two tests on public data at ONE pIn := ps[k]? (sentPlaceB · membersPlanB) · hlay (closed) · hF
(two clauses of K2.Fence at the front) · h0 · hen · hBook (Tw/K2C/ThreeCounts.lean's three).
CALLED: hS_seatNew · sentFit_of_place (SentByPlace.lean) · hbase_at_place (ThreeCounts.lean; over
counts_one's second equation) · membersLike_plan (OneSeat.lean) · K2.sent_of_test ·
K2.count_of_front · K2.count_finish (Tw/K2C/SentAtPlan.lean) · K1.bookAt_of_onAt
(Johnson/Desc/K1/Law/SmpNamedEarlierMessages.lean). (1) AND (2) EACH GO TO N.treesAt ps[k]? ON A ROAD OF THEIR
OWN: (2) spends neither h0 nor hBook; counts_one's first equation, the one of the find, is their
corollary and is spent by nothing. That (2) IS the structures' field: Lean's comparison in
Johnson/Loose/PVK2/OneSeatFits.lean.
LIMITS. It shows that the three do not shut each other out FOR THE REASON FOUND: no state is shown
to meet the promise and Rch; the tests' values are premises (evaluated at the stored full-size
example: the files named in SentByPlace.lean and others on the members). The debts'
five other fields are not spoken of. Nothing on hσ, hseat, the letter base. No soundness is claimed.
On hiding nothing.
-/
import Johnson.Top.H0.Tw.K2C.ThreeCounts
import Johnson.Top.H0.Tw.K2C.SentByPlace
import Johnson.Top.H0.Tw.K2C.OneSeat
import Johnson.Top.H0.Tw.K2C.SentAtPlan
import Johnson.Desc.K1.Law.SmpNamedEarlierMessages

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Caller
open OnBytes
open VerifiableInference.Desc (Wit MemberLists)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (ModelPart Item Meaning Numbers sameMembers)
open VerifiableInference.Desc.First.K2Hands
open VerifiableInference.Desc.K12.Door (atFirstBook)
open _root_.Tw.K2 (switchNotices)

/-- The two tests give the typed list's length. -/
theorem len_of_tests {N : Numbers} {m : ℕ} {pIn : Option VerifiableInference.Desc.Place}
    {codes : Codes} {sent : Array OracleNotice} {lay₀ : TreeLay} {L : MemberLists}
    {kq : List (ℕ × ℕ)} {r : SwRow} (h : sentPlaceB N (m + 1) pIn codes sent = true)
    (hlay : layTrees codes sent = some lay₀)
    (hB : membersK2B L kq (N.sent (m + 1) 0) r = true) : r.l.length = sent.size - 1 := by
  unfold membersK2B at hB
  rw [Bool.and_eq_true] at hB
  rw [← beq_iff_eq.1 hB.2, sent_of_place h hlay, List.length_map, List.length_range]

/-- The two ways of naming the front that a code switch takes off a state are one: the converse. -/
theorem frontOf_of_at {p : K2.P2} {s : Rec} {x : _root_.Tw.K2.Front}
    (h : K2.frontAt p s = some x) : K2.FrontOf p s x := by
  unfold K2.frontAt at h
  split at h
  · rename_i hp
    refine Or.inl ⟨hp, ?_⟩
    cases hf : _root_.Tw.K2.firstFront s.st s.check.frame with
    | error e =>
      rw [hf] at h
      cases h
    | ok y =>
      rw [hf] at h
      exact congrArg Except.ok (Option.some.inj h)
  · rename_i a hp ha
    obtain ⟨G, hG, e⟩ := Option.map_eq_some_iff.1 h
    exact Or.inr (Or.inl ⟨hp, a, G, ha, hG, e.symm⟩)
  · rename_i a hp ha
    obtain ⟨G, hG, e⟩ := Option.map_eq_some_iff.1 h
    exact Or.inr (Or.inr ⟨hp, a, G, ha, hG, e.symm⟩)
  · cases h

/-- **The three hold together.** -/
theorem three_together {F : Frame} {P Cells Tok : Type} {r : SwRow} {N : Numbers} {m : ℕ}
    {codes : Codes} {sent : Array OracleNotice} {lay₀ : TreeLay} (p : K2.P2)
    (enter : Rec → Except String Rec) (Mg : Meaning P (Wit Cells Tok MsgT)) (links : List ModelPart)
    (ps : List VerifiableInference.Desc.Place) (z : P) (Rch : ℕ → Rec × F.E.Str → Prop) (k ft : ℕ)
    (Z : ProofFile.Pub) (rad : ℕ → ℕ → ℕ)
    (hPl : sentPlaceB N (m + 1) ps[k]? codes sent = true) (hlay : layTrees codes sent = some lay₀)
    (hB : membersPlanB Z rad N (m + 1) r = true)
    (hF : ∀ a, onQ N Mg links ps (fun s => (z, s)) k a → Rch k a → ¬ a.1.failed ≠ none →
      ∀ t, enter a.1 = .ok t → ∀ fx, K2.frontAt p t = some fx →
        switchNotices fx.T fx.others = sent ∧ fx.st.codes = codes)
    (h0 : p.firstTree = 0)
    (hen : ∀ s t, enter s = .ok t → t.book = s.book ∧ t.roots = s.roots)
    (hBook : ∀ a, onQ N Mg links ps (fun s => (z, s)) k a → Rch k a → ¬ a.1.failed ≠ none →
      ∀ t, enter a.1 = .ok t → atFirstBook ft t = true) :
    K2.MembersLike (P5T.msAtR Z rad) ⟨r.l, seatNew N m r⟩ (N.sent (m + 1) 0) ∧
    ∀ a, onQ N Mg links ps (fun s => (z, s)) k a → Rch k a → ¬ a.1.failed ≠ none →
      ∀ t, enter a.1 = .ok t → ∀ fx, K2.frontAt p t = some fx →
        ∀ lay, layTrees fx.st.codes (switchNotices fx.T fx.others) = some lay →
          (∀ i : Fin r.l.length, seatNew N m r i =
            (p.firstTree + (t.roots + lay.tree.getD i.val 0), lay.part.getD i.val 0)) ∧
          (∀ n, (n = (switchNotices fx.T fx.others).size - 1 ∨
              n = 1 + fx.T.kept.size + fx.own.length ∨
              (p.stands = .finish ∧ n = 1 + fx.T.kept.size)) →
            sameMembers ((List.range n).map fun i =>
              (t.book.trees.size + lay.tree.getD i 0, lay.part.getD i 0)) (N.sent (m + 1) 0) =
                true) := by
  refine ⟨membersLike_plan hB, fun a ha hrc hm t et fx hf lay hl => ⟨?_, fun n hn => ?_⟩⟩
  · exact hS_seatNew p enter Mg links ps z Rch k hPl hlay
      (Nat.le_of_eq (len_of_tests hPl hlay hB)) hF
      (hbase_at_place N Mg links ps z k p enter Rch ft h0 hen hBook) a ha hrc hm t et fx hf lay hl
  · have hb : VerifiableInference.Desc.First.bookAt N ps[k]? a.1 = true :=
      VerifiableInference.Desc.K1.bookAt_of_onAt N Mg links _ _ _ (z, a.1) _ ha (not_not.1 hm)
    have hx := frontOf_of_at hf
    have hk : n = (switchNotices fx.T fx.others).size - 1 := by
      rcases hn with e | e | ⟨hp, e⟩
      · exact e
      · exact e.trans (K2.count_of_front hx)
      · exact e.trans (K2.count_finish hp hx)
    rw [(hen a.1 t et).1]
    exact K2.sent_of_test (sentFit_of_place hPl) hb (hF a ha hrc hm t et fx hf).1
      (hF a ha hrc hm t et fx hf).2 hl hk

end VerifiableInference.Desc.First.K2Caller

#print axioms VerifiableInference.Desc.First.K2Caller.len_of_tests
#print axioms VerifiableInference.Desc.First.K2Caller.frontOf_of_at
#print axioms VerifiableInference.Desc.First.K2Caller.three_together
