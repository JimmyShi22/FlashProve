-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/Law/GrowsOfAllSay.lean: FROM
"EVERY ROW THAT THE PROXIMITY TEST TAKES IN SAYS ITS CLAIM OF THE WORDS" TO "EVERY OPEN ROW OF THE
GROUP, AND EVERY SAMPLE ROW OF A MEMBER, HOLDS": from the conclusion of the kind K12's law (AllSay
at the begun statement, on runRows) to the sentence that a table in other files closes at a key
file's proximity test (its item "grows"). General in the statement, the group and its members.

Main names:
  off_members: a row that has passed the adding's tests reads as 0 on every message that is no
    member of its group.
  says_members: Says at two families of words that agree on the members' tables.
  says_own: Says at the begun statement gives Says at the statement itself.
  run_holds: EVERY ROW THAT THE TEST TAKES IN (runRows) HOLDS, at any reading val that agrees with
    the words on the members' tables.
  holds_of_allSay: so the open rows and the members' sample rows hold.
  grows_of_allSay: the item "grows" of meaning₁ (Johnson/Desc/Key/KeyMeaning.lean).

TWO PREMISES THAT STAY. hval: the words are what val reads, on the members' tables: at the table's
own reading valOf K R w that is a fact on its letter R. OpenKinds (no open row is marked as a sample
row): spent by holds_of_allSay and grows_of_allSay alone, for "an open row is among the rows taken
in" (open_taken); run_holds does not spend it.
That a row reads as 0 off the statement's tables is no premise: it comes off InOrder.

Object: Means.AllSay, Slice.runRows, Slice.begun; RowHolds. User: none yet.
Limits. It closes no row. Nothing on soundness.

-/
import Johnson.RunOne.Law.TieRows
import Johnson.Desc.Means.Holds
import Johnson.Desc.Means.Order
import Johnson.Desc.K14.Law.Carry
import Johnson.Desc.K12.Law.OutK2
import Johnson.Desc.Key.KeyMeaning

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.Law.GrowsOfAllSay
open OnBytes OnBytes.Slice
open OnBytes.Model (Reading)
open OnBytes.Means (Words AllSay Says OpenKinds InOrder RowIn open_taken samples_taken)
open VerifiableInference.Desc (Grows grows_begun)
open VerifiableInference.Desc.Key (RowHolds OffTables rowHolds_iff_says offTables_of_rowIn
  sum_map_zero_of)

variable {S : Statement} {G : Group}

/-- A summand that fits its place is on a member of the group. -/
theorem member_of_placeOk {o : ℕ} {pt : Part} {vars index : ℕ}
    (h : Blk.placeOk S G o pt vars index = true) : o ∈ G.members.toList := by
  simp only [Blk.placeOk, Bool.and_eq_true] at h
  simpa using h.1.1.1

/-- **A row that has passed the adding's tests reads as 0 on every message that is no member.** -/
theorem off_members {r : Row} (h : RowIn S G r) {o : ℕ} (ho : o ∉ G.members.toList) (pt : Part)
    (i : ℕ) : Reading.gl.val (r.coefficient o pt i) = 0 := by
  have no : ∀ o', o' ∈ G.members.toList → o' ≠ o := by
    rintro o' h1 rfl
    exact ho h1
  rw [Row.coefficient_val, sum_map_zero_of, sum_map_zero_of, sum_map_zero_of, sum_map_zero_of]
  · simp
  · intro f hf
    exact if_neg fun e => no f.oracle (member_of_placeOk (h.forms f hf).1) e.1
  · intro w hw
    exact if_neg fun e => no w.oracle (member_of_placeOk (h.runs w hw).2.2) e.1
  · intro u hu
    exact if_neg fun e => no u.oracle (member_of_placeOk (h.units u hu)) e.1
  · intro t ht
    exact if_neg fun e => no t.oracle (member_of_placeOk (h.terms t ht)) e.1

/-- **Says at two families of words that agree on the members' tables.** -/
theorem says_members {r : Row} (hr : RowIn S G r) (w w' : Words GE)
    (h : ∀ o ∈ G.members.toList, ∀ pt, ∀ i < Means.tableSize S o pt, w o pt i = w' o pt i) :
    Says Reading.gl S r w ↔ Says Reading.gl S r w' := by
  unfold Means.Says Means.value
  have one : ∀ o pt,
      Means.onTable Reading.gl S r w o pt = Means.onTable Reading.gl S r w' o pt := by
    intro o pt
    unfold Means.onTable
    refine Finset.sum_congr rfl fun i hi => ?_
    by_cases ho : o ∈ G.members.toList
    · rw [h o ho pt i (Finset.mem_range.1 hi)]
    · rw [off_members hr ho pt i, zero_mul, zero_mul]
  rw [Finset.sum_congr rfl fun o _ => by rw [one o .main, one o .mask]]

/-- Says at the begun statement gives Says at the statement itself: the beginning brings no message
and turns no table's size. -/
theorem says_own (g : ℕ) (G0 : Group) (r : Row) (W : Words GE)
    (h : Says Reading.gl (begun S g G0) r W) : Says Reading.gl S r W := by
  unfold Means.Says at h ⊢
  have e : Means.value Reading.gl (begun S g G0) r W = Means.value Reading.gl S r W := by
    unfold Means.value
    rw [show (begun S g G0).oracles.size = S.oracles.size from H2K.Out.closeLedgers_size _ _]
    refine Finset.sum_congr rfl fun o ho => ?_
    unfold Means.onTable
    rw [_root_.Desc.K14.Law.tableSize_grows S (begun S g G0) (grows_begun _ _ _) o
        (Finset.mem_range.1 ho),
      _root_.Desc.K14.Law.tableSize_grows S (begun S g G0) (grows_begun _ _ _) o
        (Finset.mem_range.1 ho)]
  rw [← e]
  exact h

/-- **EVERY ROW THAT THE TEST TAKES IN HOLDS.** No premise on the open rows' kinds. -/
theorem run_holds (hI : InOrder S) {g : ℕ} {G0 : Group} (hG : S.groups[g]? = some G0)
    (W : Words GE) (h : AllSay Reading.gl (begun S g G0) (runRows S G0).toList W)
    (val : ℕ → Part → ℕ → E)
    (hval : ∀ o ∈ G0.members.toList, ∀ pt, ∀ i < Means.tableSize S o pt,
      W o pt i = readE (val o pt i)) :
    ∀ r ∈ (runRows S G0).toList, RowHolds (fun a b => readE a = readE b) S val r := fun r hm =>
  (rowHolds_iff_says Reading.gl S val r
    (offTables_of_rowIn Reading.gl S G0 r (hI.runRows g G0 hG r hm))).2
      ((says_members (hI.runRows g G0 hG r hm) W _ hval).1 (says_own g G0 r W (h r hm)))

/-- **The open rows and the members' sample rows hold.** -/
theorem holds_of_allSay (hI : InOrder S) (hK : OpenKinds S) {g : ℕ} {G0 : Group}
    (hG : S.groups[g]? = some G0) (W : Words GE)
    (h : AllSay Reading.gl (begun S g G0) (runRows S G0).toList W) (val : ℕ → Part → ℕ → E)
    (hval : ∀ o ∈ G0.members.toList, ∀ pt, ∀ i < Means.tableSize S o pt,
      W o pt i = readE (val o pt i)) :
    (∀ r ∈ G0.rows.toList, RowHolds (fun a b => readE a = readE b) S val r) ∧
      ∀ o ∈ G0.members.toList, ∀ x, S.oracles[o]? = some x →
        ∀ r ∈ x.sampleRows.toList, RowHolds (fun a b => readE a = readE b) S val r := by
  have key := run_holds hI hG W h val hval
  exact ⟨fun r hr => key r (open_taken hK g G0 hG r hr),
    fun o ho x hx r hr => key r (samples_taken S G0 ho hx r hr)⟩

open VerifiableInference.Desc (Strs Wit) in
open VerifiableInference.Desc.Key (KPlan KRead KReaders meaning₁ valOf) in
/-- **The item "grows".** -/
theorem grows_of_allSay {P St Cells M : Type} (K : KPlan) (R : KRead Cells M) (X : KReaders St)
    (near : ℕ → P × St → Strs → Prop)
    (forms worth other : ℕ → String → P × St → Strs → Wit Cells Unit M → Prop) (a : P × St)
    (y : Strs) (w : Wit Cells Unit M) (g : ℕ) (G0 : Group) (o : ℕ) (x : Oracle)
    (hg : X.grpB a.2 = some g) (hG : (X.st a.2).groups[g]? = some G0) (ho : K.orc 1 = some o)
    (hx : (X.st a.2).oracles[o]? = some x) (hne : G0.rows.size ≠ 0)
    (hm : o ∈ G0.members.toList) (hsame : R.same = fun a b => readE a = readE b)
    (hI : InOrder (X.st a.2)) (hK : OpenKinds (X.st a.2)) (W : Words GE)
    (h : AllSay Reading.gl (begun (X.st a.2) g G0) (runRows (X.st a.2) G0).toList W)
    (hval : ∀ o ∈ G0.members.toList, ∀ pt, ∀ i < Means.tableSize (X.st a.2) o pt,
      W o pt i = readE (valOf K R w o pt i)) :
    (meaning₁ K R X near forms worth other).grows a y w := by
  obtain ⟨h1, h2⟩ := holds_of_allSay hI hK hG W h (valOf K R w) hval
  refine ⟨g, G0, o, x, hg, hG, ho, hx, hne, ?_, ?_⟩
  · rw [hsame]
    exact h1
  · rw [hsame]
    exact h2 o hm x hx

end Johnson.RunOne.Law.GrowsOfAllSay

#print axioms Johnson.RunOne.Law.GrowsOfAllSay.member_of_placeOk
#print axioms Johnson.RunOne.Law.GrowsOfAllSay.off_members
#print axioms Johnson.RunOne.Law.GrowsOfAllSay.says_members
#print axioms Johnson.RunOne.Law.GrowsOfAllSay.says_own
#print axioms Johnson.RunOne.Law.GrowsOfAllSay.run_holds
#print axioms Johnson.RunOne.Law.GrowsOfAllSay.holds_of_allSay
#print axioms Johnson.RunOne.Law.GrowsOfAllSay.grows_of_allSay
