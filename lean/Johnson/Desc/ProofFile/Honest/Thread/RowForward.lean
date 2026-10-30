-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Thread/RowForward.lean: the open item `row m c` of the first chain's
invariant passes over a sub-protocol whose step adds oracle messages to the statement. The item
states that every row of one class of segment `m` holds of the witness's words (`rowSays`,
Johnson/Desc/First/Close/Law/FillRow.lean). RowPileRides.lean shows that it passes where the step
leaves the statement and the list of commitment trees as they were. That is false for a sending of
oracle messages (kind K1). No definition.

The library shows the opposite direction: what the item states after such a step it states before it
(`rowSays_back`, FillRow.lean; `rowSaysFirst_back`, FillRowRides.lean; `K1.row_back`,
Johnson/Desc/K1/Law/RowBack.lean). The two steps of that proof are equivalences, so the proofs of
part 1 below are those proofs read in the other direction. One hypothesis turns round with them. The
library asks that the rows of the class before the step are among its rows after it. Here the rows
of the class after the step have to be among its rows before it: the step adds no row to the class.

  1  `rowSays_fwd`, `rowSaysFirst_fwd`   the item's statement passes from the state before the step
     to the state after it
  2  `classRows_sup`   the step adds no row to the class, from the library's `K1.RowKept` and two
     further facts: the statement has as many groups after the step as before it, and no new
     message has a place among the places of the class
  3  `rowKept_of_rels`, `noNew_of_trees`   `K1.RowKept` and the second of these facts, from plain
     relations between the two states and plain facts on the state before the step
  4  `row_older`   part 1 at the library's meaning `mgAll`
  5  `ridesPastAt_row_older`   the hypothesis `RidesPastAt` (Honest/Thread/Shares.lean) for the item
     at `lettersHead`, at every sub-protocol number `b`

The hypothesis of 5 may use the invariant before the step (`Thr`).

Limits.
  * Part 5: full size only, and only under the library's hypothesis `AtMgA` at the hash function
    `secondHashFunction` (FirstAt.lean says which that is).
  * The hypotheses on the two states have to be shown for each kind. This file shows them for no
    kind and at no state.
  * The witness is the same before and after the step.
  * Nothing here shows that the item's statement holds at any state of a run.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.FirstHead
import Johnson.Desc.ProofFile.Honest.Thread.Shares
import Johnson.Desc.K1.Law.RowAtStep
import Johnson.IMR.BookFitsSeat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Chain Strs Wit Place)
open VerifiableInference.Desc.First (S Item Numbers RowClass Meaning classRows rowSays wordsAtFirst
  BookKept classRows_in says_congr wordsFirst_older)
open VerifiableInference.Desc.K1 (RowKept OldMsgs TreesOlder)
open VerifiableInference.Desc.Sound (MsgT MgData mgAll mgBase mgAll_row CellsQ)
open OnBytes.Means (Words InOrder Extends tableSize says_extends)
open OnBytes.Slice (GE rdE)
open OnBytes.Maker (WholeD)
open Meaning.K2 (PlacesStay)
open P5J (AtMgA CellsM TS F0T)

/-! ## 1 The item's statement passes forward -/

section
variable {P W : Type}

/-- What the item states before the step it states after it, if the statement before the step is in
order, the statement after it extends it, the step adds no row to the class, and the reader gives
the same words at the messages of the statement before the step, below their tables' sizes. -/
theorem rowSays_fwd (N : Numbers) (words : P × S → Strs → W → Words GE) (m : Nat) (c : RowClass)
    (a b : P × S) (y y' : Strs) (w w' : W) (hI : InOrder a.2.st) (hE : Extends a.2.st b.2.st)
    (hsup : ∀ r ∈ classRows N m c b.2, r ∈ classRows N m c a.2)
    (hw : ∀ o, o < a.2.st.oracles.size → ∀ part i, i < tableSize a.2.st o part →
      words b y' w' o part i = words a y w o part i)
    (h : rowSays N words m c a y w) : rowSays N words m c b y' w' := by
  intro r hr
  obtain ⟨G, hG⟩ := classRows_in N m c a.2 hI r (hsup r hr)
  exact (says_extends rdE hE hG _).2 ((says_congr a.2.st r _ _ hw).2 (h r (hsup r hr)))

end

section
variable {P Cells Tok : Type}

/-- The same at the first chain's reader of the witness's words, if every message of the statement
before the step keeps its place in the list of commitment trees, and the tree there. -/
theorem rowSaysFirst_fwd (arr : ℕ → ℕ → ℕ) (N : Numbers) (m : Nat) (c : RowClass) (a b : P × S)
    (y y' : Strs) (w : Wit Cells Tok MsgT) (hI : InOrder a.2.st) (hE : Extends a.2.st b.2.st)
    (hsup : ∀ r ∈ classRows N m c b.2, r ∈ classRows N m c a.2) (hB : BookKept a.2 b.2)
    (h : rowSays N (wordsAtFirst arr) m c a y w) : rowSays N (wordsAtFirst arr) m c b y' w := by
  refine rowSays_fwd N (wordsAtFirst arr) m c a b y y' w w hI hE hsup (fun o ho part i _ => ?_) h
  obtain ⟨x', hx', e⟩ := hE.shape o _ (Array.getElem?_eq_getElem ho)
  refine wordsFirst_older arr a.2.st b.2.st a.2.book b.2.book w o hE.codes ?_ (hB o ho).1
    (hB o ho).2 part i
  rw [hx', Array.getElem?_eq_getElem ho, Option.map_some, Option.map_some, e]

end

/-! ## 2 The step adds no row to the class -/

/-- **The rows of a class after the step are among its rows before it.** `hz`: no new group.
`hNew`: at a class of sample rows, no new message has a place among the places of the class. -/
theorem classRows_sup (N : Numbers) (m : Nat) (c : RowClass) {s s' : S} (hK : RowKept s s')
    (hz : s'.st.groups.size = s.st.groups.size)
    (hNew : ∀ t, c = .sample t → ∀ o, s.st.oracles.size ≤ o → ∀ x, s'.book.place[o]? = some x →
      x ∉ N.sent m t) :
    ∀ r ∈ classRows N m c s', r ∈ classRows N m c s := by
  intro r hr
  have list : ∀ a n : Nat, (r ∈ match s'.st.groups[N.groupAt m]? with
      | none => []
      | some G => (List.range n).filterMap fun j => G.rows[a + j]?) →
      r ∈ match s.st.groups[N.groupAt m]? with
      | none => []
      | some G => (List.range n).filterMap fun j => G.rows[a + j]? := by
    intro a n h0
    cases hG : s.st.groups[N.groupAt m]? with
    | none =>
      have hge : s'.st.groups.size ≤ N.groupAt m := by
        rw [hz]
        by_contra hn
        rw [Array.getElem?_eq_getElem (Nat.lt_of_not_le hn)] at hG
        cases hG
      rw [Array.getElem?_eq_none hge] at h0
      cases h0
    | some G =>
      obtain ⟨G', hG', e⟩ := hK.rows _ G hG
      rw [hG'] at h0
      show r ∈ (List.range n).filterMap fun j => G.rows[a + j]?
      rw [← e]
      exact h0
  cases c with
  | carried => exact list _ _ hr
  | position => exact list _ _ hr
  | equation => exact list _ _ hr
  | sample t =>
    obtain ⟨o, -, hr⟩ := List.mem_flatMap.1 hr
    split at hr
    · rename_i hpl
      by_cases hlt : o < s.st.oracles.size
      · cases hor : s'.st.oracles[o]? with
        | none =>
          rw [hor] at hr
          cases hr
        | some X' =>
          rw [hor] at hr
          have e := hK.msgs o hlt
          rw [hor] at e
          obtain ⟨X, hX, e⟩ := Option.map_eq_some_iff.1 e.symm
          refine List.mem_flatMap.2 ⟨o, List.mem_range.2 hlt, ?_⟩
          rw [← hK.place o hlt, if_pos hpl, hX]
          show r ∈ X.sampleRows.toList
          rw [(Prod.mk.inj (Prod.mk.inj e).2).2]
          exact hr
      · exfalso
        cases hq : s'.book.place[o]? with
        | none =>
          rw [hq] at hpl
          cases hpl
        | some x =>
          rw [hq] at hpl
          have hc : (N.sent m t).contains x = true := hpl
          exact hNew t rfl o (Nat.le_of_not_lt hlt) x hq (List.contains_iff_mem.1 hc)
    · cases hr

/-! ## 3 From plain relations between the two states -/

/-- The library's `K1.RowKept`, from four relations between the two states and two facts on the
state before the step. It is the library's `K1.rowKept_of_step` with `PlacesStay` in the place of
`K1.Booked`, which has the sub-protocol's parameters as an argument. -/
theorem rowKept_of_rels {s s' : S} (hO : OldMsgs s.st s'.st)
    (hR : ∀ (j : Nat) (G : OnBytes.Group), s.st.groups[j]? = some G →
      ∃ G' : OnBytes.Group, s'.st.groups[j]? = some G' ∧ G'.rows = G.rows)
    (hP : PlacesStay s.book s'.book) (hT : TreesOlder s.book s'.book)
    (hn : s.book.place.size = s.st.oracles.size)
    (hold : ∀ (o : Nat) (x : Nat × Nat), s.book.place[o]? = some x → x.1 < s.book.trees.size) :
    RowKept s s' where
  codes := hO.1
  msgs := hO.2
  rows := hR
  place := fun o ho => hP o (by omega)
  trees := fun o q hq => hT q.1 (hold o q hq)

/-- No new message has a place among the places of the class, if every new message's place names a
new tree and every place of the class names a tree that is there before the step. -/
theorem noNew_of_trees (N : Numbers) (m t : Nat) {s s' : S}
    (hn : s.book.place.size = s.st.oracles.size)
    (hD : ∀ o, s.book.place.size ≤ o → ∀ x, s'.book.place[o]? = some x →
      s.book.trees.size ≤ x.1)
    (hF : ∀ x ∈ N.sent m t, x.1 < s.book.trees.size) :
    ∀ o, s.st.oracles.size ≤ o → ∀ x, s'.book.place[o]? = some x → x ∉ N.sent m t :=
  fun o ho x hx hm => absurd (hF x hm) (Nat.not_lt.2 (hD o (by omega) x hx))

/-! ## 4 At the library's meaning -/

section
variable {Xi P Tok : Type} {rows cols nR : Nat} {X : OnBytes.Model.Verify.Public}
  (𝔇 : MgData Xi P Tok rows cols nR X) (Mg : Meaning P (Wit (CellsQ rows cols) Tok MsgT))
  {s s' : S}

/-- The statement of `row m c` passes from `s` to `s'`. -/
theorem row_older (hI : InOrder s.st) (hK : RowKept s s') (m : Nat) (c : RowClass)
    (hsup : ∀ r ∈ classRows 𝔇.N m c s', r ∈ classRows 𝔇.N m c s) (z : P) (y y' : Strs)
    (w : Wit (CellsQ rows cols) Tok MsgT) (h0 : (mgAll 𝔇 Mg).row m c (z, s) y w) :
    (mgAll 𝔇 Mg).row m c (z, s') y' w := by
  rw [mgAll_row] at h0 ⊢
  exact rowSaysFirst_fwd 𝔇.arr 𝔇.N m c (z, s) (z, s') y y' w hI hK.extends hsup hK.bookKept h0

end

/-! ## 5 At the invariant -/

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

/-- The item `row m c` passes over sub-protocol `b` if, wherever the invariant holds before the
step, the statement is in order, the step leaves what `K1.RowKept` lists, and it adds no row to the
class. -/
theorem ridesPastAt_row_older {b : Nat} (m : Nat) (c : RowClass)
    (hk : ∀ k s mm E s',
      Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread b k s mm E →
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.keeps b s s' →
      InOrder s.st ∧ RowKept s s' ∧ ∀ q ∈ classRows h.𝔇.N m c s', q ∈ classRows h.𝔇.N m c s) :
    RidesPastAt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread b
      (Item.row m c) := by
  intro k s mm E s' ps v hA hK h0
  obtain ⟨hI, hR, hsup⟩ := hk k s mm E s' hA hK
  exact row_older { h.𝔇 with decT := fun _ _ => some (Q.cells mm.st.input), cr1 := carryX } mgBase
    hI hR m c hsup mm.st.input.x.pub
    ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.strs E)
    ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.strs (E.add ps)) v h0

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.rowSays_fwd
#print axioms ProofFile.Honest.FirstThread.rowSaysFirst_fwd
#print axioms ProofFile.Honest.FirstThread.classRows_sup
#print axioms ProofFile.Honest.FirstThread.rowKept_of_rels
#print axioms ProofFile.Honest.FirstThread.noNew_of_trees
#print axioms ProofFile.Honest.FirstThread.row_older
#print axioms ProofFile.Honest.FirstThread.ridesPastAt_row_older
