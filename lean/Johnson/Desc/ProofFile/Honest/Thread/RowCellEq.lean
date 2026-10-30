-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Thread/RowCellEq.lean: an item `row m c` of the first chain's
invariant that is open before K9's "the one equation" passes over it, in each of the 25 segments.
`ridesPastAt_row_older` (RowForward.lean) does not apply there: it asks the library's `K1.RowKept`,
which says that every group keeps its list of open rows, and "the one equation" adds a row to the
list of the segment's group. `rowSaysFirst_fwd` (RowForward.lean) asks less: the statement is in order
before the step, the statement after it extends it, every message keeps its place and its tree, and
no row comes to the class. The last holds because the new row is added at the end of the list, and
the invariant's own test `rowsHeld` says that every place of an open class is there before the step.
No definition.

  1  `classRows_push_fwd`   every row of a class after a row is added at the end of a group's list
     is a row of the class before, if the places of the class are there before. The library's
     `classRows_push` (Johnson/Desc/First/Link/Law/FifthTieEq.lean) is the converse inclusion
  2  `eqKeeps_lays`   under K9's clause at "the one equation": one row is added to one group's list,
     there are as many messages as before, and each is the same but for its mask ledger
  3  `row_older_ext`   the statement of `row m c` passes from one state to another under the four
     conditions of `rowSaysFirst_fwd`
  4  `head_rowsHeld`   wherever the invariant holds, the test `rowsHeld` accepts
  5  `row_cell_eq`   **the cell**, at the numbers `14 * l + IM.nAt l + 4`

Limits.
  * Nothing shows that a clause of `keeps` holds at any step.
  * Items 4 and 5: full size only, under the library's `AtMgA` at the hash function `secondHashFunction`.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.PileCellsEqK7
import Johnson.Desc.ProofFile.Honest.Thread.RowForward
import Johnson.Desc.ProofFile.Honest.Thread.FormXK
import Johnson.Desc.First.Link.Law.CountsOfHeld
import Johnson.Desc.First.Batch.Law.Door
import Johnson.Desc.First.Batch.Law.DoorFacts
import Johnson.Desc.First.Batch.Law.Hout

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Chain Strs Wit Place KindName)
open VerifiableInference.Desc.First (S Item Numbers RowClass Meaning classRows BookKept rowsHeld
  mem_rowSegs)
open VerifiableInference.Desc.Sound (MsgT MgData mgAll mgBase mgAll_row CellsQ)
open VerifiableInference.Desc.LinkJoin (door_both part_reads bare_blind held_at)
open VerifiableInference.Desc.K9L (door_parts asRow_groups asRow_size)
open ProofFile.Honest.K9 (EqKeeps k9KeepsAt)
open OnBytes.Means (InOrder Extends)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)

/-! ## 1 A row more at the end of a list -/

/-- Every row of a class after the step is a row of the class before it. `hth`: the places of a
class that lies in the list are there before the step. -/
theorem classRows_push_fwd (N : Numbers) (m : Nat) (c : RowClass) {s t : S} (g : Nat)
    (row : OnBytes.Row)
    (hg : t.st.groups = s.st.groups.modify g fun G => { G with rows := G.rows.push row })
    (hsz : t.st.oracles.size = s.st.oracles.size) (hbk : t.book = s.book)
    (hm : ∀ i : Nat, (t.st.oracles[i]?).map VerifiableInference.Desc.LinkJoin.bare =
      (s.st.oracles[i]?).map VerifiableInference.Desc.LinkJoin.bare)
    (hth : c.inList = true → ∀ G, s.st.groups[N.groupAt m]? = some G →
      ∀ j, j < (N.rowsAt m c).2 → (N.rowsAt m c).1 + j < G.rows.size) :
    ∀ r ∈ classRows N m c t, r ∈ classRows N m c s := by
  have hsm : ∀ o : Nat, (t.st.oracles[o]?).map (fun a : OnBytes.Oracle => a.sampleRows.toList) =
      (s.st.oracles[o]?).map (fun a : OnBytes.Oracle => a.sampleRows.toList) := by
    intro o
    have h1 := congrArg (Option.map fun a : OnBytes.Oracle => a.sampleRows.toList) (hm o)
    rw [Option.map_map, Option.map_map] at h1
    exact h1
  have list : ∀ (st n : Nat),
      (∀ G, s.st.groups[N.groupAt m]? = some G → ∀ j, j < n → st + j < G.rows.size) →
      ∀ r : OnBytes.Row,
      r ∈ (match t.st.groups[N.groupAt m]? with
        | none => []
        | some G => (List.range n).filterMap fun j => G.rows[st + j]?) →
      r ∈ (match s.st.groups[N.groupAt m]? with
        | none => []
        | some G => (List.range n).filterMap fun j => G.rows[st + j]?) := by
    intro st n hth' r hr
    rw [hg, Array.getElem?_modify] at hr
    cases hG : s.st.groups[N.groupAt m]? with
    | none =>
      rw [hG] at hr
      by_cases hi : g = N.groupAt m
      · rw [if_pos hi] at hr
        cases hr
      · rw [if_neg hi] at hr
        cases hr
    | some G =>
      rw [hG] at hr
      by_cases hi : g = N.groupAt m
      · rw [if_pos hi] at hr
        obtain ⟨j, hj, e⟩ := List.mem_filterMap.1 hr
        have e' : (G.rows.push row)[st + j]? = some r := e
        have hlt : st + j < G.rows.size := hth' G hG j (List.mem_range.1 hj)
        rw [Array.getElem?_push_lt hlt] at e'
        refine List.mem_filterMap.2 ⟨j, hj, ?_⟩
        rw [Array.getElem?_eq_getElem hlt]
        exact e'
      · rw [if_neg hi] at hr
        exact hr
  intro r hr
  cases c with
  | sample k =>
    simp only [classRows, hsz, hbk, hsm] at hr ⊢
    exact hr
  | _ => exact list _ _ (hth rfl) r hr

/-! ## 2 What "the one equation" does to the statement -/

/-- One row is added to one group's list. The messages are the same but for their mask ledgers. -/
theorem eqKeeps_lays {s s' : S} (k : EqKeeps s s') :
    ∃ (g : Nat) (row : OnBytes.Row),
      s'.st.groups = s.st.groups.modify g (fun G => { G with rows := G.rows.push row }) ∧
      s'.st.oracles.size = s.st.oracles.size ∧
      ∀ i : Nat, (s'.st.oracles[i]?).map VerifiableInference.Desc.LinkJoin.bare =
        (s.st.oracles[i]?).map VerifiableInference.Desc.LinkJoin.bare := by
  obtain ⟨a, out, ha, hdoor, rfl⟩ := k.laid
  obtain ⟨-, hst⟩ := part_reads s a ha
  obtain ⟨n, q, G, row, d1, -, -, -, hr, hout, -, -⟩ := door_parts _ _ _ _ _ _ hdoor
  have e1 := (door_both bare_blind _ _ _ _ _ _ hdoor).1.2
  refine ⟨a.L.check.group, row, ?_, ?_, fun i => ?_⟩
  · show out.d.st.groups = _
    rw [hout, ← hst, ← asRow_groups _ _ _ _ _ _ hr]
    rfl
  · show out.d.st.oracles.size = _
    rw [hout, ← hst, ← asRow_size _ _ _ _ _ _ hr]
    rfl
  · have e := e1 i
    rw [hst] at e
    exact e

/-! ## 3 At the library's meaning -/

section
variable {Xi P Tok : Type} {rows cols nR : Nat} {X : OnBytes.Model.Verify.Public}
  (𝔇 : MgData Xi P Tok rows cols nR X) (Mg : Meaning P (Wit (CellsQ rows cols) Tok MsgT))
  {s s' : S}

/-- The statement of `row m c` passes from `s` to `s'`. -/
theorem row_older_ext (hI : InOrder s.st) (hE : Extends s.st s'.st) (hB : BookKept s s') (m : Nat)
    (c : RowClass) (hsup : ∀ r ∈ classRows 𝔇.N m c s', r ∈ classRows 𝔇.N m c s) (z : P)
    (y y' : Strs) (w : Wit (CellsQ rows cols) Tok MsgT) (h0 : (mgAll 𝔇 Mg).row m c (z, s) y w) :
    (mgAll 𝔇 Mg).row m c (z, s') y' w := by
  rw [mgAll_row] at h0 ⊢
  exact rowSaysFirst_fwd 𝔇.arr 𝔇.N m c (z, s) (z, s') y y' w hI hE hsup hB h0

end

/-! ## 4 and 5 At the invariant -/

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)

/-- Wherever the invariant holds, the lists of open rows are as the open classes say. -/
theorem head_rowsHeld (Kp : Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr) {b : Nat}
    {k : Coins Bk} {s : TS} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env}
    (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread b k s m E) :
    rowsHeld (P5J.At.N Zp cF) (IM.openAt P5J.At.links P5J.At.ps b) s = true := by
  have hT' := hT
  unfold Thr at hT'
  obtain ⟨-, -, hF, -, -, -, -⟩ := hT'
  obtain ⟨-, c2, -, -, -⟩ := IM.xk_parts
    (xk_of_form (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w) hF)
  exact c2

variable (f : KindName → Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr)

/-- **The cell of `row m c` at "the one equation" of segment `l`.** `ho`: the item is open before
the sub-protocol. -/
theorem row_cell_eq (hf9 : f KindName.K9 = k9KeepsAt cF Zp) {l : Nat} (hl : l < 25) (m : Nat)
    (c : RowClass)
    (ho : Item.row m c ∈ IM.openAt P5J.At.links P5J.At.ps (14 * l + IM.nAt l + 4)) :
    RidesPastAt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w).thread
      (14 * l + IM.nAt l + 4) (Item.row m c) := by
  have hn : IM.nAt l = 7 ∨ IM.nAt l = 9 := by
    by_cases h24 : l = 24
    · subst h24
      exact Or.inr nAt_head
    · exact Or.inl (nAt_lt (by omega))
  have hlen : cF.blocksInOrder.length = 358 := head_len h
  intro k s mm E s' ps v hA hK h0
  have K := head_keeps_eq h H Q test carryX item n₁ n₂ b₀ Vd Rd f w hf9 hl s s' hK
  obtain ⟨-, e2, e3⟩ := eqKeeps_pile K
  obtain ⟨g, row, hg, hsz, hm⟩ := eqKeeps_lays K
  have hheld := head_rowsHeld h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w hA
  have hsup : ∀ q ∈ classRows (P5J.At.N Zp cF) m c s', q ∈ classRows (P5J.At.N Zp cF) m c s :=
    classRows_push_fwd (P5J.At.N Zp cF) m c g row hg hsz e3 hm fun hin G hG j hj => by
      have e := (held_at hheld (mem_rowSegs ho) hG).2 m c ho
        (by rw [beq_self_eq_true, hin]; rfl) j hj
      by_contra hlt
      rw [Array.getElem?_eq_none (Nat.le_of_not_lt hlt)] at e
      cases e
  exact row_older_ext
    { h.𝔇 with decT := fun _ _ => some (Q.cells mm.st.input), cr1 := carryX } mgBase
    (head_tidy h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w (by omega) hA).inOrder e2
    (fun o _ => by
      rw [e3]
      exact ⟨rfl, fun _ _ => rfl⟩) m c hsup mm.st.input.x.pub
    ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w).thread.strs E)
    ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w).thread.strs (E.add ps)) v h0

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.classRows_push_fwd
#print axioms ProofFile.Honest.FirstThread.eqKeeps_lays
#print axioms ProofFile.Honest.FirstThread.row_older_ext
#print axioms ProofFile.Honest.FirstThread.head_rowsHeld
#print axioms ProofFile.Honest.FirstThread.row_cell_eq
