-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K9/RowPushed.lean: THE OPEN ITEMS THAT READ THE STATEMENT PASS OVER THE SUB-PROTOCOL "THE ONE EQUATION", WHICH TURNS THE STATEMENT. Its door
takes mask entries (one message's ledger turns) and PUSHES ONE ROW onto the list of open rows of the segment's group. The library's law for
the item `row m c` over a step that turns the statement (`ridesPastAt_row_older`, Honest/Thread/RowForward.lean) asks that every group keeps its
list of rows: false here. But a push at the end leaves the rows at the older places, and the table's promise says that each place
of an open class holds a row: so the rows of an open class are the same in front and behind.

  **`eq_groups`**       the step's clause `EqKeeps` (Honest/K9/CloseKeeps.lean): the groups behind are the groups in front with one row pushed at
                        the link's group
  `eq_tri`, `size_of_sameBy`, `eq_extends`, `eq_bookKept`, **`eq_rowAt₀`**   of each message its shape, mark and sample rows stay, and the list of commitment
                        trees: so the statement behind extends the one in front, and each message's first sample row stays
  `held_places`         the promise `rowsHeld`: each place of an open class in the list lies below the list's length
  **`classRows_eq`**      the rows of a class behind are its rows in front
  `row_ext`             the item's statement passes from s to s', from "in order", "extends", "the trees are kept" and "no row more"
  **`ridesPastAt_row_eq`**, **`ridesPastAt_pin_eq`**, **`ridesPastAt_pinI_eq`**   three sorts of item at the first chain's thread

Limits. The library's hypothesis `AtMgA` is a premise of the four end statements, and that the member's "keeps" gives the clause. The class
"equation" is owed at this member and is not spoken of. Nothing here shows that an item's statement holds at any state. This file
proves no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K9.AsRowGroups
import Johnson.Desc.ProofFile.Honest.K9.CloseKeeps
import Johnson.Desc.ProofFile.Honest.K10.Pay.Run
import Johnson.Desc.ProofFile.Honest.Thread.RowForward
import Johnson.Desc.ProofFile.Honest.Thread.RowPileForwardKinds
import Johnson.Desc.ProofFile.Honest.Thread.PinForward
import Johnson.Desc.ProofFile.Honest.Thread.PinForwardKinds
import Johnson.Desc.ProofFile.Honest.Thread.PileForward
import Johnson.Desc.ProofFile.Honest.Thread.WoEq
import Johnson.Desc.First.Batch.Law.DoorTests

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Chain Strs Wit Place)
open VerifiableInference.Desc.First (S Item Numbers RowClass Meaning classRows rowSays wordsAtFirst BookKept rowsHeld
  rowSegs)
open VerifiableInference.Desc.Sound (MsgT MgData mgAll mgBase mgAll_row CellsQ)
open VerifiableInference.Desc.LinkJoin (SameBy tri tri_blind door_both door_link rb_putLink rb_putFork)
open VerifiableInference.Desc.K9 (asRow St Equation)
open VerifiableInference.Desc.K9.Shape (ans_bind need_ok there_ok)
open OnBytes.Means (InOrder Extends)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread

/-! ## 1 What the step does to the statement -/

/-- **One row is pushed at the link's group; every other group stays.** -/
theorem eq_groups {s s' : S} (K : EqKeeps s s') : ∃ (L : LinkCtx) (row : OnBytes.Row), s.link? = some L ∧
    s'.st.groups = s.st.groups.modify L.check.group fun G => { G with rows := G.rows.push row } := by
  obtain ⟨a, o, ha, hdoor, rfl⟩ := K.laid
  obtain ⟨hL, hst⟩ := VerifiableInference.Desc.LinkJoin.part_reads s a ha
  obtain ⟨q, G, row, d1, -, hr, hadd⟩ := VerifiableInference.Desc.K9L.door_addRowP _ _ _ _ _ _ hdoor
  have hout : o.d = { d1 with st := Slice.withRow d1.st a.L.check.group row } := by
    unfold VerifiableInference.Desc.Ground.addRowP at hadd
    split at hadd
    · exact (Option.some.inj hadd).symm
    · simp at hadd
  refine ⟨a.L, row, hL, ?_⟩
  show o.d.st.groups = _
  rw [hout]
  show d1.st.groups.modify a.L.check.group (fun G => { G with rows := G.rows.push row }) = _
  rw [show d1.st.groups = a.d.st.groups from asRow_groups _ _ _ _ _ hr, hst]

/-- Of each message its shape, mark and sample rows stay; so does the list of commitment trees. -/
theorem eq_tri {s s' : S} (K : EqKeeps s s') : SameBy tri s.st s'.st ∧ s'.book = s.book := by
  obtain ⟨a, o, ha, hdoor, rfl⟩ := K.laid
  obtain ⟨hL, hst⟩ := VerifiableInference.Desc.LinkJoin.part_reads s a ha
  have e1 := (door_both tri_blind _ _ _ _ _ _ hdoor).1
  rw [hst] at e1
  exact ⟨e1, ((rb_putLink s a.L o.L hL (by rw [door_link _ _ _ _ _ _ hdoor])).trans (rb_putFork _ o.F)).book⟩

theorem size_of_sameBy {A B : Statement} (h : SameBy tri A B) : B.oracles.size = A.oracles.size := by
  apply Nat.le_antisymm
  · by_contra hn
    have e := h.2 A.oracles.size
    rw [Array.getElem?_eq_none (Nat.le_refl _), Array.getElem?_eq_getElem (by omega)] at e
    exact nomatch e
  · by_contra hn
    have e := h.2 B.oracles.size
    rw [Array.getElem?_eq_none (Nat.le_refl _), Array.getElem?_eq_getElem (by omega)] at e
    exact nomatch e

theorem eq_extends {s s' : S} (K : EqKeeps s s') : Extends s.st s'.st := by
  obtain ⟨e1, -⟩ := eq_tri K
  refine ⟨e1.1, fun j x hx => ?_⟩
  have e := e1.2 j
  rw [hx] at e
  obtain ⟨x', h1, h2⟩ := Option.map_eq_some_iff.1 e
  exact ⟨x', h1, congrArg (·.1) h2⟩

theorem eq_bookKept {s s' : S} (K : EqKeeps s s') : BookKept s s' := by
  obtain ⟨-, hB⟩ := eq_tri K
  exact fun o _ => ⟨by rw [hB], fun q _ => by rw [hB]⟩

/-- **Each message's first sample row stays.** -/
theorem eq_rowAt₀ {s s' : S} (K : EqKeeps s s') (o : ℕ) : rowAt₀ s'.st o = rowAt₀ s.st o := by
  obtain ⟨e1, -⟩ := eq_tri K
  have e := e1.2 o
  unfold rowAt₀
  cases hA : s.st.oracles[o]? with
  | none =>
    rw [hA] at e
    cases hB : s'.st.oracles[o]? with
    | none => rfl
    | some y =>
      rw [hB] at e
      exact nomatch e
  | some x =>
    rw [hA] at e
    obtain ⟨y, hy, h2⟩ := Option.map_eq_some_iff.1 e
    rw [hy]
    show y.sampleRows[0]? = x.sampleRows[0]?
    rw [show y.sampleRows = x.sampleRows from congrArg (·.2.2) h2]

/-! ## 2 The rows of a class -/

/-- The promise on the open rows: each place of an open class in the list lies below the list's length. -/
theorem held_places (N : Numbers) {O : List Item} {s : S} {m : ℕ} {c : RowClass} {G : Group}
    (h : rowsHeld N O s = true) (hi : Item.row m c ∈ O) (hc : c.inList = true)
    (hG : s.st.groups[N.groupAt m]? = some G) :
    ∀ j, j < (N.rowsAt m c).2 → (N.rowsAt m c).1 + j < G.rows.size := by
  unfold rowsHeld at h
  have hm : m ∈ rowSegs O := by
    unfold rowSegs
    rw [List.mem_eraseDups]
    exact List.mem_filterMap.2 ⟨_, hi, rfl⟩
  have h1 := List.all_eq_true.1 h m hm
  simp only [hG, Bool.and_eq_true] at h1
  have h2 := List.all_eq_true.1 h1.2 _ hi
  simp only [beq_self_eq_true, hc, Bool.and_self, Bool.not_true, Bool.false_or] at h2
  intro j hj
  have h3 := List.all_eq_true.1 h2 j (List.mem_range.2 hj)
  by_contra hn
  rw [Array.getElem?_eq_none (Nat.le_of_not_lt hn)] at h3
  exact nomatch h3

/-- The rows at a stretch of places below the list's length, in front and behind. -/
theorem listRows_eq {s s' : S} (K : EqKeeps s s') (g first cnt : ℕ)
    (hheld : ∀ G, s.st.groups[g]? = some G → ∀ j, j < cnt → first + j < G.rows.size) :
    (match s'.st.groups[g]? with
      | none => []
      | some G => (List.range cnt).filterMap fun j => G.rows[first + j]?) =
    (match s.st.groups[g]? with
      | none => []
      | some G => (List.range cnt).filterMap fun j => G.rows[first + j]?) := by
  obtain ⟨L, row, -, hg⟩ := eq_groups K
  rw [hg, Array.getElem?_modify]
  by_cases e : L.check.group = g
  · rw [if_pos e]
    cases hG : s.st.groups[g]? with
    | none => rfl
    | some G =>
      show (List.range cnt).filterMap (fun j => (G.rows.push row)[first + j]?) =
        (List.range cnt).filterMap fun j => G.rows[first + j]?
      refine List.filterMap_congr fun j hj => ?_
      have hlt := hheld G hG j (List.mem_range.1 hj)
      rw [Array.getElem?_push, if_neg (by omega)]
  · rw [if_neg e]

/-- **The rows of a class behind "the one equation" are its rows in front**, where each place of the class holds a row. -/
theorem classRows_eq (N : Numbers) (m : ℕ) (c : RowClass) {s s' : S} (K : EqKeeps s s')
    (hheld : c.inList = true → ∀ G, s.st.groups[N.groupAt m]? = some G →
      ∀ j, j < (N.rowsAt m c).2 → (N.rowsAt m c).1 + j < G.rows.size) :
    classRows N m c s' = classRows N m c s := by
  cases c with
  | sample t =>
    obtain ⟨hT, hB⟩ := eq_tri K
    show ((List.range s'.st.oracles.size).flatMap fun o =>
        if (s'.book.place[o]?).any fun x => (N.sent m t).contains x then
          ((s'.st.oracles[o]?).map fun x => x.sampleRows.toList).getD []
        else []) =
      ((List.range s.st.oracles.size).flatMap fun o =>
        if (s.book.place[o]?).any fun x => (N.sent m t).contains x then
          ((s.st.oracles[o]?).map fun x => x.sampleRows.toList).getD []
        else [])
    rw [size_of_sameBy hT, hB]
    congr 1
    funext o
    have e : (s'.st.oracles[o]?).map (fun x => x.sampleRows.toList) =
        (s.st.oracles[o]?).map (fun x => x.sampleRows.toList) := by
      have e0 := congrArg (Option.map fun y : OracleShape × Bool × Array OnBytes.Row => y.2.2.toList) (hT.2 o)
      rw [Option.map_map, Option.map_map] at e0
      exact e0
    rw [e]
  | carried => exact listRows_eq K _ _ _ (hheld rfl)
  | position => exact listRows_eq K _ _ _ (hheld rfl)
  | equation => exact listRows_eq K _ _ _ (hheld rfl)

/-! ## 3 At the library's meaning -/

/-- The statement of `row m c` passes from s to s'. -/
theorem row_ext {Xi P Tok : Type} {rows cols nR : ℕ} {X : OnBytes.Model.Verify.Public}
    (𝔇 : MgData Xi P Tok rows cols nR X) (Mg : Meaning P (Wit (CellsQ rows cols) Tok MsgT)) {s s' : S}
    (hI : InOrder s.st) (hE : Extends s.st s'.st) (hB : BookKept s s') (m : ℕ) (c : RowClass)
    (hsup : ∀ r ∈ classRows 𝔇.N m c s', r ∈ classRows 𝔇.N m c s) (z : P) (y y' : Strs)
    (w : Wit (CellsQ rows cols) Tok MsgT) (h0 : (mgAll 𝔇 Mg).row m c (z, s) y w) :
    (mgAll 𝔇 Mg).row m c (z, s') y' w := by
  rw [mgAll_row] at h0 ⊢
  exact rowSaysFirst_fwd 𝔇.arr 𝔇.N m c (z, s) (z, s') y y' w hI hE hsup hB h0

/-! ## 4 At the invariant -/

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

/-- **The item `row m c` passes over a member whose "keeps" gives the clause of "the one equation"**, if a class in the list
is open there. -/
theorem ridesPastAt_row_eq {b : ℕ} (hb : b ≤ cF.blocksInOrder.length) (m : ℕ) (c : RowClass)
    (ho : c.inList = true → Item.row m c ∈ P5J.oAt b)
    (hk : ∀ s s', (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.keeps b s s' → EqKeeps s s') :
    RidesPastAt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread b (Item.row m c) := by
  intro k s mm E s' ps v hA hK h0
  have K := hk s s' hK
  obtain ⟨-, hH⟩ := ProofFile.Honest.K10.run_held_thr h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hA
  have e : classRows h.𝔇.N m c s' = classRows h.𝔇.N m c s :=
    classRows_eq h.𝔇.N m c K fun hc G hG => held_places _ hH (ho hc) hc hG
  exact row_ext { h.𝔇 with decT := fun _ _ => some (Q.cells mm.st.input), cr1 := carryX } mgBase
    (head_tidy h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hb hA).inOrder (eq_extends K) (eq_bookKept K) m c
    (fun q hq => by
      have hq' : q ∈ classRows h.𝔇.N m c s' := hq
      rw [e] at hq'
      exact hq') mm.st.input.x.pub
    ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.strs E) ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.strs (E.add ps)) v h0

theorem ridesPastAt_pin_eq {b : ℕ} (m t : ℕ) (hk : ∀ s s', (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.keeps b s s' → EqKeeps s s') :
    RidesPastAt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread b (Item.pin m t) :=
  ridesPastAt_pin_older h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w m t fun _ s _ _ s' _ hK o q hq => by
    rw [eq_rowAt₀ (hk s s' hK)]
    exact hq

theorem ridesPastAt_pinI_eq {b : ℕ} (hk : ∀ s s', (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.keeps b s s' → EqKeeps s s') :
    RidesPastAt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread b Item.pinI :=
  ridesPastAt_pinI_older h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w fun _ s _ _ s' _ hK o q hq => by
    rw [eq_rowAt₀ (hk s s' hK)]
    exact hq

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.eq_groups
#print axioms ProofFile.Honest.K9.eq_tri
#print axioms ProofFile.Honest.K9.size_of_sameBy
#print axioms ProofFile.Honest.K9.eq_extends
#print axioms ProofFile.Honest.K9.eq_bookKept
#print axioms ProofFile.Honest.K9.eq_rowAt₀
#print axioms ProofFile.Honest.K9.held_places
#print axioms ProofFile.Honest.K9.listRows_eq
#print axioms ProofFile.Honest.K9.classRows_eq
#print axioms ProofFile.Honest.K9.row_ext
#print axioms ProofFile.Honest.K9.ridesPastAt_row_eq
#print axioms ProofFile.Honest.K9.ridesPastAt_pin_eq
#print axioms ProofFile.Honest.K9.ridesPastAt_pinI_eq
