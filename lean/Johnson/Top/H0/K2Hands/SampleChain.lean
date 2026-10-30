-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Hands/SampleChain.lean: the code switch's law: an invariant on the
messages' stored sample rows ALONG THE FIRST CHAIN. A law file; no running text imports it.

This file is GENERAL IN WHAT IS SAID OF A MESSAGE's STORED ROWS (the letter Q), since
the clause of the law that spends the invariant needs more of each seed than SampleGood
(K2Hears/SampleGood.lean) says; and a block's law may lean on the rounds' drawn elements being in
canonical form (OkDrawn), which the fold's own test on the view's words pays once.

RowsInv Q St: of every message of the statement St that has stored sample rows (its field
`sampleRows`: the rows that a sending lays for the sample that is drawn at it), Q holds at St's
codes, the message's shape, its number and these rows. SampleGood is RowsInv QGood, by definition.

  RowsInv, QGood, sampleGood_iff; QGoodS: QGood with three clauses more on each seed (enough
                      coordinates; a factor that is not zero; a factor in canonical form).
  rowsInv_first, rowsInv_startP, rowsInv_startReqP   at the first state: it has no message.
  rowsInv_congr       two statements with the same codes and messages.
  SameRows A B        the codes, and every message's shape and stored rows, are in B as in A. WEAKER
                      than SameMsgs (K1/Law/SeedIs.lean): it does not read the mark `sampled`.
  OldRows A B         the like for the messages of A alone: B may have more.
  sameRows_of_same, oldRows_of_old, oldRows_of_sameRows, SameRows.trans, OldRows.trans
  NewInv Q n St       the messages of St from number n on that have stored rows have Q.
  rowsInv_rows, rowsInv_oldRows   how the invariant passes from A to B.
  OkDrawn r, okDrawn_noDigest, okDrawn_of_view   a round's drawn elements are in canonical form; the
                      fold's test viewWordsBelowPrime gives it at every round of the view.
  Inv Q s, KeepsInv Q b   the invariant at a state of the verifier; ChainKeeps.lean's KeepsD at it,
                      on rounds with OkDrawn.
  keepsInv_of_rows, keepsInv_of_leaves, keepsInv_of_old, keepsInv_of_oldRows
  keepsInv_k2         the kind K2's own block, from a law on its decision at two rounds.
  keepsGood_k2        that law at QGood is sampleGood_yes.
  inv_at_cut          where every block of a list keeps it: at the state in front of any block of
                      the list, behind the fold over the blocks in front of it.
  inv_in_chain        the like for a chain's flat list, from ChainKeeps.
Limits. THAT THE DESCRIPTION's FIRST CHAIN HAS ChainKeeps IS NOT SHOWN HERE: each kind's files owe
its own clause by its law on what its yes leaves; K2's kind alone is paid here, at QGood. The
senders' share (K1's three blocks lay new stored rows) is not shown. Nothing on soundness or on
hiding.

-/
import Johnson.Top.H0.K2Hears.SampleGood
import Johnson.Desc.K1.Law.GoodSend5
import Johnson.Top.H0.Tw.K2C.Laws
import Johnson.Top.H0.K2Hands.ChainKeeps

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Chain OpenedColumn foldBlocks)
open VerifiableInference.Desc.K1 (SameMsgs OldMsgs LeavesMsgs KeepsOld)
open VerifiableInference.Desc.Keeps1

/-! ## The invariant -/

/-- Of every message that has stored sample rows, Q holds at the codes, its shape, its number and
these rows. -/
def RowsInv (Q : Codes → OracleShape → Nat → Array OnBytes.Row → Prop) (St : Statement) : Prop :=
  ∀ (o : Nat) (x : OnBytes.Oracle), St.oracles[o]? = some x → x.sampleRows.size ≠ 0 →
    Q St.codes x.shape o x.sampleRows

/-- The rows are the program's Send.form at some seeds. -/
def QGood (cs : Codes) (s : OracleShape) (o : Nat) (rows : Array OnBytes.Row) : Prop :=
  ∃ seeds, RowsAre cs s o seeds rows

theorem sampleGood_iff (St : Statement) : SampleGood St ↔ RowsInv QGood St := Iff.rfl

/-- The like, and each seed has enough coordinates and a factor that is not zero and is in canonical
form. -/
def QGoodS (cs : Codes) (s : OracleShape) (o : Nat) (rows : Array OnBytes.Row) : Prop :=
  ∃ seeds, RowsAre cs s o seeds rows ∧
    ∀ sd ∈ seeds, (Send.cube cs s).bits ≤ sd.z.length ∧ isZeroE sd.beta = false ∧
      okE sd.beta = true

variable {Q : Codes → OracleShape → Nat → Array OnBytes.Row → Prop}

theorem rowsInv_congr {A B : Statement} (hc : B.codes = A.codes) (ho : B.oracles = A.oracles)
    (h : RowsInv Q A) : RowsInv Q B := by
  intro o x hx hs
  rw [hc]
  rw [ho] at hx
  exact h o x hx hs

/-! ## At the first state -/

theorem rowsInv_first (codes : Codes) (shape : Params.ReqShape) (layout : Params.ReqLayout) :
    RowsInv Q (S.firstRecord codes shape layout).st := by
  intro o x hx _
  exact absurd hx (by simp [S.firstRecord])

theorem rowsInv_startP {P : Par} {codes : Codes} {shape : Params.ReqShape}
    {layout : Params.ReqLayout} {s : S} (h : S.startP P codes shape layout = some s) :
    RowsInv Q s.st := by
  unfold S.startP at h
  split at h
  · cases h
    exact rowsInv_first codes shape layout
  · cases h

theorem rowsInv_startReqP {P : Par} {codes : Codes} {shape : Params.ReqShape}
    {layout : Params.ReqLayout} {T V : Nat} {req : Array UInt32} {s : S}
    (h : S.startReqP P codes shape layout T V req = some s) : RowsInv Q s.st := by
  unfold S.startReqP at h
  obtain ⟨s0, h0, h1⟩ := Option.bind_eq_some_iff.1 h
  split at h1
  · cases h1
    have g : RowsInv Q s0.st := rowsInv_startP h0
    exact g
  · cases h1

/-! ## From one statement to another -/

/-- The codes, and every message's shape and stored rows, are in B as in A. -/
def SameRows (A B : Statement) : Prop :=
  B.codes = A.codes ∧ ∀ j : Nat,
    (B.oracles[j]?).map (fun x : OnBytes.Oracle => (x.shape, x.sampleRows)) =
      (A.oracles[j]?).map fun x : OnBytes.Oracle => (x.shape, x.sampleRows)

/-- The like for the messages of A alone. -/
def OldRows (A B : Statement) : Prop :=
  B.codes = A.codes ∧ ∀ j : Nat, j < A.oracles.size →
    (B.oracles[j]?).map (fun x : OnBytes.Oracle => (x.shape, x.sampleRows)) =
      (A.oracles[j]?).map fun x : OnBytes.Oracle => (x.shape, x.sampleRows)

theorem drop_mark {a b : Option OnBytes.Oracle}
    (h : a.map (fun x : OnBytes.Oracle => (x.shape, x.sampled, x.sampleRows)) =
      b.map fun x : OnBytes.Oracle => (x.shape, x.sampled, x.sampleRows)) :
    a.map (fun x : OnBytes.Oracle => (x.shape, x.sampleRows)) =
      b.map fun x : OnBytes.Oracle => (x.shape, x.sampleRows) := by
  have := congrArg (Option.map fun t : OracleShape × Bool × Array OnBytes.Row => (t.1, t.2.2)) h
  simpa [Option.map_map, Function.comp_def] using this

theorem sameRows_of_same {A B : Statement} (h : SameMsgs A B) : SameRows A B :=
  ⟨h.1, fun j => drop_mark (h.2 j)⟩

theorem oldRows_of_old {A B : Statement} (h : OldMsgs A B) : OldRows A B :=
  ⟨h.1, fun j hj => drop_mark (h.2 j hj)⟩

theorem oldRows_of_sameRows {A B : Statement} (h : SameRows A B) : OldRows A B :=
  ⟨h.1, fun j _ => h.2 j⟩

theorem SameRows.refl (A : Statement) : SameRows A A := ⟨rfl, fun _ => rfl⟩

theorem SameRows.trans {A B C : Statement} (h1 : SameRows A B) (h2 : SameRows B C) :
    SameRows A C := ⟨h2.1.trans h1.1, fun j => (h2.2 j).trans (h1.2 j)⟩

theorem OldRows.size {A B : Statement} (h : OldRows A B) : A.oracles.size ≤ B.oracles.size := by
  by_contra hn
  have hlt : B.oracles.size < A.oracles.size := Nat.lt_of_not_le hn
  have e := congrArg Option.isSome (h.2 _ hlt)
  simp only [Option.isSome_map] at e
  rw [Array.getElem?_eq_getElem hlt, Array.getElem?_eq_none (Nat.le_refl _)] at e
  cases e

theorem OldRows.trans {A B C : Statement} (h1 : OldRows A B) (h2 : OldRows B C) : OldRows A C :=
  ⟨h2.1.trans h1.1, fun j hj => (h2.2 j (Nat.lt_of_lt_of_le hj h1.size)).trans (h1.2 j hj)⟩

/-- The messages from number n on that have stored rows have Q. -/
def NewInv (Q : Codes → OracleShape → Nat → Array OnBytes.Row → Prop) (n : Nat) (St : Statement) :
    Prop :=
  ∀ (o : Nat) (x : OnBytes.Oracle), n ≤ o → St.oracles[o]? = some x → x.sampleRows.size ≠ 0 →
    Q St.codes x.shape o x.sampleRows

theorem rowsInv_oldRows {A B : Statement} (h : OldRows A B) (hn : NewInv Q A.oracles.size B)
    (hA : RowsInv Q A) : RowsInv Q B := by
  intro o x hx hs
  by_cases ho : o < A.oracles.size
  · have e := h.2 o ho
    rw [hx] at e
    obtain ⟨x0, hx0, e0⟩ := Option.map_eq_some_iff.1 e.symm
    obtain ⟨e1, e3⟩ := Prod.mk.inj e0
    rw [h.1, ← e1, ← e3]
    exact hA o x0 hx0 (by rw [e3]; exact hs)
  · exact hn o x (Nat.le_of_not_lt ho) hx hs

theorem rowsInv_rows {A B : Statement} (h : SameRows A B) (hA : RowsInv Q A) : RowsInv Q B := by
  intro o x hx hs
  have e := h.2 o
  rw [hx] at e
  obtain ⟨x0, hx0, e0⟩ := Option.map_eq_some_iff.1 e.symm
  obtain ⟨e1, e3⟩ := Prod.mk.inj e0
  rw [h.1, ← e1, ← e3]
  exact hA o x0 hx0 (by rw [e3]; exact hs)

/-! ## The rounds' drawn elements -/

/-- The round's drawn elements are in canonical form. -/
def OkDrawn (r : Fmt.RoundView) : Prop := ∀ e ∈ r.drawn.elems.map E.ofTriple, okE e = true

theorem okDrawn_noDigest (r : Fmt.RoundView) (h : OkDrawn r) :
    OkDrawn (VerifiableInference.Desc.noDigest r) := h

theorem okDrawn_of_view {v : Fmt.View} (h : VerifiableInference.Desc.viewWordsBelowPrime v = true) :
    ∀ r ∈ v.rounds, OkDrawn r := by
  intro r hr e he
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 he
  simp only [VerifiableInference.Desc.viewWordsBelowPrime, Bool.and_eq_true, List.all_eq_true] at h
  have := (h.1 r hr).1 x hx
  simp only [decide_eq_true_eq] at this
  simp only [okE, okF, E.ofTriple, Bool.and_eq_true, decide_eq_true_eq]
  exact this

/-! ## Blocks -/

variable {Cl : Type}

/-- The invariant at a state of the verifier. -/
def Inv (Q : Codes → OracleShape → Nat → Array OnBytes.Row → Prop) (s : S) : Prop := RowsInv Q s.st

/-- A yes of the block's decision, on rounds whose drawn elements are in canonical form, keeps the
invariant. -/
abbrev KeepsInv (Q : Codes → OracleShape → Nat → Array OnBytes.Row → Prop) (b : Block S Cl) :
    Prop := KeepsD OkDrawn (Inv Q) b

theorem keepsInv_of_rows {b : Block S Cl}
    (h : ∀ s s' rs gs, b.decide s rs gs = .ok s' → SameRows s.st s'.st) : KeepsInv Q b :=
  fun s s' rs gs _ hy hg => rowsInv_rows (h s s' rs gs hy) hg

theorem keepsInv_of_oldRows {b : Block S Cl}
    (h : ∀ s s' rs gs, (∀ r ∈ rs, OkDrawn r) → b.decide s rs gs = .ok s' →
      OldRows s.st s'.st ∧ NewInv Q s.st.oracles.size s'.st) : KeepsInv Q b :=
  fun s s' rs gs hr hy hg => rowsInv_oldRows (h s s' rs gs hr hy).1 (h s s' rs gs hr hy).2 hg

theorem keepsInv_of_leaves {b : Block S Cl} (h : LeavesMsgs (fun s : S => s.st) b) :
    KeepsInv Q b := keepsInv_of_rows fun s s' rs gs hy => sameRows_of_same (h s s' rs gs hy)

theorem keepsInv_of_old {b : Block S Cl} (h : KeepsOld (fun s : S => s.st) b)
    (hn : ∀ s s' rs gs, (∀ r ∈ rs, OkDrawn r) → b.decide s rs gs = .ok s' →
      NewInv Q s.st.oracles.size s'.st) : KeepsInv Q b :=
  keepsInv_of_oldRows fun s s' rs gs hr hy =>
    ⟨oldRows_of_old (h s s' rs gs hy), hn s s' rs gs hr hy⟩

/-- The kind's own block, on whatever rounds it says yes, from a law on its decision at two
rounds. -/
theorem keepsInv_k2 (p : P2)
    (hk : ∀ s r₁ r₂ gs s', OkDrawn r₁ → decideWith _root_.Tw.K2.sendByL8 p s [r₁, r₂] gs = .ok s' →
      RowsInv Q s.st → RowsInv Q s'.st) : KeepsInv Q (codeSwitchKind p : Block S Cl) := by
  intro s s' rs gs hr h hg
  have h' : decideWith _root_.Tw.K2.sendByL8 p s rs gs = .ok s' := h
  have h2 : rs.length = 2 := two _ p s rs gs s' h'
  match rs, h2, hr, h' with
  | [r₁, r₂], _, hr, h' => exact hk s r₁ r₂ gs s' (hr r₁ List.mem_cons_self) h' hg

theorem keepsGood_k2 (p : P2) : KeepsInv QGood (codeSwitchKind p : Block S Cl) :=
  keepsInv_k2 p fun s r₁ r₂ gs s' _ h hg => sampleGood_yes p s r₁ r₂ gs s' h hg

/-! ## Along a list of blocks, along a chain -/

/-- **In front of any block of the list.** -/
theorem inv_at_cut {ft : Nat} {bs pre l : List (Block S Cl)} {B : Block S Cl}
    (hb : ∀ b ∈ bs, KeepsInv Q b) (hcut : bs = pre ++ B :: l) {s m : S} {rs rs' : List Fmt.RoundView}
    {cols cols' : List Col} (hr : ∀ r ∈ rs, OkDrawn r)
    (h : foldBlocks ft pre s rs cols = .ok (m, rs', cols')) (hs : RowsInv Q s.st) :
    RowsInv Q m.st :=
  fold_keeps (R := OkDrawn) (P := Inv Q) okDrawn_noDigest ft pre s m rs rs' cols cols'
    (fun b hm => hb b (by rw [hcut]; exact List.mem_append_left _ hm)) hr h hs

/-- The like for a chain's flat list. -/
theorem inv_in_chain {ft : Nat} {c : Chain S Cl} (hc : ChainKeeps OkDrawn (Inv Q) c)
    {pre l : List (Block S Cl)} {B : Block S Cl} (hcut : c.blocksInOrder = pre ++ B :: l) {s m : S}
    {rs rs' : List Fmt.RoundView} {cols cols' : List Col} (hr : ∀ r ∈ rs, OkDrawn r)
    (h : foldBlocks ft pre s rs cols = .ok (m, rs', cols')) (hs : RowsInv Q s.st) :
    RowsInv Q m.st := inv_at_cut (chain_flat_keeps hc) hcut hr h hs

end VerifiableInference.Desc.First.K2

#print axioms VerifiableInference.Desc.First.K2.inv_in_chain
#print axioms VerifiableInference.Desc.First.K2.keepsGood_k2
#print axioms VerifiableInference.Desc.First.K2.keepsInv_of_old
#print axioms VerifiableInference.Desc.First.K2.okDrawn_of_view
#print axioms VerifiableInference.Desc.First.K2.rowsInv_startReqP
