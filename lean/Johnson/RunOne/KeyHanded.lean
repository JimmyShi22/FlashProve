-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/KeyHanded.lean. handed₂B: what the shared chain's last state must hold. EvalIs: the row (Eval) as it lies IS the claim's. borderB: what the last chain's first border's own copy of the shared chain's end must hold; among it: every vector of the border's row weights is Tensor.ok (the law of the last chain's first block wants it; no test asks it; it rides in from the first chain), and the border's copy's codes are the own statement's. SampleIn · OpenIn · HandedIn: THE FENCE ON THE ROWS' CONTENT: every sample row of a pinned message, and every open row of a group, lies on tables that its group's members have (Means.RowIn: here off Johnson/Desc/Means/Says.lean, after Johnson/RunOne/BorderShapes/LLP7L/Says.lean [not in this library]: RowIn's text is alike in both [by diff]): a promise that COUNTS rows fences no made-up row. SampleIn AND OpenIn ARE TWO FIELDS OF THE INVARIANT Means.InOrder (Johnson/Desc/Means/Order.lean), which the plain ground's routines keep by merged laws: sampleIn_of_order · openIn_of_order · handedIn_of_order. Bools with code, propositions, and two small theorems (rowInB_iff · borderB_spec). WHAT THE KEY FILE's LAST CHAIN's FIRST BOUNDARY's BOOK-KEEPING WANTS OF THE FIRST CHAIN's LAST STATEMENT, beyond what the last chain's start tests itself: in the words of
Johnson/RunOne/BorderShapes/LKFU/Shape23.lean's shape₃ at boundary 0, with the counts read off the statement itself:
  the last message but one (W) is sampled, with a sample rows, and is not spent as a mask · the last message (the own test's first mask) has no sample, no sample row, and is not spent ·
  the last group (the own group) has just the members idx ++ [W], one open plain row, no generator row, and its test has not begun.
WHERE IT IS PROMISED: at the first chain's last boundaries (behind W's sending); it then rides, unread and unturned, in what is handed to the shared chain, through all thirteen boundaries of that chain, and is spent at the seam to the last chain.
Nothing on soundness.
-/
import Johnson.Desc.Key.Link
import Johnson.Desc.Key.Chain1
import Johnson.Desc.Key.FileOk
import Johnson.Desc.Key.Desc
import Johnson.RunOne.BorderShapes.LKFU.Shape23
import Johnson.Desc.Means.Says
import Johnson.Desc.Means.Order

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.KeyRows23
open OnBytes

/-- On a statement. a: the answers to a sample. idx: the claim's masks' messages, members of the own group in front of W. -/
def handedSt (a : Nat) (idx : List Nat) (st : Statement) : Bool :=
  LKFU.Shape23.msgIs st (st.oracles.size - 2) (some a) false && LKFU.Shape23.msgIs st (st.oracles.size - 1) none false &&
    LKFU.Shape23.grpIs st (st.groups.size - 1) (idx ++ [st.oracles.size - 2]) 1 0 false

/-- On the first chain's state. -/
def handedB (a : Nat) (idx : List Nat) (s₁ : VerifiableInference.Desc.Key.FirstState) : Bool := handedSt a idx s₁.d.st

/-- WHAT THE LAST CHAIN's SECOND BOUNDARY's BOOK-KEEPING WANTS OF THE SHARED CHAIN's LAST STATE: Omega is its message 2, sampled, with a sample rows, not spent as a mask: so that Omega's copy, which the last chain's first block takes over, is so too. -/
def handed₂B (a : Nat) (s₂ : _root_.Desc.K14.St) : Bool := s₂.loc.oOmega == 2 && LKFU.Shape23.msgIs s₂.st 2 (some a) false

/-- THE SAME ON THE LAST CHAIN's OWN RECORD, while the border lies: the border's copy of the shared chain's end names Omega as message 2 of its statement, sampled, with a sample rows, not spent; every vector of the border's row weights is Tensor.ok; and the copy's codes are the own statement's. -/
def borderB (a : Nat) (s : VerifiableInference.Desc.Third.S₃) : Bool :=
  match s.loc.border with
  | some b => b.shared.omega == 2 && LKFU.Shape23.msgIs b.shared.st 2 (some a) false && b.g.all (·.ok) && decide (b.shared.st.codes = s.st.codes)
  | none => false

/-- What borderB says, BY NAME: FOR WHOEVER TYPES OVER IT: take the fields by their names and do not open the Bool by its places: a clause more is then a field more and turns no proof of yours. -/
structure BorderSays (a : Nat) (s : VerifiableInference.Desc.Third.S₃) (b : VerifiableInference.Desc.Third.Border) : Prop where
  lies : s.loc.border = some b
  omega : b.shared.omega = 2
  msg : LKFU.Shape23.msgIs b.shared.st 2 (some a) false = true
  weights : ∀ g ∈ b.g, g.ok = true
  codes : b.shared.st.codes = s.st.codes

theorem borderB_spec (a : Nat) (s : VerifiableInference.Desc.Third.S₃) (h : borderB a s = true) : ∃ b, BorderSays a s b := by
  unfold borderB at h
  cases hb : s.loc.border with
  | none => rw [hb] at h; cases h
  | some b =>
    rw [hb] at h
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    exact ⟨b, hb, h.1.1.1, h.1.1.2, fun g hg => List.all_eq_true.1 h.1.2 g hg, h.2⟩

/-- **THE ROW (Eval) AS IT LIES IS THE CLAIM's.** Behind W's sending the first chain's state holds the claim that the batching left (lin) and, as the own group's first open row, the row that the program's pure linEvalRow makes of that claim at W's number
(Johnson/Desc/K13/Text.lean: rows). A PROPOSITION: a row has no decidable equality. WHO SPENDS IT: the law of «LIN point», which closes «pile» (read off the claim) against «Eval» (read as it lies). WHO EARNS IT: W's sending. -/
def EvalIs (S : OnBytes.Params.LinShape) (s : VerifiableInference.Desc.Key.FirstState) : Prop :=
  ∃ L r, s.lin = some L ∧ linEvalRow S L.claim L.w (linLayW s.d.st.codes S) = some r ∧ (s.d.st.groups[L.own]?).bind (·.rows[0]?) = some r

/-- Every sample row of message o lies on that message's own tables alone (Means.RowIn, at the group of that one message). WHO EARNS IT: the message's sending. -/
def SampleIn (St : Statement) (o : Nat) : Prop :=
  ∀ y, St.oracles[o]? = some y → ∀ r ∈ y.sampleRows.toList, Means.RowIn St { code := 0, members := #[o] } r

/-- Every open row of group g lies on tables that the group's members have. WHO EARNS IT: whoever adds the row (by RowIn's own docstring it is «what the call that adds an open row has tested»: said there of the program's call; the description's addRowsP I have not opened). -/
def OpenIn (St : Statement) (g : Nat) : Prop :=
  ∀ G, St.groups[g]? = some G → ∀ r ∈ G.rows.toList, Means.RowIn St G r

/-- Means.RowIn's four clauses as a Bool, for sheets. -/
def rowInB (St : Statement) (G : Group) (r : OnBytes.Row) : Bool :=
  r.terms.all (fun t => Blk.placeOk St G t.oracle t.part t.v.vars 0) &&
  r.units.all (fun u => Blk.placeOk St G u.oracle u.part (St.tableBits u.oracle u.part) u.index) &&
  r.runs.all (fun w => decide (0 < w.coeffs.size) && decide (1 ≤ w.step) && Blk.placeOk St G w.oracle w.part (St.tableBits w.oracle w.part) (w.first + w.step * (w.coeffs.size - 1))) &&
  r.forms.all (fun f => Blk.placeOk St G f.oracle .main (St.tableBits f.oracle .main) 0 && f.c.fits (St.tableBits f.oracle .main))

/-- The Bool says RowIn. -/
theorem rowInB_iff (St : Statement) (G : Group) (r : OnBytes.Row) : rowInB St G r = true ↔ Means.RowIn St G r := by
  unfold rowInB
  simp only [Bool.and_eq_true, Array.all_eq_true_iff_forall_mem, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
    exact ⟨fun t ht => h1 t (Array.mem_toList_iff.1 ht), fun u hu => h2 u (Array.mem_toList_iff.1 hu),
      fun w hw => ⟨(h3 w (Array.mem_toList_iff.1 hw)).1.1, (h3 w (Array.mem_toList_iff.1 hw)).1.2, (h3 w (Array.mem_toList_iff.1 hw)).2⟩,
      fun f hf => h4 f (Array.mem_toList_iff.1 hf)⟩
  · intro H
    exact ⟨⟨⟨fun t ht => H.terms t (Array.mem_toList_iff.2 ht), fun u hu => H.units u (Array.mem_toList_iff.2 hu)⟩,
      fun w hw => ⟨⟨(H.runs w (Array.mem_toList_iff.2 hw)).1, (H.runs w (Array.mem_toList_iff.2 hw)).2.1⟩, (H.runs w (Array.mem_toList_iff.2 hw)).2.2⟩⟩,
      fun f hf => H.forms f (Array.mem_toList_iff.2 hf)⟩

/-- Of the first chain's last state: I's and V's sample rows and the own group's open row. orc: the plan's numbers. -/
def HandedIn (orc : Nat → Option Nat) (s : VerifiableInference.Desc.Key.FirstState) : Prop :=
  (∀ k ∈ [0, 2], ∀ o, orc k = some o → SampleIn s.d.st o) ∧ OpenIn s.d.st (s.d.st.groups.size - 1)

/-- A statement in order (Means.InOrder) has the fence on the rows' content at every message and every group. -/
theorem sampleIn_of_order {St : Statement} (h : Means.InOrder St) (o : Nat) : SampleIn St o := fun y hy r hr => h.samples o y hy r hr

theorem openIn_of_order {St : Statement} (h : Means.InOrder St) (g : Nat) : OpenIn St g := fun G hG r hr => h.rows g G hG r hr

theorem handedIn_of_order (orc : Nat → Option Nat) (s : VerifiableInference.Desc.Key.FirstState) (h : Means.InOrder s.d.st) : HandedIn orc s :=
  ⟨fun _ _ o _ => sampleIn_of_order h o, openIn_of_order h _⟩

end Johnson.RunOne.KeyRows23

#print axioms Johnson.RunOne.KeyRows23.handedIn_of_order
#print axioms Johnson.RunOne.KeyRows23.rowInB_iff
#print axioms Johnson.RunOne.KeyRows23.borderB_spec
