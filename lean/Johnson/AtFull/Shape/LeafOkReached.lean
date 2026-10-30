-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Shape/LeafOkReached.lean: IN FRONT OF THE FIRST SUB-PROTOCOL OF LINK m + 1 (m < 24)
OF THE PROOF FILE's OWN FIRST CHAIN THE CODE SWITCH's TEST "WHAT SHARES A LEAF" (leafOk,
Johnson/Top/H0/Tw/K2C/Asks.lean; [G9] of Johnson/Top/H0/Tw/K2/Switch.lean) ACCEPTS AT EVERY TREE
WHOSE PARTS ARE AMONG THE MESSAGES OF THE CARRIED ROWS. At the proof file's seat, in the goals'
scope, from the fold's return alone, and at a reached state; whoever plays.

How. The carried rows' messages are the layout's members and the fresh mask's message
(singleRowsOracles, OnBytes/Iop/Fold.lean). Each member has the list [m] (lists_at_switch,
MarksReached.lean). The fresh mask's message counts no answer, so the test does not read its list:
the closing spends it as a mask, and the ground's routine for that asks "its shape counts no answer"
(spendAsMaskL, Johnson/Desc/First/Base/Ground.lean); the statement only grows from there
(closed_behind_laid, Johnson/Desc/K2/Honest/Returns/ClosedReached.lean), and the carried rows name
that message (closeFrame_reads, Johnson/Desc/First/Link/Law/CloseReads.lean).

  Blank id T: the message number id is there and its shape counts no answer. blank_can_fail: a
    CONTROL. blank_grows, blank_spent.
  fold_clause: a yes of the fold gives Blank at its mask, of the statement that the fold is HANDED.
    closing_blank, closeFrame_blank: behind a yes of the closing, of the frame's closing: the
    frame's mask is some id, and Blank id of the statement behind. (The walk through the three texts
    is that of fold_st, closing_st, closeFrame_st, Johnson/Desc/First/Close/Law/StBehind.lean.)
  leafOk_of_rows: the law on a statement and carried rows: from the members' lists and Blank at the
    fresh mask.
  fresh_blank: Blank at the carried rows' fresh mask, at the cut 14 (m + 1) + 2.
  **leafOk_at_switch**, **leafOk_reached**: the top, of a fold's return and of a reached state.

Limits. The cuts 14 (m + 1) + 2, m < 24: in front of the switch at the links 1 to 23; AT LINK 24
(338) IN FRONT OF THE PLACE "H:1", NOT OF THE HEAD's SWITCH (339): that, and the place behind the
last segment: LeafOkArms.lean. THAT A TREE WHICH THE SWITCH OPENS HAS ITS PARTS AMONG THESE MESSAGES
IS A PREMISE HERE. At the state's own statement: the switch asks the test at the statement behind
its own sending, which has these messages as they are; that step is not taken here. It stands over
one file of another house's (Returns/ClosedReached.lean). leafOk_reached asks "reached" over the
wrapped sub-protocols and spends it through the members' own family alone. Of a reached state: that
anything is reached is not said. Nothing on soundness, completeness or hiding.
-/
import Johnson.AtFull.Shape.MarksReached
import Johnson.Desc.K2.Honest.Returns.ClosedReached
import Johnson.Desc.First.Link.Law.CloseReads

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Chain FileDescription foldBlocks Grows)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Close
open VerifiableInference.Desc.LinkJoin (closeFrame_reads)
open VerifiableInference.Desc.K2.Honest.Returns (closed_behind_laid)
open VerifiableInference.Desc.Sound (below)
open Johnson.Desc.First.Walk.Tied (Reach reach_raw)
open _root_.Tw.K2 (leafOk)
open ProofFile (Cl)

/-! ## 1 A message that counts no answer -/

/-- The message number id is there and its shape counts no answer. -/
def Blank (id : Nat) (T : Statement) : Prop :=
  ∃ x, T.oracles[id]? = some x ∧ x.shape.answers = 0

/-- CONTROL: a message whose shape counts an answer is not blank. -/
theorem blank_can_fail : ¬ Blank 0 { oracles := #[{ shape := { answers := 1 } }] } := by
  rintro ⟨x, hx, ha⟩
  obtain rfl := Option.some.inj hx
  cases ha

/-- A statement that grows keeps each message's shape. -/
theorem blank_grows {T T' : Statement} {id : Nat} (h : Grows T T') (b : Blank id T) :
    Blank id T' := by
  obtain ⟨x, hx, ha⟩ := b
  obtain ⟨x', hx', g⟩ := h.2.2 id x hx
  exact ⟨x', hx', by rw [g.1]; exact ha⟩

/-- Spending a message as a mask leaves its shape. -/
theorem blank_spent {T : Statement} {id : Nat} (b : Blank id T) : Blank id (spent T id) := by
  obtain ⟨x, hx, ha⟩ := b
  refine ⟨{ x with spentAsMask := true }, ?_, ha⟩
  show (T.oracles.modify id fun x => { x with spentAsMask := true })[id]? = _
  rw [Array.getElem?_modify, if_pos rfl, hx]
  rfl

/-- A yes of the fold: in the statement that it is handed the mask's message is there and counts no
answer. -/
theorem fold_clause {T T' : Statement} {F : FoldShape} {row : GroupRow} {m : Nat}
    {es : List Fmt.Entry} {rs : List Fmt.RoundView} {out : SingleRows}
    (h : fold T F row m es rs = .ok (out, T')) : Blank m T := by
  unfold fold at h
  cases hD : foldD 0 (onSt T) F row (some m) es rs with
  | error e => rw [hD] at h; exact absurd h (by simp [Except.map])
  | ok y =>
    clear h
    unfold foldD at hD
    split at hD
    · rename_i eE eR rE rR
      obtain ⟨_, -, hD⟩ := ok_bind hD
      obtain ⟨_, -, hD⟩ := ok_bind hD
      obtain ⟨_, -, hD⟩ := ok_bind hD
      obtain ⟨p, k2, hD⟩ := ok_bind hD
      simp only [pure, Except.pure, Except.ok.injEq] at k2
      subst k2
      obtain ⟨_, -, hD⟩ := ok_bind hD
      obtain ⟨_, -, hD⟩ := ok_bind hD
      obtain ⟨d2, k5, hD⟩ := ok_bind hD
      have k5 := got_ok k5
      clear hD
      unfold VerifiableInference.Desc.Ground.spendAsMaskP at k5
      split at k5
      · rename_i hok
        have h1 : (T.oracles[m]?).isSome = true :=
          VerifiableInference.Desc.Ground.clause_of_ok _ hok
            ("spendAsMask: the message is there", (T.oracles[m]?).isSome)
            (by simp [VerifiableInference.Desc.Ground.spendAsMaskL, onSt])
        have h3 : VerifiableInference.Desc.Ground.has (T.oracles[m]?)
            (fun x => x.shape.answers == 0) = true :=
          VerifiableInference.Desc.Ground.clause_of_ok _ hok
            ("spendAsMask: its shape counts no answer",
              VerifiableInference.Desc.Ground.has (T.oracles[m]?) (fun x => x.shape.answers == 0))
            (by simp [VerifiableInference.Desc.Ground.spendAsMaskL, onSt])
        cases hx : T.oracles[m]? with
        | none => rw [hx] at h1; cases h1
        | some x =>
          rw [hx] at h3
          exact ⟨x, hx, by simpa [VerifiableInference.Desc.Ground.has] using h3⟩
      · cases k5
    · exact absurd hD (by simp)

/-- **Behind a yes of the closing.** -/
theorem closing_blank {Q : Plan} {T T' : Statement} {g : Nat} {mask : Option Nat}
    {rs : List Fmt.RoundView} {out : SingleRows} (h : closing Q T g mask rs = .ok (out, T')) :
    ∃ id, mask = some id ∧ Blank id T' := by
  unfold closing at h
  split at h
  · obtain ⟨m, k0, h⟩ := ok_bind h
    obtain ⟨p, k1, h⟩ := ok_bind h
    obtain ⟨_, -, h⟩ := ok_bind h
    refine ⟨m, got_ok k0, ?_⟩
    rw [fold_st h]
    exact blank_spent (fold_clause h)
  · exact absurd h (by simp)

/-- **Behind a yes of the frame's closing.** -/
theorem closeFrame_blank {owed : Option Nat} {f : ReqFrame} {T : Statement} {es : List Fmt.Entry}
    {rs : List Fmt.RoundView} {x : ReqFrame × Statement} (h : closeFrame owed f T es rs = .ok x) :
    ∃ id, f.mask = some id ∧ Blank id x.2 := by
  unfold closeFrame at h
  obtain ⟨_, -, h⟩ := ok_bind h
  obtain ⟨L, -, h⟩ := ok_bind h
  obtain ⟨Gf, -, h⟩ := ok_bind h
  obtain ⟨_, -, h⟩ := ok_bind h
  obtain ⟨y, kc, h⟩ := ok_bind h
  obtain ⟨id, e1, e2⟩ := closing_blank (out := y.1) (T' := y.2) kc
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  exact ⟨id, e1, e2⟩

/-- **Where each member of the rows' layout has the list [k] and the fresh mask's message counts no
answer, the test accepts at every tree whose parts are among the rows' messages.** -/
theorem leafOk_of_rows {T : Statement} {rows : SingleRows} {k : Nat}
    (hl : ∀ o ∈ rows.layout.members, listAt T o = some [k]) (hb : Blank rows.fresh T) (tree : Tree)
    (hp : ∀ q ∈ tree.parts.toList, q ∈ (singleRowsOracles rows).toList) :
    leafOk T tree = true := by
  refine leafOk_of_lists T tree k fun o ho x hx hne => ?_
  have member : o ∈ rows.layout.members → x.groups = [k] := by
    intro hm
    have h := hl o hm
    unfold listAt at h
    rw [hx] at h
    exact Option.some.inj h
  have hq := hp o ho
  unfold singleRowsOracles at hq
  split at hq
  · rw [Array.toList_push, List.mem_append, List.mem_singleton] at hq
    rcases hq with hq | rfl
    · exact member (Array.mem_toList_iff.1 hq)
    · obtain ⟨x', hx', ha⟩ := hb
      rw [hx] at hx'
      obtain rfl := Option.some.inj hx'
      exact absurd ha hne
  · exact member (Array.mem_toList_iff.1 hq)

variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-! ## 2 At the chain -/

/-- **The carried rows' fresh mask's message counts no answer.** -/
theorem fresh_blank (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {m : Nat} (h24 : m < 24)
    {p : ProofFile.InstPub} {R R₂ : List Fmt.RoundView} {C C₂ : List VerifiableInference.Desc.OpenedColumn} {t₂ : S}
    (f₂ : foldBlocks 0 (c.blocksInOrder.take (14 * (m + 1) + 2)) (ProofFile.startS Z p) R C = .ok (t₂, R₂, C₂)) :
    Blank t₂.check.frame.rows.fresh t₂.st := by
  obtain ⟨owed, f, T₀, es, rs, x, hx, hf, hg⟩ := closed_behind_laid hS hR O h24 f₂
  obtain ⟨id, e1, hb⟩ := closeFrame_blank hx
  obtain ⟨_, id', -, -, e2, e3⟩ := closeFrame_reads hx
  obtain rfl : id = id' := Option.some.inj (e1.symm.trans e2)
  rw [hf, e3]
  exact blank_grows hg hb

/-- **"WHAT SHARES A LEAF" ACCEPTS AT EVERY TREE WHOSE PARTS ARE AMONG THE CARRIED ROWS'
MESSAGES.** -/
theorem leafOk_at_switch (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {m : Nat} (h24 : m < 24)
    {p : ProofFile.InstPub} {R R₂ : List Fmt.RoundView} {C C₂ : List VerifiableInference.Desc.OpenedColumn} {t₂ : S}
    (f₂ : foldBlocks 0 (c.blocksInOrder.take (14 * (m + 1) + 2)) (ProofFile.startS Z p) R C = .ok (t₂, R₂, C₂))
    (tree : Tree)
    (hp : ∀ q ∈ tree.parts.toList, q ∈ (singleRowsOracles t₂.check.frame.rows).toList) :
    leafOk t₂.st tree = true :=
  leafOk_of_rows (lists_at_switch hS hR O h24 f₂) (fresh_blank hS hR O h24 f₂) tree hp

/-- **The same at a reached state.** -/
theorem leafOk_reached (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {m : Nat} (h24 : m < 24)
    {z : ProofFile.InstPub} {s : S}
    (hr : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) (14 * (m + 1) + 2) (z, s)) (tree : Tree)
    (hp : ∀ q ∈ tree.parts.toList, q ∈ (singleRowsOracles s.check.frame.rows).toList) :
    leafOk s.st tree = true := by
  obtain ⟨-, rs, cols, f⟩ := (reach_raw hr).fold
  exact leafOk_at_switch hS hR O h24 f tree hp

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.Blank
#print axioms Johnson.AtFull.Shape.blank_can_fail
#print axioms Johnson.AtFull.Shape.blank_grows
#print axioms Johnson.AtFull.Shape.blank_spent
#print axioms Johnson.AtFull.Shape.fold_clause
#print axioms Johnson.AtFull.Shape.closing_blank
#print axioms Johnson.AtFull.Shape.closeFrame_blank
#print axioms Johnson.AtFull.Shape.leafOk_of_rows
#print axioms Johnson.AtFull.Shape.fresh_blank
#print axioms Johnson.AtFull.Shape.leafOk_at_switch
#print axioms Johnson.AtFull.Shape.leafOk_reached
