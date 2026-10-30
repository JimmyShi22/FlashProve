-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Link/Law/DoorBlind.lean: WHAT THE ONE EQUATION's SUB-PROTOCOL TURNS OF THE
STATEMENT's ORACLE MESSAGES: THE MASK LEDGER OF ONE MESSAGE OF THE LINK's OWN, AND NOTHING ELSE (our
files call a sub-protocol a block). So whatever reads a message without its mask ledger, and
whatever reads another message, is as it was: «the verifier's state holds the OOD sample»
(`smpHeld`), «the index masks' message is there», and, where the link's own messages are not the
index masks' message, «the pending claim on the weights can be made» (`hasRow`). Theorems.

What is said.
  `Blind f`: f does not read a message's mask ledger. `SameBy f A B`: the codes, and at every number
    the value of f, are as they were. `takeMask_blind`, `takeN_blind`; `takeMask_other`,
    `takeN_other`; `asRow_both`, `door_both`, `eq_both`: a blind f's values are as they were; and
    the oracle messages are as they were, or there is a message o of the link's own (`messageNow` at
    the link's frame) such that every other message is as it was. `tri`, `smpHeld_same`: `smpHeld`
    reads the codes, the book, and the blind triple (shape, the mark «sampled», the stored sample
    rows). `out_set`, `check_set`, `leftOf_set`. `eq_held`, `eq_there`, `eq_hasRow`: **the three
    sentences at an accepting step of a block each of whose accepting steps is the one equation's**;
    the third under «no message of the link's own is the index masks' message».

Limits. «No message of the link's own is the index masks' message» is a premise: a fact on the
frame's numbering of the messages: shown here of no frame. Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.EqLays
import Johnson.Desc.SmpRows
import Johnson.Top.H0.Walk.FrameRow
import Johnson.Desc.First.Pend.RowMeans

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open VerifiableInference.Desc.K9 (atS Where door asRow takeN messageNow)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.First (S)

/-- f does not read a message's mask ledger. -/
def Blind {β : Type} (f : OnBytes.Oracle → β) : Prop := ∀ x l, f { x with ledger := l } = f x

/-- At every number the value of f is as it was; the codes too. -/
abbrev SameBy {β : Type} (f : OnBytes.Oracle → β) (A B : Statement) : Prop :=
  B.codes = A.codes ∧ ∀ j : ℕ, (B.oracles[j]?).map f = (A.oracles[j]?).map f

variable {β : Type} {f : OnBytes.Oracle → β}

theorem takeMask_blind (hf : Blind f) {X : Type} (d d' : K9.St X) (o n : ℕ)
    (h : Ground.takeMaskP d o = some (n, d')) : SameBy f d.st d'.st := by
  unfold Ground.takeMaskP at h
  split at h
  · obtain ⟨l, _, e⟩ := Option.map_eq_some_iff.mp h
    have e2 : d' = _ := (congrArg Prod.snd e).symm
    rw [e2]
    refine ⟨rfl, fun j => ?_⟩
    show ((d.st.oracles.modify o _)[j]?).map f = _
    rw [Array.getElem?_modify]
    by_cases e : o = j
    · rw [if_pos e]
      cases d.st.oracles[j]? with
      | none => rfl
      | some x => exact congrArg some (hf x _)
    · rw [if_neg e]
  · simp at h

theorem takeN_blind (hf : Blind f) {X : Type} (o : ℕ) : ∀ (n : ℕ) (d : K9.St X) (acc : List ℕ)
    (x : List ℕ × K9.St X), takeN o n d acc = .ok x → SameBy f d.st x.2.st
  | 0, d, acc, x, h => by
    have e : (acc.reverse, d) = x := Except.ok.inj h
    rw [← e]
    exact ⟨rfl, fun _ => rfl⟩
  | n + 1, d, acc, x, h => by
    rw [takeN] at h
    obtain ⟨y, hy, h⟩ := ok_bind h
    have a := takeMask_blind hf d y.2 o y.1 (there_ok hy)
    have b := takeN_blind hf o n y.2 _ x h
    exact ⟨b.1.trans a.1, fun j => (b.2 j).trans (a.2 j)⟩

theorem takeMask_other {X : Type} (d d' : K9.St X) (o n : ℕ)
    (h : Ground.takeMaskP d o = some (n, d')) (j : ℕ) (hj : j ≠ o) :
    d'.st.oracles[j]? = d.st.oracles[j]? := by
  unfold Ground.takeMaskP at h
  split at h
  · obtain ⟨l, _, e⟩ := Option.map_eq_some_iff.mp h
    have e2 : d' = _ := (congrArg Prod.snd e).symm
    rw [e2]
    show (d.st.oracles.modify o _)[j]? = _
    rw [Array.getElem?_modify, if_neg (Ne.symm hj)]
  · simp at h

theorem takeN_other {X : Type} (o j : ℕ) (hj : j ≠ o) : ∀ (n : ℕ) (d : K9.St X) (acc : List ℕ)
    (x : List ℕ × K9.St X), takeN o n d acc = .ok x → x.2.st.oracles[j]? = d.st.oracles[j]?
  | 0, d, acc, x, h => by
    have e : (acc.reverse, d) = x := Except.ok.inj h
    rw [← e]
  | n + 1, d, acc, x, h => by
    rw [takeN] at h
    obtain ⟨y, hy, h⟩ := ok_bind h
    rw [takeN_other o j hj n y.2 _ x h, takeMask_other d y.2 o y.1 (there_ok hy) j hj]

/-- The row's making: blind values stay; and all messages but one of the link's own. -/
theorem asRow_both (hf : Blind f) {X : Type} (Rr : ReqRows) (fr : ReqFrame) (q : K9.Equation)
    (d d' : K9.St X) (row : OnBytes.Row) (h : asRow Rr fr q d = .ok (row, d')) :
    SameBy f d.st d'.st ∧ (d' = d ∨ ∃ m o, messageNow fr fr.link m = some o ∧
      ∀ j, j ≠ o → d'.st.oracles[j]? = d.st.oracles[j]?) := by
  unfold asRow at h
  obtain ⟨row0, _, h⟩ := ok_bind h
  by_cases he : q.onMasks.isEmpty = true
  · simp only [he, if_true] at h
    have e : d = d' := congrArg Prod.snd (Except.ok.inj h)
    rw [← e]
    exact ⟨⟨rfl, fun _ => rfl⟩, Or.inl rfl⟩
  · simp only [he, Bool.false_eq_true, if_false] at h
    obtain ⟨m, _, h⟩ := ok_bind h
    obtain ⟨_, _, h⟩ := ok_bind h
    obtain ⟨o', ho', h⟩ := ok_bind h
    obtain ⟨x, hx, h⟩ := ok_bind h
    obtain ⟨_, _, h⟩ := ok_bind h
    have e : x.2 = d' := congrArg Prod.snd (Except.ok.inj h)
    rw [← e]
    exact ⟨takeN_blind hf o' _ d [] x hx, Or.inr ⟨m, o', there_ok ho', fun j hj =>
      takeN_other o' j hj _ d [] x hx⟩⟩

/-- The one equation's door. -/
theorem door_both (hf : Blind f) {X : Type} (owed : K9.RowsOwed) (laid : Option ℕ) (L : LinkCtx)
    (F : Fork) (d : K9.St X) (out : K9.Out X) (h : door owed laid L F d = .ok out) :
    SameBy f d.st out.d.st ∧ (out.d.st.oracles = d.st.oracles ∨
      ∃ m o, messageNow L.check.frame L.check.frame.link m = some o ∧
        ∀ j, j ≠ o → out.d.st.oracles[j]? = d.st.oracles[j]?) := by
  obtain ⟨q, G, row, d1, _, hr, hadd⟩ := door_addRowP _ _ _ _ _ _ h
  have hout : out.d = { d1 with st := Slice.withRow d1.st L.check.group row } := by
    unfold Ground.addRowP at hadd
    split at hadd
    · exact (Option.some.inj hadd).symm
    · simp at hadd
  obtain ⟨e1, e2⟩ := asRow_both hf _ _ _ _ _ _ hr
  rw [hout]
  refine ⟨e1, ?_⟩
  rcases e2 with rfl | ⟨m, o, ho, hj⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨m, o, ho, hj⟩

theorem bind_blind {α γ δ : Type} (g : α → γ) (k : γ → Option δ) (x y : Option α)
    (h : x.map g = y.map g) : (x.bind fun a => k (g a)) = y.bind fun a => k (g a) := by
  cases x <;> cases y <;> simp_all

/-- The triple that «the state holds the OOD sample» reads of a message. -/
def tri (x : OnBytes.Oracle) : OracleShape × Bool × Array OnBytes.Row :=
  (x.shape, x.sampled, x.sampleRows)

theorem tri_blind : Blind tri := fun _ _ => rfl

/-- «The state holds the OOD sample» reads the codes, the book and the triple. -/
theorem smpHeld_same (A B : Statement) (book : TreeBook) (h : SameBy tri A B) (j t : ℕ) :
    smpHeld B book j t = smpHeld A book j t := by
  have hrows : smpRows B book j t = smpRows A book j t := by
    unfold smpRows
    refine congrArg (Option.bind (oracleNo book j t)) (funext fun o => ?_)
    exact bind_blind tri (fun y => if y.2.1 && decide (0 < y.1.answers) &&
      y.2.2.size == y.1.answers then some y.2.2 else none) _ _ (h.2 o)
  have hseed : smpSeed B book j t = smpSeed A book j t := by
    unfold smpSeed
    rw [hrows, h.1]
    refine congrArg (Option.bind (oracleNo book j t)) (funext fun o => ?_)
    exact bind_blind tri (fun y => (smpRows A book j t).bind fun rows => (rows[0]?).bind fun r =>
      (seedOf A.codes y.1 r).map fun sd => (sd, rows.toList.map (·.target))) _ _ (h.2 o)
  unfold smpHeld
  rw [hseed]

/-- What goes on to the later chains is not what the lens writes. -/
theorem out_set (s : S) (q : K9.Part) : (atS.set s q).out = s.out := by
  obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := s
  cases here with
  | head x =>
    show ((S.putLink ⟨st, book, roots, rowsOwed, failed, check, out, .head x, req⟩ q.L).putFork
      q.F).out = _
    by_cases ho : x.opened = true <;> simp [S.putLink, S.putFork, ho]
  | _ => rfl

/-- Nor is the state of the calls over the links. -/
theorem check_set (s : S) (q : K9.Part) : (atS.set s q).check = s.check := by
  obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := s
  cases here with
  | head x =>
    show ((S.putLink ⟨st, book, roots, rowsOwed, failed, check, out, .head x, req⟩ q.L).putFork
      q.F).check = _
    by_cases ho : x.opened = true <;> simp [S.putLink, S.putFork, ho]
  | _ => rfl

/-- What is left for the pending claim is not read off what the lens writes. -/
theorem leftOf_set (s : S) (q : K9.Part) :
    Johnson.Desc.First.Walk.Law.leftOf (atS.set s q) = Johnson.Desc.First.Walk.Law.leftOf s := by
  obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := s
  cases here with
  | head x =>
    by_cases ho : x.opened = true
    · show Johnson.Desc.First.Walk.Law.leftOf
        ((S.putLink ⟨st, book, roots, rowsOwed, failed, check, out, .head x, req⟩ q.L).putFork
          q.F) = _
      simp only [S.putLink, S.putFork, ho, if_true]
      rfl
    · show Johnson.Desc.First.Walk.Law.leftOf
        ((S.putLink ⟨st, book, roots, rowsOwed, failed, check, out, .head x, req⟩ q.L).putFork
          q.F) = _
      simp only [S.putLink, S.putFork, ho, Bool.false_eq_true, if_false]
  | _ => rfl

section
variable {Cl : Type} (pw : Where) (b₃ : Block S Cl)
  (hb₃ : ∀ ft s rs cols x, b₃.step ft s rs cols = .ok x →
    (K9.oneEquation (Cl := Cl) atS pw).step ft s rs cols = .ok x)
include hb₃

/-- What an accepting step says, at the state's own statement. -/
theorem eq_both (hf : Blind f) (ft : ℕ) (s : S) (rs : List Fmt.RoundView) (cols : List OpenedColumn) (s' : S)
    (k : ℕ) (h : b₃.step ft s rs cols = .ok (s', k)) :
    ∃ a, atS.get? s = some a ∧ SameBy f s.st s'.st ∧ (s'.st.oracles = s.st.oracles ∨
      ∃ m o, messageNow a.L.check.frame a.L.check.frame.link m = some o ∧
        ∀ j, j ≠ o → s'.st.oracles[j]? = s.st.oracles[j]?) := by
  obtain ⟨a, out, ha, hdoor, rfl⟩ := oneEquation_inv atS pw _ _ _ _ _ k (hb₃ _ _ _ _ _ h)
  have e := door_both hf _ _ _ _ _ _ hdoor
  rw [(part_reads s a ha).2] at e
  exact ⟨a, ha, e⟩

/-- **«The state holds the OOD sample» is as it was.** -/
theorem eq_held (ft : ℕ) (s : S) (rs : List Fmt.RoundView) (cols : List OpenedColumn) (s' : S) (k : ℕ)
    (h : b₃.step ft s rs cols = .ok (s', k)) (j t : ℕ) :
    smpHeld s'.st s'.book j t = smpHeld s.st s.book j t := by
  obtain ⟨_, _, _, _, _, El⟩ := eq_lays pw b₃ hb₃ ft s rs cols s' k h
  obtain ⟨_, _, e, _⟩ := eq_both pw b₃ hb₃ tri_blind ft s rs cols s' k h
  rw [El.book]
  exact smpHeld_same _ _ _ e j t

/-- **A message that was there is there.** -/
theorem eq_there (ft : ℕ) (s : S) (rs : List Fmt.RoundView) (cols : List OpenedColumn) (s' : S) (k : ℕ)
    (h : b₃.step ft s rs cols = .ok (s', k)) (j : ℕ) :
    (s'.st.oracles[j]?).isSome = (s.st.oracles[j]?).isSome := by
  obtain ⟨_, _, e, _⟩ := eq_both pw b₃ hb₃ tri_blind ft s rs cols s' k h
  rw [← Option.isSome_map (f := tri), e.2 j, Option.isSome_map]

/-- **«The pending claim on the weights can be made» is as it was**, where no message of the link's
own is the index masks' message. -/
theorem eq_hasRow (ft : ℕ) (s : S) (rs : List Fmt.RoundView) (cols : List OpenedColumn) (s' : S) (k : ℕ)
    (h : b₃.step ft s rs cols = .ok (s', k))
    (hne : ∀ a, atS.get? s = some a → ∀ m o,
      messageNow a.L.check.frame a.L.check.frame.link m = some o → o ≠ s.out.indexMasks)
    (lay : WsLay) (n : ℕ) (lin : Params.LinShape) :
    Johnson.Desc.First.Walk.Law.hasRow lay n lin s' =
      Johnson.Desc.First.Walk.Law.hasRow lay n lin s := by
  obtain ⟨a, ha, _, e⟩ := eq_both pw b₃ hb₃ tri_blind ft s rs cols s' k h
  obtain ⟨a0, out, ha0, _, hs'⟩ := oneEquation_inv atS pw _ _ _ _ _ k (hb₃ _ _ _ _ _ h)
  have hout : s'.out = s.out := by
    rw [hs']
    exact out_set s _
  have hleft : Johnson.Desc.First.Walk.Law.leftOf s' = Johnson.Desc.First.Walk.Law.leftOf s := by
    rw [hs']
    exact leftOf_set s _
  have hor : s'.st.oracles[s.out.indexMasks]? = s.st.oracles[s.out.indexMasks]? := by
    rcases e with e | ⟨m, o, ho, hj⟩
    · rw [e]
    · exact hj _ (Ne.symm (hne a ha m o ho))
  have key : ∀ (A B : Array OnBytes.Oracle) (i : ℕ) (w : WsForkOut) (r : TensorRow),
      B[i]? = A[i]? → (∃ os, First.Pend.pendingRowO lay i w n lin A = .ok (r, os)) →
      ∃ os, First.Pend.pendingRowO lay i w n lin B = .ok (r, os) := by
    intro A B i w r hAB ⟨os, hos⟩
    obtain ⟨c1, c2, c3, c4, fi, la, c5, c6, c7, c8, c9, Ga, c10, g, c11, l, c12, c, l', c13, c14,
      _⟩ := (First.Pend.pendingRowO_iff lay i w n lin A os r).1 hos
    exact ⟨_, (First.Pend.pendingRowO_iff lay i w n lin B _ r).2 ⟨c1, c2, c3, c4, fi, la, c5, c6,
      c7, c8, c9, Ga, c10, g, c11, l, by rw [hAB]; exact c12, c, l', c13, c14, rfl⟩⟩
  have hrow : Johnson.Desc.First.Walk.Law.rowAt lay n lin s' =
      Johnson.Desc.First.Walk.Law.rowAt lay n lin s := by
    apply Option.ext
    intro r
    unfold Johnson.Desc.First.Walk.Law.rowAt
    rw [Johnson.Desc.First.Walk.Law.rowBy_some, Johnson.Desc.First.Walk.Law.rowBy_some, hleft,
      hout]
    constructor
    · rintro ⟨w, os, hw, hp⟩
      obtain ⟨os', hp'⟩ := key _ _ _ w r hor.symm ⟨os, hp⟩
      exact ⟨w, os', hw, hp'⟩
    · rintro ⟨w, os, hw, hp⟩
      obtain ⟨os', hp'⟩ := key _ _ _ w r hor ⟨os, hp⟩
      exact ⟨w, os', hw, hp'⟩
  unfold Johnson.Desc.First.Walk.Law.hasRow
  rw [hrow]

end

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.door_both
#print axioms VerifiableInference.Desc.LinkJoin.smpHeld_same
#print axioms VerifiableInference.Desc.LinkJoin.eq_both
#print axioms VerifiableInference.Desc.LinkJoin.eq_held
#print axioms VerifiableInference.Desc.LinkJoin.eq_there
#print axioms VerifiableInference.Desc.LinkJoin.eq_hasRow
