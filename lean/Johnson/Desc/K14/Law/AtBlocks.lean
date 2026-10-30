-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Law/AtBlocks.lean: the shared chain's eight blocks in front of the two proximity
tests: where their decisions say yes one behind the other, the places have run (SharedRun).

Main names: why_some, named_some, recvP_relabel, layRows_keeps, decideSend_inv, sendAt_inv,
blocks_inv, sharedRun_of_blocks, decidesBySplit_of_blocks.

What is not claimed. Nothing on the rounds' form, which the format's step asks in front of a
decision. Nothing on the two proximity tests or on the chain's end. Nothing on soundness.

-/
import Johnson.Desc.K14.Law.Admit
import Johnson.Desc.K14.Blocks

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain
open VerifiableInference.Desc (Grows Block named need)
open VerifiableInference.Desc.Ground
open VerifiableInference.Desc.K1 (decideSend layRows sendOwn Owing)

/-- A yes under a clause's name is the function's yes. -/
theorem why_some {l : Clauses} {x : Option St} {d : St} (h : why l x = .ok d) : x = some d := by
  cases x with
  | none => cases h
  | some y => cases h; rfl

/-- A value under a test's name is there. -/
theorem named_some {α : Type} {n : String} {x : Option α} {a : α} (h : named n x = .ok a) :
    x = some a := by
  cases x with
  | none => cases h
  | some y => cases h; rfl

/-- Two steps that end well: the first has ended well. -/
theorem ebind_ok {α β : Type} {x : Except String α} {f : α → Except String β} {b : β}
    (h : x.bind f = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

/-- The same, for the sign of a do block. -/
theorem dbind_ok {α β : Type} {x : Except String α} {f : α → Except String β} {b : β}
    (h : (x >>= f) = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := ebind_ok h

/-- A step that ends well behind a map. -/
theorem emap_ok {α β : Type} {x : Except String α} {f : α → β} {b : β}
    (h : x.map f = .ok b) : ∃ a, x = .ok a ∧ f a = b := by
  cases x with
  | error e => cases h
  | ok a => cases h; exact ⟨a, rfl, rfl⟩

/-- The receiving of oracle messages does not read the carried record's own value. -/
theorem recvP_relabel {L L' : Type} (ft : Nat) (d : DState L) (l' : L')
    (sent : Array OracleNotice) (ids : Array Nat) (x : DState L')
    (h : recvP ft (⟨d.st, d.book, d.roots, d.opened, l'⟩ : DState L') sent = some (ids, x)) :
    recvP ft d sent = some (ids, ⟨x.st, x.book, x.roots, x.opened, d.loc⟩) := by
  unfold recvP at h ⊢
  dsimp only at h ⊢
  split at h
  · rename_i hc
    rw [if_pos hc]
    simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h ⊢
    obtain ⟨lay, hl, rfl, rfl⟩ := h
    exact ⟨lay, hl, rfl, rfl⟩
  · cases h

/-- The laying of the sample rows: the statement grows; no group turns. -/
theorem layRows_keeps {L : Type} (codes : Codes) (seeds : List (List E × E)) :
    ∀ (l : List (Nat × OracleShape)) (ys : List E) (d d' : DState L),
      layRows codes seeds l ys d = .ok d' →
      Grows d.st d'.st ∧ d'.st.groups = d.st.groups := by
  intro l
  induction l with
  | nil =>
    intro ys d d' h
    simp only [layRows] at h
    split at h
    · cases h; exact ⟨Grows.refl _, rfl⟩
    · cases h
  | cons x l ih =>
    intro ys d d' h
    obtain ⟨o, s⟩ := x
    simp only [layRows] at h
    split at h
    · exact ih _ _ _ h
    · split at h
      · cases h
      · split at h
        · cases h
        · obtain ⟨d1, h1, h2⟩ := ebind_ok h
          have h1' := named_some h1
          obtain ⟨g2, e2⟩ := ih _ _ _ h2
          have g1 := admitP_grows d d1 o _ h1'
          refine ⟨g1.trans g2, e2.trans ?_⟩
          unfold admitP at h1'
          split at h1'
          · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h1'
            obtain ⟨y, _, places, _, rfl⟩ := h1'
            rfl
          · cases h1'

/-- What a yes of the sending's decision is made of. -/
theorem decideSend_inv {L : Type} (Q : VerifiableInference.Desc.K1.Par) (owed : Option Nat)
    (d : DState L) (rs : List Fmt.RoundView) (ids : Array Nat) (d' : DState L)
    (h : decideSend Q owed d rs = .ok (ids, d')) :
    ∃ x1, recvP Q.gp.firstTree d Q.sent = some (ids, x1) ∧ Grows x1.st d'.st ∧
      d'.st.groups = x1.st.groups := by
  unfold decideSend at h
  split at h
  · obtain ⟨_, _, h⟩ := dbind_ok h
    obtain ⟨_, _, h⟩ := dbind_ok h
    obtain ⟨_, _, h⟩ := dbind_ok h
    obtain ⟨_, _, h⟩ := dbind_ok h
    obtain ⟨x, hx, h⟩ := dbind_ok h
    obtain ⟨_, _, h⟩ := dbind_ok h
    obtain ⟨_, _, h⟩ := dbind_ok h
    obtain ⟨d2, hl, h⟩ := dbind_ok h
    cases h
    obtain ⟨g, e⟩ := layRows_keeps _ _ _ _ _ _ hl
    exact ⟨x.2, named_some hx, g, e⟩
  · cases h

/-- What a yes of a sending at this chain's state is made of: the messages are received; the state
goes onward and the small record stays; the kind notes the new messages' numbers. -/
theorem sendAt_inv (P : P14) (n : String) (Q : VerifiableInference.Desc.K1.Par)
    (inFront : Option Fmt.Entry) (groups : List (List Nat)) (behind : St → Array Nat → Option St)
    (d d' : St) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h : (sendAt P n Q inFront groups behind).decide d rs gs = .ok d') :
    ∃ (ids : Array Nat) (a1 a2 : St), recvP Q.gp.firstTree d Q.sent = some (ids, a1) ∧
      Onward a1 a2 ∧ a2.loc = a1.loc ∧ behind a2 ids = some d' := by
  simp only [sendAt, Block.inside] at h
  obtain ⟨t, ht, h⟩ := ebind_ok h
  cases ht
  obtain ⟨t', ht', h⟩ := ebind_ok h
  simp only [sendOwn] at ht'
  obtain ⟨⟨ids, x2⟩, hx, rfl⟩ := emap_ok ht'
  obtain ⟨x1, hr, g, e⟩ := decideSend_inv Q none _ rs ids x2 hx
  refine ⟨ids, ⟨x1.st, x1.book, x1.roots, x1.opened, d.loc⟩,
    ⟨x2.st, x2.book, x2.roots, x2.opened, d.loc⟩, recvP_relabel _ d #[] _ ids x1 hr,
    ⟨g, fun gi => ⟨[], ?_⟩⟩, rfl, named_some h⟩
  rw [List.append_nil]
  unfold rowsOn
  show ((x2.st.groups[gi]?).map (·.rows.toList)).getD [] = _
  rw [e]

/-- The messages of a sending at this chain are those that it is given. -/
theorem parK1_sent (P : P14) (piece : Nat) (part : String) (sent : Array OracleNotice) :
    (parK1 P piece part sent).sent = sent := by
  simp [parK1, VerifiableInference.Desc.K1.Par.sent]

/-- "LOC" says yes at one round and one group of columns alone. -/
theorem loc_one (p : Par) (d d' : St) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h : loc p d rs gs = some d') : ∃ r cols, rs = [r] ∧ gs = [cols] := by
  unfold loc at h
  split at h
  · exact ⟨_, _, rfl, rfl⟩
  · cases h

/-- "LIN zeta" says yes at one round alone. -/
theorem linZeta_one (d d' : St) (rs : List Fmt.RoundView) (h : linZeta d rs = some d') :
    ∃ r, rs = [r] := by
  unfold linZeta at h
  split at h
  · exact ⟨_, rfl⟩
  · cases h

/-- **Where the eight blocks' decisions say yes one behind the other, the places have run.** -/
theorem sharedRun_of_blocks (P : P14) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hb : blocks P = some [b1, b2, b3, b4, b5, b6, b7, b8])
    (hS : P.S.sharedSplitNeeded = true) (d0 d1 d2 d3 d4 d5 d6 d7 d8 : St)
    (rs1 rs2 rs3 rs4 rs5 rs6 rs7 rs8 : List Fmt.RoundView)
    (gs1 gs2 gs3 gs4 gs5 gs6 gs7 gs8 : List (List (Nat × List UInt64)))
    (h1 : b1.decide d0 rs1 gs1 = .ok d1) (h2 : b2.decide d1 rs2 gs2 = .ok d2)
    (h3 : b3.decide d2 rs3 gs3 = .ok d3) (h4 : b4.decide d3 rs4 gs4 = .ok d4)
    (h5 : b5.decide d4 rs5 gs5 = .ok d5) (h6 : b6.decide d5 rs6 gs6 = .ok d6)
    (h7 : b7.decide d6 rs7 gs7 = .ok d7) (h8 : b8.decide d7 rs8 gs8 = .ok d8) :
    ∃ r4 cols, rs4 = [r4] ∧ gs4 = [cols] ∧ SharedRun P.par d0 d2 d3 d7 d8 r4 cols := by
  unfold blocks at hb
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq,
    List.cons.injEq, and_true] at hb
  obtain ⟨sentU, hU, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hb
  have k1 : linPoint P.par d0 rs1 = some d1 := why_some h1
  obtain ⟨idsU, a1, a2, rU, cU, cUl, k2⟩ := sendAt_inv _ _ _ _ _ _ d1 d2 rs2 gs2 h2
  have k3 : laysRec P.par d2 rs3 = some d3 := why_some h3
  have k4 : loc P.par d3 rs4 gs4 = some d4 := why_some h4
  obtain ⟨idsO, c1, c2, rO, cO, cOl, k5⟩ := sendAt_inv _ _ _ _ _ _ d4 d5 rs5 gs5 h5
  have k6 : joins P.par d5 rs6 = some d6 := why_some h6
  have k7 : linZeta d6 rs7 = some d7 := why_some h7
  have k8 : split P.par d7 rs8 = some d8 := why_some h8
  obtain ⟨r4, cols, rfl, rfl⟩ := loc_one _ _ _ _ _ k4
  obtain ⟨r7, rfl⟩ := linZeta_one _ _ _ k7
  obtain ⟨r8, rfl⟩ := split_one _ _ _ _ hS k8
  rw [parK1_sent] at rU rO
  exact ⟨r4, cols, rfl, rfl, hS, d1, a1, a2, d4, c1, c2, d5, d6, rs1, rs3, rs6, r7, r8, _, _,
    sentU, idsU, idsO, k1, hU, rU, cU, cUl, k2, k3, k4, rO, cO, cOl, k5, k6, k7, k8⟩

/-- The eighth block decides by "SPLIT". -/
theorem decidesBySplit_of_blocks (P : P14) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hb : blocks P = some [b1, b2, b3, b4, b5, b6, b7, b8]) : DecidesBySplit P.par b8 := by
  unfold blocks at hb
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq,
    List.cons.injEq, and_true] at hb
  obtain ⟨sentU, hU, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hb
  exact fun d rs gs d' h => why_some h

end Desc.K14.Law
