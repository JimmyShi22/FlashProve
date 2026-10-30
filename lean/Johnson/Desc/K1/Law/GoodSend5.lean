-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/GoodSend5.lean: what a sending leaves of the older messages, so that a promise
on them can be carried past it: a yes of each of the kind's three blocks at the first chain's
carried record leaves the codes and every older message's shape, mark and sample rows; and a message
that is sealed stays sealed along such a step.

Main names: OldMsgs, OldMsgs.trans, old_of_same, old_of_kept; SeedIs.old, Sealed.old; KeepsOld;
keepsOld_sendAtS, keepsOld_commitAtS, keepsOld_firstAtS; keepsOld_andThen.

What is not claimed. The word of an older message is an argument of Sealed: that a reader of the
oracles returns the same word behind the step is not said here. Nothing on soundness of a protocol,
on an honest prover or on hiding.

-/
import Johnson.Desc.K1.Law.GoodSend4

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model Desc.Plain
open OnBytes.Slice Johnson.Pack Cb Cb.Ood
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.First (S)

/-- The codes and every message of A stand in B, each with its shape, mark and sample rows. -/
def OldMsgs (A B : Statement) : Prop :=
  B.codes = A.codes ∧ ∀ j : Nat, j < A.oracles.size →
    (B.oracles[j]?).map (fun x : OnBytes.Oracle => (x.shape, x.sampled, x.sampleRows)) =
      (A.oracles[j]?).map fun x : OnBytes.Oracle => (x.shape, x.sampled, x.sampleRows)

theorem OldMsgs.size {A B : Statement} (h : OldMsgs A B) : A.oracles.size ≤ B.oracles.size := by
  by_contra hn
  have hlt : B.oracles.size < A.oracles.size := Nat.lt_of_not_le hn
  have e := congrArg Option.isSome (h.2 _ hlt)
  simp only [Option.isSome_map] at e
  rw [Array.getElem?_eq_getElem hlt, Array.getElem?_eq_none (Nat.le_refl _)] at e
  cases e

theorem OldMsgs.trans {A B C : Statement} (h1 : OldMsgs A B) (h2 : OldMsgs B C) : OldMsgs A C :=
  ⟨h2.1.trans h1.1, fun j hj =>
    (h2.2 j (Nat.lt_of_lt_of_le hj h1.size)).trans (h1.2 j hj)⟩

theorem old_of_same {A B : Statement} (h : SameMsgs A B) : OldMsgs A B :=
  ⟨h.1, fun j _ => h.2 j⟩

theorem old_of_kept {L : Type} {d d' : DState L} (h : Kept d d') : OldMsgs d.st d'.st :=
  ⟨h.1, fun j hj => by rw [h.2.2 j hj]⟩

/-- The record's sample rows of an older message are as they were. -/
theorem SeedIs.old {cs : Codes} {s : OracleShape} {A B : Statement} {o : Nat}
    {ρ : (Fin (bitsZ cs s) → GE) × GEˣ} {y : GE} (h : SeedIs cs s A o ρ y) (hs : OldMsgs A B) :
    SeedIs cs s B o ρ y := by
  obtain ⟨hc, x, z, β, t, hx, h1, h2, h3, h4, h5⟩ := h
  have ho : o < A.oracles.size := by
    by_contra hn
    rw [Array.getElem?_eq_none (Nat.le_of_not_lt hn)] at hx
    cases hx
  have e := hs.2 o ho
  rw [hx] at e
  obtain ⟨x', hx', e⟩ := Option.map_eq_some_iff.1 e
  obtain ⟨e1, e23⟩ := Prod.mk.inj e
  obtain ⟨e2, e3⟩ := Prod.mk.inj e23
  exact ⟨hs.1.trans hc, x', z, β, t, hx', e1.trans h1, e2.trans h2, e3.trans h3, h4, h5⟩

/-- **A sealed message stays sealed.** -/
theorem Sealed.old {cs : Codes} {s : OracleShape} {e : Nat} {f : (portOmZ cs s e).Str}
    {A B : Statement} {o : Nat} (h : Sealed cs s e f A o) (hs : OldMsgs A B) :
    Sealed cs s e f B o := by
  obtain ⟨ρ, y, h1, h2⟩ := h
  exact ⟨ρ, y, h1.old hs, h2⟩

variable {T Cl : Type}

/-- A block's yes leaves the codes and the older messages. -/
def KeepsOld (stOf : T → Statement) (b : Block T Cl) : Prop :=
  ∀ s s' rs gs, b.decide s rs gs = .ok s' → OldMsgs (stOf s) (stOf s')

theorem keepsOld_of_leaves (stOf : T → Statement) (q : Block T Cl) (h : LeavesMsgs stOf q) :
    KeepsOld stOf q := fun s s' rs gs hy => old_of_same (h s s' rs gs hy)

theorem keepsOld_andThen (stOf : T → Statement) (name : String) (p q : Block T Cl)
    (hp : KeepsOld stOf p) (hq : KeepsOld stOf q) : KeepsOld stOf (p.andThen name q) := by
  intro s s' rs gs h
  have h' : (p.decide s (rs.take p.rounds.length) (gs.take p.openings)).bind (fun s₁ =>
      q.decide s₁ (rs.drop p.rounds.length) (gs.drop p.openings)) = .ok s' := h
  obtain ⟨s₁, h1, h2⟩ := (bind_ok _ _ _).1 h'
  exact (hp _ _ _ _ h1).trans (hq _ _ _ _ h2)

/-- A yes of the kind's decision leaves the older messages, on whatever rounds. -/
theorem decideSend_old {L : Type} (P : Par) (owed : Option Nat) (d d' : DState L)
    (rs : List Fmt.RoundView) (ids : Array Nat) (h : decideSend P owed d rs = .ok (ids, d')) :
    OldMsgs d.st d'.st := by
  match rs, h with
  | [r₁, r₂], h =>
    obtain ⟨_, _, rfl⟩ := (decideSend_iff P owed d d' r₁ r₂ ids).1 h
    exact old_of_kept (kept_behind P d _ _)

theorem keepsOld_sendAtS (P : Par) : KeepsOld (fun s : S => s.st) (sendAtS P : Block S Cl) := by
  intro s s' rs gs h
  obtain ⟨ids, d', h1, e1, _⟩ := sendAtS_ok P s s' _ gs h
  show OldMsgs s.st s'.st
  rw [e1]
  exact decideSend_old P _ (stateOf s (#[] : Array Nat)) d' rs ids h1

theorem keepsOld_commitAtS (P : Par) (link moment : Nat) (arrays : Option (List Nat)) :
    KeepsOld (fun s : S => s.st) (commitAtS P link moment arrays : Block S Cl) := by
  intro s s' rs gs h
  obtain ⟨t, y, e0, h1, e1, _⟩ := commitAtS_ok P link moment arrays s s' _ gs h
  obtain ⟨ids, d₁, f', h2, h3⟩ := commitOwn_ok P link moment arrays t y _ gs h1
  have a := decideSend_old P _ _ d₁ rs ids h2
  rw [e0] at a
  show OldMsgs s.st s'.st
  rw [e1]
  exact OldMsgs.trans a (old_of_same (joinOwnP_msgs _ _ _ _ _ _ _ h3))

theorem keepsOld_firstAtS (q : Params.First) (gp : GPar) :
    KeepsOld (fun s : S => s.st) (firstSegmentOpening q gp : Block S Cl) := by
  intro s s' rs gs h
  obtain ⟨c, d', h1, e1, _⟩ := firstAtS_ok q gp s s' _ gs h
  obtain ⟨g, d₁, ids, d₂, h0, h2, f₁, own, mine, f₂, h3⟩ := firstOwn_ok _ _ _ _ _ _ _ h1
  have a0 : OldMsgs (stateOf s ()).st d₁.st := by
    unfold Ground.newGroupP at h0
    split at h0
    · obtain rfl : _ = d₁ := (Prod.mk.inj (Option.some.inj h0)).2
      exact ⟨rfl, fun _ _ => rfl⟩
    · cases h0
  show OldMsgs s.st s'.st
  rw [e1]
  exact (a0.trans (decideSend_old _ _ d₁ d₂ rs ids h2)).trans
    (old_of_same (joinOwnP_msgs _ _ _ _ _ _ _ h3))

end VerifiableInference.Desc.K1
