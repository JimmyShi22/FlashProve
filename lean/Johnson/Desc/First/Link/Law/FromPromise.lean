-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Link/Law/FromPromise.lean: WHAT THE TABLE's OWN PROMISE AT AN UNMARKED STATE
(`onT`, LinkTiedAt.lean) GIVES TO THE LAW OF A LINK's THREE PIECES: three of the law's premises on
its conditions, paid from the promise's Bools on the verifier's state. Theorems.

Why. With the law's four conditions closed at the table's promise, each premise «the condition gives
…» is a sentence on what that promise holds. Two of its six Bools serve here: the test on where the
chain stands, and the test on where the book stands.

What is said.
  `onT_bools`: the promise at an unmarked state gives its six Bools. `part_of_shape`: **where the
    test on the stand holds at a place of a layers' or an attention segment, from the segment's
    second block on, the batching kind's lens finds its part** (the stand is «in a segment of that
    sort»: there the link's context, the ledger, the smallness test's state and the slots taken are
    all at hand). `msgs_of_book`: where the test on the book holds, the statement has just as many
    oracle messages as the plan counts at the place. `hs_of_onT`, `hN_of_onT`: **the premises hs1,
    hs2 and hN of the law, at `onT`.**

Limits. AT THE HEAD's SEGMENT `part_of_shape` SAYS NOTHING: there the lens asks beside that the
head's slot is laid, which no clause of the promise reads. The place's segment, its sort and its
piece are premises (facts on the written list). Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.LinkTiedAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open VerifiableInference.Desc.K9 (atS)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S ModelPart Meaning Numbers start openSets pubSets shapeAt rowsHeld
  membersHeld pubHeld bookAt standOf standAt onAt)

variable {P W : Type} {F : Frame}

/-- The promise at an unmarked state gives its six Bools. -/
theorem onT_bools (Nm : Numbers) (Mg : Meaning P W) (links : List ModelPart) (pl : List Place) (z : P)
    (k : ℕ) (a : S × F.E.Str) (h : onT Nm Mg links pl (fun s : S => (z, s)) k a) :
    shapeAt links pl[k]? a.1 = true ∧
      rowsHeld Nm ((openSets links pl (start links))[k]?.getD []) a.1 = true ∧
      membersHeld Nm ((openSets links pl (start links))[k]?.getD []) a.1 = true ∧
      Mg.inOrder (z, a.1) = true ∧
      pubHeld Mg ((openSets links pl (start links))[k]?.getD [])
        ((pubSets Mg.more links pl)[k]?.getD []) (z, a.1) = true ∧
      bookAt Nm pl[k]? a.1 = true := by
  obtain ⟨hq, hu⟩ := h
  unfold onQ onAt at hq
  rcases hq.2 with hm | hb
  · exact absurd hm hu
  · have h6 := hb.1
    simp only [Bool.and_eq_true] at h6
    obtain ⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩, a6⟩ := h6
    exact ⟨a1, a2, a3, a4, a5, a6⟩

/-- **Where the chain stands in a layers' or an attention segment, the lens finds its part.** -/
theorem part_of_shape (links : List ModelPart) (p : Place) (s : S) (m : ℕ) (sub : ModelPart)
    (hl : p.link = some m) (hs : links[m]? = some sub) (hsub : sub = .layers ∨ sub = .attention)
    (h2 : 2 ≤ p.piece) (h : shapeAt links (some p) s = true) :
    (atS.get? s).isSome = true := by
  have h' : (standOf s == standAt links p && (s.noneWaits || First.mayWait links p) &&
      s.link?.all fun L => p.link == some L.link) = true := h
  have h1 : standOf s = standAt links p := by
    have := (Bool.and_eq_true_iff.1 (Bool.and_eq_true_iff.1 h').1).1
    simpa using this
  have hat : standAt links p = .link sub := by
    unfold standAt
    rw [hl]
    have e1 : ¬ p.piece ≤ 1 := by omega
    have e2 : (sub == ModelPart.head) = false := by rcases hsub with rfl | rfl <;> rfl
    simp [hs, e1, e2]
  rw [hat] at h1
  obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := s
  cases here with
  | lay x => rfl
  | att x => rfl
  | head x =>
    unfold standOf at h1
    simp only [] at h1
    split at h1
    · rcases hsub with rfl | rfl <;> exact nomatch h1
    · exact nomatch h1
  | _ => exact nomatch h1

/-- Where the test on the book holds, the statement has as many oracle messages as the plan
counts. -/
theorem msgs_of_book (Nm : Numbers) (p : Option Place) (s : S) (h : bookAt Nm p s = true) :
    s.st.oracles.size = Nm.msgsAt p := by
  unfold bookAt at h
  have := (Bool.and_eq_true_iff.1 h).2
  simpa using this

/-- **hs1 | hs2 AT onT.** -/
theorem hs_of_onT (Nm : Numbers) (Mg : Meaning P W) (links : List ModelPart) (pl : List Place) (z : P)
    (k : ℕ) (p : Place) (m : ℕ) (sub : ModelPart) (hp : pl[k]? = some p) (hl : p.link = some m)
    (hs : links[m]? = some sub) (hsub : sub = .layers ∨ sub = .attention) (h2 : 2 ≤ p.piece) :
    ∀ b : S × F.E.Str, onT Nm Mg links pl (fun s : S => (z, s)) k b →
      (atS.get? b.1).isSome = true := by
  intro b hb
  have h := (onT_bools Nm Mg links pl z k b hb).1
  rw [hp] at h
  exact part_of_shape links p b.1 m sub hl hs hsub h2 h

/-- **hN AT onT**, at the plan's own count. -/
theorem hN_of_onT (Nm : Numbers) (Mg : Meaning P W) (links : List ModelPart) (pl : List Place) (z : P)
    (k : ℕ) : ∀ s : S × F.E.Str, onT Nm Mg links pl (fun s : S => (z, s)) k s →
      ∀ a, atS.get? s.1 = some a → a.d.st.oracles.size ≤ Nm.msgsAt pl[k]? := by
  intro s hs a ha
  have h := (onT_bools Nm Mg links pl z k s hs).2.2.2.2.2
  have e : a.d.st = s.1.st := by
    unfold atS at ha
    simp only [Option.bind_eq_bind, Option.pure_def] at ha
    obtain ⟨_, _, ha⟩ := Option.bind_eq_some_iff.1 ha
    obtain ⟨_, _, ha⟩ := Option.bind_eq_some_iff.1 ha
    obtain ⟨_, _, ha⟩ := Option.bind_eq_some_iff.1 ha
    obtain ⟨_, _, ha⟩ := Option.bind_eq_some_iff.1 ha
    rw [← Option.some.inj ha]
  rw [e, msgs_of_book Nm _ _ h]

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.onT_bools
#print axioms VerifiableInference.Desc.LinkJoin.part_of_shape
#print axioms VerifiableInference.Desc.LinkJoin.hs_of_onT
#print axioms VerifiableInference.Desc.LinkJoin.hN_of_onT
