-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/SentFits.lean: WHERE THE OUTPUT HEAD's BLOCK's DECISION GOES ON, EACH ROUND SHOWN SENDS JUST AS MANY ITEMS AS THE KIND's TABLE OF
ROUNDS SAYS AT ITS NUMBER: STATED AND PROVED: off the decision's own test "the rounds' shape" (the strict reading tapeT,
Johnson/Desc/First/Tape/Tape.lean: an entry's bytes are 24 times the message's elements).
WHAT IT DOES NOT SAY. Nothing on what is drawn, on names or on work. No chance in it.
  elemsOf_length · roundT_msg · tapeT_msg   the strict reading's clause on a message's length, at each round of a stretch.
  decide_tape    where decideBy goes on: given returns and the strict reading returns.
  sentAt p j     the number of scalars that round number j of Head.lean's rounds sends, at the plan's sizes; 0 behind the last.
  decide_shape   the law.

-/
import Mathlib
import Johnson.Desc.Kinds.Law.FromGiven
import Johnson.Desc.Kinds.HeadKind

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E)
open VerifiableInference.Desc.First.Tape (TapeRule elemsOf roundT tapeT)

/-- The number of scalars that round number j of the kind's table of rounds sends. -/
def sentAt (p : Par) (j : Nat) : Nat :=
  let _ := p.sizes
  ((rounds[j]?).map (·.sent)).getD 0

namespace Came

theorem elemsOf_length : ∀ (l : List Fmt.ItemValue) (s : List E), elemsOf l = some s → s.length = l.length
  | [], s, h => by
    simp only [elemsOf, Option.some.injEq] at h
    subst h; rfl
  | .e x :: l, s, h => by
    simp only [elemsOf] at h
    cases hl : elemsOf l with
    | none => rw [hl] at h; simp at h
    | some s' =>
      rw [hl] at h
      simp only [Option.map_some, Option.some.injEq] at h
      subst h
      simp [elemsOf_length l s' hl]
  | .f _ :: _, _, h => by simp [elemsOf] at h
  | .word _ :: _, _, h => by simp [elemsOf] at h
  | .root _ :: _, _, h => by simp [elemsOf] at h
  | .answer _ :: _, _, h => by simp [elemsOf] at h

theorem roundT_msg {rule : TapeRule} {r : Fmt.RoundView} {e : Fmt.Entry} {x : OnBytes.K.Kc.FlatRound}
    (h : roundT rule r e = some x) : e.msg = 24 * r.vals.length := by
  unfold roundT at h
  cases hs : elemsOf r.vals with
  | none => rw [hs] at h; simp at h
  | some sent =>
    rw [hs] at h
    dsimp only at h
    split at h
    · rename_i hc
      rw [← elemsOf_length _ _ hs]
      by_contra hne
      have hb : (e.msg == 24 * sent.length) = false := by simpa using hne
      rw [hb] at hc
      simp at hc
    · simp at h

theorem tapeT_msg (rule : TapeRule) : ∀ (rs : List Fmt.RoundView) (es : List Fmt.Entry)
    (t : OnBytes.K.Kc.Tape), tapeT rule rs es = some t → ∀ (i : Nat) (r : Fmt.RoundView), rs[i]? = some r →
    ∃ e : Fmt.Entry, es[i]? = some e ∧ e.msg = 24 * r.vals.length
  | [], _, _, _, i, r, hi => by simp at hi
  | _ :: _, [], t, h, _, _, _ => by simp [tapeT] at h
  | r0 :: rs, e0 :: es, t, h, i, r, hi => by
    unfold tapeT at h
    cases h1 : roundT rule r0 e0 with
    | none => rw [h1] at h; simp at h
    | some x =>
      cases h2 : tapeT rule rs es with
      | none => rw [h1, h2] at h; simp at h
      | some t' =>
        cases i with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
          subst hi
          exact ⟨e0, by simp, roundT_msg h1⟩
        | succ i =>
          obtain ⟨e, he, hm⟩ := tapeT_msg rule rs es t' h2 i r (by simpa using hi)
          exact ⟨e, by simpa using he, hm⟩

variable {S : Type}

/-- Where the block's decision goes on, the strict reading of its rounds returned. -/
theorem decide_tape {rounds : Given → List Round} {hear : Given → Hear HeardAll}
    {weights : Given → Behind → SumOnMatrix} {p : Par} {L : Seat S} {s s' : S}
    {rs : List Fmt.RoundView} (h : decideBy rounds hear weights p L s rs = .ok s') :
    ∃ (g : Given) (t : OnBytes.K.Kc.Tape), given p L s = .ok g ∧
      tapeT { rows := fun e => e.name == "BAT-sigma" } rs
        ((p.declare (rounds g)).map (·.entry)) = some t := by
  unfold decideBy at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · simp at h
  · rename_i g hg
    split at h
    · simp at h
    · rename_i t ht
      refine ⟨g, t, hg, ?_⟩
      unfold named at ht
      split at ht
      · rename_i y hy
        simp only [Except.ok.injEq] at ht
        rw [← ht]; exact hy
      · simp at ht

/-- **Each round shown sends as many items as the table of rounds says at its number.** -/
theorem decide_shape {Cl : Type} (cl : Form → Cl) (L : Seat S) (link piece : Nat) (p : Par)
    {s s' : S} {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (hd : (kind cl L link piece p).decide s rs gs = .ok s') :
    ∀ i r, rs[i]? = some r → r.vals.length = sentAt p i := by
  intro i r hi
  have hd' : decideBy (fun _ => rounds) (fun _ => hear) (fun _ _ => forTheMerge) p L s rs
      = .ok s' := hd
  obtain ⟨g, t, hg, ht⟩ := decide_tape hd'
  obtain ⟨z, y, _, _, _, rfl⟩ := given_ok p L s g hg
  obtain ⟨e, he, hm⟩ := tapeT_msg _ _ _ _ ht i r hi
  have he' : (((@rounds p.sizes).map fun r => ({ entry := r.entry p.work } : Fmt.DeclaredRound)).map
      (·.entry))[i]? = some e := he
  rw [List.map_map, List.getElem?_map] at he'
  show r.vals.length = (((@rounds p.sizes)[i]?).map (·.sent)).getD 0
  cases hR : (@rounds p.sizes)[i]? with
  | none => rw [hR] at he'; simp at he'
  | some R =>
    rw [hR] at he'
    simp only [Option.map_some, Option.some.injEq, Function.comp] at he'
    subst he'
    have hm' : 24 * R.sent = 24 * r.vals.length := hm
    simp only [Option.map_some, Option.getD_some]
    omega

end Came

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.decide_shape
