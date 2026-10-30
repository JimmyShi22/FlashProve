-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Key/Laid/Laid2.lean: A YES OF THE SHARED CHAIN's TWO SENDINGS GIVES
Laid22 | Laid25 (Johnson/Desc/Key/Laid/Laid2Def.lean). Statements and proofs.
Built over
Johnson/Desc/Key/Laid/SendLaid.lean.
OBJECT. The block Desc.K14.sendAt P n Q inFront groups (behindU P.par | behindOmega P.par) of
Johnson/Desc/K14/Blocks.lean, its field decide, at free n, Q, inFront, groups.
  sendAt_yes      a yes of sendAt is a yes of K1's decision at inFrontOf d, and "behind" says yes.
  sentAt_of_yes   SentAt from the two yeses, where "behind" turns the small part alone.
  laid22_of_yes | laid25_of_yes.
Nothing on soundness.
-/
import Johnson.Desc.K14.Blocks
import Johnson.Desc.Key.Laid.SendMore
import Johnson.Desc.Key.Laid.Laid2Def

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Key.LaidW
open OnBytes OnBytes.Params
open Desc.Plain (DState)
open VerifiableInference.Desc (Block roundsFit named)
open _root_.Desc.K14 (St P14 sendAt behindU behindOmega)

theorem bind_ok' {ε α β : Type} (x : Except ε α) (f : α → Except ε β) (b : β) :
    x.bind f = .ok b ↔ ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => simp [Except.bind]
  | ok a => simp [Except.bind]

theorem map_ok' {ε α β : Type} (x : Except ε α) (f : α → β) (b : β) :
    x.map f = .ok b ↔ ∃ a, x = .ok a ∧ f a = b := by
  cases x with
  | error e => simp [Except.map]
  | ok a => simp [Except.map]

/-- **A yes of sendAt.** -/
theorem sendAt_yes (P : P14) (n : String) (Q : K1.Par) (inFront : Option Fmt.Entry)
    (groups : List (List Nat)) (behind : St → Array Nat → Option St) (d d' : St)
    (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h : (sendAt P n Q inFront groups behind).decide d rs gs = .ok d') :
    ∃ (ids : Array Nat) (x : DState (Array Nat)),
      K1.decideSend Q none (inFrontOf d) rs = .ok (ids, x) ∧
      behind { d with st := x.st, book := x.book, roots := x.roots, opened := x.opened } ids =
        some d' := by
  obtain ⟨t, ht, h1⟩ := (bind_ok' _ _ _).1 h
  obtain ⟨y, hy, rfl⟩ := (map_ok' _ _ _).1 ht
  exact ⟨y.1, y.2, hy, (K1.named_ok _ _ _).1 h1⟩

/-- SentAt, from the two yeses, where "behind" turns the small part alone. -/
theorem sentAt_of_yes (Q : K1.Par) (d d' : St) (r₁ r₂ : Fmt.RoundView) (ids : Array Nat)
    (x : DState (Array Nat)) (hB : K1.planOkOwn Q = true)
    (hfit : roundsFit (K1.rounds Q) [r₁, r₂] = true)
    (hx : K1.decideSend Q none (inFrontOf d) [r₁, r₂] = .ok (ids, x))
    (e1 : d'.st = x.st) (e2 : d'.book = x.book) (e3 : d'.roots = x.roots)
    (e4 : d'.opened = x.opened) : SentAt Q d d' ids := by
  have S := send_laid _ _ _ _ _ _ _ hx
  have ex : inFrontOf d' = x := by
    have el : x.loc = #[] := S.loc
    cases x
    simp only at e1 e2 e3 e4 el
    simp [inFrontOf, e1, e2, e3, e4, el]
  refine ⟨by rw [ex]; exact S, fun i n hn h0 => ?_, fun hI => ?_⟩
  · rw [e1]
    exact (send_more _ _ _ _ _ _ _ hx).ledger i n hn h0
  · rw [e1]
    exact send_order Q none (inFrontOf d) x r₁ r₂ ids hB hfit hx hI

/-- **The yes of "send o_u" gives Laid22.** -/
theorem laid22_of_yes (P : P14) (n : String) (Q : K1.Par) (inFront : Option Fmt.Entry)
    (groups : List (List Nat)) (d d' : St) (r₁ r₂ : Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) (hB : K1.planOkOwn Q = true)
    (hfit : roundsFit (K1.rounds Q) [r₁, r₂] = true) (hM : P.par.S.masksAhead = true)
    (h : (sendAt P n Q inFront groups (behindU P.par)).decide d [r₁, r₂] gs = .ok d') :
    Laid22 P.par.S Q d d' := by
  obtain ⟨ids, x, hx, hb⟩ := sendAt_yes _ _ _ _ _ _ _ _ _ _ h
  unfold behindU at hb
  rw [if_pos hM] at hb
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.map_eq_some_iff,
    Option.some.injEq] at hb
  obtain ⟨m, ⟨i1, h1, rfl⟩, i0, h0, rfl⟩ := hb
  exact ⟨ids, i0, i1, sentAt_of_yes Q d _ r₁ r₂ ids x hB hfit hx rfl rfl rfl rfl, h0, h1, rfl⟩

/-- **The yes of "send o_omega" gives Laid25.** -/
theorem laid25_of_yes (P : P14) (n : String) (Q : K1.Par) (inFront : Option Fmt.Entry)
    (groups : List (List Nat)) (d d' : St) (r₁ r₂ : Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) (hB : K1.planOkOwn Q = true)
    (hfit : roundsFit (K1.rounds Q) [r₁, r₂] = true) (hS : P.par.S.sharedSplitNeeded = true)
    (h : (sendAt P n Q inFront groups (behindOmega P.par)).decide d [r₁, r₂] gs = .ok d') :
    Laid25 Q d d' := by
  obtain ⟨ids, x, hx, hb⟩ := sendAt_yes _ _ _ _ _ _ _ _ _ _ h
  unfold behindOmega at hb
  rw [if_pos hS] at hb
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hb
  obtain ⟨i1, h1, i0, h0, rfl⟩ := hb
  exact ⟨ids, i0, i1, sentAt_of_yes Q d _ r₁ r₂ ids x hB hfit hx rfl rfl rfl rfl, h0, h1, rfl⟩

end VerifiableInference.Desc.Key.LaidW
