-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Tw/K2C/SendsOpen.lean: the kind «the code switch»: A YES OF THE DECISION HOLDS A YES
OF
THE PLAIN GROUND's SENDING sendP, at its flag false (the caller closes the round of answers).
NO BLOCK IMPORTS THIS FILE.
  sendByL8_iff   the sending that the block lays says y  ⇔  the first entry's test on the plan
                 (planOk1), the first round fits its entry (fits), and sendP … false … returns, with
                 y's five fields read off what it returns
  yes_sendP      a yes of the decision, at any of its three sorts of place: there are two rounds
                 r₁, r₂ and a front x with: sendP groundG ⟨p.samples, p.firstTree⟩ false
                 ⟨x.st, s.book, s.roots, [], ()⟩ (switchNotices x.T x.others) r₁ r₂ returns, and the
                 step behind the sending starts from the statement and the book that it returns
WHAT IT DOES NOT SAY. THE ANNOUNCEMENTS ARE THE RECORD's: switchNotices x.T x.others is made of the
carried frame (its shape and its groups' targets), not of the place's numbers p: no test of this
text holds them against a plan. So this is no statement at a fixed list of announcements. Nothing
here on what the step behind the sending does to the older messages.
No Mathlib. No soundness is claimed.
-/
import Johnson.Top.H0.Tw.K2C.AsksWhole

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2
open OnBytes OnBytes.Model
open _root_.Tw.K2 (SwIn SwOut switchBehind switchNotices sendByL8)
open VerifiableInference.Desc.First.Send (sendOpen planOk1)

/-- What the laid sending's yes is. -/
theorem sendByL8_iff (P : _root_.Tw.K2.Par9) (S : Statement) (B : TreeBook) (roots : Nat) (settled :
    Bool)
    (notices : Array OracleNotice) (rS rL : Fmt.RoundView) (y : _root_.Tw.K2.Sent) :
    sendByL8 P S B roots settled notices rS rL = .ok y ↔
      ∃ ids took d, sendOpen (Desc.Plain.groundG : Desc.Plain.Ground Unit) ⟨P.samples, P.firstTree⟩
          (if settled then none else some 1) notices P.eSeed ⟨S, B, roots, [], ()⟩ rS rL = some
              (ids, took, d) ∧
        y = ⟨d.st, d.book, d.roots, ids, took⟩ := by
  unfold sendByL8
  constructor
  · intro h
    split at h
    · rename_i ids took d hs
      cases h
      exact ⟨ids, took, d, hs, rfl⟩
    · cases h
  · rintro ⟨ids, took, d, hs, rfl⟩
    simp only [hs]

/-- The sending inside a code switch, opened: its two tests and sendP at the flag false. -/
theorem sendOpen_iff {L : Type} (G : Desc.Plain.Ground L) (p : Desc.Plain.GPar) (owed : Option Nat)
    (sent : Array OracleNotice) (e₁ : Fmt.Entry) (d : Desc.Plain.DState L) (r₁ r₂ : Fmt.RoundView) (ids :
               Array Nat) (took : Nat)
    (d' : Desc.Plain.DState L) :
    sendOpen G p owed sent e₁ d r₁ r₂ = some (ids, took, d') ↔
      planOk1 owed sent e₁ = true ∧ Desc.Plain.fits e₁ r₁ = true ∧
        ∃ sd an, Desc.Plain.sendP G p false d sent r₁ r₂ = some (ids, sd, an, took, d') := by
  unfold sendOpen
  constructor
  · intro h
    split at h
    · rename_i c
      have c' := Bool.and_eq_true_iff.1 c
      cases hx : Desc.Plain.sendP G p false d sent r₁ r₂ with
      | none => simp [hx] at h
      | some x =>
        obtain ⟨i, sd, an, t, e⟩ := x
        simp [hx] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact ⟨c'.1, c'.2, sd, an, rfl⟩
    · cases h
  · rintro ⟨h1, h2, sd, an, hx⟩
    simp [h1, h2, hx]

/-- **A yes of the decision holds a yes of sendP.** -/
theorem yes_sendP {p : P2} {s : S} {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))} {s' :
           S}
    (h : decideWith sendByL8 p s rs gs = .ok s') :
    ∃ (r₁ r₂ : Fmt.RoundView) (x : _root_.Tw.K2.Front) (w : SwOut), ∃ ids sd an took d', rs = [r₁, r₂] ∧
      Desc.Plain.sendP (Desc.Plain.groundG : Desc.Plain.Ground Unit) ⟨p.samples, p.firstTree⟩ false
        ⟨x.st, s.book, s.roots, [], ()⟩ (switchNotices x.T x.others) r₁ r₂ = some (ids, sd, an,
            took, d') ∧
      switchBehind (behindArgs (par9 p) x ⟨d'.st, d'.book, d'.roots, ids, took⟩ r₂ (flat p gs)) =
          .ok w ∧
      s'.book = w.book := by
  have key : ∀ {f : ReqFrame} {x : _root_.Tw.K2.Front} {r₁ r₂ : Fmt.RoundView} {w : SwOut} {roots : Nat},
      _root_.Tw.K2.switchE switchBehind (par9 p) sendByL8 ⟨s.st, s.book, s.roots, f, [],
          s.noneWaits⟩ x r₁ r₂ (flat p gs) =
        .ok (w, roots) →
      ∃ ids sd an took d', Desc.Plain.sendP (Desc.Plain.groundG : Desc.Plain.Ground Unit)
          ⟨p.samples, p.firstTree⟩ false
        ⟨x.st, s.book, s.roots, [], ()⟩ (switchNotices x.T x.others) r₁ r₂ = some (ids, sd, an,
            took, d') ∧
      switchBehind (behindArgs (par9 p) x ⟨d'.st, d'.book, d'.roots, ids, took⟩ r₂ (flat p gs)) =
          .ok w := by
    intro f x r₁ r₂ w roots hw
    obtain ⟨y, k⟩ := switchE_inv hw
    obtain ⟨ids, took, d', hs, rfl⟩ := (sendByL8_iff _ _ _ _ _ _ _ _ _).1 k.hSend
    obtain ⟨_, _, sd, an, hx⟩ := (sendOpen_iff _ _ _ _ _ _ _ _ _ _ _).1 hs
    exact ⟨ids, sd, an, took, d', hx, k.hBehind⟩
  rcases (stands _ _ _ _ _ _ h) with ⟨hp, _⟩ | ⟨hp, _⟩ | ⟨hp, _⟩
  · obtain ⟨r₁, r₂, x, w, roots, S', f, mine, rfl, k⟩ := link_inv hp h
    obtain ⟨ids, sd, an, took, d', h1, h2⟩ := key k.hSwitch
    exact ⟨r₁, r₂, x, w, ids, sd, an, took, d', rfl, h1, h2, by rw [k.hOut]⟩
  · obtain ⟨r₁, r₂, a, G, w, roots, rfl, k⟩ := head_inv hp h
    obtain ⟨ids, sd, an, took, d', h1, h2⟩ := key k.hSwitch
    exact ⟨r₁, r₂, _, w, ids, sd, an, took, d', rfl, h1, h2, by rw [k.hOut]⟩
  · obtain ⟨r₁, r₂, a, G, w, roots, rfl, k⟩ := finish_inv hp h
    obtain ⟨ids, sd, an, took, d', h1, h2⟩ := key k.hSwitch
    exact ⟨r₁, r₂, _, w, ids, sd, an, took, d', rfl, h1, h2, by rw [k.hOut]⟩

end VerifiableInference.Desc.First.K2

#print axioms VerifiableInference.Desc.First.K2.sendByL8_iff
#print axioms VerifiableInference.Desc.First.K2.sendOpen_iff
#print axioms VerifiableInference.Desc.First.K2.yes_sendP
