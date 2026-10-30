-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import Johnson.Desc.K12.Law.SwUnfold
/-
Johnson/Desc/K12/Law/SwSendP.lean: THE BARE EQUATION INSIDE THE SWITCH: a yes of switchE (Johnson/Desc/K12/Parts.lean) on a stretch of two rounds HOLDS a yes of the ground's sending sendP at the switch's own notices and these two rounds, AND a yes of the step behind it (Tw.L9.switchBehind) on what the sending left. NO SOUNDNESS IS CLAIMED. NOTHING ON HIDING.
  switchE_sendP   switchE old T gp others true s = .ok ((out, theta), s') · s.rounds = [rS, rC] ⇒ there are the stretch's second entry e₂ and ids sd an took d₂ x o with: sendP Ground.groundG s.p false s.d (Tw.L9.switchNotices T others) rS rC = some (ids, sd, an, took, d₂) · rC draws just the one element x, and theta is x read · switchBehind's yes o on the record made of d₂ (written out) · out = o.out · s'.d is d₂ with o's statement, book and opened columns
NO PREMISE ON THE TARGET's ANSWERS OR KEPT MEMBERS, unlike switchE_ok (Johnson/Desc/K12/Law/SwUnfold.lean), which unfolds both calls; no byte of that file turns. So that a law on sendP reaches every sending «CS» of a proximity test.
No sorry, no axiom of ours; the theorem has its premises; what it rests on is printed at the file's end.
-/
set_option autoImplicit false
namespace H2K.Sw
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.JointK
open H2K.FoldLaw (bind_ok)
open _root_.Desc.Plain (DState GPar sendP)


theorem switchE_sendP (old : SingleRows) (T : SwitchTarget) (gp : Nat)
    (others : Array OracleNotice) (s s' : H2K.PS) (out : Switched) (theta : E) (rS rC : Fmt.RoundView)
    (hrs : s.rounds = [rS, rC])
    (h : H2K.switchE old T gp others true s = .ok ((out, theta), s')) :
    ∃ (e₁ e₂ : Fmt.Entry) (es : List Fmt.Entry) (ids : Array Nat) (sd an : List E) (took : Nat)
      (d₂ : DState Unit) (x : UInt64 × UInt64 × UInt64) (o : Tw.L9.SwOut),
      s.entries = e₁ :: e₂ :: es ∧
      sendP Ground.groundG s.p false s.d (Tw.L9.switchNotices T others) rS rC =
        some (ids, sd, an, took, d₂) ∧
      rC.drawn.elems = [x] ∧ theta = E.ofTriple x ∧
      Tw.L9.switchBehind
        { st := d₂.st, book := d₂.book, firstTree := s.p.firstTree, opened := d₂.opened,
          old := old, T := T, grp := gp, ids := ids,
          entry := { e₂ with name := "LOC", drawE := 0 }, settled := true,
          drawn := { rC.drawn with elems := [] }, itemsLeft := rC.vals.length - took } = .ok o ∧
      out = o.out ∧
      s'.d = { d₂ with st := o.st, book := o.book, opened := o.opened } := by
  unfold H2K.switchE at h
  rw [hrs] at h
  split at h
  · rename_i e₁ e₂ es r₁ r₂ rs he hr
    cases hr
    dsimp only at h
    obtain ⟨_, _, h⟩ := bind_ok h
    obtain ⟨_, _, h⟩ := bind_ok h
    obtain ⟨_, _, h⟩ := bind_ok h
    obtain ⟨_, _, h⟩ := bind_ok h
    obtain ⟨_, _, h⟩ := bind_ok h
    obtain ⟨_, _, h⟩ := bind_ok h
    obtain ⟨_, _, h⟩ := bind_ok h
    obtain ⟨_, _, h⟩ := bind_ok h
    obtain ⟨_, _, h⟩ := bind_ok h
    obtain ⟨⟨ids, sd, an, took, d₂⟩, hsend, h⟩ := bind_ok h
    dsimp only at h
    split at h
    · rename_i x hx
      simp only [pure_bind] at h
      obtain ⟨o, hb, h⟩ := bind_ok h
      cases h
      exact ⟨e₁, e₂, es, ids, sd, an, took, d₂, x, o, he, opt_ok hsend, hx, rfl, mapError_ok hb,
        rfl, rfl⟩
    · cases h
  · cases h

end H2K.Sw

#print axioms H2K.Sw.switchE_sendP
