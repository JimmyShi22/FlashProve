-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Tw/K2C/HeadTl.lean: the kind «the code switch»: THE HEAD's LINK AND THE RECORD OF THE
SMALLNESS TEST (HeadOwn.tl; the reading S.tl?, which answers nothing until the head's link is
opened). NO BLOCK IMPORTS THIS FILE.
  headFrontQ_tl   a yes of "H.0.front": the record stands in the head's link, not opened, and its tl
                  is the letter that the step was handed
  headSwitch_tl   a yes of the switch at the head's link: tl and «opened» are as they were
  headOpenQ_tl    a yes of "H.1.quiet", THE OPENER: in front the link was not opened; behind S.tl?
                  answers, and its answer is the tl that lay in the record in front
  placeH2_tl      the whole place «H:2» (the switch, then "H.1.quiet"): the same, of the record in
                  front of the place
These are frame facts: they say what the texts leave and lay, not that a yes means a test.
No Mathlib. No soundness is claimed.
-/
import Johnson.Top.H0.Tw.K2C.AsksWhole

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block)

theorem headFrontQ_tl {tl : HTailF2} {s s' : S} (h : headFrontQ tl s = .ok s') :
    ∃ a, s'.here = .head a ∧ a.opened = false ∧ a.tl = tl := by
  obtain ⟨x, s₁, a, k⟩ := (headFrontQ_iff tl s s').1 h
  have h0 : (s.enterHead tl).unmarked = .ok s₁ := k.enters
  have h1 := ((S.unmarked_ok _ _).1 h0).1
  have ha := k.entered
  rw [← h1] at ha
  simp [S.enterHead, k.between] at ha
  refine ⟨{ a with fr := x.f }, by rw [k.out], ?_, ?_⟩
  · rw [← ha]
  · rw [← ha]

theorem headSwitch_tl {snd : _root_.Tw.K2.SendFn} {p : P2} {s : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} {s' : S} (hp : p.stands = .head)
    (h : decideWith snd p s rs gs = .ok s') :
    ∃ a b, s.here = .head a ∧ s'.here = .head b ∧ b.tl = a.tl ∧ b.opened = a.opened := by
  obtain ⟨r₁, r₂, a, G, w, roots, _, k⟩ := head_inv hp h
  exact ⟨a, { a with kept := w.out.kept, ids := w.out.others }, k.hHere, by rw [k.hOut], rfl, rfl⟩

theorem headOpenQ_tl {P : HeadPar} {s s' : S} (h : headOpenQ P s = .ok s') :
    ∃ a, s.here = .head a ∧ a.opened = false ∧ s'.tl? = some a.tl := by
  obtain ⟨a, st, f, mine, L, out, y, cov, s₁, b, k⟩ := (headOpenQ_iff P s s').1 h
  have h0 : s.openHead.unmarked = .ok s₁ := k.opens
  have h1 := ((S.unmarked_ok _ _).1 h0).1
  have hb := k.opened
  rw [← h1] at hb
  simp [S.openHead, k.here, k.fresh] at hb
  refine ⟨a, k.here, k.fresh, ?_⟩
  rw [k.out', ← hb]
  simp [S.tl?]

theorem placeH2_tl {p : P2} {n : String} {P : HeadPar} {s : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} {s' : S} (hp : p.stands = .head)
    (h : ((codeSwitchKind p : Block S Unit).andThen n (headOpened n p.place P)).decide s rs gs = .ok s') :
    ∃ a, s.here = .head a ∧ a.opened = false ∧ s'.tl? = some a.tl := by
  obtain ⟨t, ht, h⟩ :=
    bindOk (x := (codeSwitchKind p : Block S Unit).decide s (rs.take (codeSwitchKind p : Block S Unit).rounds.length)
      (gs.take (codeSwitchKind p : Block S Unit).openings)) h
  have ht : decideWith _root_.Tw.K2.sendByL8 p s _ _ = .ok t := ht
  have h : headOpenQ P t = .ok s' := h
  obtain ⟨a, b, ha, hb, e1, e2⟩ := headSwitch_tl hp ht
  obtain ⟨c, hc, ho, hl⟩ := headOpenQ_tl h
  rw [hb] at hc
  cases hc
  exact ⟨a, ha, by rw [← e2]; exact ho, by rw [hl, e1]⟩

end VerifiableInference.Desc.First.K2

#print axioms VerifiableInference.Desc.First.K2.headFrontQ_tl
#print axioms VerifiableInference.Desc.First.K2.headSwitch_tl
#print axioms VerifiableInference.Desc.First.K2.headOpenQ_tl
#print axioms VerifiableInference.Desc.First.K2.placeH2_tl
