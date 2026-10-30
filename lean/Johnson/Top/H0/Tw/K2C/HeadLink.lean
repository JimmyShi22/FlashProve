-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Tw/K2C/HeadLink.lean: the kind «the code switch»: THE OPEN LINK's RECORD BEHIND THE
WHOLE PLACE «H:2»: five small facts more, beside K2C/HeadNumbers.lean's: of the same L (s'.link? =
some L: there is but one). NO BLOCK IMPORTS THIS FILE.
  placeH2_link     a yes of the whole place: s.here = .head a; s'.link? = some L; and the frame's
                   own list has as many members more than a.fr.own as the frame in the state of
                   the calls has messages of moment 0 L.check.frame.shape = a.fr.shape ·
                   L.check.frame.link = a.fr.link · L.check.frame.groups = a.fr.groups L.link =
                   L.check.frame.link · L.moments = 1
  headFrontQ_fr    behind "H.0.front": the head's part's frame has the shape, the link and the
                   groups of the frame in the state of the calls, which that step leaves; moment
                   1; no own message
WHY a.fr AND NOT s.check.frame: "H.1.quiet" makes the open link's frame of the frame that
"H.0.front" laid into the head's own part (HeadOwn.fr), not of the one in the state of the calls.
The two have one shape and one link behind "H.0.front" (headFrontQ_fr); that the block which
stands between «H:1»'s front and «H:2» leaves both is its own kind's files' to show. A frame fact.
No soundness is claimed.
-/
import Johnson.Top.H0.Tw.K2C.HeadNumbers
import Johnson.Top.H0.Tw.K2C.FrontGroup

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block)
open _root_.Tw.K2 (SwIn SwOut switchBehind switchNotices sendByL8 firstFront firstBehind)
open Johnson.Desc.First.Walk (firstKept)

theorem placeH2_link {p : P2} {n : String} {P : HeadPar} {s s' : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))}
    (h : ((codeSwitchKind p : Block S Unit).andThen n (headOpened n p.place P)).decide s rs gs = .ok s') :
    ∃ (a : HeadOwn) (L : LinkCtx), s.here = .head a ∧ s'.link? = some L ∧
      L.check.frame.own.size = a.fr.own.size + (s.check.frame.atMoment 0).length ∧
      L.check.frame.shape = a.fr.shape ∧ L.check.frame.link = a.fr.link ∧
      L.check.frame.groups = a.fr.groups ∧ L.link = L.check.frame.link ∧ L.moments = 1 := by
  have hp := placeH2_stands h
  obtain ⟨a₀, _, _, L₀, ha₀, hL₀, _⟩ := placeH2_frame h
  simp only [Block.andThen] at h
  obtain ⟨m, h₁, h₂⟩ := bindOk h
  have h₁' : decideWith sendByL8 p s _ _ = .ok m := h₁
  obtain ⟨r₁, r₂, a, G, w, roots, _, k⟩ := head_inv hp h₁'
  obtain ⟨a2, st, f, mine, L, out, y, cov, s₁, b, q⟩ := (headOpenQ_iff P m s').1 h₂
  obtain ⟨_, ⟨b', hb', ho⟩, _⟩ := headOpenOpens P m s' h₂
  have ha2 : a2 = { a with kept := w.out.kept, ids := w.out.others } := by
    have e := q.here
    rw [k.hOut] at e
    injection e with e
    exact e.symm
  have hmc : m.check = s.check := by rw [k.hOut]
  obtain ⟨mask, bA⟩ := (_root_.Tw.K2.firstBehind_iff _ _ _ _ _ _ _).1 q.behind
  obtain ⟨_, hl, hL, _⟩ := Johnson.Desc.First.Walk.Law.front_ok q.front
  have hb2 : b' = { b with
      L := L
      F := Johnson.Desc.First.Walk.emptySlots
        (Johnson.Desc.First.Walk.weightsAtZero { trees := P.X.Fp.trees }) P.hp.ns } := by
    have e := hb'
    rw [q.out'] at e
    injection e with e
    exact e.symm
  have hlink : s'.link? = some L := by
    unfold S.link?
    rw [hb']
    simp only [ho, if_true]
    rw [hb2]
  have hfr : a2.fr = a.fr := by rw [ha2]
  refine ⟨a, L, k.hHere, hlink, ?_, ?_, ?_, ?_, ?_, by rw [hL]⟩
  · rw [hL]
    show f.own.size = _
    rw [bA.frame]
    show (a2.fr.own ++ mine).size = _
    rw [Array.size_append, hfr, ← bA.own]
    show _ + (m.check.frame.atMoment 0).length = _
    rw [hmc]
  · rw [hL]
    show f.shape = _
    rw [bA.frame]
    show a2.fr.shape = _
    rw [hfr]
  · rw [hL]
    show f.link = _
    rw [bA.frame]
    show a2.fr.link = _
    rw [hfr]
  · rw [hL]
    show f.groups = _
    rw [bA.frame]
    show a2.fr.groups = _
    rw [hfr]
  · rw [hL]
    exact hl.symm

theorem headFrontQ_fr {tl : HTailF2} {s s' : S} (h : headFrontQ tl s = .ok s') :
    ∃ a, s'.here = .head a ∧ a.fr.shape = s'.check.frame.shape ∧
      a.fr.link = s'.check.frame.link ∧ a.fr.groups = s'.check.frame.groups ∧ a.fr.moment = 1 ∧
      a.fr.own = #[] ∧ s'.check = s.check := by
  have hc := (headFrontQ_rest h).2.2.2.2.1
  obtain ⟨x, s₁, a, k⟩ := (headFrontQ_iff tl s s').1 h
  obtain ⟨L, G, S0, g, fa⟩ := (_root_.Tw.K2.firstFront_iff _ _ _).1 k.front
  refine ⟨{ a with fr := x.f }, by rw [k.out], ?_, ?_, ?_, ?_, ?_, hc⟩
  · rw [hc, fa.out]
  · rw [hc, fa.out]
  · rw [hc, fa.out]
  · rw [fa.out]
  · rw [fa.out]

end VerifiableInference.Desc.First.K2

#print axioms VerifiableInference.Desc.First.K2.placeH2_link
#print axioms VerifiableInference.Desc.First.K2.headFrontQ_fr
