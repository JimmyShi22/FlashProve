-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Tw/K2C/HeldAtPlace.lean: code switching (the kind K2): THE VERIFIER's STATE BEHIND
A PLACE OF THE KIND HOLDS THE OOD SAMPLE OF EACH TENANT WHOSE PIN IS OPEN THERE, THROUGH THE
PLACE's WAY IN AND WAY OUT. For the second tie's premise on «held». NO BLOCK IMPORTS THIS FILE.
  smpHeld_left     «what an accept of the switch leaves of the state» (Left,
                   Johnson/Top/H0/K2Ties/Left.lean: its fields smp and places) carries «the state
                   holds the sample of tenant t of tree j», where the book behind fits
                   (BookFits, Johnson/Desc/Book/BookFits.lean)
  held_at_place    where B sits over the kind's own sub-protocol behind a door whose way in and
                   way out each give Left, and whose way in leaves the book: at every accept s ↦
                   s' of B: from BookFits in front and behind · SeedReads · the sample of the
                   index masks' tenant held in front · at the state that the way in lets in: the
                   front, the lay of the trees, the field «sent» and «each of the first n notices
                   counts an answer and has a row» ⟹ ∀ q ∈ N.index :: N.sent m 0, smpHeld s'.st
                   s'.book q.1 q.2 = true
BY: K2.held_behind · smpHeld_inv | smpHeld_of · place_of_no · oracleNo_of_fits
(Tw/K2C/HeldAtYes.lean) · K2.k2_step_two (Tw/K2C/HandsLink.lean).
LIMITS. The premises are named, none is shown met. No soundness is claimed.
-/
import Johnson.Top.H0.Tw.K2C.HeldAtYes
import Johnson.Top.H0.Tw.K2C.HandsLink
import Johnson.Top.H0.K2Ties.Left
import Johnson.Desc.K12.Law.Sits

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2
open OnBytes OnBytes.Model
open _root_.Tw.K2 (switchNotices sendByL8)
open VerifiableInference.Desc (Block OpenedColumn smpHeld)
open VerifiableInference.Desc.Book (BookFits)
open VerifiableInference.Desc.First.K2Ties (Left)
open H2K.JointK (Sits)

theorem smpHeld_left {s s' : S} (L : Left s s') (hB : BookFits s'.book) {j t : Nat}
    (h : smpHeld s.st s.book j t = true) : smpHeld s'.st s'.book j t = true := by
  obtain ⟨o, x, r, ho, hx, hm, ha, hz, hr, hs⟩ := smpHeld_inv h
  obtain ⟨x', hx', e1, e2, e3⟩ := L.smp.2 o x hx hm
  refine smpHeld_of (oracleNo_of_fits hB (L.places o (j, t) (place_of_no ho))) hx' e2
    (by rw [e1]; exact ha) (by rw [e1, e3]; exact hz) (by rw [e3]; exact hr) ?_
  rw [L.smp.1, e1]
  exact hs

theorem held_at_place {Cl : Type} {ft : Nat} {B : Block S Cl} {p : P2}
    {enter : S → Except String S} {leave : S → S → Except String S}
    (hS : Sits B (codeSwitchKind p : Block S Unit) enter leave)
    (hin : ∀ s t, enter s = .ok t → Left s t) (hout : ∀ s t s', leave s t = .ok s' → Left t s')
    (hbk : ∀ s t, enter s = .ok t → t.book = s.book)
    {s s' : S} {rs : List Fmt.RoundView} {cols : List Col} {n₁ : Nat}
    (hy : B.step ft s rs cols = .ok (s', n₁)) (hB : BookFits s.book) (hB' : BookFits s'.book)
    (hSR : SeedReads) {N : Numbers} {m : Nat}
    (hnew : ∀ t, enter s = .ok t → ∃ (x : _root_.Tw.K2.Front) (lay : TreeLay) (n : Nat),
      frontAt p t = some x ∧ layTrees x.st.codes (switchNotices x.T x.others) = some lay ∧
      sameMembers ((List.range n).map fun i =>
        (t.book.trees.size + lay.tree.getD i 0, lay.part.getD i 0)) (N.sent m 0) = true ∧
      ∀ i, i < n → ∃ nt, (switchNotices x.T x.others)[i]? = some nt ∧
        nt.shape.answers ≠ 0 ∧ 0 < nt.shape.mainRows + nt.shape.maskRows)
    (hI : smpHeld s.st s.book N.index.1 N.index.2 = true) :
    ∀ q ∈ N.index :: N.sent m 0, smpHeld s'.st s'.book q.1 q.2 = true := by
  obtain ⟨t, t', e1, e2, e3⟩ := hS.step ft s s' rs cols n₁ hy
  obtain ⟨r₁, r₂, gs, _, hd⟩ := k2_step_two e2
  obtain ⟨x, lay, n, hx, hl, hsent, hall⟩ := hnew t e1
  have hBt : BookFits t.book := by
    rw [hbk s t e1]
    exact hB
  intro q hq
  exact smpHeld_left (hout s t' s' e3) hB'
    (held_behind hd hBt hSR hx hl hsent hall (smpHeld_left (hin s t e1) hBt hI) q hq)

end VerifiableInference.Desc.First.K2

#print axioms VerifiableInference.Desc.First.K2.smpHeld_left
#print axioms VerifiableInference.Desc.First.K2.held_at_place
