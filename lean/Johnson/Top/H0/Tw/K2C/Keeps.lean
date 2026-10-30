-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Tw/K2C/Keeps.lean: the kind «the code switch»: WHATEVER RELATION ON STATEMENTS THE
PLAIN
GROUND's FUNCTIONS KEEP (GroundKeeps R, Johnson/Desc/GroundKeeps.lean), THE SWITCH's OWN STEPS
AROUND
THE SENDING KEEP: for they write the statement by these functions alone. NO BLOCK IMPORTS THIS FILE.
  closeLedgerG_keeps · joinG_keeps · addRowsG_keeps · newGroupG_keeps    the four adapters
  joins_keep            a fold of joinG over a list
  switchBehind_keeps    the step behind the sending: R i.st o.st
  firstFront_keeps · finishFront_keeps      the new group in front: R S x.st
  firstBehind_keeps     the own messages' joins: R S S'
  yes_keeps             a yes of the decision, at any of its three sorts of place: with the front x
  and
                        the state d' that sendP returns (yes_sendP): R s.st x.st and R d'.st s'.st
General in R: «a statement only grows», «a sampled message's sample rows stay», and the like.
WHAT IT DOES NOT SAY: nothing on the sending itself (from x.st to d'.st): that is the plain
ground's.
(Johnson/Desc/GroundKeeps.lean stands on Mathlib; the code switch's other law files do not.) No
soundness is claimed.
-/
import Johnson.Top.H0.Tw.K2C.SendsOpen
import Johnson.Desc.GroundKeeps

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2
open OnBytes OnBytes.Model
open _root_.Tw.K2 (SwIn SwOut switchBehind switchNotices sendByL8 closeLedgerG joinG addRowsG
    newGroupG dOf firstFront
  finishFront firstBehind)
open VerifiableInference.Desc.Ground (GroundKeeps)

variable {R : Statement → Statement → Prop}

theorem closeLedgerG_keeps (H : GroundKeeps R) {S S' : Statement} {o : Nat} (h : closeLedgerG S o =
    .ok S') : R S S' := by
  unfold closeLedgerG at h
  split at h
  · rename_i d hd
    cases h
    exact H.closeLedger (dOf S) d o hd
  · cases h

theorem joinG_keeps (H : GroundKeeps R) {S S' : Statement} {g o : Nat} {kept : Bool} (h : joinG S g
    o kept = .ok S') :
    R S S' := by
  unfold joinG at h
  split at h
  · rename_i d hd
    cases h
    exact H.join (dOf S) d g o kept hd
  · cases h

theorem addRowsG_keeps (H : GroundKeeps R) {S S' : Statement} {g : Nat} {rows : List OnBytes.Row}
    (h : addRowsG S g rows = .ok S') : R S S' := by
  unfold addRowsG at h
  split at h
  · rename_i d hd
    cases h
    exact H.addRows (dOf S) d g rows hd
  · cases h

theorem newGroupG_keeps (H : GroundKeeps R) {S S' : Statement} {c m g : Nat} (h : newGroupG S c m =
    .ok (S', g)) :
    R S S' := by
  unfold newGroupG at h
  split at h
  · rename_i g' d hd
    cases h
    exact H.newGroup (dOf S) d c m _ hd
  · cases h

/-- A fold of joins. -/
theorem joins_keep (H : GroundKeeps R) {α : Type} (f : Statement → α → Except String Statement)
    (hf : ∀ S a S', f S a = .ok S' → R S S') : ∀ (l : List α) (S S' : Statement),
        l.foldlM f S = .ok S' → R S S'
  | [], S, S', h => by
    cases h
    exact H.refl _
  | a :: l, S, S', h => by
    rw [List.foldlM_cons] at h
    obtain ⟨T, h1, h2⟩ := bindOk h
    exact H.trans (hf _ _ _ h1) (joins_keep H f hf l T S' h2)

theorem switchBehind_keeps (H : GroundKeeps R) {i : SwIn} {o : SwOut} (h : switchBehind i = .ok o) :
    R i.st o.st := by
  obtain ⟨c, y, S1, S2, S3, rows, b⟩ := switchBehind_inv h
  have h1 : R i.st S1 := by
    have hl := b.hLedger
    split at hl
    · exact closeLedgerG_keeps H hl
    · cases hl
      exact H.refl _
  have h2 : R S1 S2 := joinG_keeps H b.hJoinG
  have h3 : R S2 S3 := by
    have hk := b.hJoinKept
    rw [← Array.foldlM_toList] at hk
    exact joins_keep H _ (fun _ _ _ e => joinG_keeps H e) _ _ _ hk
  have h4 : R S3 o.st := addRowsG_keeps H b.hAdded
  exact H.trans h1 (H.trans h2 (H.trans h3 h4))

theorem firstFront_keeps (H : GroundKeeps R) {S : Statement} {f : ReqFrame} {x : _root_.Tw.K2.Front}
    (h : firstFront S f = .ok x) : R S x.st := by
  obtain ⟨L, G, S', g, a⟩ := (_root_.Tw.K2.firstFront_iff S f x).1 h
  rw [a.out]
  exact newGroupG_keeps H a.opened

theorem finishFront_keeps (H : GroundKeeps R) {S : Statement} {f : ReqFrame} {x :
    _root_.Tw.K2.Front}
    (h : finishFront S f = .ok x) : R S x.st := by
  obtain ⟨G, S', g, a⟩ := (_root_.Tw.K2.finishFront_iff S f x).1 h
  rw [a.out]
  exact newGroupG_keeps H a.opened

theorem firstBehind_keeps (H : GroundKeeps R) {S : Statement} {x : _root_.Tw.K2.Front} {s :
    Switched} {plain : List E}
    {S' : Statement} {f : ReqFrame} {mine : Array Nat} (h : firstBehind S x s plain = .ok (S', f,
        mine)) : R S S' := by
  obtain ⟨mask, a⟩ := (_root_.Tw.K2.firstBehind_iff S x s plain S' f mine).1 h
  exact joins_keep H _ (fun _ _ _ e => joinG_keeps H e) _ _ _ a.joins

/-- **A yes of the decision: the sending in the midst, and R on both sides of it.** -/
theorem yes_keeps (H : GroundKeeps R) {p : P2} {s : S} {rs : List Fmt.RoundView} {gs : List (List (Nat ×
           List UInt64))} {s' : S}
    (h : decideWith sendByL8 p s rs gs = .ok s') :
    ∃ (r₁ r₂ : Fmt.RoundView) (x : _root_.Tw.K2.Front), ∃ ids sd an took d', rs = [r₁, r₂] ∧
      Desc.Plain.sendP (Desc.Plain.groundG : Desc.Plain.Ground Unit) ⟨p.samples, p.firstTree⟩ false
        ⟨x.st, s.book, s.roots, [], ()⟩ (switchNotices x.T x.others) r₁ r₂ = some (ids, sd, an,
            took, d') ∧
      R s.st x.st ∧ R d'.st s'.st := by
  have key : ∀ {f : ReqFrame} {x : _root_.Tw.K2.Front} {r₁ r₂ : Fmt.RoundView} {w : SwOut} {roots : Nat},
      _root_.Tw.K2.switchE switchBehind (par9 p) sendByL8 ⟨s.st, s.book, s.roots, f, [],
          s.noneWaits⟩ x r₁ r₂ (flat p gs) =
        .ok (w, roots) →
      ∃ ids sd an took d',
          Desc.Plain.sendP (Desc.Plain.groundG : Desc.Plain.Ground Unit) ⟨p.samples,
              p.firstTree⟩ false
        ⟨x.st, s.book, s.roots, [], ()⟩ (switchNotices x.T x.others) r₁ r₂ = some (ids, sd, an,
            took, d') ∧
      R d'.st w.st := by
    intro f x r₁ r₂ w roots hw
    obtain ⟨y, k⟩ := switchE_inv hw
    obtain ⟨ids, took, d', hs, rfl⟩ := (sendByL8_iff _ _ _ _ _ _ _ _ _).1 k.hSend
    obtain ⟨_, _, sd, an, hx⟩ := (sendOpen_iff _ _ _ _ _ _ _ _ _ _ _).1 hs
    exact ⟨ids, sd, an, took, d', hx, switchBehind_keeps H k.hBehind⟩
  rcases (stands _ _ _ _ _ _ h) with ⟨hp, _⟩ | ⟨hp, _⟩ | ⟨hp, _⟩
  · obtain ⟨r₁, r₂, x, w, roots, S', f, mine, rfl, k⟩ := link_inv hp h
    obtain ⟨ids, sd, an, took, d', h1, h2⟩ := key k.hSwitch
    refine ⟨r₁, r₂, x, ids, sd, an, took, d', rfl, h1, firstFront_keeps H k.hFront, ?_⟩
    rw [k.hOut]
    exact H.trans h2 (firstBehind_keeps H k.hBehind)
  · obtain ⟨r₁, r₂, a, G, w, roots, rfl, k⟩ := head_inv hp h
    obtain ⟨ids, sd, an, took, d', h1, h2⟩ := key k.hSwitch
    refine ⟨r₁, r₂, _, ids, sd, an, took, d', rfl, h1, H.refl _, ?_⟩
    rw [k.hOut]
    exact h2
  · obtain ⟨r₁, r₂, a, G, w, roots, rfl, k⟩ := finish_inv hp h
    obtain ⟨ids, sd, an, took, d', h1, h2⟩ := key k.hSwitch
    refine ⟨r₁, r₂, _, ids, sd, an, took, d', rfl, h1, H.refl _, ?_⟩
    rw [k.hOut]
    exact h2

end VerifiableInference.Desc.First.K2

#print axioms VerifiableInference.Desc.First.K2.switchBehind_keeps
#print axioms VerifiableInference.Desc.First.K2.firstFront_keeps
#print axioms VerifiableInference.Desc.First.K2.firstBehind_keeps
#print axioms VerifiableInference.Desc.First.K2.yes_keeps
