-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K2R/HandsEnds.lean (over Johnson/IMR/TableW.lean, Johnson/P1K2R/HandsForm.lean and
K2C/HandsEnds.lean): code switching (K2): ITS SHARE OF «EACH SUB-PROTOCOL's ACCEPT HANDS THE
GROWTH ON» AT ITS TWO OTHER PLACES OF THE WRITTEN LIST: number 339 (the head's link, «H:2») and
number 353 (the finish, «F:1»). NO BLOCK IMPORTS THIS FILE.
  aroundB · around_head · around_finish   THE CLOSED FACTS ON THE WRITTEN LIST, BY THE KERNEL:
                                          where the chain stands in front and behind; which link
                                          the place behind names; the open classes of rows behind
                                          are the switch's three; of that segment's pins «pin m 0»
                                          alone is open
  around_wrong      a negative test: with the segment's number one too low the test rejects
  head_shape · finish_shape   what "H.1.quiet" and "F.0.quiet" hand on of the stand, the open link
                              and the count of rows that waits
  hands_head_ofR · hands_finish_ofR   AT HandsR:
                                      HeadFresh, the debts and «more» are
                                      asked at fenced states alone; the proofs stand at these; the
                                      names without R are their case «no fence»
  hands_head_of · hands_head_other · hands_finish_of   the ways out as letters (whatever ends in
                                                       "H.1.quiet"'s | "F.0.quiet"'s accept); p a
                                                       letter; the other dress at the head's place
  hands_at_head     KeepsAt at ⟨1, some 24, 2, K2⟩ (what k02_sits_file gives there) · the head's
                    public parameters name link 24 · AT THE PLACE's OWN NUMBERS n (prepOf Z G =
                    some P · numsAt P (some 24) = some n): N.groupAt 24 = n.grp, and SwitchDebts
                    with n.positions · HeadFresh at every state that meets X in front · the field
                    «more»: Hands N linksW placesW E ft 339 b
  hands_at_finish   KeepsAt at the finish's place · the like (no HeadFresh: the way in pushes the
                    group): Hands N linksW placesW E ft 353 b
PAID HERE: mark · shape · rows · members · book. PREMISES: hl24 · hgrp · HeadFresh · SwitchDebts'
six fields · more.
THE OTHER DRESSES. KeepsAt has three arms. At a place that names a link the finish's arm cannot
be, and at the finish's place the two others cannot. At the head's place the arm «dressed as a
link's switch» accepts no state that meets X in front: there the chain stands in the head's front,
and that dress asks «between two links». No soundness is claimed.
-/
import Johnson.IMR.TableW
import Johnson.P1K2R.HandsForm
import Johnson.Top.H0.Tw.K2C.HandsEnds
import Johnson.Top.H0.Tw.K2C.HeadLedger

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace P1K2
open VerifiableInference.Desc (Block Place OpenedColumn)
open VerifiableInference.Desc.First (S ModelPart Numbers Item Stand standOf standAt mayWait shapeAt
  rowsHeld membersHeld bookAt)
open VerifiableInference.Desc.First.K2 (P2 codeSwitchKind headOpenQ finishFrontQ finishBehindQ switchRowsOpen
  SwitchDebts HeadFresh head_three finish_three k2_step_two frameAt frontAt HeadPar)
open H2K.JointK (Sits)
open ProofFile (Cl)
open IM (Hands HandsR XK BK Yes xk_parts openAt linksW placesW k2P)
open _root_.Tw.K2 (switchNotices)

/-- The closed facts around the switch at number k of the written list: it stands at «front» in
front and at «behind» behind; the place behind names the link «lk»; m: the segment. -/
def aroundB (k m : Nat) (front behind : Stand) (lk : Option Nat) : Bool :=
  match placesW[k]?, placesW[k + 1]? with
  | some p, some p' =>
    decide (standAt linksW p = front) && decide (standAt linksW p' = behind) &&
      decide (p'.link = lk) &&
      decide ((openAt linksW placesW (k + 1)).filter Item.isRow = switchRowsOpen m) &&
      (openAt linksW placesW (k + 1)).contains (.pin m 0) &&
      !(openAt linksW placesW (k + 1)).contains (.pin m 1) &&
      !(openAt linksW placesW (k + 1)).contains (.pin m 2)
  | _, _ => false

set_option maxRecDepth 1000000 in
theorem around_head : aroundB 339 24 .headFront (.link .head) (some 24) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem around_finish : aroundB 353 25 .between .fin none = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem around_wrong : aroundB 339 23 .headFront (.link .head) (some 24) = false := by
  decide +kernel

/-- aroundB, cut in its parts. -/
theorem around_parts {k m : Nat} {front behind : Stand} {lk : Option Nat}
    (h : aroundB k m front behind lk = true) :
    ∃ p p', placesW[k]? = some p ∧ placesW[k + 1]? = some p' ∧ standAt linksW p = front ∧
      standAt linksW p' = behind ∧ p'.link = lk ∧
      (openAt linksW placesW (k + 1)).filter Item.isRow = switchRowsOpen m ∧
      (openAt linksW placesW (k + 1)).contains (.pin m 0) = true ∧
      (openAt linksW placesW (k + 1)).contains (.pin m 1) = false ∧
      (openAt linksW placesW (k + 1)).contains (.pin m 2) = false := by
  unfold aroundB at h
  cases hp : placesW[k]? with
  | none =>
    rw [hp] at h
    cases h
  | some p =>
    cases hp' : placesW[k + 1]? with
    | none =>
      rw [hp, hp'] at h
      cases h
    | some p' =>
      rw [hp, hp'] at h
      simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h
      obtain ⟨⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩, a6⟩, a7⟩ := h
      exact ⟨p, p', rfl, rfl, a1, a2, a3, a4, a5, a6, a7⟩

theorem head_shape {P : HeadPar} {m u : S} (h : headOpenQ P m = .ok u) :
    standOf u = .link .head ∧ (∃ L, u.link? = some L ∧ L.link = P.l) ∧
      u.rowsOwed = m.rowsOwed := by
  obtain ⟨_, ⟨b', hb', ho⟩, _⟩ := VerifiableInference.Desc.First.K2.headOpenOpens P m u h
  obtain ⟨a2, st, f, mine, L, out, y, cov, s₁, b, q⟩ :=
    (VerifiableInference.Desc.First.K2.headOpenQ_iff P m u).1 h
  obtain ⟨_, _, hL, _⟩ := Johnson.Desc.First.Walk.Law.front_ok q.front
  have hfk := VerifiableInference.Desc.First.K2.headOpenQ_fork h
  have hb2 : b'.L = L := by
    have e := hb'
    rw [q.out'] at e
    injection e with e
    rw [← e]
  refine ⟨?_, ⟨L, ?_, by rw [hL]⟩, ?_⟩
  · unfold standOf
    rw [hb']
    simp only
    rw [if_pos (by unfold S.inLink; rw [hfk]; rfl)]
  · unfold S.link?
    rw [hb']
    simp only [ho, if_true]
    rw [hb2]
  · rw [q.out']
    show s₁.rowsOwed = _
    rw [VerifiableInference.Desc.First.K2.openHeadQ q.opens]
    unfold S.openHead
    rw [q.here]
    simp only [q.fresh]
    rfl

theorem finish_shape {t' u : S} (h : finishBehindQ t' = .ok u) :
    standOf u = .fin ∧ u.link? = none ∧ u.rowsOwed = t'.rowsOwed := by
  obtain ⟨a, m, _, _, rfl⟩ := (VerifiableInference.Desc.First.K2.finishBehindQ_iff t' u).1 h
  exact ⟨rfl, rfl, rfl⟩

theorem xk_of {N : Numbers} {E : Nat → S → Bool} {k : Nat} {u : S}
    (d1 : shapeAt linksW placesW[k + 1]? u = true)
    (d2 : rowsHeld N (openAt linksW placesW (k + 1)) u = true)
    (d3 : membersHeld N (openAt linksW placesW (k + 1)) u = true)
    (d4 : bookAt N placesW[k + 1]? u = true) (d5 : E (k + 1) u = true) :
    XK N linksW placesW E (k + 1) u = true := by
  unfold XK BK
  rw [d1, d2, d3, d4, d5]
  rfl

/-- **At the head's link, the door a letter**: whatever way out ends in "H.1.quiet"'s accept. -/
theorem hands_head_ofR {Fk : Nat → S → Prop} {b : Block S Cl} {p : P2} {HP : HeadPar} {leave : S → S
    → Except String S}
    (hp : p.stands = .head) (hS : Sits b (codeSwitchKind p : Block S Unit) (fun s => .ok s) leave)
    (hd : MarkDoor (fun s => .ok s) leave)
    (hlv : ∀ s t u, leave s t = .ok u → headOpenQ HP t = .ok u) (hl24 : HP.l = 24)
    {N : Numbers} {E : Nat → S → Bool} {ft : Nat} (hgrp : N.groupAt 24 = p.grp)
    (fresh : ∀ s, Fk 339 s → XK N linksW placesW E 339 s = true → HeadFresh s)
    (D : ∀ (s : S) x W lay, Fk 339 s → XK N linksW placesW E 339 s = true → frontAt p s = some x →
      frameAt x = some W →
      OnBytes.layTrees x.st.codes (switchNotices x.T x.others) = some lay →
      SwitchDebts N 24 placesW[339]? placesW[339 + 1]? s.book.trees.size p.positions
        (1 + x.T.kept.size + x.own.length) x W lay)
    (more : ∀ s s', Fk 339 s → Yes ft b s s' → s.failed = none → s'.failed = none →
      XK N linksW placesW E 339 s = true → E (339 + 1) s' = true) :
    HandsR Fk N linksW placesW E ft 339 b := by
  obtain ⟨p₀, p', hp₀, hp', a1, a2, a3, a4, a5, a6, a7⟩ := around_parts around_head
  refine hands_of_sitsR hS hd fun s t t' s' rs cols k hfk hy e1 e2 e3 h0 h1 hx => ?_
  obtain rfl : s = t := Except.ok.inj e1
  obtain ⟨r₁, r₂, gs, hc, hd'⟩ := k2_step_two e2
  have hm := hlv s t' s' e3
  obtain ⟨c1, c2, c3⟩ := head_three hp hd' hm (fresh s hfk hx) N 24
    placesW[339]? placesW[339 + 1]? (openAt linksW placesW (339 + 1)) a4 a5 a6 a7
    hgrp (xk_parts hx).2.2.2.1 fun x W lay q1 q2 q3 => by
      rw [hc]
      exact D s x W lay hfk hx q1 q2 q3
  obtain ⟨s1, ⟨L, hL, hLl⟩, s3⟩ := head_shape hm
  have hown : t'.rowsOwed = none :=
    (VerifiableInference.Desc.First.K2.nothingWaits _ _ _ _ _ _ hd').2
  have d1 : shapeAt linksW placesW[339 + 1]? s' = true := by
    have hn : s'.noneWaits = true := by
      unfold S.noneWaits
      rw [s3, hown]
    rw [hp']
    unfold shapeAt
    simp only [s1, a2, hn, hL, a3, hLl, hl24, beq_self_eq_true, Bool.true_or,
      Option.all_some, Bool.and_self]
  exact xk_of d1 c1 c2 c3 (more s s' hfk hy h0 h1 hx)

/-- The same without a fence. -/
theorem hands_head_of {b : Block S Cl} {p : P2} {HP : HeadPar} {leave : S → S → Except String S}
    (hp : p.stands = .head) (hS : Sits b (codeSwitchKind p : Block S Unit) (fun s => .ok s) leave)
    (hd : MarkDoor (fun s => .ok s) leave)
    (hlv : ∀ s t u, leave s t = .ok u → headOpenQ HP t = .ok u) (hl24 : HP.l = 24)
    {N : Numbers} {E : Nat → S → Bool} {ft : Nat} (hgrp : N.groupAt 24 = p.grp)
    (fresh : ∀ s, XK N linksW placesW E 339 s = true → HeadFresh s)
    (D : ∀ (s : S) x W lay, XK N linksW placesW E 339 s = true → frontAt p s = some x →
      frameAt x = some W →
      OnBytes.layTrees x.st.codes (switchNotices x.T x.others) = some lay →
      SwitchDebts N 24 placesW[339]? placesW[339 + 1]? s.book.trees.size p.positions
        (1 + x.T.kept.size + x.own.length) x W lay)
    (more : ∀ s s', Yes ft b s s' → s.failed = none → s'.failed = none →
      XK N linksW placesW E 339 s = true → E (339 + 1) s' = true) :
    Hands N linksW placesW E ft 339 b :=
  (hands_head_ofR (Fk := fun _ _ => True) hp hS hd hlv hl24 hgrp (fun s _ => fresh s)
    (fun s x W lay _ => D s x W lay) fun s s' _ => more s s').free

/-- At the head's place the switch dressed as a link's accepts no state that meets X in front. -/
theorem hands_head_other {b : Block S Cl} {p : P2} {leave : S → S → Except String S}
    (hp : p.stands = .link) (hS : Sits b (codeSwitchKind p : Block S Unit) (fun s => .ok s) leave)
    (hd : MarkDoor (fun s => .ok s) leave) {N : Numbers} {E : Nat → S → Bool} {ft : Nat} :
    Hands N linksW placesW E ft 339 b := by
  obtain ⟨p₀, p', hp₀, hp', a1, _⟩ := around_parts around_head
  refine hands_of_sits hS hd fun s t t' s' rs cols k _ e1 e2 _ _ _ hx => ?_
  obtain rfl : s = t := Except.ok.inj e1
  obtain ⟨r₁, r₂, gs, _, hd'⟩ := k2_step_two e2
  have hst := VerifiableInference.Desc.First.K2.stands _ _ _ _ _ _ hd'
  have hsh := (xk_parts hx).1
  rw [hp₀] at hsh
  unfold shapeAt at hsh
  simp only [Bool.and_eq_true, beq_iff_eq, a1] at hsh
  have hbt : standOf s = .headFront := hsh.1.1
  rcases hst with ⟨_, hb⟩ | ⟨hq, _⟩ | ⟨hq, _⟩
  · unfold standOf at hbt
    rw [hb] at hbt
    cases hbt
  · rw [hp] at hq
    cases hq
  · rw [hp] at hq
    cases hq

/-- **At the finish, the way out a letter**: whatever ends in "F.0.quiet"'s accept. -/
theorem hands_finish_ofR {Fk : Nat → S → Prop} {b : Block S Cl} {p : P2} {leave : S → S → Except
    String S}
    (hp : p.stands = .finish) (hS : Sits b (codeSwitchKind p : Block S Unit) finishFrontQ leave)
    (hd : MarkDoor finishFrontQ leave)
    (hlv : ∀ s t u, leave s t = .ok u → finishBehindQ t = .ok u)
    {N : Numbers} {E : Nat → S → Bool} {ft : Nat} (hgrp : N.groupAt 25 = p.grp)
    (D : ∀ (s t : S) x W lay,
        Fk 353 s → XK N linksW placesW E 353 s = true → finishFrontQ s = .ok t →
      frontAt p t = some x → frameAt x = some W →
      OnBytes.layTrees x.st.codes (switchNotices x.T x.others) = some lay →
      SwitchDebts N 25 placesW[353]? placesW[353 + 1]? s.book.trees.size p.positions
        (1 + x.T.kept.size) x W lay)
    (more : ∀ s s', Fk 353 s → Yes ft b s s' → s.failed = none → s'.failed = none →
      XK N linksW placesW E 353 s = true → E (353 + 1) s' = true) :
    HandsR Fk N linksW placesW E ft 353 b := by
  obtain ⟨p₀, p', hp₀, hp', a1, a2, a3, a4, a5, a6, a7⟩ := around_parts around_finish
  refine hands_of_sitsR hS hd fun s t t' s' rs cols k hfk hy e1 e2 e3 h0 h1 hx => ?_
  obtain ⟨r₁, r₂, gs, hc, hd'⟩ := k2_step_two e2
  have hm := hlv s t' s' e3
  obtain ⟨c1, c2, c3⟩ := finish_three hp e1 hd' hm N 25
    placesW[353]? placesW[353 + 1]? (openAt linksW placesW (353 + 1)) a4 a5 a6 a7
    hgrp (xk_parts hx).2.2.2.1 fun x W lay q1 q2 q3 => by
      rw [hc]
      exact D s t x W lay hfk hx e1 q1 q2 q3
  obtain ⟨s1, s2, s3⟩ := finish_shape hm
  have hown : t'.rowsOwed = none :=
    (VerifiableInference.Desc.First.K2.nothingWaits _ _ _ _ _ _ hd').2
  have d1 : shapeAt linksW placesW[353 + 1]? s' = true := by
    have hn : s'.noneWaits = true := by
      unfold S.noneWaits
      rw [s3, hown]
    rw [hp']
    unfold shapeAt
    simp only [s1, a2, hn, s2, beq_self_eq_true, Bool.true_or, Option.all_none, Bool.and_self]
  exact xk_of d1 c1 c2 c3 (more s s' hfk hy h0 h1 hx)

/-- The same without a fence. -/
theorem hands_finish_of {b : Block S Cl} {p : P2} {leave : S → S → Except String S}
    (hp : p.stands = .finish) (hS : Sits b (codeSwitchKind p : Block S Unit) finishFrontQ leave)
    (hd : MarkDoor finishFrontQ leave)
    (hlv : ∀ s t u, leave s t = .ok u → finishBehindQ t = .ok u)
    {N : Numbers} {E : Nat → S → Bool} {ft : Nat} (hgrp : N.groupAt 25 = p.grp)
    (D : ∀ (s t : S) x W lay, XK N linksW placesW E 353 s = true → finishFrontQ s = .ok t →
      frontAt p t = some x → frameAt x = some W →
      OnBytes.layTrees x.st.codes (switchNotices x.T x.others) = some lay →
      SwitchDebts N 25 placesW[353]? placesW[353 + 1]? s.book.trees.size p.positions
        (1 + x.T.kept.size) x W lay)
    (more : ∀ s s', Yes ft b s s' → s.failed = none → s'.failed = none →
      XK N linksW placesW E 353 s = true → E (353 + 1) s' = true) :
    Hands N linksW placesW E ft 353 b :=
  (hands_finish_ofR (Fk := fun _ _ => True) hp hS hd hlv hgrp
    (fun s t x W lay _ => D s t x W lay) fun s s' _ => more s s').free

theorem bind_guards {x : Except String S} {s u : S} (h : x.bind (guards s) = .ok u) :
    x = .ok u := by
  obtain ⟨m, hm, hg⟩ := (VerifiableInference.Desc.Except.bind_eq_ok _ _ _).1 h
  rw [guards_same hg]
  exact hm

/-- **The share at the head's link**, at the seated sub-protocol. -/
theorem hands_at_head {Z : ProofFile.Pub} {G : ProofFile.Ground} {nm : String} {b : Block S Cl}
    (hK : KeepsAt Z G { chain := 1, link := some 24, piece := 2, kind := .K2 } nm b)
    (hl24 : ∀ HP, pureLetters G 24 = some HP → HP.l = 24)
    {N : Numbers} {E : Nat → S → Bool} {ft : Nat}
    (hgrp : ∀ P n, prepOf Z G = some P → numsAt P (some 24) = some n → N.groupAt 24 = n.grp)
    (fresh : ∀ s, XK N linksW placesW E 339 s = true → HeadFresh s)
    (D : ∀ P n (s : S) x W lay, prepOf Z G = some P → numsAt P (some 24) = some n →
      XK N linksW placesW E 339 s = true →
      frontAt (k2P Z { chain := 1, link := some 24, piece := 2, kind := .K2 } nm .head n) s =
        some x → frameAt x = some W →
      OnBytes.layTrees x.st.codes (switchNotices x.T x.others) = some lay →
      SwitchDebts N 24 placesW[339]? placesW[339 + 1]? s.book.trees.size n.positions
        (1 + x.T.kept.size + x.own.length) x W lay)
    (more : ∀ s s', Yes ft b s s' → s.failed = none → s'.failed = none →
      XK N linksW placesW E 339 s = true → E (339 + 1) s' = true) :
    Hands N linksW placesW E ft 339 b := by
  obtain ⟨P, n, hP, hn, hA⟩ := hK
  rcases hA with ⟨h0, _⟩ | ⟨l, HP, hl, hHP, hS, _⟩ | ⟨l, _, hS, _⟩
  · cases h0
  · obtain rfl : 24 = l := Option.some.inj hl
    exact hands_head_of (HP := HP) rfl hS (door_head HP).mark (fun s t u e => bind_guards e)
      (hl24 HP hHP) (hgrp P n hP hn) fresh (fun s x W lay => D P n s x W lay hP hn) more
  · exact hands_head_other rfl hS door_guards.mark

/-- **The share at the finish**, at the seated sub-protocol. -/
theorem hands_at_finish {Z : ProofFile.Pub} {G : ProofFile.Ground} {nm : String} {b : Block S Cl}
    (hK : KeepsAt Z G IM.k2PlaceF nm b) {N : Numbers} {E : Nat → S → Bool} {ft : Nat}
    (hgrp : ∀ P n, prepOf Z G = some P → numsAt P none = some n → N.groupAt 25 = n.grp)
    (D : ∀ P n (s t : S) x W lay, prepOf Z G = some P → numsAt P none = some n →
      XK N linksW placesW E 353 s = true → finishFrontQ s = .ok t →
      frontAt (k2P Z IM.k2PlaceF nm .finish n) t = some x → frameAt x = some W →
      OnBytes.layTrees x.st.codes (switchNotices x.T x.others) = some lay →
      SwitchDebts N 25 placesW[353]? placesW[353 + 1]? s.book.trees.size n.positions
        (1 + x.T.kept.size) x W lay)
    (more : ∀ s s', Yes ft b s s' → s.failed = none → s'.failed = none →
      XK N linksW placesW E 353 s = true → E (353 + 1) s' = true) :
    Hands N linksW placesW E ft 353 b := by
  obtain ⟨P, n, hP, hn, hA⟩ := hK
  rcases hA with ⟨_, hS, _⟩ | ⟨l, HP, hl, _⟩ | ⟨l, hl, _⟩
  · exact hands_finish_of rfl hS door_finish.mark (fun s t u e => bind_guards e)
      (hgrp P n hP hn) (fun s t x W lay => D P n s t x W lay hP hn) more
  · cases hl
  · cases hl

end P1K2

#print axioms P1K2.around_head
#print axioms P1K2.around_finish
#print axioms P1K2.hands_head_ofR
#print axioms P1K2.hands_finish_ofR
#print axioms P1K2.hands_head_of
#print axioms P1K2.hands_finish_of
#print axioms P1K2.hands_at_head
#print axioms P1K2.hands_at_finish
