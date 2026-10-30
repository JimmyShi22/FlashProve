-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K2R/HandsLinks.lean (over Johnson/IMR/TableW.lean, P1K2R/HandsForm.lean, K2C/HandsLink.lean
and Walk/FrameOpenedShape.lean): code switching (K2): ITS SHARE OF «EACH SUB-PROTOCOL's ACCEPT
HANDS THE GROWTH ON» AT THE 23 LINKS' FIRST PLACES (numbers 14 l + 2, 1 ≤ l < 24, of the written
list of places): Hands N linksW placesW E ft (14 l + 2) b, b the seated sub-protocol (the switch
with the link's own «opened» joined). NO BLOCK IMPORTS THIS FILE.
  frontLinkB · behindLinkB · around_links   THE CLOSED FACTS ON THE WRITTEN LIST, BY THE KERNEL,
                                            at all 23: in front the chain stands between two
                                            links; behind it stands in link l, of the written
                                            sort; no count of rows may wait there; the open
                                            classes of rows are the switch's three; of segment l's
                                            pins «pin l 0» alone is open
  around_at         the two tests at one l
  around_bent       a negative test: at l = 0 (where no switch stands) the test behind rejects
  shape_behind      shapeAt behind, from opened_shape (Walk/FrameOpenedShape.lean)
  hands_link_ofR · hands_at_linkR   AT THE FENCED FORM HandsR
                                    (IMR/HandsFence.lean): the debts and «more» are asked at fenced
                                    states alone (Fk (14 l + 2) s); the proofs stand at these; the
                                    names without R are their case «no fence»
  hands_link_of     the way out a letter (whatever ends in the link's own «opened»); p a letter
                    with p.stands = .link
  hands_link_other  the other dress
  hands_at_link     KeepsJoined (P1K2R/SitsDoor.lean: what k02_sits_file gives at the place) · the
                    l-th link's public parameters are not the head's and are of the written sort ·
                    AT THE PLACE's OWN NUMBERS n (prepOf Z G = some P · numsAt P (some l) = some
                    n): N.groupAt l = n.grp, and LinkDebts with n.positions at every state that
                    meets X in front · the field «more»: Hands
PAID HERE: mark · shape · rows · members · book. PREMISES: the sort (hsort: P1L20R/FrameFold.lean's
kind_of_sort with subW_eq) · hgrp · LinkDebts' six fields · more.
THE OTHER DRESS. KeepsJoined has a second arm (the switch dressed as the head's): there no state
that meets X in front is accepted: the chain stands between two links, and that dress asks the
head's front. No soundness is claimed.
-/
import Johnson.IMR.TableW
import Johnson.P1K2R.HandsForm
import Johnson.Top.H0.Tw.K2C.HandsLink
import Johnson.Top.H0.Walk.FrameOpenedShape

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace P1K2
open VerifiableInference.Desc (Block Place OpenedColumn)
open VerifiableInference.Desc.First (S ModelPart Numbers Item Stand standOf standAt mayWait shapeAt
  rowsHeld membersHeld bookAt)
open VerifiableInference.Desc.First.K2 (P2 codeSwitchKind headOpenQ switchRowsOpen LinkDebts link_three
  k2_step_two frameAt)
open Johnson.Desc.First.Walk.Seat (LinkFrame framesOf)
open H2K.JointK (Sits)
open ProofFile (Cl)
open IM (Hands HandsR XK BK Yes xk_parts openAt linksW placesW subW k2P)
open _root_.Tw.K2 (firstFront switchNotices sendByL8)

/-- In front of the switch into group l the chain stands between two links. -/
def frontLinkB (l : Nat) : Bool :=
  match placesW[14 * l + 2]? with
  | some p => decide (standAt linksW p = .between)
  | none => false

/-- Behind it. -/
def behindLinkB (l : Nat) : Bool :=
  match placesW[14 * l + 3]? with
  | some p' =>
    decide (standAt linksW p' = .link (subW l)) && decide (p'.link = some l) &&
      decide ((openAt linksW placesW (14 * l + 3)).filter Item.isRow = switchRowsOpen l) &&
      (openAt linksW placesW (14 * l + 3)).contains (.pin l 0) &&
      !(openAt linksW placesW (14 * l + 3)).contains (.pin l 1) &&
      !(openAt linksW placesW (14 * l + 3)).contains (.pin l 2)
  | none => false

set_option maxRecDepth 1000000 in
theorem around_links : ((List.range' 1 23).all fun l => frontLinkB l && behindLinkB l) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem around_bent : behindLinkB 0 = false := by decide +kernel

theorem around_at {l : Nat} (h1 : 1 ≤ l) (h24 : l < 24) :
    frontLinkB l = true ∧ behindLinkB l = true := by
  have h := List.all_eq_true.1 around_links l (List.mem_range'_1.2 ⟨h1, by omega⟩)
  exact Bool.and_eq_true_iff.1 h

/-- shapeAt behind the link's own «opened». -/
theorem shape_behind {l : Nat} (h1 : 1 ≤ l) (h24 : l < 24) {u : S} {L : OnBytes.Model.LinkCtx}
    (hL : u.link? = some L) (hl : L.link = l) (hw : u.rowsOwed = none)
    (hs : standOf u = .link (subW l)) : shapeAt linksW placesW[14 * l + 3]? u = true := by
  have hB := (around_at h1 h24).2
  unfold behindLinkB at hB
  cases hp : placesW[14 * l + 3]? with
  | none =>
    rw [hp] at hB
    cases hB
  | some p' =>
    rw [hp] at hB
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hB
    obtain ⟨⟨⟨⟨⟨a1, a2⟩, _⟩, _⟩, _⟩, _⟩ := hB
    have hn : u.noneWaits = true := by
      unfold S.noneWaits
      rw [hw]
    unfold shapeAt
    simp only [hs, a1, hn, hL, a2, hl, beq_self_eq_true, Bool.true_or, Option.all_some,
      Bool.and_self]

/-- **At a link's first place, the way out a letter**: whatever ends in the link's own «opened». -/
theorem hands_link_ofR {Fk : Nat → S → Prop} {built : Array OnBytes.Model.Stages.LinkH} {first :
    OnBytes.Params.First}
    {Wp : OnBytes.Model.Verify.Public} {l : Nat} (h1 : 1 ≤ l) (h24 : l < 24) {b : Block S Cl}
    {p : P2} {leave : S → S → Except String S} {fs : List LinkFrame} {f : LinkFrame}
    {X : OnBytes.Model.Stages.LinkH} (hfs : framesOf built first Wp = .ok fs)
    (hf : fs[l]? = some f) (hX : built[l]? = some X) (hk : X.kind ≠ 2)
    (hsort : (X.kind = 0 → subW l = .layers) ∧ (X.kind = 1 → subW l = .attention))
    (hp : p.stands = .link) (hS : Sits b (codeSwitchKind p : Block S Unit) (fun s => .ok s) leave)
    (hd : MarkDoor (fun s => .ok s) leave)
    (hlv : ∀ s t u, leave s t = .ok u → f.opened t = .ok u)
    {N : Numbers} {E : Nat → S → Bool} {ft : Nat} (hgrp : N.groupAt l = p.grp)
    (D : ∀ (s : S) x W lay, Fk (14 * l + 2) s → XK N linksW placesW E (14 * l + 2) s = true →
      firstFront s.st s.check.frame = .ok x → frameAt x = some W →
      OnBytes.layTrees x.st.codes (switchNotices x.T x.others) = some lay →
      LinkDebts N l placesW[14 * l + 2]? placesW[14 * l + 3]? s p.positions x W lay)
    (more : ∀ s s', Fk (14 * l + 2) s → Yes ft b s s' → s.failed = none → s'.failed = none →
      XK N linksW placesW E (14 * l + 2) s = true → E (14 * l + 2 + 1) s' = true) :
    HandsR Fk N linksW placesW E ft (14 * l + 2) b := by
  have hB := (around_at h1 h24).2
  refine hands_of_sitsR hS hd fun s t t' s' rs cols k hfk hy e1 e2 e3 h0 h1' hx => ?_
  obtain rfl : s = t := Except.ok.inj e1
  obtain ⟨r₁, r₂, gs, hc, hd'⟩ := k2_step_two e2
  have ho := hlv s t' s' e3
  obtain ⟨k1, k2', _, k4, _, _⟩ := Johnson.Desc.First.Walk.Tied.opened_keeps hfs hf ho
  obtain ⟨⟨L, hL, hl⟩, hw, hst⟩ := Johnson.Desc.First.Walk.Tied.opened_shape hfs hf hX hk ho
  unfold behindLinkB at hB
  cases hpl : placesW[14 * l + 3]? with
  | none =>
    rw [hpl] at hB
    cases hB
  | some p' =>
    rw [hpl] at hB
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hB
    obtain ⟨⟨⟨⟨⟨_, _⟩, b3⟩, b4⟩, b5⟩, b6⟩ := hB
    obtain ⟨c1, c2, c3⟩ := link_three hp hd' N l placesW[14 * l + 2]?
      placesW[14 * l + 3]? (openAt linksW placesW (14 * l + 3)) b3 b4 b5 b6 hgrp
      (xk_parts hx).2.2.2.1 fun x W lay q1 q2 q3 => by
        rw [hc]
        exact D s x W lay hfk hx q1 q2 q3
    have hown : t'.rowsOwed = none :=
      (VerifiableInference.Desc.First.K2.nothingWaits _ _ _ _ _ _ hd').2
    have hsd : standOf s' = .link (subW l) := by
      rcases hst with ⟨q, e⟩ | ⟨q, e⟩
      · rw [e, hsort.1 q]
      · rw [e, hsort.2 q]
    have d1 : shapeAt linksW placesW[14 * l + 2 + 1]? s' = true :=
      shape_behind h1 h24 hL hl (by rw [hw, hown]) hsd
    have d2 : rowsHeld N (openAt linksW placesW (14 * l + 2 + 1)) s' = true := by
      rw [VerifiableInference.Desc.First.rowsHeld_of_groups N _ t' s' (by rw [k1])]
      exact c1
    have d3 : membersHeld N (openAt linksW placesW (14 * l + 2 + 1)) s' = true := by
      rw [VerifiableInference.Desc.First.membersHeld_of_groups N _ t' s' (by rw [k1])
        (by rw [k2'])]
      exact c2
    have d4 : bookAt N placesW[14 * l + 2 + 1]? s' = true := by
      unfold bookAt at c3 ⊢
      rw [k1, k2']
      exact c3
    have d5 := more s s' hfk hy h0 h1' hx
    unfold XK BK
    rw [d1, d2, d3, d4, d5]
    rfl

/-- The same without a fence. -/
theorem hands_link_of {built : Array OnBytes.Model.Stages.LinkH} {first : OnBytes.Params.First}
    {Wp : OnBytes.Model.Verify.Public} {l : Nat} (h1 : 1 ≤ l) (h24 : l < 24) {b : Block S Cl}
    {p : P2} {leave : S → S → Except String S} {fs : List LinkFrame} {f : LinkFrame}
    {X : OnBytes.Model.Stages.LinkH} (hfs : framesOf built first Wp = .ok fs)
    (hf : fs[l]? = some f) (hX : built[l]? = some X) (hk : X.kind ≠ 2)
    (hsort : (X.kind = 0 → subW l = .layers) ∧ (X.kind = 1 → subW l = .attention))
    (hp : p.stands = .link) (hS : Sits b (codeSwitchKind p : Block S Unit) (fun s => .ok s) leave)
    (hd : MarkDoor (fun s => .ok s) leave)
    (hlv : ∀ s t u, leave s t = .ok u → f.opened t = .ok u)
    {N : Numbers} {E : Nat → S → Bool} {ft : Nat} (hgrp : N.groupAt l = p.grp)
    (D : ∀ (s : S) x W lay, XK N linksW placesW E (14 * l + 2) s = true →
      firstFront s.st s.check.frame = .ok x → frameAt x = some W →
      OnBytes.layTrees x.st.codes (switchNotices x.T x.others) = some lay →
      LinkDebts N l placesW[14 * l + 2]? placesW[14 * l + 3]? s p.positions x W lay)
    (more : ∀ s s', Yes ft b s s' → s.failed = none → s'.failed = none →
      XK N linksW placesW E (14 * l + 2) s = true → E (14 * l + 2 + 1) s' = true) :
    Hands N linksW placesW E ft (14 * l + 2) b :=
  (hands_link_ofR (Fk := fun _ _ => True) h1 h24 hfs hf hX hk hsort hp hS hd hlv hgrp
    (fun s x W lay _ => D s x W lay) fun s s' _ => more s s').free

/-- At a link's first place the switch dressed as the head's accepts no state that meets X in
front. -/
theorem hands_link_other {l : Nat} (h1 : 1 ≤ l) (h24 : l < 24) {b : Block S Cl} {p : P2}
    {leave : S → S → Except String S} (hp : p.stands = .head)
    (hS : Sits b (codeSwitchKind p : Block S Unit) (fun s => .ok s) leave)
    (hd : MarkDoor (fun s => .ok s) leave) {N : Numbers} {E : Nat → S → Bool} {ft : Nat} :
    Hands N linksW placesW E ft (14 * l + 2) b := by
  have hFr := (around_at h1 h24).1
  refine hands_of_sits hS hd fun s t t' s' rs cols k _ e1 e2 _ _ _ hx => ?_
  obtain rfl : s = t := Except.ok.inj e1
  obtain ⟨r₁, r₂, gs, _, hd'⟩ := k2_step_two e2
  have hst := VerifiableInference.Desc.First.K2.stands _ _ _ _ _ _ hd'
  have hsh := (xk_parts hx).1
  unfold frontLinkB at hFr
  cases hpl : placesW[14 * l + 2]? with
  | none =>
    rw [hpl] at hFr
    cases hFr
  | some p₀ =>
    rw [hpl] at hFr hsh
    have a0 : standAt linksW p₀ = .between := of_decide_eq_true hFr
    unfold shapeAt at hsh
    simp only [Bool.and_eq_true, beq_iff_eq, a0] at hsh
    have hbt : standOf s = .between := hsh.1.1
    rcases hst with ⟨hq, _⟩ | ⟨_, a, ha⟩ | ⟨hq, _⟩
    · rw [hp] at hq
      cases hq
    · unfold standOf at hbt
      rw [ha] at hbt
      have hb2 : (if s.inLink then Stand.link ModelPart.head else Stand.headFront) = Stand.between :=
        hbt
      split at hb2 <;> cases hb2
    · rw [hp] at hq
      cases hq

/-- **The share at a link's first place**, at the seated sub-protocol. THE PREMISES ON THE NUMBERS
ARE BOUND TO THE PLACE's OWN NUMBERS n (the lot's numsAt at the link). -/
theorem hands_at_linkR {Fk : Nat → S → Prop} {Z : ProofFile.Pub} {G : ProofFile.Ground} {l : Nat} (h1 : 1 ≤ l)
    (h24 : l < 24)
    {nm : String} {b : Block S Cl} {fs : List LinkFrame} {f : LinkFrame}
    {X : OnBytes.Model.Stages.LinkH}
    (hfs : framesOf Z.p.built.links Z.first Z.p.X = .ok fs) (hf : fs[l]? = some f)
    (hX : Z.p.built.links[l]? = some X) (hk : X.kind ≠ 2)
    (hsort : (X.kind = 0 → subW l = .layers) ∧ (X.kind = 1 → subW l = .attention))
    (hK : KeepsJoined Z G { chain := 1, link := some l, piece := 1, kind := .K2 } nm b f)
    {N : Numbers} {E : Nat → S → Bool} {ft : Nat}
    (hgrp : ∀ P n, prepOf Z G = some P → numsAt P (some l) = some n → N.groupAt l = n.grp)
    (D : ∀ P n (s : S) x W lay, prepOf Z G = some P → numsAt P (some l) = some n →
      Fk (14 * l + 2) s → XK N linksW placesW E (14 * l + 2) s = true →
      firstFront s.st s.check.frame = .ok x → frameAt x = some W →
      OnBytes.layTrees x.st.codes (switchNotices x.T x.others) = some lay →
      LinkDebts N l placesW[14 * l + 2]? placesW[14 * l + 3]? s n.positions x W lay)
    (more : ∀ s s', Fk (14 * l + 2) s → Yes ft b s s' → s.failed = none → s'.failed = none →
      XK N linksW placesW E (14 * l + 2) s = true → E (14 * l + 2 + 1) s' = true) :
    HandsR Fk N linksW placesW E ft (14 * l + 2) b := by
  obtain ⟨P, n, hP, hn, hA⟩ := hK
  rcases hA with ⟨l', HP, _, _, hS, _⟩ | ⟨l', _, hS, _⟩
  · exact (hands_link_other h1 h24 rfl hS (door_head_opened f HP).mark).fenced
  · exact hands_link_ofR h1 h24 hfs hf hX hk hsort rfl hS (door_opened f).mark
      (fun s t u e => leaveOpened_is e) (hgrp P n hP hn)
      (fun s x W lay => D P n s x W lay hP hn) more

/-- The same without a fence. -/
theorem hands_at_link {Z : ProofFile.Pub} {G : ProofFile.Ground} {l : Nat} (h1 : 1 ≤ l) (h24 : l < 24)
    {nm : String} {b : Block S Cl} {fs : List LinkFrame} {f : LinkFrame}
    {X : OnBytes.Model.Stages.LinkH}
    (hfs : framesOf Z.p.built.links Z.first Z.p.X = .ok fs) (hf : fs[l]? = some f)
    (hX : Z.p.built.links[l]? = some X) (hk : X.kind ≠ 2)
    (hsort : (X.kind = 0 → subW l = .layers) ∧ (X.kind = 1 → subW l = .attention))
    (hK : KeepsJoined Z G { chain := 1, link := some l, piece := 1, kind := .K2 } nm b f)
    {N : Numbers} {E : Nat → S → Bool} {ft : Nat}
    (hgrp : ∀ P n, prepOf Z G = some P → numsAt P (some l) = some n → N.groupAt l = n.grp)
    (D : ∀ P n (s : S) x W lay, prepOf Z G = some P → numsAt P (some l) = some n →
      XK N linksW placesW E (14 * l + 2) s = true →
      firstFront s.st s.check.frame = .ok x → frameAt x = some W →
      OnBytes.layTrees x.st.codes (switchNotices x.T x.others) = some lay →
      LinkDebts N l placesW[14 * l + 2]? placesW[14 * l + 3]? s n.positions x W lay)
    (more : ∀ s s', Yes ft b s s' → s.failed = none → s'.failed = none →
      XK N linksW placesW E (14 * l + 2) s = true → E (14 * l + 2 + 1) s' = true) :
    Hands N linksW placesW E ft (14 * l + 2) b :=
  (hands_at_linkR (Fk := fun _ _ => True) h1 h24 hfs hf hX hk hsort hK hgrp
    (fun P n s x W lay a b _ => D P n s x W lay a b) fun s s' _ => more s s').free

end P1K2

#print axioms P1K2.around_links
#print axioms P1K2.shape_behind
#print axioms P1K2.hands_link_ofR
#print axioms P1K2.hands_at_linkR
#print axioms P1K2.hands_link_of
#print axioms P1K2.hands_at_link
