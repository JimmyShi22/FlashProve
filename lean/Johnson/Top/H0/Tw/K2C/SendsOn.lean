-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Tw/K2C/SendsOn.lean: the kind «the code switch»: THE FENCE, AND THE PREMISE OF THE
LAW OF A
SENDING WHOSE BLOCK GOES ON, for the switch's block and for the two whole places that hold it.
NO BLOCK IMPORTS THIS FILE.
  FrontOf p s x   x is the front that the switch's block takes off the record s: at a link what
                  firstFront makes of the statement and the frame; at the head's link and at the
                  finish
                  the record's own parts (headFrontOf · finFrontOf, K2C/Closed.lean)
  Fence …         a condition on the record IN FRONT: the front's announcements are a given list,
  its
                  statement has given codes and a given number of messages
  yes_front       yes_keeps (K2C/Keeps.lean) with FrontOf p s x in its conclusion
  k2_door         inside the fence, a yes of the switch's block holds a yes of sendP at the given
                  announcements, codes and number, and R holds from what sendP returns to the
                  statement
                  behind the block: for every R that the plain ground's functions keep
  h2_door · f1_door   the same of the whole place «H:2» (the switch, then "H.1.quiet") and of the
  whole
                  place «F:1» ("F.0.front", the switch, "F.0.quiet"); at «F:1» the fence speaks of
                  the
                  record behind "F.0.front"
THE FENCE IS A PREMISE. NO RECORD IS SHOWN HERE TO MEET IT: that the carried frame's shape and
groups are
the plan's at the records that a run reaches is said by no theorem of this library yet.
(Where this and lean/THEOREM.md differ, the page
holds.) A fence that
no record meets makes these statements idle.
(Johnson/Desc/GroundKeeps.lean stands on Mathlib.) No soundness is claimed.
-/
import Johnson.Top.H0.Tw.K2C.Keeps

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block roundlessBlock)
open _root_.Tw.K2 (SwIn SwOut switchBehind switchNotices sendByL8 firstFront)
open VerifiableInference.Desc.Ground (GroundKeeps)

variable {R : Statement → Statement → Prop}

/-- x is the front that the switch's block takes off the record s. -/
def FrontOf (p : P2) (s : S) (x : _root_.Tw.K2.Front) : Prop :=
  (p.stands = .link ∧ firstFront s.st s.check.frame = .ok x) ∨
  (p.stands = .head ∧ ∃ a G, s.here = .head a ∧ s.check.frame.groups[s.check.frame.link]? = some G ∧
    x = headFrontOf s a G.target) ∨
  (p.stands = .finish ∧ ∃ a G, s.here = .fin a ∧ a.G = some G ∧ x = finFrontOf s a G)

/-- The fence on the record in front. -/
def Fence (p : P2) (sent : Array OracleNotice) (codes : Codes) (n₀ : Nat) (s : S) : Prop :=
  ∀ x,
      FrontOf p s x → switchNotices x.T x.others = sent ∧ x.st.codes = codes ∧ x.st.oracles.size =
          n₀

theorem yes_front (H : GroundKeeps R) {p : P2} {s : S} {rs : List Fmt.RoundView} {gs : List (List (Nat ×
           List UInt64))} {s' : S}
    (h : decideWith sendByL8 p s rs gs = .ok s') :
    ∃ (r₁ r₂ : Fmt.RoundView) (x : _root_.Tw.K2.Front), ∃ ids sd an took d', rs = [r₁,
               r₂] ∧ FrontOf p s x ∧
      Desc.Plain.sendP (Desc.Plain.groundG : Desc.Plain.Ground Unit) ⟨p.samples, p.firstTree⟩ false
        ⟨x.st, s.book, s.roots, [], ()⟩ (switchNotices x.T x.others) r₁ r₂ = some (ids, sd, an,
            took, d') ∧
      R d'.st s'.st := by
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
    refine ⟨r₁, r₂, x, ids, sd, an, took, d', rfl, Or.inl ⟨hp, k.hFront⟩, h1, ?_⟩
    rw [k.hOut]
    exact H.trans h2 (firstBehind_keeps H k.hBehind)
  · obtain ⟨r₁, r₂, a, G, w, roots, rfl, k⟩ := head_inv hp h
    obtain ⟨ids, sd, an, took, d', h1, h2⟩ := key k.hSwitch
    refine ⟨r₁, r₂, _, ids, sd, an, took, d', rfl, Or.inr (Or.inl ⟨hp, a, G, k.hHere, k.hGroup,
        rfl⟩), h1, ?_⟩
    rw [k.hOut]
    exact h2
  · obtain ⟨r₁, r₂, a, G, w, roots, rfl, k⟩ := finish_inv hp h
    obtain ⟨ids, sd, an, took, d', h1, h2⟩ := key k.hSwitch
    refine ⟨r₁, r₂, _, ids, sd, an, took, d', rfl, Or.inr (Or.inr ⟨hp, a, G, k.hHere, k.hLaid,
        rfl⟩), h1, ?_⟩
    rw [k.hOut]
    exact h2

/-- What the law of a sending whose block goes on asks of a block, at a record s and a record s'
behind. -/
def DoorAt (R : Statement → Statement → Prop) (p : P2) (sent : Array OracleNotice) (codes : Codes)
    (n₀ : Nat) (r₁ : Fmt.RoundView)
    (s' : S) : Prop :=
  ∃ (L : Type) (d d' : Desc.Plain.DState L) (gp : Desc.Plain.GPar) (sent' : Array OracleNotice) (own
      : Bool) (r₂ : Fmt.RoundView)
    (ids : Array Nat) (sd an : List E) (need : Nat),
    Desc.Plain.sendP Desc.Plain.groundG gp own d sent' r₁ r₂ = some (ids, sd, an, need, d') ∧
      gp = ⟨p.samples,
          p.firstTree⟩ ∧ sent' = sent ∧ d.st.codes = codes ∧ R d'.st s'.st ∧ n₀ = d.st.oracles.size

theorem door_of_yes (H : GroundKeeps R) {p : P2} {sent : Array OracleNotice} {codes : Codes} {n₀ :
    Nat} {s s' : S}
    {r₁ : Fmt.RoundView} {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))} (hF : Fence p sent codes
                      n₀ s)
    (h : decideWith sendByL8 p s (r₁ :: rs) gs = .ok s') : DoorAt R p sent codes n₀ r₁ s' := by
  obtain ⟨a₁, r₂, x, ids, sd, an, took, d', e, hx, hs, hr⟩ := yes_front H h
  obtain ⟨rfl, _⟩ := List.cons.inj e
  obtain ⟨f1, f2, f3⟩ := hF x hx
  exact ⟨Unit, ⟨x.st, s.book, s.roots, [], ()⟩, d', ⟨p.samples, p.firstTree⟩, _, false, r₂, ids, sd,
      an, took, hs, rfl, f1,
    f2, hr, f3.symm⟩

/-- **The switch's block.** -/
theorem k2_door (H : GroundKeeps R) (p : P2) (sent : Array OracleNotice) (codes : Codes) (n₀ : Nat)
    :
    ∀ s s' r₁ rs gs,
        Fence p sent codes n₀ s → (codeSwitchKind p : Block S Unit).decide s (r₁ :: rs) gs = .ok s' →
      DoorAt R p sent codes n₀ r₁ s' :=
  fun _ _ _ _ _ hF h => door_of_yes H hF h

theorem DoorAt.then (H : GroundKeeps R) {p : P2} {sent : Array OracleNotice} {codes : Codes} {n₀ :
    Nat} {r₁ : Fmt.RoundView} {t s' : S}
    (h : DoorAt R p sent codes n₀ r₁ t) (k : R t.st s'.st) : DoorAt R p sent codes n₀ r₁ s' := by
  obtain ⟨L, d, d', gp, sent', own, r₂, ids, sd, an, need, a1, a2, a3, a4, a5, a6⟩ := h
  exact ⟨L, d, d', gp, sent', own, r₂, ids, sd, an, need, a1, a2, a3, a4, H.trans a5 k, a6⟩

/-- "H.1.quiet" writes the statement by the own messages' joins alone. -/
theorem headOpenQ_keeps (H : GroundKeeps R) {P : HeadPar} {s s' : S} (h : headOpenQ P s = .ok s') :
    R s.st s'.st := by
  obtain ⟨a, st, f, mine, L, out, y, cov, s₁, b, k⟩ := (headOpenQ_iff P s s').1 h
  rw [k.out']
  exact firstBehind_keeps H k.behind

/-- "F.0.front" writes the statement by the new group alone. -/
theorem finishFrontQ_keeps (H : GroundKeeps R) {s s' : S} (h : finishFrontQ s = .ok s') : R s.st
    s'.st := by
  obtain ⟨G, x, s₁, a, k⟩ := (finishFrontQ_iff s s').1 h
  rw [k.out]
  exact finishFront_keeps H k.front

/-- "F.0.quiet" leaves the statement. -/
theorem finishBehindQ_st {s s' : S} (h : finishBehindQ s = .ok s') : s'.st = s.st := by
  obtain ⟨a, m, _, _, rfl⟩ := (finishBehindQ_iff s s').1 h
  rfl

/-- **The whole place «H:2».** -/
theorem h2_door (H : GroundKeeps R) (p : P2) (n : String) (P : HeadPar) (sent : Array OracleNotice)
    (codes : Codes) (n₀ : Nat) :
    ∀ s s' r₁ rs gs, Fence p sent codes n₀ s →
      ((codeSwitchKind p : Block S Unit).andThen n (headOpened n p.place P)).decide s (r₁ :: rs) gs = .ok s' →
      DoorAt R p sent codes n₀ r₁ s' := by
  intro s s' r₁ rs gs hF h
  obtain ⟨t, ht, h⟩ :=
    bindOk (x := (codeSwitchKind p : Block S Unit).decide s ((r₁ :: rs).take (codeSwitchKind p : Block S
                    Unit).rounds.length)
      (gs.take (codeSwitchKind p : Block S Unit).openings)) h
  have ht : decideWith sendByL8 p s (r₁ :: rs.take 1) (gs.take (codeSwitchKind p : Block S Unit).openings) = .ok
      t := ht
  have h : headOpenQ P t = .ok s' := h
  exact (door_of_yes H hF ht).then H (headOpenQ_keeps H h)

/-- **The whole place «F:1».** The fence speaks of the record behind "F.0.front". -/
theorem f1_door (H : GroundKeeps R) (p : P2) (sent : Array OracleNotice) (codes : Codes) (n₀ : Nat)
    :
    ∀ s s' r₁ rs gs, (∀ s₁, finishFrontQ s = .ok s₁ → Fence p sent codes n₀ s₁) →
      (finishPlace p : Block S Unit).decide s (r₁ :: rs) gs = .ok s' → DoorAt R p sent codes n₀ r₁
          s' := by
  intro s s' r₁ rs gs hF h
  simp only [finishPlace, Block.andThen, roundlessBlock] at h
  obtain ⟨s₂, h₂, h₃⟩ := bindOk h
  obtain ⟨s₁, h₁, h₂⟩ := bindOk h₂
  have h₂ : decideWith sendByL8 p s₁ (r₁ :: rs.take 1) _ = .ok s₂ := h₂
  have e := finishBehindQ_st h₃
  exact (door_of_yes H (hF s₁ h₁) h₂).then H (by rw [e]; exact H.refl _)

end VerifiableInference.Desc.First.K2

#print axioms VerifiableInference.Desc.First.K2.yes_front
#print axioms VerifiableInference.Desc.First.K2.k2_door
#print axioms VerifiableInference.Desc.First.K2.h2_door
#print axioms VerifiableInference.Desc.First.K2.f1_door
