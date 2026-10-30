-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Tw/K2C/Reply.lean: THE CODE SWITCH's TEXTS AND THE HEARD REPLY: THEOREMS ABOUT THE
TEXT ITSELF, AT EVERY RECORD, ROUNDS, COLUMNS. No Mathlib. No soundness is claimed.
THE HEARD REPLY HAS ONE SEAT IN THE CARRIED RECORD: S.out.reply, LAID AT THE PLACE «H:1» OF THE
ROUND «REPLY». "H.1.quiet" AT «H:2» READS IT AND LEAVES S.out AS IT WAS. (The program hears the
scalar in front of the switch and lays the reply behind it: Iop/Req.lean:330, :342;
Model/StagesLinks.lean:567.)
  switchPlain      the switch's yes at the head's link: «opened» as it was (S.out as it was at all
  its places: Laws.lean: keeps); in spite of its name the statement speaks of no
  plain scalar
  headOpenLays     a yes of "H.1.quiet" ⇒ a reply y lies in the seat (s.out.reply = some y); y lies
  in the base field and below V; S.out behind is S.out in front (in spite of its name the step
  lays no reply)
  headFrontOut · finishFrontOut · finishBehindOut     these three quiet steps: S.out as it was
  headOpenOpens    a yes of "H.1.quiet" ⇒ the head's link was not opened in front, counts as opened
  behind; NO MARK IS LAID · finishFrontMarks · finishBehindMarks · headFrontMarks: S.failed as it
  was: NONE OF THESE TEXTS MARKS THE STATE AND GOES ON (the switch: Laws.lean: keeps)
  placeF1Out       the whole place «F:1» (Finish.lean's finishPlace): S.out as it was
  placeH2Lays      the whole place «H:2» (the switch andThen headOpened): as headOpenLays, of the
  record IN FRONT of the place
V IS A LETTER HERE: that it is the record's vocabulary is said by whoever lays the block.

-/
import Johnson.Top.H0.Tw.K2C.Closed
import Johnson.Top.H0.Tw.K2C.Finish
import Johnson.Top.H0.Tw.K2C.Head

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block roundlessBlock)
open Johnson.Desc.First.Walk (front firstKept)

theorem mark_out (s : S) (n : String) : (s.mark n).out = s.out := by
  unfold S.mark
  split <;> rfl

theorem enterFin_out (s : S) : s.enterFin.out = s.out := by
  unfold S.enterFin
  split
  · rfl
  · exact mark_out s _

theorem enterHead_out (s : S) (tl : HTailF2) : (s.enterHead tl).out = s.out := by
  unfold S.enterHead
  split
  · rfl
  · exact mark_out s _

theorem enterFinQ {s s₁ : S} (h : s.enterFin? = .ok s₁) : s₁ = s.enterFin :=
    ((S.unmarked_ok _ _).1 h).1.symm
theorem enterHeadQ {s s₁ : S} {tl : HTailF2} (h : s.enterHead? tl = .ok s₁) : s₁ = s.enterHead tl :=
    ((S.unmarked_ok _ _).1 h).1.symm
theorem openHeadQ {s s₁ : S} (h : s.openHead? = .ok s₁) : s₁ = s.openHead :=
    ((S.unmarked_ok _ _).1 h).1.symm

theorem firstBehind_plain {S0 x sw plain st f mine} (h : _root_.Tw.K2.firstBehind S0 x sw plain =
    .ok (st, f, mine)) : f.plain = plain := by
  unfold _root_.Tw.K2.firstBehind at h
  simp only at h
  repeat' split at h
  all_goals first | (cases h; done) | skip
  cases h
  rfl

def FinishFrontOut : Prop := ∀ s s', finishFrontQ s = .ok s' → s'.out = s.out
theorem finishFrontOut : FinishFrontOut := fun s s' h => by
  unfold finishFrontQ at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · obtain ⟨s₁, h₁, h⟩ := bindOk h
        cases enterFinQ h₁
        split at h
        · cases h
          exact enterFin_out s
        · cases h
      · cases h
      · cases h

def FinishBehindOut : Prop := ∀ s s', finishBehindQ s = .ok s' → s'.out = s.out
theorem finishBehindOut : FinishBehindOut := fun s s' h => by
  unfold finishBehindQ at h
  split at h
  · cases hb : _root_.Tw.K2.finishBehind _ with
    | error e => rw [hb] at h; cases h
    | ok m => rw [hb] at h; cases h; rfl
  · cases h

def HeadFrontOut : Prop := ∀ tl s s', headFrontQ tl s = .ok s' → s'.out = s.out
theorem headFrontOut : HeadFrontOut := fun tl s s' h => by
  unfold headFrontQ at h
  repeat' split at h
  all_goals first | (cases h; done) | skip
  obtain ⟨x, _, h⟩ := bindOk h
  obtain ⟨s₁, h₁, h⟩ := bindOk h
  cases enterHeadQ h₁
  split at h
  · cases h
    exact enterHead_out s tl
  · cases h

/-- The walk's «front» leaves S.out as it was handed in (since the heard reply has one seat, which
the block of the round «REPLY» alone lays). -/
theorem front_out {X l check out0 L out} (h : front X l check out0 = .ok (L, out)) : out = out0 :=
    by
  unfold front at h
  repeat' split at h
  all_goals first | (cases h; rfl) | cases h

def HeadOpenLays : Prop := ∀ P s s', headOpenQ P s = .ok s' →
  ∃ a y,
      s.here = .head a ∧ s.out.reply = some y ∧ y.c1 = 0 ∧ y.c2 = 0 ∧ y.c0.toNat < P.V ∧ s'.out =
          s.out
theorem headOpenLays : HeadOpenLays := fun P s s' h => by
  unfold headOpenQ at h
  split at h
  · rename_i a ha
    split at h
    · cases h
    · split at h
      · cases h
      · dsimp only at h
        obtain ⟨⟨st, f, mine⟩, hb, h⟩ := bindOk h
        dsimp only at h
        obtain ⟨⟨L, out⟩, hf, h⟩ := bindOk h
        dsimp only at h
        have hpl : (firstKept s.check f mine).frame.plain = s.out.reply.toList :=
            firstBehind_plain hb
        split at h
        · rename_i y hy
          split at h
          · cases h
          · rename_i hY
            split at h
            · cases h
            · split at h
              · cases h
              · obtain ⟨s₁, h₁, h⟩ := bindOk h
                split at h
                · cases h
                  simp at hY
                  exact ⟨a, y, ha, hy, hY.1.1, hY.1.2, hY.2, front_out hf⟩
                · cases h
        · cases h
  · cases h

/-- The switch at the head's link: the head's record behind is the one in front but for «kept» and
«ids»: so «opened» is as it was. -/
def SwitchPlain : Prop :=
    ∀ snd p s rs gs s' a, decideWith snd p s rs gs = .ok s' → s.here = .head a → ∃ b,
        s'.here = .head b ∧ b.opened = a.opened
theorem switchPlain : SwitchPlain := fun snd p s rs gs s' a h ha => by
  unfold decideWith at h
  simp only at h
  split at h
  · cases h
  · split at h
    · rename_i _ hh
      rw [ha] at hh
      cases hh
    · rename_i a' _ hh
      rw [ha] at hh
      cases hh
      obtain ⟨_, _, h⟩ := bindOk h
      obtain ⟨x, _, h⟩ := bindOk h
      obtain ⟨_, _, h⟩ := bindOk h
      cases h
      exact ⟨_, rfl, rfl⟩
    · rename_i _ hh
      rw [ha] at hh
      cases hh
    · cases h

theorem switchBetween {snd p s rs gs s'} (h : decideWith snd p s rs gs = .ok s') (hb : s.here =
    .between) : s'.here = .between := by
  unfold decideWith at h
  simp only at h
  split at h
  · cases h
  · split at h
    · obtain ⟨x, _, h⟩ := bindOk h
      obtain ⟨_, _, h⟩ := bindOk h
      obtain ⟨_, _, h⟩ := bindOk h
      cases h
      exact hb
    · rename_i _ hh
      rw [hb] at hh
      cases hh
    · rename_i _ hh
      rw [hb] at hh
      cases hh
    · cases h

theorem switchFin {snd p s rs gs s' a} (h : decideWith snd p s rs gs = .ok s') (hb : s.here = .fin
    a) : ∃ b, s'.here = .fin b := by
  unfold decideWith at h
  simp only at h
  split at h
  · cases h
  · split at h
    · rename_i _ hh
      rw [hb] at hh
      cases hh
    · rename_i _ hh
      rw [hb] at hh
      cases hh
    · obtain ⟨_, _, h⟩ := bindOk h
      obtain ⟨_, _, h⟩ := bindOk h
      obtain ⟨x, _, h⟩ := bindOk h
      obtain ⟨_, _, h⟩ := bindOk h
      cases h
      exact ⟨_, rfl⟩
    · cases h

/-! ### none of these texts marks the state and goes on: each refuses, under a name, where the
record stands at the wrong place -/

theorem enterFin_failed {s : S} (h : s.atBetween = true) : s.enterFin.failed = s.failed := by
  unfold S.enterFin
  rw [if_pos h]

theorem enterHead_failed {s : S} {tl : HTailF2} (h : s.atBetween = true) : (s.enterHead tl).failed =
    s.failed := by
  unfold S.enterHead
  rw [if_pos h]

def FinishFrontMarks : Prop := ∀ s s', finishFrontQ s = .ok s' → s'.failed = s.failed
theorem finishFrontMarks : FinishFrontMarks := fun s s' h => by
  unfold finishFrontQ at h
  split at h
  · cases h
  · rename_i hB
    split at h
    · cases h
    · split at h
      · obtain ⟨s₁, h₁, h⟩ := bindOk h
        cases enterFinQ h₁
        split at h
        · cases h
          exact enterFin_failed (by simpa using hB)
        · cases h
      · cases h
      · cases h

def FinishBehindMarks : Prop := ∀ s s', finishBehindQ s = .ok s' → s'.failed = s.failed
theorem finishBehindMarks : FinishBehindMarks := fun s s' h => by
  unfold finishBehindQ at h
  split at h
  · cases hb : _root_.Tw.K2.finishBehind _ with
    | error e => rw [hb] at h; cases h
    | ok m => rw [hb] at h; cases h; rfl
  · cases h

def HeadFrontMarks : Prop := ∀ tl s s', headFrontQ tl s = .ok s' → s'.failed = s.failed
theorem headFrontMarks : HeadFrontMarks := fun tl s s' h => by
  unfold headFrontQ at h
  split at h
  · cases h
  · rename_i hB
    split at h
    · cases h
    · obtain ⟨x, _, h⟩ := bindOk h
      obtain ⟨s₁, h₁, h⟩ := bindOk h
      cases enterHeadQ h₁
      split at h
      · cases h
        exact enterHead_failed (by simpa using hB)
      · cases h

/-- A yes of "H.1.quiet": the head's link was not opened in front, counts as opened behind, and no
mark is laid. -/
def HeadOpenOpens : Prop := ∀ P s s', headOpenQ P s = .ok s' →
  (∃ a, s.here = .head a ∧ a.opened = false) ∧ (∃ b,
      s'.here = .head b ∧ b.opened = true) ∧ s'.failed = s.failed
theorem headOpenOpens : HeadOpenOpens := fun P s s' h => by
  unfold headOpenQ at h
  split at h
  · rename_i a ha
    split at h
    · cases h
    · rename_i hO
      have hO' : a.opened = false := by simpa using hO
      have hOpen : s.openHead = { s with here := .head { a with opened := true,
                                                                L :=
                                                                    { a.L with check := s.check } }
                                                                        } := by
        unfold S.openHead
        rw [ha]
        simp [hO']
      split at h
      · cases h
      · dsimp only at h
        obtain ⟨⟨st, f, mine⟩, _, h⟩ := bindOk h
        dsimp only at h
        obtain ⟨⟨L, out⟩, _, h⟩ := bindOk h
        dsimp only at h
        split at h
        · split at h
          · cases h
          · split at h
            · cases h
            · split at h
              · cases h
              · obtain ⟨s₁, h₁, h⟩ := bindOk h
                cases openHeadQ h₁
                rw [hOpen] at h
                dsimp only at h
                cases h
                exact ⟨⟨a, ha, hO'⟩, ⟨_, rfl, rfl⟩, rfl⟩
        · cases h
  · cases h

/-- The whole place «F:1»: S.out as it was. -/
def PlaceF1Out : Prop :=
    ∀ (p : P2) s rs gs s', (finishPlace p : Block S Unit).decide s rs gs = .ok s' → s'.out = s.out
theorem placeF1Out : PlaceF1Out := fun p s rs gs s' h => by
  simp only [finishPlace, Block.andThen, roundlessBlock] at h
  obtain ⟨s₂, h₂, h₃⟩ := bindOk h
  obtain ⟨s₁, h₁, h₂⟩ := bindOk h₂
  rw [finishBehindOut _ _ h₃, (keeps _ _ _ _ _ _ h₂).2.1, finishFrontOut _ _ h₁]

/-- The whole place «H:2» (the switch, then "H.1.quiet"): a reply lies in the seat in front, an
entry of the vocabulary; S.out is as it was. -/
def PlaceH2Lays : Prop := ∀ (p : P2) (n : String) (P : HeadPar) s rs gs s',
  ((codeSwitchKind p : Block S Unit).andThen n (headOpened n p.place P)).decide s rs gs = .ok s' →
    ∃ a y,
        s.here = .head a ∧ s.out.reply = some y ∧ y.c1 = 0 ∧ y.c2 = 0 ∧ y.c0.toNat < P.V ∧ s'.out =
            s.out
theorem placeH2Lays : PlaceH2Lays := fun p n P s rs gs s' h => by
  simp only [Block.andThen, headOpened, roundlessBlock] at h
  obtain ⟨s₁, h₁, h₂⟩ := bindOk h
  obtain ⟨b, y, hb, hy, h1, h2, h3, ho⟩ := headOpenLays _ _ _ h₂
  have hk := (keeps _ _ _ _ _ _ h₁).2.1
  rcases (stands _ _ _ _ _ _ h₁) with ⟨_, hh⟩ | ⟨_, a, hh⟩ | ⟨_, a, hh⟩
  · have := switchBetween h₁ hh
    rw [hb] at this
    cases this
  · exact ⟨a, y, hh, hk ▸ hy, h1, h2, h3, by rw [ho, hk]⟩
  · obtain ⟨c, hc⟩ := switchFin h₁ hh
    rw [hb] at hc
    cases hc

end VerifiableInference.Desc.First.K2

#print axioms VerifiableInference.Desc.First.K2.finishFrontOut
#print axioms VerifiableInference.Desc.First.K2.finishBehindOut
#print axioms VerifiableInference.Desc.First.K2.headFrontOut
#print axioms VerifiableInference.Desc.First.K2.headOpenLays
#print axioms VerifiableInference.Desc.First.K2.switchPlain
#print axioms VerifiableInference.Desc.First.K2.placeF1Out
#print axioms VerifiableInference.Desc.First.K2.placeH2Lays
#print axioms VerifiableInference.Desc.First.K2.headOpenOpens
#print axioms VerifiableInference.Desc.First.K2.finishFrontMarks
#print axioms VerifiableInference.Desc.First.K2.finishBehindMarks
#print axioms VerifiableInference.Desc.First.K2.headFrontMarks
