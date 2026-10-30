-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Meaning/K2Share/RecKept.lean: the code switch: K2's OWN SHARE OF THE INVARIANT: a yes
of the switch's text keeps the record's codes, and its frame's shape and groups (RecPub,
K2Share/FrontPlan.lean); and it says how the list of the oracle messages' shapes grows.


  switch_tables: behind a yes of switchE with sendByL8 at a front x: the statement has x.st's codes,
    x.st's messages' shapes at the old numbers, and the announcements' shapes behind them (the rows
    laid last: by K2Hears/Whole.lean's same_added).
  behind_frame: firstBehind keeps the front's frame's shape and groups, and the tables.
  recPub_link, recPub_head, recPub_finish, recPub_kept: RecPub cs sh s and a yes of decideWith
    sendByL8 p s rs gs = .ok s' give RecPub cs sh s'.
LIMITS. Of the switch's own text alone: what the other kinds' blocks do to the record is theirs. At
the head's and the finish's places the frame s.check.frame is not touched; the frames a.fr in the
record's field "here" are not spoken of. No soundness is claimed.
-/
import Johnson.Goal.Meaning.K2Share.FrontPlan
import Johnson.Top.H0.K2Hears.BehindSame
import Johnson.Top.H0.K2Hears.Whole

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2
open OnBytes OnBytes.Model
open OnBytes.Params (ReqShape)
open _root_.Tw.K2 (switchNotices firstFront firstBehind sendByL8 switchE switchBehind addRowsG dOf
  SwOut)

/-- **The tables behind a yes of the switch.** -/
theorem switch_tables {p : P2} {s9 : _root_.Tw.K2.S9} {x : _root_.Tw.K2.Front} {r₁ r₂ : Fmt.RoundView}
    {cols w roots}
    (h : switchE switchBehind (par9 p) sendByL8 s9 x r₁ r₂ cols = .ok (w, roots)) :
    SameShapes (skelOf x) w.st ∧
      w.st.oracles.size = x.st.oracles.size + (switchNotices x.T x.others).size := by
  obtain ⟨y, S3, Y, rows, R, hS⟩ := rows_of_switch_same h
  have K := sent_ok R.sent
  have T := same_added R.laid
  refine ⟨⟨T.codes.trans (hS.codes.trans K.codes), fun o => ?_⟩, ?_⟩
  · rw [T.shape o, hS.shape o]
    by_cases ho : o < x.st.oracles.size
    · rw [K.old o ho]
      unfold skelOf
      rw [OnBytes.Slice.stSent_old _ _ o ho]
    · obtain ⟨i, rfl⟩ : ∃ i, o = x.st.oracles.size + i := ⟨o - x.st.oracles.size, by omega⟩
      rw [K.shape i]
      unfold skelOf
      rw [OnBytes.Slice.stSent_new, Option.map_map]
      rfl
  · rw [T.size, hS.size, K.size]

/-- firstBehind keeps the frame's shape and groups, and the tables. -/
theorem behind_frame {S S' : Statement} {x : _root_.Tw.K2.Front} {sw : Switched} {plain : List E}
    {f : ReqFrame} {mine : Array Nat} (h : firstBehind S x sw plain = .ok (S', f, mine)) :
    f.shape = x.f.shape ∧ f.groups = x.f.groups ∧ SameTables S S' := by
  unfold firstBehind at h
  dsimp only at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · cases h
        · rename_i S1 hj
          have hs := same_joins (α := Params.ReqMessage × Nat) _ (fun y => y.2)
            (fun y => decide (0 < y.1.life)) _ S S1 hj
          cases h
          exact ⟨rfl, rfl, hs⟩

theorem front_frame {S0 : Statement} {f : ReqFrame} {x : _root_.Tw.K2.Front}
    (h : firstFront S0 f = .ok x) : x.f.shape = f.shape ∧ x.f.groups = f.groups := by
  unfold firstFront at h
  repeat' split at h
  all_goals first | (cases h; done) | skip
  cases h
  exact ⟨rfl, rfl⟩

/-- firstBehind leaves the frame's carried rows and its link. -/
theorem behind_carried {S S' : Statement} {x : _root_.Tw.K2.Front} {sw : Switched} {plain : List E}
    {f : ReqFrame} {mine : Array Nat} (h : firstBehind S x sw plain = .ok (S', f, mine)) :
    f.rows = x.f.rows ∧ f.link = x.f.link := by
  unfold firstBehind at h
  dsimp only at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · cases h
        · cases h
          exact ⟨rfl, rfl⟩

/-- So does firstFront. -/
theorem front_carried {S0 : Statement} {f : ReqFrame} {x : _root_.Tw.K2.Front}
    (h : firstFront S0 f = .ok x) : x.f.rows = f.rows ∧ x.f.link = f.link := by
  unfold firstFront at h
  repeat' split at h
  all_goals first | (cases h; done) | skip
  cases h
  exact ⟨rfl, rfl⟩

/-- **At a link's place.** -/
theorem recPub_link {cs : Codes} {sh : ReqShape} {p : P2} {s s' : S} {rs gs}
    (R : RecPub cs sh s) (hp : p.stands = .link) (h : decideWith sendByL8 p s rs gs = .ok s') :
    RecPub cs sh s' := by
  obtain ⟨r₁, r₂, x, w, roots, S', f, mine, -, L⟩ := link_inv hp h
  obtain ⟨f1, f2, f3⟩ := behind_frame L.hBehind
  obtain ⟨g1, g2⟩ := front_frame L.hFront
  have c1 := (switch_tables L.hSwitch).1.codes
  have c2 := (link_front L.hFront).2.1
  rw [L.hOut]
  exact ⟨(f3.codes.trans c1).trans (c2.trans R.codes), (f1.trans g1).trans R.shape,
    (f2.trans g2).trans R.groups, R.ok⟩

/-- **At the head's place.** -/
theorem recPub_head {cs : Codes} {sh : ReqShape} {p : P2} {s s' : S} {rs gs}
    (R : RecPub cs sh s) (hp : p.stands = .head) (h : decideWith sendByL8 p s rs gs = .ok s') :
    RecPub cs sh s' := by
  obtain ⟨r₁, r₂, a, G, w, roots, -, H⟩ := head_inv hp h
  have c1 := (switch_tables H.hSwitch).1.codes
  rw [H.hOut]
  exact ⟨c1.trans R.codes, R.shape, R.groups, R.ok⟩

/-- **At the finish.** -/
theorem recPub_finish {cs : Codes} {sh : ReqShape} {p : P2} {s s' : S} {rs gs}
    (R : RecPub cs sh s) (hp : p.stands = .finish) (h : decideWith sendByL8 p s rs gs = .ok s') :
    RecPub cs sh s' := by
  obtain ⟨r₁, r₂, a, G, w, roots, -, H⟩ := finish_inv hp h
  have c1 := (switch_tables H.hSwitch).1.codes
  rw [H.hOut]
  exact ⟨c1.trans R.codes, R.shape, R.groups, R.ok⟩

/-- **A YES OF THE SWITCH KEEPS THE RECORD's CODES, SHAPE AND GROUPS.** -/
theorem recPub_kept {cs : Codes} {sh : ReqShape} {p : P2} {s s' : S} {rs gs}
    (R : RecPub cs sh s) (h : decideWith sendByL8 p s rs gs = .ok s') : RecPub cs sh s' := by
  cases hp : p.stands with
  | link => exact recPub_link R hp h
  | head => exact recPub_head R hp h
  | finish => exact recPub_finish R hp h

end VerifiableInference.Desc.First.K2

#print axioms VerifiableInference.Desc.First.K2.switch_tables
#print axioms VerifiableInference.Desc.First.K2.recPub_kept
