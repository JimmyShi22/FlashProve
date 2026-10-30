-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Meaning/K2Share/FrontPlan.lean: the code switch: FIVE CLAUSES ON THE FRONT (frameIs,
codes, keptPos, first, next) AND z32, FROM ONE RECORD ON THE PUBLIC PART OF THE RECORD IN FRONT.



  RecPub cs sh s: the record s holds the plan's codes cs, and its frame the plan's shape sh, with
    groups := reqGroups sh, as ReqFrame.start lays them; reqOk cs sh, which ReqFrame.start tests.
  link_front: what the front of a link's switch is made of (firstFront's text): its target is the
    target of the frame's group at the frame's link; its codes, oracle messages and carried rows are
    the record's.
  codes_link, keptPos_link: so two clauses at a link's place, from RecPub.
  FrontPub sk old₀ T₀ others₀ fx: the front's target and announcements are T₀ and others₀; its
    statement has the shapes of a skeleton sk, number by number, and as many messages; its carried
    rows have old₀'s five public things (Meaning.K2.SameRows).
  frameOf sk old₀ T₀ others₀: THE PUBLIC FRAME: a function of these four.
  frameIs_of: FrontPub gives K2.frameAt fx = frameOf sk old₀ T₀ others₀.
  z32_of: where that frame is W₀ and sk's codes are CodesN: W₀.zk.logN ≤ 32.
  first_next_of: first and next, for a list l whose shapes begin with T₀'s and its kept members'.
LIMITS. RecPub and FrontPub are PREMISES: that the record in front of a place has them is not shown:
it is an invariant of the blocks in front. The head's and the finish's fronts: FrontPub serves them
as it stands; the like of link_front is not typed. No soundness is claimed.
-/
import Johnson.Top.H0.K2Hands.FrameOfFront
import Johnson.Top.H0.K2Hands.AtYes
import Johnson.Top.H0.K2Hears.Long
import Johnson.Goal.Meaning.CodesShort
import Johnson.Goal.Meaning.KeptRowsPos
import Johnson.Goal.Meaning.FrameRows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2
open OnBytes OnBytes.Model
open OnBytes.Params (ReqShape)
open _root_.Tw.K2 (switchNotices firstFront newGroupG)

/-- The record holds the plan's codes, shape and groups. -/
structure RecPub (cs : Codes) (sh : ReqShape) (s : S) : Prop where
  codes : s.st.codes = cs
  shape : s.check.frame.shape = sh
  groups : s.check.frame.groups = reqGroups sh
  ok : reqOk cs sh = true

/-- A new group leaves the codes and the oracle messages. -/
theorem newGroupG_tables {S S' : Statement} {c z g : Nat} (h : newGroupG S c z = .ok (S', g)) :
    S'.codes = S.codes ∧ S'.oracles = S.oracles := by
  unfold newGroupG at h
  split at h
  · rename_i g' d hd
    unfold VerifiableInference.Desc.Ground.newGroupP at hd
    split at hd
    · cases hd
      cases h
      exact ⟨rfl, rfl⟩
    · cases hd
  · cases h

/-- What the front of a link's switch is made of. -/
theorem link_front {S0 : Statement} {f : ReqFrame} {x : _root_.Tw.K2.Front}
    (h : firstFront S0 f = .ok x) :
    (∃ G, f.groups[f.link]? = some G ∧ x.T = G.target) ∧ x.st.codes = S0.codes ∧
      x.st.oracles = S0.oracles ∧ x.f.rows = f.rows := by
  unfold firstFront at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · rename_i L G hL hG
        dsimp only at h
        split at h
        · cases h
        · rename_i S' g hn
          cases h
          obtain ⟨a, b⟩ := newGroupG_tables hn
          exact ⟨⟨G, hG, rfl⟩, a, b, rfl⟩
      · cases h
      · cases h

theorem front_of_link {p : P2} {s : S} {fx : _root_.Tw.K2.Front} (hp : p.stands = .link)
    (h : frontAt p s = some fx) : firstFront s.st s.check.frame = .ok fx := by
  unfold frontAt at h
  rw [hp] at h
  cases e : firstFront s.st s.check.frame with
  | error m =>
    rw [e] at h
    cases h
  | ok y =>
    rw [e] at h
    exact congrArg Except.ok (Option.some.inj h)

/-- **codes, at a link's place.** -/
theorem codes_link {cs : Codes} {sh : ReqShape} {p : P2} {s : S} {fx : _root_.Tw.K2.Front}
    (R : RecPub cs sh s) (hp : p.stands = .link) (h : frontAt p s = some fx) :
    fx.st.codes = cs :=
  (link_front (front_of_link hp h)).2.1.trans R.codes

/-- **keptPos, at a link's place.** -/
theorem keptPos_link {cs : Codes} {sh : ReqShape} {p : P2} {s : S} {fx : _root_.Tw.K2.Front}
    (R : RecPub cs sh s) (hp : p.stands = .link) (h : frontAt p s = some fx) : KeptPos fx.T := by
  obtain ⟨⟨G, hG, eT⟩, -⟩ := link_front (front_of_link hp h)
  rw [R.groups] at hG
  rw [eT]
  exact Meaning.K2.kept_pos_ok R.ok hG

/-! ## The frame -/

/-- The public part of a front. -/
structure FrontPub (sk : Statement) (old₀ : SingleRows) (T₀ : SwitchTarget)
    (others₀ : Array OracleNotice) (fx : _root_.Tw.K2.Front) : Prop where
  T : fx.T = T₀
  others : fx.others = others₀
  shapes : SameShapes sk fx.st
  size : fx.st.oracles.size = sk.oracles.size
  rows : Meaning.K2.SameRows old₀ fx.f.rows

/-- **The public frame.** -/
def frameOf (sk : Statement) (old₀ : SingleRows) (T₀ : SwitchTarget)
    (others₀ : Array OracleNotice) : Option SwitchFrame :=
  frameAt ⟨sk, { shape := default, groups := #[], rows := old₀ }, [], others₀, T₀, 0⟩

/-- Received notices keep SameShapes, at statements with as many messages. -/
theorem sameShapes_sent {S S' : Statement} (h : SameShapes S S')
    (hn : S'.oracles.size = S.oracles.size) (N : Array OracleNotice) :
    SameShapes (OnBytes.Slice.stSent S N) (OnBytes.Slice.stSent S' N) := by
  refine ⟨h.codes, fun o => ?_⟩
  by_cases ho : o < S.oracles.size
  · rw [OnBytes.Slice.stSent_old _ _ o ho, OnBytes.Slice.stSent_old _ _ o (by rw [hn]; exact ho)]
    exact h.shape o
  · obtain ⟨i, rfl⟩ : ∃ i, o = S.oracles.size + i := ⟨o - S.oracles.size, by omega⟩
    rw [OnBytes.Slice.stSent_new]
    rw [← hn, OnBytes.Slice.stSent_new]

/-- **frameIs.** -/
theorem frameIs_of {sk : Statement} {old₀ : SingleRows} {T₀ : SwitchTarget}
    {others₀ : Array OracleNotice} {fx : _root_.Tw.K2.Front} (P : FrontPub sk old₀ T₀ others₀ fx) :
    frameAt fx = frameOf sk old₀ T₀ others₀ := by
  unfold frameOf frameAt idsOf skelOf
  dsimp only
  rw [P.T, P.others, P.size, Meaning.K2.frame_rows P.rows]
  exact frame_congr (sameShapes_sent P.shapes P.size _) _ _ _ _

/-- **z32.** -/
theorem z32_of {sk : Statement} {old₀ : SingleRows} {T₀ : SwitchTarget}
    {others₀ : Array OracleNotice} {W₀ : SwitchFrame} (h : frameOf sk old₀ T₀ others₀ = some W₀)
    (H : Meaning.K2.CodesN sk.codes) : W₀.zk.logN ≤ 32 :=
  (Meaning.K2.frame_n (S := skelOf ⟨sk, { shape := default, groups := #[], rows := old₀ }, [],
    others₀, T₀, 0⟩) h H).1

/-- **first and next.** -/
theorem first_next_of {sk : Statement} {old₀ : SingleRows} {T₀ : SwitchTarget}
    {others₀ : Array OracleNotice} {fx : _root_.Tw.K2.Front} (P : FrontPub sk old₀ T₀ others₀ fx)
    {l : List (OracleShape × ℕ)} {rest : List OracleShape}
    (hl : l.map (·.1) = T₀.shape :: (T₀.kept.toList.map (·.shape) ++ rest)) :
    (∃ g0 : 0 < l.length, (l.get ⟨0, g0⟩).1 = fx.T.shape) ∧
      ∀ i (hi : i < fx.T.kept.size), ∃ h : 1 + i < l.length,
        (l.get ⟨1 + i, h⟩).1 = fx.T.kept[i].shape := by
  rw [P.T]
  exact Meaning.K2.heads_of hl

end VerifiableInference.Desc.First.K2

#print axioms VerifiableInference.Desc.First.K2.codes_link
#print axioms VerifiableInference.Desc.First.K2.keptPos_link
#print axioms VerifiableInference.Desc.First.K2.frameIs_of
#print axioms VerifiableInference.Desc.First.K2.z32_of
#print axioms VerifiableInference.Desc.First.K2.first_next_of
