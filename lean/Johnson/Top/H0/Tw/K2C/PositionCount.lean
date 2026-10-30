-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Tw/K2C/PositionCount.lean: the kind «the code switch»: HOW MANY ROWS A SWITCH LAYS,
AS A NUMBER OF THE TARGET: the switch's kept rows are the target's. NO BLOCK IMPORTS THIS FILE.
Why. The table of joints' promise reads where in a group's list of open rows each class of rows
stands and how many there are. For the class «position» (the generators' rows) the count is: draws
× (1 + the kept members' main rows + 2). Here: that at a yes of the switch the middle summand is
the sum of the main rows of THE TARGET's kept shapes (the target is the plan's group's), and that
the rows which a yes lays end in just so many generators' rows.
  targetRows T      the sum of the main rows of the target's kept shapes
  KeptPos T         THE ONE PREMISE (K2Hands/AtYes.lean's own): on the target alone, which is
                    public: each shape that takes a kept member has a main row. With the public
                    test's yes it gives KeptOld (keptOld_of, there): each kept member of the
                    carried rows is a message of the statement in front. Without it the frame
                    could read, at a kept member's number, the shape of a message that the switch
                    itself sends.
  frame_kept_rows   the frame at a front (frameAt, K2Hands/FrameOfFront.lean), the public test on
                    the target, KeptOld: the frame's kept places have, place by place, the main
                    rows of the target's kept shapes
  frame_keptRows    so keptRows W = targetRows x.T
  gens_count        each draw's list of generators' rows has 1 + targetRows x.T + 2 members
  rows_split        what the rows' maker returns is: the carried claim, the kept members' stored
                    samples, and one such list a draw, REPEATS COUNTED
  yes_position_rows AT A YES (AtYes, K2Hears/Whole.lean): the group's list behind is the list in
  front, then the carried claim, then the samples, then r₂.drawn.poss.length × (1 + targetRows x.T +
  2) generators' rows
CALLED, NOT TYPED: gens_length (K2Hands/GenJoin.lean) · frame_of_front · KeptOld | KeptPos |
keptOld_of (K2Hands/AtYes.lean) · targetOk_means | targetOk_eq.
LIMITS. That the round's draws are as many as the plan's entry says (p.positions) is the step's
test on the view, not the decision's: not here. That x.T is the plan's group's target: frontAt's
own text. KeptPos is a premise: a closed fact at a written target. No soundness is claimed.

-/
import Johnson.Top.H0.K2Hands.GenJoin
import Johnson.Top.H0.K2Hands.FrameOfFront
import Johnson.Top.H0.K2Hands.AtYes
import Johnson.Top.H0.Tw.K2.TargetMeans

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First.K2Hands (keptRows gens_length)
open _root_.Tw.K2 (switchNotices)

/-- The sum of the main rows of the target's kept shapes. -/
def targetRows (T : SwitchTarget) : Nat := (T.kept.toList.map (·.shape.mainRows)).sum

theorem skel_old (x : _root_.Tw.K2.Front) {o : Nat} (h : o < x.st.oracles.size) :
    ((skelOf x).oracles.getD o default).shape = (x.st.oracles.getD o default).shape := by
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?]
  unfold skelOf
  rw [OnBytes.Slice.stSent_old _ _ o h]

theorem frame_kept_rows {x : _root_.Tw.K2.Front} {W : SwitchFrame} (hW : frameAt x = some W)
    (hT : switchTargetCheck x.st x.f.rows x.T = true) (hK : KeptOld x.st x.f.rows) :
    W.kept.map (·.rows) = x.T.kept.toList.map (·.shape.mainRows) := by
  have F := (_root_.Tw.K2.targetOk_means x.st x.f.rows x.T).1
    ((_root_.Tw.K2.targetOk_eq x.st x.f.rows x.T).trans hT)
  unfold frameAt switchFrame at hW
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at hW
  obtain ⟨_, _, _, _, _, _, _, _, rfl⟩ := hW
  simp only [List.map_map]
  refine List.ext_getElem (by simp [F.keptCount]) fun i h1 h2 => ?_
  have hi : i < (switchKept x.f.rows).size := by simpa using h1
  have hi' : i < x.T.kept.size := by rw [F.keptCount]; exact hi
  simp only [List.getElem_map, List.getElem_range, Function.comp_apply, Array.getElem_toList]
  have hg : (switchKept x.f.rows).getD i noId = (switchKept x.f.rows)[i] := by
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi]
    rfl
  rw [hg, skel_old x (hK _ (by simp))]
  have hm : ((switchKept x.f.rows)[i], x.T.kept[i]) ∈ (switchKept x.f.rows).zip x.T.kept := by
    rw [Array.mem_iff_getElem]
    exact ⟨i, by simp [hi, hi'], by simp⟩
  have e := (F.keptShapes _ hm).rows
  exact e.symm

theorem frame_keptRows {x : _root_.Tw.K2.Front} {W : SwitchFrame} (hW : frameAt x = some W)
    (hT : switchTargetCheck x.st x.f.rows x.T = true) (hK : KeptOld x.st x.f.rows) :
    keptRows W = targetRows x.T := by
  unfold keptRows targetRows
  rw [frame_kept_rows hW hT hK]

theorem gens_count {x : _root_.Tw.K2.Front} {W : SwitchFrame} (hW : frameAt x = some W)
    (hT : switchTargetCheck x.st x.f.rows x.T = true) (hK : KeptOld x.st x.f.rows) (q : Nat) (sy :
        Nat → E) :
    (switchGenerators W x.f.rows q sy).length = 1 + targetRows x.T + 2 := by
  have F := (_root_.Tw.K2.targetOk_means x.st x.f.rows x.T).1
    ((_root_.Tw.K2.targetOk_eq x.st x.f.rows x.T).trans hT)
  rw [gens_length, frame_keptRows hW hT hK, F.masks]

/-- A list of lists of one length, laid flat. -/
theorem flatten_len {α : Type} (n : Nat) : ∀ L : List (List α), (∀ l ∈ L, l.length = n) →
    L.flatten.length = L.length * n
  | [], _ => by simp
  | l :: L, h => by
    rw [List.flatten_cons, List.length_append, h l (by simp),
      flatten_len n L fun m hm => h m (by simp [hm]), List.length_cons]
    ring

/-- What an Option's mapM returns has as many members, each a value. -/
theorem mapM_len {α β : Type} (f : α → Option β) : ∀ (l : List α) (r : List β),
    l.mapM f = some r → r.length = l.length ∧ ∀ b ∈ r, ∃ a ∈ l, f a = some b
  | [], r, h => by
    have : r = [] := by simpa using h.symm
    subst this
    exact ⟨rfl, fun _ hb => nomatch hb⟩
  | a :: l, r, h => by
    rw [List.mapM_cons] at h
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨b, hb, r', hr, rfl⟩ := h
    obtain ⟨k1, k2⟩ := mapM_len f l r' hr
    refine ⟨by simp [k1], fun c hc => ?_⟩
    rcases List.mem_cons.1 hc with rfl | hc
    · exact ⟨a, by simp, hb⟩
    · obtain ⟨a', ha', e⟩ := k2 c hc
      exact ⟨a', by simp [ha'], e⟩

theorem rows_split {S : Statement} {old : SingleRows} {T : SwitchTarget} {g : Nat}
    {anew : Array Nat} {pos : Positions} {y : Array E} {rows : List OnBytes.Row}
    (h : switchRows S old T g anew pos y = some rows) :
    ∃ (W : SwitchFrame) (carried : OnBytes.Row) (samples : List OnBytes.Row)
      (gens : List (List OnBytes.Row)), switchFrame S old T g anew = some W ∧
      rows = carried :: samples ++ gens.flatten ∧ gens.length = pos.draws.size ∧
      ∀ l ∈ gens, ∃ q sy, l = switchGenerators W old q sy := by
  unfold switchRows at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
  obtain ⟨_, _, W, hW, carried, _, samples, _, gens, hg, rfl⟩ := h
  obtain ⟨k1, k2⟩ := mapM_len _ _ _ hg
  refine ⟨W, carried, samples, gens, hW, rfl, by simpa using k1, fun l hl => ?_⟩
  obtain ⟨q, _, e⟩ := k2 l hl
  simp only [Option.bind_eq_some_iff, Option.some.injEq] at e
  obtain ⟨i, _, rfl⟩ := e
  exact ⟨q, _, rfl⟩

/-- **At a yes: how many rows of the class «position» the switch lays.** -/
theorem yes_position_rows {p : P2} {s s' : S} {r₁ r₂ : Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} {x : _root_.Tw.K2.Front} {y : _root_.Tw.K2.Sent}
    {S3 : Statement} {Y : Array E} {rows : List OnBytes.Row} {G : Group} {c : Code}
    (A : AtYes p s s' r₁ r₂ gs x y S3 Y rows G c) (hp : KeptPos x.T) :
    ∃ (carried : OnBytes.Row) (samples gens : List OnBytes.Row),
      (s'.st.groups[x.f.group]?).map (·.rows) =
        some (G.rows ++ (carried :: samples ++ gens).toArray) ∧
      (x.st.groups[x.f.group]?).map (·.rows) = some G.rows ∧
      gens.length = r₂.drawn.poss.length * (1 + targetRows x.T + 2) := by
  obtain ⟨W, carried, samples, gens, hW, rfl, hl, hg⟩ := rows_split A.made
  rw [frame_of_front A] at hW
  refine ⟨carried, samples, gens.flatten, A.kept, A.before, ?_⟩
  rw [flatten_len (1 + targetRows x.T + 2) gens fun l hm => by
    obtain ⟨q, sy, rfl⟩ := hg l hm
    exact gens_count hW A.check (keptOld_of A.check hp) q sy, hl]
  simp [Positions.ofDraws]

end VerifiableInference.Desc.First.K2

#print axioms VerifiableInference.Desc.First.K2.frame_kept_rows
#print axioms VerifiableInference.Desc.First.K2.gens_count
#print axioms VerifiableInference.Desc.First.K2.rows_split
#print axioms VerifiableInference.Desc.First.K2.yes_position_rows
