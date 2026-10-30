-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Coin/ShapesAppend.lean: **WHAT THE PROXIMITY TEST's OWN SWITCHES APPEND TO THE
STATEMENT's LIST OF MESSAGES' SHAPES** (first arm: the first fold's mask has come from outside): a
yes of the test's decision leaves the shapes that the statement's oracle messages had, in their
order, and behind them just the shapes of the notices of the test's sendings (`sendsFrom`,
BookAppends.lean), one sending for each switch, in turn. Statements and proofs. For the item
"K12.msgShapes" at the test's own block. It goes along the stages as BookAppends.lean does, over the
kind's files' closed forms; a switch's share is its `Did.shape_at`.
  (`shapesIn st`: the shapes of the statement's oracle messages, in their order:
    Johnson/Desc/K12/Door/MsgShapesRide.lean.)
  `shapesIn_of_map`: two statements whose messages have one shape, number by number, have one list.
  `noticesOf sends`: the shapes of the sendings' notices, in turn.
  `fold_shapes`, `switch_shapes`, `stages_shapes`, `k12_shapes`: part by part; along the stages; the
    whole test. `atFinish_shapes`: at the first chain's finish.
Limits. Nothing on soundness. The own mask's arm is not here.

-/
import Johnson.Desc.K12.Coin.BookAppends
import Johnson.Desc.K12.Door.MsgShapesRide

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K12.Coin
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Sound
open H2K.JointK H2K.Sw H2K.Out
open VerifiableInference.Desc.K12.Door (shapesIn)

/-- One shape, number by number: one list. -/
theorem shapesIn_of_map (S S' : Statement)
    (h : ∀ i : ℕ, (S'.oracles[i]?).map (·.shape) = (S.oracles[i]?).map (·.shape)) :
    shapesIn S' = shapesIn S := by
  apply List.ext_getElem?
  intro i
  unfold shapesIn
  rw [List.getElem?_map, List.getElem?_map, Array.getElem?_toList, Array.getElem?_toList]
  exact h i

/-- The shapes of the sendings' notices, in turn. -/
def noticesOf (sends : List (Array OracleNotice)) : List OracleShape :=
  sends.flatMap fun s => s.toList.map (·.shape)

theorem shapesIn_sent (S : Statement) (sent : Array OracleNotice) :
    shapesIn (stSent S sent) = shapesIn S ++ sent.toList.map (·.shape) := by
  unfold shapesIn stSent
  simp [Function.comp_def]

/-- The fold's part, where the mask has come: no shape turns, none comes. -/
theorem fold_shapes (p : P12) (j : ℕ) (cur : Fmt.M1.Stage) (cut : List Fmt.DeclaredRound) (t t1 : T12)
    (rs : List Fmt.RoundView) (gs : Gs) (hm : t.mask.isSome = true)
    (h : (foldJ p j cur cut).decide t rs gs = .ok t1) : shapesIn t1.st = shapesIn t.st := by
  obtain ⟨row, L, c, n, id, d1, d', rows, _, _, hcase, hsp, rfl⟩ :=
    foldJ_form p j cur cut t t1 rs gs h
  have hd' := spendP_form hsp
  subst hd'
  rcases hcase with ⟨_, rfl⟩ | ⟨hn, _⟩
  · refine shapesIn_of_map _ _ fun i => ?_
    show ((t.st.oracles.modify id fun x => { x with spentAsMask := true })[i]?).map (·.shape) = _
    rw [Array.getElem?_modify]
    split
    · cases t.st.oracles[i]? <;> rfl
    · rfl
  · rw [hn] at hm
    cases hm

/-- The switch's part and the batching behind it append the sending's notices' shapes. -/
theorem switch_shapes (p : P12) (he : p.early = true) (ha : p.answers = 1) (j : ℕ)
    (cur nxt : Fmt.M1.Stage) (last : Bool) (cut : List Fmt.DeclaredRound) (t1 t2 t3 : T12)
    (rs : List Fmt.RoundView) (gs : Gs) (hlen : rs.length ≤ 2)
    (h1 : (switchJ p j cur nxt last cut).decide t1 rs gs = .ok t2)
    (h2 : (behindJ p (j + 1) nxt cut).decide t2 [] [] = .ok t3) :
    shapesIn t3.st = shapesIn t1.st ++ (sendAt p j nxt last).toList.map (·.shape) := by
  have h1' := h1
  simp only [switchJ] at h1'
  split at h1'
  · rename_i rows gp nx e1 e2
    obtain ⟨⟨⟨out0, theta0⟩, s'⟩, hx, _⟩ := H2K.FoldLaw.bind_ok h1'
    obtain ⟨r1, r2, rest, hr⟩ := switchE_two hx
    have hr' : rs = r1 :: r2 :: rest := hr
    have hrest : rest = [] := by
      rw [hr'] at hlen
      simp only [List.length_cons] at hlen
      exact List.eq_nil_of_length_eq_zero (by omega)
    subst hrest
    subst hr'
    obtain ⟨out, row, L, th, D, _, _, hd, _, _⟩ :=
      switchUnfolds p j cur nxt last cut t1 t2 t3 r1 r2 gs rows gp nx he ha e1 e2 h1 h2
    have es : sendAt p j nxt last =
        Slice.sentOf (switchTargetStage nx.code nx.maskCode nx.k nx.h 1) (othersOf last nx) := by
      unfold sendAt
      rw [e2]
    rw [es, ← shapesIn_sent]
    exact shapesIn_of_map _ _ hd.shape_at
  · cases h1'

/-- **Along the stages.** -/
theorem stages_shapes (p : P12) (he : p.early = true) (ha : p.answers = 1) :
    ∀ (rest : List Fmt.M1.Stage) (j : ℕ) (cur : Fmt.M1.Stage) (l : K12.Laid) (t tE : T12)
      (rs : List Fmt.RoundView) (gs : Gs), t.mask.isSome = true →
      (stagesFrom guardedProximityTestParts p j cur rest l : Blk').decide t rs gs = .ok tE →
      shapesIn tE.st = shapesIn t.st ++ noticesOf (sendsFrom p j rest)
  | [], j, cur, l, t, tE, rs, gs, _, h => by
    rw [stagesFrom_last] at h
    have h' := (ranged_ok _ _ _ _ _ _ h).1
    obtain ⟨star, a, _, _, rfl⟩ := baseJ5_form p j cur _ t tE rs gs h'
    show shapesIn _ = shapesIn t.st ++ []
    rw [List.append_nil]
    refine shapesIn_of_map _ _ fun i => ?_
    show ((t.st.oracles.modify star fun x => { x with spentAsMask := true })[i]?).map (·.shape) = _
    rw [Array.getElem?_modify]
    split
    · cases t.st.oracles[i]? <;> rfl
    · rfl
  | nxt :: rest, j, cur, l, t, tE, rs, gs, hm, h => by
    obtain ⟨t1, t2, t3, f1, f2, f3, f4, f5⟩ :=
      (stagesFrom_ok guardedProximityTestParts p j cur nxt rest l t tE rs gs).1 h
    have hX := like_P5 p
    have hlen : ((rs.drop (foldAt guardedProximityTestParts p j cur l : Blk').rounds.length).take
        (switchAt guardedProximityTestParts p j cur nxt rest.isEmpty l : Blk').rounds.length).length ≤ 2 := by
      refine (List.length_take_le _ _).trans ?_
      show (((l.drop (1 + cur.k)).take 2).map (·.1)).length ≤ 2
      rw [List.length_map]
      exact List.length_take_le _ _
    have e1 := fold_shapes p j cur _ t t1 _ _ hm (hX.fold _ _ _ _ _ _ _ f1)
    have e2 := switch_shapes p he ha j cur nxt rest.isEmpty _ t1 t2 t3 _ _ hlen
      (hX.switch _ _ _ _ _ _ _ _ _ f2) (hX.behind _ _ _ _ _ f3)
    have hm3 : t3.mask.isSome = true := by
      rw [he] at f4
      simpa using f4
    have e3 := stages_shapes p he ha rest (j + 1) nxt _ t3 tE _ _ hm3 f5
    rw [e3, e2, e1, List.append_assoc]
    rfl

/-- **The whole test**: from a record at which the first fold's mask has come. -/
theorem k12_shapes (p : P12) (he : p.early = true) (ha : p.answers = 1) (t0 tE : T12)
    (rs : List Fmt.RoundView) (gs : Gs) (hm : t0.mask.isSome = true)
    (h : (proximityTestKind guardedProximityTestParts p : Blk').decide t0 rs gs = .ok tE) :
    ∃ first rest, p.nums.stages = first :: rest ∧
      shapesIn tE.st = shapesIn t0.st ++ noticesOf (sendsFrom p 0 rest) := by
  have hX := like_P5 p
  obtain ⟨first, rest, ds, tF, t1, hs, _, hfr, hbat, _, hst⟩ := k12_ok guardedProximityTestParts p t0 tE rs gs h
  have hF : tF = t0 := by
    have hfr' := hX.front _ _ hfr
    unfold frontJ at hfr'
    dsimp only at hfr'
    split at hfr'
    · obtain ⟨_, _, hfr'⟩ := H2K.FoldLaw.bind_ok hfr'
      cases hfr'
      rfl
    · cases hfr'
  subst hF
  obtain ⟨e, r, row, L, S', _, hb, rfl⟩ := batJ_ok p he _ _ _ _ _ (hX.bat _ _ _ _ _ hbat)
  obtain ⟨G, _, rfl⟩ := bat_st _ _ _ _ _ _ _ hb
  have a := stages_shapes p he ha rest 0 first _
    { tF with st := begun tF.st tF.g G, pass := .claim row L } tE _ _ hm hst
  have hc : shapesIn (begun tF.st tF.g G) = shapesIn tF.st :=
    shapesIn_of_map _ _ fun i => closeLedgers_shape _ _ i
  dsimp only at a
  rw [hc] at a
  exact ⟨first, rest, hs, a⟩

/-- **At the first chain's finish.** -/
theorem atFinish_shapes (p : P12) (he : p.early = true) (ha : p.answers = 1) (s s' : First.S)
    (rs : List Fmt.RoundView) (gs : Gs) (h : (atFinish p).decide s rs gs = .ok s')
    (hm : ∀ t, enterFinish s = .ok t → t.mask.isSome = true) :
    ∃ first rest, p.nums.stages = first :: rest ∧
      shapesIn s'.st = shapesIn s.st ++ noticesOf (sendsFrom p 0 rest) := by
  have h' : ((enterFinish s).bind fun t =>
      ((proximityTestKind guardedProximityTestParts p : Blk').decide t rs gs).bind (leaveFinish s)) = .ok s' := h
  obtain ⟨t, ht, h1⟩ := H2K.FoldLaw.bind_ok h'
  obtain ⟨tE, hk, h2⟩ := H2K.FoldLaw.bind_ok h1
  have e2 : s' = { s with st := tE.st, book := tE.book, roots := tE.roots } :=
    (Except.ok.inj h2).symm
  have et : t.st = s.st := by
    unfold enterFinish at ht
    split at ht
    · obtain ⟨_, _, ht⟩ := H2K.FoldLaw.bind_ok ht
      obtain ⟨_, _, ht⟩ := H2K.FoldLaw.bind_ok ht
      cases ht
      rfl
    · cases ht
  obtain ⟨first, rest, hs, a⟩ := k12_shapes p he ha t tE rs gs (hm t ht) hk
  rw [et] at a
  rw [e2]
  exact ⟨first, rest, hs, a⟩

end VerifiableInference.Desc.K12.Coin

#print axioms VerifiableInference.Desc.K12.Coin.switch_shapes
#print axioms VerifiableInference.Desc.K12.Coin.stages_shapes
#print axioms VerifiableInference.Desc.K12.Coin.k12_shapes
#print axioms VerifiableInference.Desc.K12.Coin.atFinish_shapes
