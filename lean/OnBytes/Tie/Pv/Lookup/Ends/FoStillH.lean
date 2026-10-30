-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoStillH.lean.
The head's key forms are made without turning state or context; what a run of Head.claimJoin is.

States:
  still_keyForm: if Head.keyForm returns, the state of the sub-proof and the context are as they
    were; so are they behind the routines that it calls (tabAt, U3at, segOf, ewOf, ewh, Sl, sh2,
    gapAt, ztSeg, middleDigit, lowDigit, LINE).
  claimJoin_ok: a run of Head.claimJoin that returns: there is an array KF with one form for each
    call of the layout; form number q is what a run of Head.keyForm for call q returned from the
    very state and context in which claimJoin began, on some array of counts (laid), which the
    statement leaves open; Forest.join on this array returned a form; and that form was added as a
    claim.
Not claimed: that any run of Head.claimJoin returns. Nor is the converse of claimJoin_ok claimed:
the test Forest.paddingLaid is not in its conclusion.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoStill
import OnBytes.Tie.Pv.Lookup.Forest.FoJoinRun

set_option autoImplicit false

namespace Fo
open OnBytes OnBytes.Model OnBytes.PscRun

/-- Takes a routine apart by the laws of OnBytes/Tie/Pv/Lookup/Ends/FoStill.lean. -/
macro "still_steps" : tactic => `(tactic| repeat (first
  | exact Still.pure _
  | exact Still.lift (StillB.mustAs _ _)
  | exact Still.lift (StillB.getAs _ _)
  | exact Still.lift (StillB.held _)
  | exact Still.lift (StillB.refuse _)
  | exact still_uEnt _ _
  | assumption
  | refine Still.bind ?_ (fun _ => ?_)
  | refine Still.forInR _ (fun _ _ => ?_) _ _
  | refine Still.forInL _ (fun _ _ => ?_) _ _
  | refine Still.ite ?_ ?_
  | split))

theorem still_tabAt (R : Head.Run) (n : String) : Still (Head.tabAt R n) := by
  unfold Head.tabAt
  still_steps

theorem still_U3at (R : Head.Run) (t i : ℕ) : Still (Head.U3at R t i) := by
  unfold Head.U3at
  still_steps

theorem still_segOf (R : Head.Run) (sn : String) : Still (Head.segOf R sn) := by
  unfold Head.segOf
  still_steps

theorem still_ewOf (R : Head.Run) (sn : String) : Still (Head.ewOf R sn) := by
  have h1 := still_segOf R sn
  unfold Head.ewOf
  still_steps

theorem still_ewh (R : Head.Run) (sn : String) : Still (Head.ewh R sn) := by
  have h1 := still_segOf R sn
  unfold Head.ewh
  still_steps

theorem still_Sl (R : Head.Run) (sn : String) (OFF nl J : ℕ) : Still (Head.Sl R sn OFF nl J) := by
  have h1 := still_ewh R sn
  have h2 := still_tabAt R "hf@Z"
  have h3 := fun t i => still_U3at R t i
  unfold Head.Sl
  still_steps

theorem still_sh2 (R : Head.Run) (t j : ℕ) : Still (Head.sh2 R t j) := by
  have h3 := fun t i => still_U3at R t i
  unfold Head.sh2
  exact Still.bind (h3 _ _) fun _ => Still.bind (h3 _ _) fun _ => Still.pure _

theorem still_gapAt (R : Head.Run) (P : String) (i : ℕ) (w : E) : Still (Head.gapAt R P i w) := by
  have h2 := fun n => still_tabAt R n
  have h3 := fun t i => still_U3at R t i
  unfold Head.gapAt
  refine Still.bind (h2 _) fun _ => ?_
  still_steps

theorem still_ztSeg (R : Head.Run) (sn : String) : Still (Head.ztSeg R sn) := by
  unfold Head.ztSeg
  still_steps

theorem still_middleDigit (R : Head.Run) (sn : String) (w : E) :
    Still (Head.middleDigit R sn w) := by
  unfold Head.middleDigit
  exact Still.bind (still_Sl _ _ _ _ _) fun _ => Still.pure _

theorem still_lowDigit (R : Head.Run) (sn : String) (w : E) : Still (Head.lowDigit R sn w) := by
  unfold Head.lowDigit
  exact Still.bind (still_Sl _ _ _ _ _) fun _ => Still.pure _

/-- Takes a routine of the head apart. The ways of putting routines together are tried first, and
without unfolding. -/
macro "still_head" : tactic => `(tactic| repeat (first
  | with_reducible refine Still.bind ?_ (fun _ => ?_)
  | with_reducible refine Still.ite ?_ ?_
  | with_reducible refine Still.forInR _ (fun _ _ => ?_) _ _
  | with_reducible refine Still.forInL _ (fun _ _ => ?_) _ _
  | with_reducible exact Still.pure _
  | with_reducible exact still_tabAt _ _
  | with_reducible exact still_U3at _ _ _
  | with_reducible exact still_ewOf _ _
  | with_reducible exact still_Sl _ _ _ _ _
  | with_reducible exact still_sh2 _ _ _
  | with_reducible exact still_gapAt _ _ _ _
  | with_reducible exact still_ztSeg _ _
  | with_reducible exact still_middleDigit _ _ _
  | with_reducible exact still_lowDigit _ _ _
  | with_reducible assumption
  | split
  | exact Still.lift (StillB.mustAs _ _)
  | exact Still.lift (StillB.getAs _ _)
  | exact Still.lift (StillB.held _)
  | exact Still.lift (StillB.refuse _)))

/-- The same without taking matches apart. -/
macro "still_flat" : tactic => `(tactic| repeat (first
  | with_reducible refine Still.bind ?_ (fun _ => ?_)
  | with_reducible refine Still.ite ?_ ?_
  | with_reducible refine Still.forInR _ (fun _ _ => ?_) _ _
  | with_reducible refine Still.forInL _ (fun _ _ => ?_) _ _
  | with_reducible exact Still.pure _
  | with_reducible exact still_tabAt _ _
  | with_reducible exact still_U3at _ _ _
  | with_reducible exact still_ewOf _ _
  | with_reducible exact still_Sl _ _ _ _ _
  | with_reducible exact still_sh2 _ _ _
  | with_reducible exact still_gapAt _ _ _ _
  | with_reducible exact still_ztSeg _ _
  | with_reducible exact still_middleDigit _ _ _
  | with_reducible exact still_lowDigit _ _ _))

theorem still_LINE (R : Head.Run) (sn : String) : Still (Head.LINE R sn) := by
  unfold Head.LINE
  still_flat
  exact Still.lift (StillB.refuse _)

theorem still_keyForm (R : Head.Run) (q : ℕ) (laid : Array ℕ) :
    Still (Head.keyForm R q laid) := by
  unfold Head.keyForm
  repeat (first
    | with_reducible exact still_LINE _ _
    | with_reducible refine Still.bind ?_ (fun _ => ?_)
    | with_reducible refine Still.ite ?_ ?_
    | with_reducible refine Still.forInR _ (fun _ _ => ?_) _ _
    | with_reducible refine Still.forInL _ (fun _ _ => ?_) _ _
    | with_reducible exact Still.pure _
    | with_reducible exact Still.liftM (StillB.getAs _ _)
    | with_reducible exact Still.liftM (StillB.mustAs _ _)
    | split
    | dsimp only)

/-! ### Head.claimJoin -/

/-- What the loop of Head.claimJoin has made of the array KF over the calls of l. -/
def Pushed (R : Head.Run) (F : Fork) (c : Ctx) (l : List ℕ) (KF KF' : Array Aff) : Prop :=
  KF'.size = KF.size + l.length ∧ (∀ i < KF.size, KF'[i]? = KF[i]?) ∧
    ∀ i < l.length, ∃ v laid laid', KF'[KF.size + i]? = some v ∧
      Head.keyForm R (l.getD i 0) laid F c = .ok (((v, laid'), F), c)

theorem loop_ok (R : Head.Run) (F : Fork) (c : Ctx)
    (body : ℕ → MProd (Array Aff) (Array ℕ) → SubM (ForInStep (MProd (Array Aff) (Array ℕ))))
    (hb : ∀ q s out, body q s F c = .ok out → ∃ v l,
      Head.keyForm R q s.snd F c = .ok (((v, l), F), c) ∧
        out = ((ForInStep.yield ⟨s.fst.push v, l⟩, F), c)) :
    ∀ (l : List ℕ) (s : MProd (Array Aff) (Array ℕ)) (out),
      (forIn l s body) F c = .ok out → out.1.2 = F ∧ out.2 = c ∧ Pushed R F c l s.fst out.1.1.fst
  | [], s, out, h => by
    rw [List.forIn_nil] at h
    rw [(pure_ok s F c out).1 h]
    exact ⟨rfl, rfl, rfl, fun _ _ => rfl, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
  | a :: l, s, out, h => by
    rw [List.forIn_cons, bind_ok] at h
    obtain ⟨st, G, c1, h1, h2⟩ := h
    obtain ⟨v, l', hk, e⟩ := hb a s _ h1
    have e1 : st = ForInStep.yield ⟨s.fst.push v, l'⟩ :=
      congrArg (fun x : (ForInStep (MProd (Array Aff) (Array ℕ)) × Fork) × Ctx => x.1.1) e
    have e2 : G = F :=
      congrArg (fun x : (ForInStep (MProd (Array Aff) (Array ℕ)) × Fork) × Ctx => x.1.2) e
    have e3 : c1 = c :=
      congrArg (fun x : (ForInStep (MProd (Array Aff) (Array ℕ)) × Fork) × Ctx => x.2) e
    rw [e1, e2, e3] at h2
    obtain ⟨a1, a2, b1, b2, b3⟩ := loop_ok R F c body hb l ⟨s.fst.push v, l'⟩ out h2
    refine ⟨a1, a2, ?_, fun i hi => ?_, fun i hi => ?_⟩
    · rw [b1, Array.size_push, List.length_cons]
      omega
    · rw [b2 i (by rw [Array.size_push]; omega), Array.getElem?_push, if_neg (by omega)]
    · cases i with
      | zero =>
        refine ⟨v, s.snd, l', ?_, hk⟩
        rw [Nat.add_zero, b2 s.fst.size (by rw [Array.size_push]; omega), Array.getElem?_push,
          if_pos rfl]
      | succ i =>
        obtain ⟨w, d0, d1, f1, f2⟩ := b3 i (by rw [List.length_cons] at hi; omega)
        refine ⟨w, d0, d1, ?_, f2⟩
        rw [← f1, Array.size_push]
        congr 1
        omega

/-- **What a run of Head.claimJoin is.** -/
theorem claimJoin_ok (R : Head.Run) (F G : Fork) (c c' : Ctx)
    (h : Head.claimJoin R F c = .ok (((), G), c')) :
    ∃ (KF : Array Aff) (jf : Aff), KF.size = R.L.calls.size ∧
      (∀ q < R.L.calls.size, ∃ laid laid',
        Head.keyForm R q laid F c = .ok (((KF.getD q (Aff.ofConst zeroE), laid'), F), c)) ∧
      Forest.join R.x.g1 KF F c = .ok ((jf, F.paid R.x.g1.owedJoin), c) ∧
      (F.paid R.x.g1.owedJoin).lin jf = some G ∧ c' = c := by
  unfold Head.claimJoin at h
  dsimp only at h
  rw [bind_ok] at h
  obtain ⟨⟨KF, laid⟩, F1, c1, h1, h⟩ := h
  rw [Std.Legacy.Range.forIn_eq_forIn_range'] at h1
  obtain ⟨a1, a2, b1, _, b3⟩ := loop_ok R F c _ (fun q s out ho => by
    rw [bind_ok] at ho
    obtain ⟨⟨v, l⟩, G1, d1, k1, k2⟩ := ho
    obtain ⟨s1, s2⟩ := still_keyForm R q s.snd F c _ k1
    have s1' : G1 = F := s1
    have s2' : d1 = c := s2
    rw [s1', s2'] at k1 k2
    dsimp only at k2
    rw [bind_ok] at k2
    obtain ⟨_, G2, d2, k3, k4⟩ := k2
    have e5 := (pure_ok _ _ _ _).1 k3
    have t1 : G2 = F := congrArg (fun x : (PUnit × Fork) × Ctx => x.1.2) e5
    have t2 : d2 = c := congrArg (fun x : (PUnit × Fork) × Ctx => x.2) e5
    rw [t1, t2] at k4
    exact ⟨v, l, k1, (pure_ok _ _ _ _).1 k4⟩) _ _ _ h1
  have a1' : F1 = F := a1
  have a2' : c1 = c := a2
  have b1' : KF.size = (#[] : Array Aff).size + (List.range' 0 R.L.calls.size 1).length := by
    simpa [Std.Legacy.Range.size] using b1
  rw [a1', a2'] at h
  dsimp only at h
  rw [bind_ok] at h
  obtain ⟨_, F2, c2, p1, h⟩ := h
  obtain ⟨p2, p3⟩ := (Still.liftM (StillB.mustAs _ _) : Still (Forest.paddingLaid R.x.g1 laid)) F c
    _ p1
  have p2' : F2 = F := p2
  have p3' : c2 = c := p3
  rw [p2', p3', bind_ok] at h
  obtain ⟨jf, F3, c3, j1, h⟩ := h
  obtain ⟨_, _, j2, j3, _⟩ := join_ok R.x.g1 KF F F3 c c3 jf j1
  rw [j2, j3] at j1 h
  obtain ⟨l1, l2⟩ := (SubM.lin_run jf _ G c c').1 h
  refine ⟨KF, jf, by simpa using b1', fun q hq => ?_, j1, l1, l2⟩
  obtain ⟨v, d0, d1, f1, f2⟩ := b3 q (by simpa [Std.Legacy.Range.size] using hq)
  refine ⟨d0, d1, ?_⟩
  have g1 : KF.getD q (Aff.ofConst zeroE) = v := by
    rw [Array.getD_eq_getD_getElem?]
    have : KF[q]? = some v := by simpa using f1
    rw [this]
    rfl
  have g2 : (List.range' 0 (Std.Legacy.Range.size [:R.L.calls.size]) 1).getD q 0 = q := by
    rw [List.getD_eq_getElem _ _ (by simpa [Std.Legacy.Range.size] using hq)]
    simp
  rw [g1]
  rw [g2] at f2
  exact f2

end Fo
