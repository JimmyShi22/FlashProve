-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Flat/LinksFreeHeadA.lean: two pieces of the check of the head at two requests
(OnBytes/Flat/LinksFreeHead.lean): `HearFree` and `WeightsClaimFree`.

Both routines run while the state of the check is still the same at both requests. `hear` lays the
checked tokens into what it returns and does nothing else with the request. `weightsClaim` makes one
factor of the claim on the weights: an array of V elements, changed at the checked token of each
covered position. Its inner loop branches on whether a position is covered, so at two requests the
two runs take different branches; but a branch holds nothing except a test that a dry run skips, and
the array keeps its size.

Main definitions: `StepRel` (two turns of a loop), `IsPure` (in a dry run the routine leaves state
and context as they are and returns a given value). Main theorems: `Cmp.forIn_list`,
`Cmp.forIn_range` (two loops over one list or range, with states in a relation); `isPure_pure`,
`isPure_bind`, `isPure_testAs`, `rel_of_isPure`; `size_winOf`; `hearFree`, `weightsClaimFree`.

Not claimed: the other pieces. Nothing on a run on a view. For proofs only; no module of the program
imports this file.


-/
import OnBytes.Flat.LinksFreeHead

set_option autoImplicit false

namespace OnBytes.Flat

open OnBytes.Model OnBytes.Model.Head

/-- Closes `Blk.Keeps b` by the walk. -/
local macro "keeps_blk" : tactic => `(tactic| (show Over.K (m := Blk) _; keeps))

/-! ## Loops -/

/-- Two turns of a loop: both end it or both go on, with states in S. -/
def StepRel {β : Type} (S : β → β → Prop) : ForInStep β → ForInStep β → Prop
  | .done a, .done b => S a b
  | .yield a, .yield b => S a b
  | _, _ => False

theorem Cmp.forIn_list {m : Type → Type} [Monad m] [Over m] (c : Cmp m) {α β : Type}
    {S : β → β → Prop} {f f' : α → β → m (ForInStep β)} (hk : ∀ a s, Over.K (f a s))
    (hf : ∀ a s s', S s s' → c.Rel (StepRel S) (f a s) (f' a s')) :
    ∀ (l : List α) {init init' : β}, S init init' → c.Rel S (forIn l init f) (forIn l init' f')
  | [], _, _, h => by
      rw [List.forIn_nil, List.forIn_nil]
      exact c.pure' h
  | a :: l, init, init', h => by
      rw [List.forIn_cons, List.forIn_cons]
      refine c.bind' (hk a init) (hf a init init' h) fun r r' hr => ?_
      cases r <;> cases r'
      · exact c.pure' hr
      · exact hr.elim
      · exact hr.elim
      · exact Cmp.forIn_list c hk hf l hr

theorem Cmp.forIn_range {m : Type → Type} [Monad m] [Over m] (c : Cmp m) {β : Type}
    {S : β → β → Prop} {f f' : Nat → β → m (ForInStep β)} (hk : ∀ a s, Over.K (f a s))
    (hf : ∀ a s s', S s s' → c.Rel (StepRel S) (f a s) (f' a s')) (r : Std.Legacy.Range)
    {init init' : β} (h : S init init') : c.Rel S (forIn r init f) (forIn r init' f') := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.forIn_eq_forIn_range']
  exact c.forIn_list hk hf _ h

/-! ## The messages up to the commitment to the reads -/

theorem size_winOf (cov : Covered) (T y : Nat) : (winOf cov T y).size = cov.hWin.size := by
  unfold winOf
  split
  · exact Array.size_setIfInBounds
  · rfl

theorem hearFree : HearFree := by
  intro h L hp cov cov' plain hc
  unfold hear
  repeat (refine cmpS.bind_same same_cmpS (by keeps) fun _ => ?_)
  exact cmpS.pure' ⟨rfl, by rw [size_winOf, size_winOf, hc.2.2.1]⟩

/-! ## Routines that do nothing in a dry run but return a value -/

/-- In a dry run x leaves state and context as they are and returns a. -/
def IsPure {α : Type} (x : SubM α) (a : α) : Prop :=
  ∀ (s : Fork) (c : Ctx), c.Dry → x s c = .ok ((a, s), c)

theorem isPure_pure {α : Type} (a : α) : IsPure (pure a) a := fun _ _ _ => rfl

theorem isPure_bind {α β : Type} {x : SubM α} {f : α → SubM β} {a : α} {b : β} (hx : IsPure x a)
    (hf : IsPure (f a) b) : IsPure (x >>= f) b := by
  intro s c hc
  show (x s >>= fun p => f p.1 p.2) c = _
  rw [Blk.bind_ok (hx s c hc)]
  exact hf s c hc

theorem isPure_testAs (name : String) (b : Bool) :
    IsPure (liftM (testAs name b) : SubM Unit) () := by
  intro s c hc
  have e : testAs name b c = .ok ((), c) := by
    unfold testAs
    show (Blk.isDry >>= fun d => if (b || d) = true then pure () else refuse name) c = _
    rw [Blk.bind_ok (show Blk.isDry c = .ok (c.ch.dry, c) from rfl), hc.1]
    simp only [Bool.or_true, if_true]
    rfl
  show (testAs name b >>= fun a => pure (a, s)) c = _
  rw [Blk.bind_ok e]
  rfl

theorem rel_of_isPure {α : Type} {R : α → α → Prop} {x x' : SubM α} {a a' : α} (hx : IsPure x a)
    (hx' : IsPure x' a') (h : R a a') : cmpS.Rel R x x' := by
  intro s s' hs c hc
  subst hs
  rw [hx s c hc, hx' s c hc]
  exact ⟨⟨h, rfl⟩, rfl⟩

/-! ## The one claim on the committed weights -/

theorem weightsClaimFree : WeightsClaimFree := by
  intro R R' wsLay hR
  obtain ⟨e, hc, ⟨ex, hw⟩, ⟨et, hf⟩⟩ := hR
  generalize R'.cov = cov' at e hc
  generalize R'.x = x' at e ex hw
  generalize R'.t = t' at e et hf
  generalize x'.win = w' at ex hw
  generalize t'.funs = f' at et hf
  subst ex et e
  unfold weightsClaim
  dsimp only
  refine cmpS.bind_same same_cmpS (by keeps) fun ew0 => ?_
  refine cmpS.bind_same same_cmpS (by keeps) fun _ => ?_
  refine cmpS.bind' (S := All2 FacAlike) (by keeps)
    (cmpS.forIn_list (fun _ _ => by keeps) (fun G r r' hr => ?_) _ .nil)
    fun r r' hr => cmpS.pure' ⟨rfl, hr⟩
  by_cases hx : (G.name == "x") = true
  · simp only [hx, if_true]
    refine cmpS.bind' (S := fun a a' => a.size = a'.size) (by keeps)
      (cmpS.forIn_range (fun _ _ => by keeps) (fun t a a' ha => ?_) _
        (by simp only [Array.size_map])) fun a a' ha => ?_
    · have p1 : ∀ (n : String) (b : Bool) (y : ForInStep (Array E)),
          IsPure (do
            liftM (testAs n b)
            pure PUnit.unit
            pure y : SubM (ForInStep (Array E))) y := fun n b y =>
        isPure_bind (isPure_testAs n b) (isPure_bind (isPure_pure _) (isPure_pure y))
      have p2 : ∀ y : ForInStep (Array E),
          IsPure (do
            pure PUnit.unit
            pure y : SubM (ForInStep (Array E))) y := fun y =>
        isPure_bind (isPure_pure _) (isPure_pure y)
      split <;> split
      · exact rel_of_isPure (p1 _ _ _) (p1 _ _ _)
          (by show Array.size _ = Array.size _; rw [Array.size_modify, Array.size_modify, ha])
      · exact rel_of_isPure (p1 _ _ _) (p2 _)
          (by show Array.size _ = Array.size _; rw [Array.size_modify, ha])
      · exact rel_of_isPure (p2 _) (p1 _ _ _)
          (by show Array.size _ = Array.size _; rw [Array.size_modify, ha])
      · exact rel_of_isPure (p2 _) (p2 _) ha
    · refine cmpS.bind_same same_cmpS (by keeps) fun _ => ?_
      exact cmpS.pure' (R := StepRel (All2 FacAlike)) (hr.append (.cons ⟨rfl, rfl, ha⟩ .nil))
  · simp only [hx, Bool.false_eq_true, if_false]
    split
    · refine cmpS.bind_same same_cmpS (by keeps) fun _ => ?_
      exact cmpS.pure' (R := StepRel (All2 FacAlike)) (hr.append (.cons (FacAlike.refl _) .nil))
    · refine cmpS.bind_same same_cmpS (by keeps) fun _ => ?_
      exact cmpS.pure' (R := StepRel (All2 FacAlike)) hr

end OnBytes.Flat
