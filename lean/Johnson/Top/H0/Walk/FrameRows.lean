-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Walk/FrameRows.lean: what every row of the frame's value framesOf
(Johnson/Top/H0/Walk/FrameLot.lean) is, whichever sort of link it stands at: for whoever has seated
a description's blocks at f.lay and f.clear and wants the frame's laws at them.

  headFrame_plan, headFrame_fv   the head's frame's test on the plan is planFlag at the head's kind;
                  where it says yes the head's record leaves a row
  mapM_mem        a member of what List.mapM returns comes of a member of the list
  framesOf_row    at every row f: f.lay is layFront f.link; f.clear is clearWith X counts left at
                  the pending row's own function, at some X, counts and left (at the head's link
                  too: tailHead is clearWith by definition); and where the row's test on the plan
                  says yes, X leaves a row just if its kind is not attention's

  frameAt_att, frameAt_lay, zeroAt_some   the letters' makers, read back: the link's record, its
                  kind, the plan's entry, and the letters to the letter
  framesOf_arms   WHICH ROW AT WHICH LINK: by the kind of the link's record: the head's (kind 2) ·
                  link 0 (kind 0) · attention (kind 1, behind link 0) · layers (kind 0, behind
                  link 0): each with plan, opened and clear at the letters

No soundness statement.

-/
import Johnson.Top.H0.Walk.FrameLot
import Johnson.Top.H0.Walk.FrameProps

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Desc.First.Walk.Seat
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First (S)

theorem mapM_mem {α β : Type} (g : α → Except String β) : ∀ (l : List α) (r : List β),
    l.mapM g = .ok r → ∀ y ∈ r, ∃ a ∈ l, g a = .ok y
  | [], r, h, y, hy => by
      simp [pure, Except.pure] at h
      subst h
      cases hy
  | a :: l, r, h, y, hy => by
      rw [List.mapM_cons] at h
      cases ha : g a with
      | error e => simp [ha, bind, Except.bind] at h
      | ok b =>
        cases hl : l.mapM g with
        | error e => simp [ha, hl, bind, Except.bind] at h
        | ok r' =>
          simp [ha, hl, bind, Except.bind, pure, Except.pure] at h
          subst h
          rcases List.mem_cons.1 hy with e | hy'
          · subst e
            exact ⟨a, List.mem_cons_self, ha⟩
          · obtain ⟨a', h1, h2⟩ := mapM_mem g l r' hl y hy'
            exact ⟨a', List.mem_cons_of_mem _ h1, h2⟩

/-- The head's frame's test on the plan, by name. -/
theorem headFrame_plan (X : LinkPub) (l : Nat) (first : Params.First) (W : Verify.Public) :
    (headFrame X l first W).plan = planFlag X 2 := rfl

/-- Where the head's frame's test on the plan says yes, the head's record leaves a row. -/
theorem headFrame_fv {X : LinkPub} {l : Nat} {first : Params.First} {W : Verify.Public}
    (h : (headFrame X l first W).plan = true) : X.fv = true :=
  Props.planFlag_head_fv (by rw [← headFrame_plan X l first W]; exact h)

theorem flag_of {X : LinkPub} {kind : Nat} (h : Props.PlanFlag X kind) :
    (X.fv = true ↔ X.kind ≠ 1) := by
  rw [h.1]
  exact h.2

/-- **Every row of the frame's value.** -/
theorem framesOf_row {built : Array Stages.LinkH} {first : Params.First} {W : Verify.Public}
    {fs : List LinkFrame} {f : LinkFrame} (h : framesOf built first W = .ok fs) (hf : f ∈ fs) :
    f.lay = layFront f.link ∧
      ∃ (X : LinkPub) (counts : S → Except String Unit) (left : S → Option WsForkOut),
        f.clear = clearWith X counts left (rowOf W first) ∧
          (f.plan = true → (X.fv = true ↔ X.kind ≠ 1)) := by
  unfold framesOf at h
  obtain ⟨a, _, e⟩ := mapM_mem _ _ _ h f hf
  dsimp only at e
  split at e
  · split at e
    · cases e
    · rename_i X hX
      cases e
      exact ⟨rfl, pubOf X, _, _, rfl, fun hp => flag_of ((Props.planFlag_iff _ 2).1 hp)⟩
  · split at e
    · split at e
      · cases e
      · rename_i P hP
        cases e
        exact ⟨rfl, P.X, _, _, rfl, fun hp =>
          flag_of ((Props.planLayZero_iff _ P).1 hp).2.2.2.2.2⟩
    · split at e
      · cases e
      · rename_i P nLin hP
        cases e
        exact ⟨rfl, P.X, _, _, rfl, fun hp => flag_of ((Props.planAtt_iff _ P).1 hp).2.2⟩
      · rename_i P hP
        cases e
        exact ⟨rfl, P.X, _, _, rfl, fun hp => flag_of ((Props.planLay_iff _ P).1 hp).2.2.2.2.2⟩

/-! ### Which row at which link -/

/-- frameAt, read back: an attention link's letters. -/
theorem frameAt_att {built : Array Stages.LinkH} {W : Verify.Public} {l : Nat} {P : AttPar}
    {n : Nat} (h : frameAt built W l = some (.att P n)) :
    ∃ X p, built[l]? = some X ∧ l ≠ 0 ∧ X.kind = 1 ∧ W.A[X.g]? = some p ∧
      P = ⟨pubOf X, l, p.ns, p.seam.tl⟩ ∧ n = p.nLin := by
  unfold frameAt at h
  cases hX : built[l]? with
  | none => simp [hX] at h
  | some X =>
    simp only [hX, Option.bind_eq_bind, Option.bind_some] at h
    by_cases h0 : (l == 0) = true
    · simp [h0] at h
    · by_cases h1 : (X.kind == 1) = true
      · cases hp : W.A[X.g]? with
        | none => simp [h0, h1, hp] at h
        | some p =>
          simp [h0, h1, hp] at h
          exact ⟨X, p, rfl, by simpa using h0, by simpa using h1, hp, h.1.symm, h.2.symm⟩
      · by_cases h2 : (X.kind == 0) = true
        · cases hp : W.G[X.g]? <;> simp [h0, h1, h2, hp] at h
        · simp [h0, h1, h2] at h

/-- frameAt, read back: a layers' link's letters, behind link 0. -/
theorem frameAt_lay {built : Array Stages.LinkH} {W : Verify.Public} {l : Nat} {P : LayPar}
    (h : frameAt built W l = some (.lay P)) :
    ∃ X hp, built[l]? = some X ∧ l ≠ 0 ∧ X.kind = 0 ∧ W.G[X.g]? = some hp ∧
      P = ⟨pubOf X, l, W.layers.y.h.p4, X.g, hp.Tp, hp.Fp, hp.ns, hp.tl⟩ := by
  unfold frameAt at h
  cases hX : built[l]? with
  | none => simp [hX] at h
  | some X =>
    simp only [hX, Option.bind_eq_bind, Option.bind_some] at h
    by_cases h0 : (l == 0) = true
    · simp [h0] at h
    · by_cases h1 : (X.kind == 1) = true
      · cases hp : W.A[X.g]? <;> simp [h0, h1, hp] at h
      · by_cases h2 : (X.kind == 0) = true
        · cases hp : W.G[X.g]? with
          | none => simp [h0, h1, h2, hp] at h
          | some q =>
            simp [h0, h1, h2, hp] at h
            exact ⟨X, q, rfl, by simpa using h0, by simpa using h2, hp, h.symm⟩
        · simp [h0, h1, h2] at h

/-- zeroAt, read back: link 0's letters. -/
theorem zeroAt_some {built : Array Stages.LinkH} {W : Verify.Public} {P : LayPar}
    (h : zeroAt built W = some P) :
    ∃ X hp, built[0]? = some X ∧ X.kind = 0 ∧ W.G[X.g]? = some hp ∧
      P = ⟨pubOf X, 0, W.layers.y.h.p4, X.g, hp.Tp, hp.Fp, hp.ns, hp.tl⟩ := by
  unfold zeroAt at h
  cases hX : built[0]? with
  | none => simp [hX] at h
  | some X =>
    simp only [hX, Option.bind_eq_bind, Option.bind_some] at h
    by_cases h2 : (X.kind != 0) = true
    · simp [h2] at h
    · cases hp : W.G[X.g]? with
      | none => simp [h2, hp] at h
      | some q =>
        simp [h2, hp] at h
        exact ⟨X, q, rfl, by simpa using h2, hp, h.symm⟩

theorem mapM_idx {α β : Type} (g : α → Except String β) : ∀ (l : List α) (r : List β),
    l.mapM g = .ok r → ∀ (i : Nat) (y : β), r[i]? = some y → ∃ a, l[i]? = some a ∧ g a = .ok y
  | [], r, h, i, y, hy => by
      simp [pure, Except.pure] at h
      subst h
      simp at hy
  | a :: l, r, h, i, y, hy => by
      rw [List.mapM_cons] at h
      cases ha : g a with
      | error e => simp [ha, bind, Except.bind] at h
      | ok b =>
        cases hl : l.mapM g with
        | error e => simp [ha, hl, bind, Except.bind] at h
        | ok r' =>
          simp [ha, hl, bind, Except.bind, pure, Except.pure] at h
          subst h
          cases i with
          | zero =>
            simp at hy
            subst hy
            exact ⟨a, rfl, ha⟩
          | succ j =>
            rw [List.getElem?_cons_succ] at hy
            obtain ⟨a', h1, h2⟩ := mapM_idx g l r' hl j y hy
            exact ⟨a', by rw [List.getElem?_cons_succ]; exact h1, h2⟩

/-- **Which row framesOf lays at link l, by the kind of the link's record**: four arms, each with
the record, its kind, the plan's entry and the letters: no two can hold at one l. -/
theorem framesOf_arms {built : Array Stages.LinkH} {first : Params.First} {W : Verify.Public}
    {fs : List LinkFrame} {f : LinkFrame} {l : Nat} (h : framesOf built first W = .ok fs)
    (hf : fs[l]? = some f) :
    (∃ X, built[l]? = some X ∧ X.kind = 2 ∧ f = headFrame (pubOf X) l first W) ∨
      (l = 0 ∧ ∃ X hp P, built[0]? = some X ∧ X.kind = 0 ∧ W.G[X.g]? = some hp ∧
        P = ⟨pubOf X, 0, W.layers.y.h.p4, X.g, hp.Tp, hp.Fp, hp.ns, hp.tl⟩ ∧
        f.plan = planLayZero first.shape P ∧
        f.opened = openLayZero P (fvsOf built) first.lin.kCol ∧
        f.clear = clearWith P.X (countsLay P.tl₀.NM) leftLay (rowOf W first)) ∨
      (l ≠ 0 ∧ ∃ X p P, built[l]? = some X ∧ X.kind = 1 ∧ W.A[X.g]? = some p ∧
        P = ⟨pubOf X, l, p.ns, p.seam.tl⟩ ∧ f.plan = planAtt first.shape P ∧
        f.opened = openAtt P ∧
        f.clear = clearWith P.X (countsAtt p.nLin) (fun _ => none) (rowOf W first)) ∨
      (l ≠ 0 ∧ ∃ X hp P, built[l]? = some X ∧ X.kind = 0 ∧ W.G[X.g]? = some hp ∧
        P = ⟨pubOf X, l, W.layers.y.h.p4, X.g, hp.Tp, hp.Fp, hp.ns, hp.tl⟩ ∧
        f.plan = planLay first.shape P ∧ f.opened = openLay P ∧
        f.clear = clearWith P.X (countsLay P.tl₀.NM) leftLay (rowOf W first)) := by
  unfold framesOf at h
  obtain ⟨a, ha, e⟩ := mapM_idx _ _ _ h l f hf
  obtain rfl : l = a := by
    obtain ⟨_, h2⟩ := List.getElem?_eq_some_iff.1 ha
    simpa using h2
  dsimp only at e
  split at e
  · rename_i hk
    split at e
    · cases e
    · rename_i X hX
      cases e
      rw [hX] at hk
      exact Or.inl ⟨X, hX, by simpa using hk, rfl⟩
  · split at e
    · rename_i h0
      obtain rfl : l = 0 := by simpa using h0
      split at e
      · cases e
      · rename_i P hP
        cases e
        obtain ⟨X, hp, h1, h2, h3, h4⟩ := zeroAt_some hP
        exact Or.inr (Or.inl ⟨rfl, X, hp, P, h1, h2, h3, h4, rfl, rfl, rfl⟩)
    · split at e
      · cases e
      · rename_i P nLin hP
        cases e
        obtain ⟨X, p, h1, h2, h3, h4, h5, h6⟩ := frameAt_att hP
        subst h6
        exact Or.inr (Or.inr (Or.inl ⟨h2, X, p, P, h1, h3, h4, h5, rfl, rfl, rfl⟩))
      · rename_i P hP
        cases e
        obtain ⟨X, hp, h1, h2, h3, h4, h5⟩ := frameAt_lay hP
        exact Or.inr (Or.inr (Or.inr ⟨h2, X, hp, P, h1, h3, h4, h5, rfl, rfl, rfl⟩))

#print axioms framesOf_row
#print axioms framesOf_arms
#print axioms frameAt_att
#print axioms frameAt_lay
#print axioms zeroAt_some
#print axioms headFrame_fv

end Johnson.Desc.First.Walk.Seat
