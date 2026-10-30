-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoFrameFolds.lean.
The two folds of Plan.reqFrame: where every declared link has an array at moment 2, every link of
the frame has three moments or more.

Plan.reqFrame (OnBytes/Plan/ReqFrame.lean) makes the links of a request, each with its oracle
messages, of the arrays that the sub-proofs declare and of the lines of a layout file. It folds
takeGroup over the file's groups, then takeBlock over its blocks, and then tests that every declared
array has got a block. This file says what the two folds keep, and draws one consequence.

* getD_set, opt_guard_not, foldlM_opt: an array with one entry set; a test in Option that lets a run
  go on; a fold in Option keeps what each of its steps keeps.
* sentL s j, msgN s j t: the oracle messages of link j so far; how many groups of link j at moment t
  have been taken in.
* groupStep, takeGroup_cut: one step of the first fold: the new message's moment is the group's, and
  is not below the moment of the link's last message.
* GInv n s, takeGroup_inv, startG_inv: what the first fold keeps: the two tables have n rows; no
  message of a link has a later moment than the link's last; a moment of which a group has been
  taken in has a message.
* arrAt, takeBlock_cut, upd, BInv, upd_inv, takeBlock_inv, startB_inv: what the second fold keeps:
  its table has the sizes of the declared arrays; an array that has got a block lies at a moment of
  which a group has been taken in.
* all_isSome, reqFrame_cut: the closing test, entry by entry; a run of reqFrame, cut into the two
  folds, the test and the links.
* reqFrame_moments: if reqFrame links file answers = some (rl, lay) and every declared link has an
  array at moment 2, then momentsB rl = true (OnBytes/Tie/Pv/Lookup/Ends/FoSizedLink.lean). No upper
  bound on the moments is shown or used.

Limits: that every declared link has an array at moment 2 is a premise here: declareLinks_moments
(OnBytes/Tie/Pv/Lookup/Ends/FoDeclMoments.lean) has it of what declareLinks returns, where every
link has a vector U. Of what reqFrame returns the links alone are described: nothing on the layout.
That reqFrame returns is not shown. getD_set is used in FoDeclMoments.lean, not in this file.

Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoCoef
import OnBytes.Tie.Pv.Lookup.Ends.FoSizedLink
import OnBytes.Plan.ReqFrame

set_option autoImplicit false

namespace Fo.ReqF
open OnBytes OnBytes.Params OnBytes.Plan OnBytes.Model.Stages

theorem getD_set {α : Type} (a : Array α) (i j : Nat) (v d : α) :
    (a.setIfInBounds i v).getD j d = if i = j ∧ j < a.size then v else a.getD j d := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds]
  by_cases hij : i = j
  · subst hij
    by_cases hi : i < a.size
    · simp [hi]
    · simp [hi]
  · simp [hij]

/-- A test in Option that lets a run go on was not met. -/
theorem opt_guard_not {β : Type} {c : Prop} [Decidable c] {next : PUnit → Option β} {b : β}
    (h : (if c then (none : Option PUnit) >>= next else pure PUnit.unit >>= next) = some b) :
    ¬ c ∧ next PUnit.unit = some b := by
  split at h
  · cases h
  · exact ⟨‹_›, h⟩

/-- A fold in Option keeps what each of its steps keeps. -/
theorem foldlM_opt {σ α : Type} (f : σ → α → Option σ) (I : σ → Prop)
    (hstep : ∀ s a s', I s → f s a = some s' → I s') :
    ∀ (l : List α) (s s' : σ), I s → l.foldlM f s = some s' → I s'
  | [], s, s', hI, h => by
    obtain rfl : s = s' := Option.some.inj h
    exact hI
  | a :: l, s, s', hI, h => by
    rw [List.foldlM_cons] at h
    obtain ⟨s1, h1, h2⟩ := opt_bind h
    exact foldlM_opt f I hstep l s1 s' (hstep s a s1 hI h1) h2

/-- The oracle messages of link j so far. -/
def sentL (s : GroupsSoFar) (j : Nat) : List ReqMessage := (s.sent.getD j #[]).toList

/-- How many groups of link j at moment t have been taken in. -/
def msgN (s : GroupsSoFar) (j t : Nat) : Nat := ((s.message.getD j #[]).getD t #[]).size

/-- What a step of the first fold returns: the message m joins link g.link, and its number joins the
groups of that link's moment g.moment. -/
def groupStep (s : GroupsSoFar) (g : LayoutGroup) (m : ReqMessage) : GroupsSoFar :=
  { sent := s.sent.modify g.link (·.push m),
    message := s.message.modify g.link fun x => x.modify g.moment fun y =>
      y.push (s.sent.getD g.link #[]).size }

/-- One step of the first fold, cut. -/
theorem takeGroup_cut {links : Array FrameLink} {answers : Nat} {s s' : GroupsSoFar}
    {g : LayoutGroup} (h : takeGroup links answers s g = some s') :
    (∀ last, (sentL s g.link).getLast? = some last → last.moment ≤ g.moment) ∧
    ∃ m : ReqMessage, m.moment = g.moment ∧ s' = groupStep s g m := by
  unfold takeGroup at h
  obtain ⟨l, _, h⟩ := opt_bind h
  replace h := opt_guard h
  dsimp only at h
  replace h := opt_guard h
  obtain ⟨hm, h⟩ := opt_guard_not h
  replace h := opt_guard h
  replace h := opt_guard h
  refine ⟨?_, _, rfl, (Option.some.inj h).symm⟩
  intro last hl
  unfold sentL at hl
  rw [Array.getLast?_toList] at hl
  rw [hl] at hm
  simpa using hm

/-- What the first fold keeps. n: the number of the declared links. -/
structure GInv (n : Nat) (s : GroupsSoFar) : Prop where
  sz : s.sent.size = n
  sz' : s.message.size = n
  mono : ∀ j m last, m ∈ sentL s j → (sentL s j).getLast? = some last → m.moment ≤ last.moment
  has : ∀ j t, 0 < msgN s j t → ∃ m ∈ sentL s j, m.moment = t

theorem takeGroup_inv {links : Array FrameLink} {answers n : Nat} {s s' : GroupsSoFar}
    {g : LayoutGroup} (I : GInv n s) (h : takeGroup links answers s g = some s') : GInv n s' := by
  obtain ⟨hlast, m, hm, rfl⟩ := takeGroup_cut h
  have eS : ∀ j, sentL (groupStep s g m) j =
      if g.link = j ∧ j < s.sent.size then sentL s j ++ [m] else sentL s j := by
    intro j
    unfold sentL groupStep
    dsimp only
    rw [Fo.getD_modify]
    split
    · rw [Array.toList_push]
    · rfl
  have eM : ∀ j t, msgN (groupStep s g m) j t =
      if (g.link = j ∧ j < s.message.size) ∧ g.moment = t ∧ t < (s.message.getD j #[]).size
      then msgN s j t + 1 else msgN s j t := by
    intro j t
    unfold msgN groupStep
    dsimp only
    rw [Fo.getD_modify]
    by_cases h1 : g.link = j ∧ j < s.message.size
    · rw [if_pos h1, Fo.getD_modify]
      by_cases h2 : g.moment = t ∧ t < (s.message.getD j #[]).size
      · rw [if_pos h2, if_pos ⟨h1, h2⟩, Array.size_push]
      · rw [if_neg h2, if_neg fun x => h2 x.2]
    · rw [if_neg h1, if_neg fun x => h1 x.1]
  refine ⟨by simp [groupStep, I.sz], by simp [groupStep, I.sz'], ?_, ?_⟩
  · intro j x last hx hl
    rw [eS] at hx hl
    split at hx
    · rename_i hj
      rw [if_pos hj, List.getLast?_append, List.getLast?_singleton] at hl
      obtain rfl : m = last := by simpa using hl
      rcases List.mem_append.1 hx with hx | hx
      · obtain rfl := hj.1
        cases hq : (sentL s g.link).getLast? with
        | none =>
          rw [List.getLast?_eq_none_iff] at hq
          rw [hq] at hx
          cases hx
        | some q => exact (I.mono _ x q hx hq).trans ((hlast q hq).trans hm.ge)
      · obtain rfl : x = m := by simpa using hx
        exact Nat.le_refl _
    · rename_i hj
      rw [if_neg hj] at hl
      exact I.mono j x last hx hl
  · intro j t ht
    rw [eM] at ht
    rw [eS]
    by_cases hc : (g.link = j ∧ j < s.message.size) ∧ g.moment = t ∧ t < (s.message.getD j #[]).size
    · rw [if_pos ⟨hc.1.1, by rw [I.sz, ← I.sz']; exact hc.1.2⟩]
      exact ⟨m, List.mem_append_right _ (List.mem_singleton.2 rfl), hm.trans hc.2.1⟩
    · rw [if_neg hc] at ht
      obtain ⟨x, hx, e⟩ := I.has j t ht
      refine ⟨x, ?_, e⟩
      split
      · exact List.mem_append_left _ hx
      · exact hx

/-- The first fold's start. -/
def startG (links : Array FrameLink) : GroupsSoFar :=
  { sent := links.map fun _ => #[], message := links.map fun l => l.moment.map fun _ => #[] }

theorem startG_inv (links : Array FrameLink) : GInv links.size (startG links) := by
  have e1 : ∀ j, sentL (startG links) j = [] := by
    intro j
    unfold sentL startG
    simp only [Array.getD_eq_getD_getElem?, Array.getElem?_map]
    cases links[j]? <;> rfl
  have e2 : ∀ j t, msgN (startG links) j t = 0 := by
    intro j t
    unfold msgN startG
    simp only [Array.getD_eq_getD_getElem?, Array.getElem?_map]
    cases links[j]? with
    | none => rfl
    | some l =>
      simp only [Option.map_some, Option.getD_some, Array.getElem?_map]
      cases l.moment[t]? <;> rfl
  refine ⟨by simp [startG], by simp [startG], ?_, ?_⟩
  · intro j m last hm
    rw [e1] at hm
    cases hm
  · intro j t ht
    rw [e2] at ht
    exact absurd ht (Nat.lt_irrefl 0)

/-- The entry of array a of moment t of link j in the second fold's table. -/
def arrAt (A : Array (Array (Array (Option Nat)))) (j t a : Nat) : Option Nat :=
  ((A.getD j #[]).getD t #[]).getD a none

/-- One step of the second fold, cut: its group has been taken in, and the table is as it was or has
one entry more. -/
theorem takeBlock_cut {links : Array FrameLink} {G : GroupsSoFar} {s s' : BlocksSoFar}
    {b : LayoutBlock} (h : takeBlock links G s b = some s') :
    0 < msgN G b.link b.moment ∧ (s'.array = s.array ∨ ∃ k : Nat, s'.array =
      s.array.modify b.link fun x => x.modify b.moment fun y =>
        y.setIfInBounds b.array (some k)) := by
  unfold takeBlock at h
  obtain ⟨l, _, h⟩ := opt_bind h
  obtain ⟨declared, _, h⟩ := opt_bind h
  obtain ⟨message, hmsg, h⟩ := opt_bind h
  obtain ⟨a, _, h⟩ := opt_bind h
  have hpos : 0 < msgN G b.link b.moment := by
    unfold msgN
    by_contra hc
    have h0 : ((G.message.getD b.link #[]).getD b.moment #[]).size = 0 := by omega
    rw [Array.getElem?_eq_none (by omega)] at hmsg
    cases hmsg
  refine ⟨hpos, ?_⟩
  dsimp only at h
  split at h
  · obtain ⟨x, _, h⟩ := opt_bind h
    replace h := opt_guard h
    obtain rfl := Option.some.inj h
    exact .inl rfl
  · obtain ⟨holds, _, h⟩ := opt_bind h
    replace h := opt_guard h
    replace h := opt_guard h
    obtain rfl := Option.some.inj h
    exact .inr ⟨_, rfl⟩

/-- The second fold's table with one entry laid. -/
def upd (A : Array (Array (Array (Option Nat)))) (i t a k : Nat) :
    Array (Array (Array (Option Nat))) :=
  A.modify i fun x => x.modify t fun y => y.setIfInBounds a (some k)

theorem upd_row (A : Array (Array (Array (Option Nat)))) (i t a k j : Nat) :
    ((upd A i t a k).getD j #[]).size = (A.getD j #[]).size := by
  unfold upd
  rw [Fo.getD_modify]
  split
  · rw [Array.size_modify]
  · rfl

theorem upd_cell (A : Array (Array (Array (Option Nat)))) (i t a k j t' : Nat) :
    ((upd A i t a k).getD j #[]).getD t' #[] =
      if (i = j ∧ j < A.size) ∧ t = t' ∧ t' < (A.getD j #[]).size then
        ((A.getD j #[]).getD t' #[]).setIfInBounds a (some k)
      else (A.getD j #[]).getD t' #[] := by
  unfold upd
  rw [Fo.getD_modify]
  by_cases h1 : i = j ∧ j < A.size
  · rw [if_pos h1, Fo.getD_modify]
    by_cases h2 : t = t' ∧ t' < (A.getD j #[]).size
    · rw [if_pos h2, if_pos ⟨h1, h2⟩]
    · rw [if_neg h2, if_neg fun x => h2 x.2]
  · rw [if_neg h1, if_neg fun x => h1 x.1]

/-- What the second fold keeps. -/
structure BInv (links : Array FrameLink) (G : GroupsSoFar)
    (A : Array (Array (Array (Option Nat)))) : Prop where
  sz0 : A.size = links.size
  sz1 : ∀ j, (A.getD j #[]).size = (links.getD j {}).moment.size
  sz2 : ∀ j t, ((A.getD j #[]).getD t #[]).size = ((links.getD j {}).moment.getD t #[]).size
  has : ∀ j t a, (arrAt A j t a).isSome = true → 0 < msgN G j t

theorem upd_inv {links : Array FrameLink} {G : GroupsSoFar}
    {A : Array (Array (Array (Option Nat)))} (I : BInv links G A) (i t a k : Nat)
    (hpos : 0 < msgN G i t) : BInv links G (upd A i t a k) := by
  refine ⟨by simp [upd, I.sz0], fun j => by rw [upd_row, I.sz1], ?_, ?_⟩
  · intro j t'
    rw [upd_cell]
    split
    · rw [Array.size_setIfInBounds, I.sz2]
    · exact I.sz2 j t'
  · intro j t' a' h
    unfold arrAt at h
    rw [upd_cell] at h
    split at h
    · rename_i hc
      obtain rfl := hc.1.1
      obtain rfl := hc.2.1
      exact hpos
    · exact I.has j t' a' h

theorem takeBlock_inv {links : Array FrameLink} {G : GroupsSoFar} {s s' : BlocksSoFar}
    {b : LayoutBlock} (I : BInv links G s.array) (h : takeBlock links G s b = some s') :
    BInv links G s'.array := by
  obtain ⟨hpos, e | ⟨k, e⟩⟩ := takeBlock_cut h
  · rw [e]
    exact I
  · rw [e]
    exact upd_inv I b.link b.moment b.array k hpos

/-- The second fold's start. -/
def startB (links : Array FrameLink) : BlocksSoFar :=
  { layout := links.map fun _ => #[],
    array := links.map fun l => l.moment.map fun m => m.map fun _ => none }

theorem startB_inv (links : Array FrameLink) (G : GroupsSoFar) :
    BInv links G (startB links).array := by
  refine ⟨by simp [startB], ?_, ?_, ?_⟩
  · intro j
    unfold startB
    simp only [Array.getD_eq_getD_getElem?, Array.getElem?_map]
    cases links[j]? <;> simp
  · intro j t
    unfold startB
    simp only [Array.getD_eq_getD_getElem?, Array.getElem?_map]
    cases links[j]? with
    | none => simp
    | some l =>
      simp only [Option.map_some, Option.getD_some, Array.getElem?_map]
      cases l.moment[t]? <;> simp
  · intro j t a h
    exfalso
    unfold arrAt startB at h
    simp only [Array.getD_eq_getD_getElem?, Array.getElem?_map] at h
    cases hl : links[j]? with
    | none =>
      rw [hl] at h
      simp at h
    | some l =>
      rw [hl] at h
      simp only [Option.map_some, Option.getD_some, Array.getElem?_map] at h
      cases hm : l.moment[t]? with
      | none =>
        rw [hm] at h
        simp at h
      | some m =>
        rw [hm] at h
        simp only [Option.map_some, Option.getD_some, Array.getElem?_map] at h
        cases ha : m[a]? <;> (rw [ha] at h; simp at h)

/-- The closing test of reqFrame, entry by entry. -/
theorem all_isSome {A : Array (Array (Array (Option Nat)))}
    (h : (A.all fun l => l.all fun m => m.all (·.isSome)) = true) (j t a : Nat) (hj : j < A.size)
    (ht : t < (A.getD j #[]).size) (ha : a < ((A.getD j #[]).getD t #[]).size) :
    (arrAt A j t a).isSome = true := by
  have e1 : A.getD j #[] = A[j] := by simp [Array.getD, hj]
  rw [e1] at ht ha
  have e2 : A[j].getD t #[] = A[j][t] := by simp [Array.getD, ht]
  rw [e2] at ha
  have e3 : A[j][t].getD a none = A[j][t][a] := by simp [Array.getD, ha]
  unfold arrAt
  rw [e1, e2, e3]
  have h1 := Array.all_eq_true_iff_forall_mem.1 h _ (Array.getElem_mem hj)
  have h2 := Array.all_eq_true_iff_forall_mem.1 h1 _ (Array.getElem_mem ht)
  exact Array.all_eq_true_iff_forall_mem.1 h2 _ (Array.getElem_mem ha)

/-- A run of reqFrame, cut. -/
theorem reqFrame_cut {links : Array FrameLink} {file : LayoutLines} {answers : Nat}
    {rl : List ReqLink} {lay : ReqLayout} (h : reqFrame links file answers = some (rl, lay)) :
    ∃ G B, file.groups.foldlM (takeGroup links answers) (startG links) = some G ∧
      file.blocks.foldlM (takeBlock links G) (startB links) = some B ∧
      (B.array.all fun l => l.all fun m => m.all (·.isSome)) = true ∧
      rl = G.sent.toList.map fun m => ⟨0, m.toList⟩ := by
  unfold reqFrame at h
  obtain ⟨G, hG, h⟩ := opt_bind h
  obtain ⟨B, hB, h⟩ := opt_bind h
  obtain ⟨hn, h⟩ := opt_guard_not h
  have hall : (B.array.all fun l => l.all fun m => m.all (·.isSome)) = true := by
    by_contra hc
    have hf := Bool.eq_false_iff.2 hc
    exact hn (by rw [hf]; rfl)
  refine ⟨G, B, hG, hB, hall, ?_⟩
  exact (congrArg Prod.fst (Option.some.inj h)).symm

/-- **Where every declared link has an array at moment 2, every link of the frame has three moments
or more.** -/
theorem reqFrame_moments {links : Array FrameLink} {file : LayoutLines} {answers : Nat}
    {rl : List ReqLink} {lay : ReqLayout} (h : reqFrame links file answers = some (rl, lay))
    (hD : ∀ j, j < links.size → 0 < ((links.getD j {}).moment.getD 2 #[]).size) :
    TwLaw.momentsB rl = true := by
  obtain ⟨G, B, hG, hB, hall, rfl⟩ := reqFrame_cut h
  have IG : GInv links.size G :=
    foldlM_opt _ (GInv links.size) (fun _ _ _ I e => takeGroup_inv I e) _ _ _ (startG_inv links) hG
  have IB : BInv links G B.array :=
    foldlM_opt _ (fun s => BInv links G s.array) (fun _ _ _ I e => takeBlock_inv I e) _ _ _
      (startB_inv links G) hB
  unfold TwLaw.momentsB
  rw [List.all_eq_true]
  intro v hv
  obtain ⟨M, hM, rfl⟩ := List.mem_map.1 hv
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hM
  rw [Array.length_toList] at hj
  have hjl : j < links.size := IG.sz ▸ hj
  have e : sentL G j = (G.sent.toList[j]).toList := by
    unfold sentL
    simp [Array.getD, hj]
  have h2 := hD j hjl
  have ht : 2 < (links.getD j {}).moment.size := by
    by_contra hc
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by omega)] at h2
    exact absurd h2 (Nat.lt_irrefl 0)
  have hs := all_isSome hall j 2 0 (by rw [IB.sz0]; exact hjl) (by rw [IB.sz1]; exact ht)
    (by rw [IB.sz2]; exact h2)
  obtain ⟨m, hm, hm2⟩ := IG.has j 2 (IB.has j 2 0 hs)
  rw [decide_eq_true_eq]
  unfold OnBytes.reqMoments
  show 3 ≤ match (G.sent.toList[j]).toList.getLast? with
    | none => 0
    | some m => m.moment + 1
  rw [← e]
  cases hq : (sentL G j).getLast? with
  | none =>
    rw [List.getLast?_eq_none_iff] at hq
    rw [hq] at hm
    cases hm
  | some q =>
    have := IG.mono j m q hm hq
    show 3 ≤ q.moment + 1
    omega

end Fo.ReqF
