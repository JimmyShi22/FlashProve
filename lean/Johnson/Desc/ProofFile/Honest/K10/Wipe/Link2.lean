-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K10/Wipe/Link2.lean: the closing of a segment (K10): from the properties of
Honest/K10/Wipe/Alike.lean to the premise Keeps of Honest/K10/WipeFold.lean, and from a link's parts to the members of
its flat list. General in the state's type σ and in a function w : σ → σ. One definition of type Prop; the rest are
theorems.

  grpShape_cols, regroup_sameG   columns of one shape, laid into groups, are groups of one shape
  alikeStep_of                   outcomes of a step that are alike under wStep w are alike in WipeFold.lean's sense
  **keeps_of_decides2**          a member whose decide has like outcomes keeps: Decides2 w b gives Keeps w ft b
  claimsInStep2, claimsInBy2     the gathering of a link's claims, with the test behind each run
  stepA2, afterIn2               the runs behind the batching
  LinkKeeps2                     what is asked of a link's parts: seven clauses, two of them on its tests
  runBehind2                     the frame's step behind the batching
  **link_flat_keeps2**           every member of the flat list of such a link has like outcomes

By what. The step's text (Johnson/Desc/Block.lean, Block.step) is followed bind by bind: the test on the rounds is one
term at both states; the test on the columns asks one Bool, since it reads keys, positions and widths; decide by the
premise. The two folds go by induction on the order, a step by cases on the outcomes of the run and of the test behind
it. The flat list is taken apart arm by arm, as Johnson/Desc/FoldKeeps.lean does for relations on one state; that file's
named_ok, lookup_mem, stepA and afterIn_eq are used.

Limits. The properties are shown of no member and of no link of the protocol here. Nothing says what w is. Nothing is
said of what stands in a chain outside its links. No property of the protocol is claimed: nothing is said on its
soundness, completeness, binding or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K10.Wipe.Alike
import Johnson.Desc.FoldKeeps

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10
open VerifiableInference.Desc (Block Link OpenedColumn regroup noDigest claimsInStep claimsInBy afterIn)

variable {σ Cl : Type} {w : σ → σ}

/-! ## 1 From Decides2 to Keeps -/

/-- The shape of a group that is made of columns is the columns' shape without the keys. -/
theorem grpShape_cols : ∀ l : List OpenedColumn,
    grpShape (l.map fun x => (x.2.1, x.2.2)) = (l.map colShape).map fun y => y.2
  | [] => rfl
  | a :: l => by
    have ih := grpShape_cols l
    show (a.2.1, a.2.2.length) :: grpShape (l.map fun x => (x.2.1, x.2.2)) =
      (a.2.1, a.2.2.length) :: (l.map colShape).map fun y => y.2
    rw [ih]

/-- Columns of one shape, laid into groups of given lengths, are groups of one shape. -/
theorem regroup_sameG (ns : List Nat) :
    ∀ {c c' : List OpenedColumn}, SameShape c c' → SameG (regroup ns c) (regroup ns c') := by
  induction ns with
  | nil =>
    intro c c' _
    exact (rfl : ([] : List (List (Nat × List UInt64))).map grpShape = [].map grpShape)
  | cons n ns ih =>
    intro c c' h
    have i1 : (regroup ns (c.drop n)).map grpShape = (regroup ns (c'.drop n)).map grpShape := ih (h.drop n)
    have i0 : (c.take n).map colShape = (c'.take n).map colShape := h.take n
    show grpShape ((c.take n).map fun x => (x.2.1, x.2.2)) :: (regroup ns (c.drop n)).map grpShape =
      grpShape ((c'.take n).map fun x => (x.2.1, x.2.2)) :: (regroup ns (c'.drop n)).map grpShape
    rw [grpShape_cols, grpShape_cols, i0, i1]

/-- Outcomes of a step that are alike under wStep w are alike as steps. -/
theorem alikeStep_of {r r' : Except String (σ × Nat)} (h : AlikeE (wStep w) r r') : AlikeStep w r r' := by
  rcases h.split with ⟨e, h1, h2⟩ | ⟨a, a', h1, h2, ha⟩
  · subst h1 h2
    exact (rfl : e = e)
  · subst h1 h2
    obtain ⟨t, k⟩ := a
    obtain ⟨t', k'⟩ := a'
    exact Prod.mk.inj ha

/-- **The bridge**: a member whose decide has like outcomes keeps. -/
theorem keeps_of_decides2 {b : Block σ Cl} (h : Decides2 w b) (ft : Nat) : Keeps w ft b := by
  intro s s' rs c c' hs hc
  have e : ∀ n, (c.take n).map (fun x : OpenedColumn => (x.1, x.2.1, x.2.2.length)) =
      (c'.take n).map (fun x : OpenedColumn => (x.1, x.2.1, x.2.2.length)) := fun n => hc.take n
  refine alikeStep_of ?_
  unfold VerifiableInference.Desc.Block.step
  refine AlikeE.head' fun _ => ?_
  refine AlikeE.head_eq' (by rw [e]) fun _ => ?_
  refine AlikeE.bind' (h s s' _ _ _ hs (regroup_sameG _ (hc.take _))) fun t t' ht => ?_
  refine AlikeE.ok ?_
  show (w t, _) = (w t', _)
  rw [ht]

/-! ## 2 A link's claims -/

/-- One run of claims, with the test behind it, has like outcomes from like states with equal claims so far. -/
theorem claimsInStep2 (each : Nat × String → List Cl → σ → Except String Unit) (bs : List (Block σ Cl))
    (hb : ∀ b ∈ bs, Whole2 w b) (he : ∀ o cl, Test2 w (each o cl)) (o : Nat × String) (x x' : List Cl × σ)
    (hx : wCl w x = wCl w x') : AlikeE (wCl w) (claimsInStep each bs x o) (claimsInStep each bs x' o) := by
  have hx1 : x'.1 = x.1 := (Prod.mk.inj hx).1.symm
  have hx2 : w x.2 = w x'.2 := (Prod.mk.inj hx).2
  unfold claimsInStep
  refine AlikeE.head_ok fun run hrun => ?_
  have ho := VerifiableInference.Desc.Keeps.named_ok hrun
  cases hq : bs[o.1]? with
  | none => simp [hq] at ho
  | some b =>
    simp only [hq, Option.bind_some] at ho
    obtain ⟨n, hn⟩ := VerifiableInference.Desc.Keeps.lookup_mem _ _ _ ho
    have A : AlikeE (wCl w) (run x.1.length x.2) (run x.1.length x'.2) :=
      (hb b (List.mem_of_getElem? hq)).2.1 (n, run) hn x.1.length x.2 x'.2 hx2
    rw [hx1]
    rcases A.split with ⟨e, a1, a2⟩ | ⟨y, y', a1, a2, hy⟩
    · simp only [a1, a2]
      exact AlikeE.error _
    · have hy1 : y'.1 = y.1 := (Prod.mk.inj hy).1.symm
      have hy2 : w y.2 = w y'.2 := (Prod.mk.inj hy).2
      have B : each o y.1 y.2 = each o y.1 y'.2 := (he o y.1).same hy2
      simp only [a1, a2, hy1, B]
      cases each o y.1 y'.2 with
      | error e => exact AlikeE.error _
      | ok u =>
        refine AlikeE.ok ?_
        show (x.1 ++ y.1, w y.2) = (x.1 ++ y.1, w y'.2)
        rw [hy2]

/-- **The gathering of a link's claims** returns equal claims and like states at states that are one under w. -/
theorem claimsInBy2 (each : Nat × String → List Cl → σ → Except String Unit) (bs : List (Block σ Cl))
    (hb : ∀ b ∈ bs, Whole2 w b) (he : ∀ o cl, Test2 w (each o cl)) (order : List (Nat × String)) :
    FnCl2 w (claimsInBy each bs order) := by
  have key : ∀ (order : List (Nat × String)) (acc acc' : Except String (List Cl × σ)),
      AlikeE (wCl w) acc acc' →
        AlikeE (wCl w) (order.foldl (fun acc o => acc.bind fun x => claimsInStep each bs x o) acc)
          (order.foldl (fun acc o => acc.bind fun x => claimsInStep each bs x o) acc') := by
    intro order
    induction order with
    | nil =>
      intro acc acc' h
      exact h
    | cons o os ih =>
      intro acc acc' h
      rw [List.foldl_cons, List.foldl_cons]
      exact ih _ _ (h.bind fun x x' hx => claimsInStep2 each bs hb he o x x' hx)
  intro s s' hs
  unfold claimsInBy
  refine key order _ _ (AlikeE.ok ?_)
  show (([] : List Cl), w s) = ([], w s')
  rw [hs]

/-! ## 3 The runs behind the batching -/

/-- One run behind the batching has like outcomes from like outcomes so far. -/
theorem stepA2 (bs : List (Block σ Cl)) (hb : ∀ b ∈ bs, Whole2 w b) (o : Nat × String)
    {acc acc' : Except String σ} (h : AlikeE w acc acc') :
    AlikeE w (VerifiableInference.Desc.Keeps.stepA bs acc o) (VerifiableInference.Desc.Keeps.stepA bs acc' o) := by
  unfold VerifiableInference.Desc.Keeps.stepA
  refine h.bind fun x x' hx => ?_
  refine AlikeE.head_ok fun run hrun => ?_
  have ho := VerifiableInference.Desc.Keeps.named_ok hrun
  cases hq : bs[o.1]? with
  | none => simp [hq] at ho
  | some b =>
    simp only [hq, Option.bind_some] at ho
    obtain ⟨n, hn⟩ := VerifiableInference.Desc.Keeps.lookup_mem _ _ _ ho
    have A : AlikeE w (run x) (run x') := (hb b (List.mem_of_getElem? hq)).2.2 (n, run) hn x x' hx
    rcases A.split with ⟨e, a1, a2⟩ | ⟨y, y', a1, a2, hy⟩
    · simp only [a1, a2]
      exact AlikeE.error _
    · simp only [a1, a2]
      exact AlikeE.ok hy

/-- **The runs behind the batching** have like outcomes at states that are one under w. -/
theorem afterIn2 (bs : List (Block σ Cl)) (hb : ∀ b ∈ bs, Whole2 w b) (order : List (Nat × String)) :
    Fn2 w (afterIn bs order) := by
  have key : ∀ (order : List (Nat × String)) (acc acc' : Except String σ), AlikeE w acc acc' →
      AlikeE w (order.foldl (VerifiableInference.Desc.Keeps.stepA bs) acc)
        (order.foldl (VerifiableInference.Desc.Keeps.stepA bs) acc') := by
    intro order
    induction order with
    | nil =>
      intro acc acc' h
      exact h
    | cons o os ih =>
      intro acc acc' h
      rw [List.foldl_cons, List.foldl_cons]
      exact ih _ _ (stepA2 bs hb o h)
  intro s s' hs
  rw [VerifiableInference.Desc.Keeps.afterIn_eq, VerifiableInference.Desc.Keeps.afterIn_eq]
  exact key order _ _ (AlikeE.ok hs)

/-! ## 4 The link -/

/-- What is asked of a link's parts. -/
def LinkKeeps2 (w : σ → σ) (L : Link σ Cl) : Prop :=
  Fn2 w L.lay ∧ (∀ b ∈ L.hear, Whole2 w b) ∧ (∀ o cl, Test2 w (L.each o cl)) ∧ Test2 w L.tests ∧
    (∀ f, FnCl2 w f → Decides2 w (L.batch f)) ∧ (∀ b ∈ L.close, Decides2 w b) ∧ Fn2 w L.clear

/-- The frame's step behind the batching has like outcomes at states that are one under w. -/
theorem runBehind2 {L : Link σ Cl} (h : LinkKeeps2 w L) : Fn2 w L.runBehind := by
  obtain ⟨_, hh, _, ht, _, _, _⟩ := h
  intro s s' hs
  have B : L.tests s = L.tests s' := ht.same hs
  unfold VerifiableInference.Desc.Link.runBehind
  rw [B]
  cases L.tests s' with
  | error e => exact AlikeE.error _
  | ok u => exact afterIn2 L.hear hh L.orderAfter s s' hs

/-- **Every member of a link's flat list has like outcomes.** -/
theorem link_flat_keeps2 (L : Link σ Cl) (h : LinkKeeps2 w L) : ∀ b ∈ L.blocksInOrder, Decides2 w b := by
  have hrb := runBehind2 h
  obtain ⟨hl, hh, he, _, hbt, hc, hcl⟩ := h
  intro b hb
  unfold VerifiableInference.Desc.Link.blocksInOrder at hb
  rcases List.mem_append.1 hb with h | h
  · rcases List.mem_append.1 h with h | h
    · rcases List.mem_append.1 h with h | h
      · rcases List.mem_cons.1 h with rfl | h
        · exact fun s s' _ _ _ hs _ => hl s s' hs
        · exact (hh b h).1
      · rcases List.mem_cons.1 h with rfl | h
        · exact hbt _ (claimsInBy2 L.each L.hear hh he L.order)
        · rcases List.mem_cons.1 h with rfl | h
          · exact fun s s' _ _ _ hs _ => hrb s s' hs
          · cases h
    · exact hc b h
  · rcases List.mem_cons.1 h with rfl | h
    · exact fun s s' _ _ _ hs _ => hcl s s' hs
    · cases h

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.grpShape_cols
#print axioms ProofFile.Honest.K10.regroup_sameG
#print axioms ProofFile.Honest.K10.alikeStep_of
#print axioms ProofFile.Honest.K10.keeps_of_decides2
#print axioms ProofFile.Honest.K10.claimsInStep2
#print axioms ProofFile.Honest.K10.claimsInBy2
#print axioms ProofFile.Honest.K10.stepA2
#print axioms ProofFile.Honest.K10.afterIn2
#print axioms ProofFile.Honest.K10.LinkKeeps2
#print axioms ProofFile.Honest.K10.runBehind2
#print axioms ProofFile.Honest.K10.link_flat_keeps2
