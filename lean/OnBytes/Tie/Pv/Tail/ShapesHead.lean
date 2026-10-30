-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Tail/ShapesHead.lean: the shapes of the tables of the head's sub-proof (of each table
its matrix, the rows in a block and the first entry in the vector of reads) are a term of the public
numbers and of the plan record's matrices' sizes; so the tables of every run at that plan record
have the shapes of the dry run on zeros. It does for the head what ShapesLay.lean does for the
layers, with the kit of that file.

By the verifier's text (`tablesOf`, `addFun`, OnBytes/Model/HeadTables.lean) the head has fifteen
tables in a fixed order. Of each, the first matrix, the number of parts and the rows in a block are
public numbers of the shape h; `addFun` places the parts one behind the other by the sizes of the
matrices `hp.tl.mats`. Of a table the weights alone hang on what was heard or on the covered
positions.

Main names (namespace OnBytes.Tie.Pv.Tail.Closed):
  `partShapes`, `asksShapes`, `headAsks h`, `headShapes h mats`: the term.
  `foldParts`, `addFun_shapes`, `foldAsks`: where the plain routines return tables, these have the
    term's shapes, behind those that stood before, and lie in the third vector.
  `ret_getAs`: one more law of `Ret`: behind a value that must be there under a name.
  `tablesOf_shapes`: every success of `tablesOf`, in a dry run or on a view, lays out tables with
    the shapes `headShapes h hp.tl.mats`, in the third vector. No hypothesis but the success.
  `shAt_head`: the dry run on zeros, where it returns, has the term's shapes.
  `run_shapes_head`: at the head's link of a chain whose dry run returns: every success of
    `tablesOf` at the chain's shape and plan record, at any layout, covered positions and heard
    values, from every state and context: its tables have the shapes `shAt c n`, and they are
    `funsOf (shAt c n)` at their own weights.
  `head_same`: so `SameShapes (recAt c n) t.funs`.
The hypotheses of the last three: hA, hH: the link's kind is "H" and not "A"; h: the dry run
returns. Besides, in the last two: hr, the success.

Limits: those of ShapesLay.lean, word for word, on the weights, on the link's record, on the first
columns and the drawn matrix. The shape and the plan record are the chain's own, `c.X.hS` and
`c.X.H`: unlike the layers' term this one reads the plan record (its matrices' sizes). By the
verifier's text (OnBytes/Model/VerifyLinks.lean) these two are what the head's check is called at;
that is not shown here. That `headAsks` is the list of `tablesOf` is checked where this file
compiles: the two are one by unfolding. Attention's tables are not looked at.

-/
import OnBytes.Tie.Pv.Tail.ShapesLay

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Tail.Closed
open OnBytes OnBytes.Model OnBytes.Tie.Pv.Tail Cb.Pv.Tail OnBytes.L5

/-! ## The term -/

/-- The shapes of the parts qs of one table from entry p on, and the first free entry behind. -/
def partShapes (mats : Array TMat) (M0 Lf : Nat) : List Nat → Nat → List Tab × Nat
  | [], p => ([], p)
  | q :: qs, p =>
    let r := partShapes mats M0 Lf qs
      (p + (mats.getD (M0 + q) {}).k * ((mats.getD (M0 + q) {}).m / Lf))
    (⟨M0 + q, Lf, p⟩ :: r.1, r.2)

/-- The shapes of a list of tables, each given by its first matrix, its number of parts and its
rows in a block, one behind the other from entry p on. -/
def asksShapes (mats : Array TMat) : List (Nat × Nat × Nat) → Nat → List Tab
  | [], _ => []
  | a :: l, p =>
    (partShapes mats a.1 a.2.2 (List.range a.2.1) p).1 ++
      asksShapes mats l (partShapes mats a.1 a.2.2 (List.range a.2.1) p).2

/-- The head's fifteen tables: of each its first matrix, its parts and its rows in a block. -/
def headAsks (h : Head.Shape) : List (Nat × Nat × Nat) :=
  [(0, h.NHf, 2 ^ h.la), (0, h.NHf, 2 ^ h.la), (h.NHf + 1 + 1 + 1, 1, 2 ^ h.la),
   (h.NHf + 1 + 1 + 1, 1, 2 ^ h.la), (h.NHf, 1, h.T), (h.NHf, 1, h.T), (h.NHf + 1, 1, h.T),
   (h.NHf + 1, 1, h.T), (h.NHf + 1, 1, h.T), (h.NHf + 1, 1, h.T), (h.NHf + 1, 1, h.T),
   (h.NHf + 1, 1, h.T), (h.NHf + 1 + 1, 1, 2 ^ h.lmbH), (h.NHf + 1 + 1, 1, 2 ^ h.lmbH),
   (h.NHf + 1 + 1, 1, 2 ^ h.lmbH)]

/-- The shapes of the tables of the head's sub-proof: a term of the public numbers and of the
matrices' sizes. -/
def headShapes (h : Head.Shape) (mats : Array TMat) : List Tab := asksShapes mats (headAsks h) 0

/-! ## The plain routine -/

/-- One table more. -/
theorem shapesOf_push (a : Array HFun) (Fn : HFun) :
    shapesOf (a.push Fn) = shapesOf a ++ [(⟨Fn.mat, Fn.len, Fn.start⟩ : Tab)] := by
  unfold shapesOf
  rw [Array.toList_push, List.map_append]
  rfl

/-- The parts of one table, added one after the other. -/
theorem foldParts (mats : Array TMat) (M0 Lf : Nat) (phi : Array E) :
    ∀ (qs : List Nat) (s : Array HFun × Nat),
      shapesOf (qs.foldl (fun (s : Array HFun × Nat) q =>
          (s.1.push { mat := M0 + q, len := Lf, phi := phi, tree := 2, start := s.2 },
            s.2 + (mats.getD (M0 + q) {}).k * ((mats.getD (M0 + q) {}).m / Lf))) s).1 =
        shapesOf s.1 ++ (partShapes mats M0 Lf qs s.2).1 ∧
      (qs.foldl (fun (s : Array HFun × Nat) q =>
          (s.1.push { mat := M0 + q, len := Lf, phi := phi, tree := 2, start := s.2 },
            s.2 + (mats.getD (M0 + q) {}).k * ((mats.getD (M0 + q) {}).m / Lf))) s).2 =
        (partShapes mats M0 Lf qs s.2).2 ∧
      ((∀ Fn ∈ s.1.toList, Fn.tree = 2) →
        ∀ Fn ∈ (qs.foldl (fun (s : Array HFun × Nat) q =>
          (s.1.push { mat := M0 + q, len := Lf, phi := phi, tree := 2, start := s.2 },
            s.2 + (mats.getD (M0 + q) {}).k * ((mats.getD (M0 + q) {}).m / Lf))) s).1.toList,
          Fn.tree = 2)
  | [], s => ⟨(List.append_nil _).symm, rfl, fun h => h⟩
  | q :: qs, s => by
    obtain ⟨i1, i2, i3⟩ := foldParts mats M0 Lf phi qs
      (s.1.push { mat := M0 + q, len := Lf, phi := phi, tree := 2, start := s.2 },
        s.2 + (mats.getD (M0 + q) {}).k * ((mats.getD (M0 + q) {}).m / Lf))
    rw [List.foldl_cons]
    refine ⟨?_, i2, fun h => i3 ?_⟩
    · rw [i1, shapesOf_push, List.append_assoc]
      rfl
    · intro Fn hFn
      rw [Array.toList_push, List.mem_append] at hFn
      rcases hFn with h1 | h1
      · exact h Fn h1
      · rw [List.mem_singleton.1 h1]

/-- One table added. -/
theorem addFun_shapes {mats : Array TMat} {t t' : Head.Tables} {M0 parts Lf : Nat} {phi : Array E}
    {nm : String} (h : Head.addFun mats t M0 parts Lf phi nm = some t') :
    shapesOf t'.funs = shapesOf t.funs ++ (partShapes mats M0 Lf (List.range parts) t.p).1 ∧
      t'.p = (partShapes mats M0 Lf (List.range parts) t.p).2 ∧
      ((∀ Fn ∈ t.funs.toList, Fn.tree = 2) → ∀ Fn ∈ t'.funs.toList, Fn.tree = 2) := by
  unfold Head.addFun at h
  dsimp only at h
  split at h
  · cases h
  · obtain rfl := Option.some.inj h
    exact foldParts mats M0 Lf phi (List.range parts) (t.funs, t.p)

/-- All tables added, one after the other. -/
theorem foldAsks (mats : Array TMat) :
    ∀ (asks : List (Nat × Nat × Nat × Array E × String)) (t t' : Head.Tables),
      asks.foldlM (fun t a => Head.addFun mats t a.1 a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2) t =
        some t' →
      shapesOf t'.funs =
          shapesOf t.funs ++ asksShapes mats (asks.map fun a => (a.1, a.2.1, a.2.2.1)) t.p ∧
        ((∀ Fn ∈ t.funs.toList, Fn.tree = 2) → ∀ Fn ∈ t'.funs.toList, Fn.tree = 2)
  | [], t, t', h => by
    rw [List.foldlM_nil] at h
    obtain rfl := Option.some.inj h
    exact ⟨(List.append_nil _).symm, fun k => k⟩
  | a :: asks, t, t', h => by
    rw [List.foldlM_cons] at h
    cases h1 : Head.addFun mats t a.1 a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2 with
    | none =>
      rw [h1] at h
      cases h
    | some t1 =>
      rw [h1] at h
      obtain ⟨j1, j2, j3⟩ := addFun_shapes h1
      obtain ⟨i1, i2⟩ := foldAsks mats asks t1 t' h
      refine ⟨?_, fun k => i2 (j3 k)⟩
      rw [i1, j1, j2, List.append_assoc]
      rfl

/-! ## Every success of the routine -/

/-- Behind a value that must be there, under a name: it was there. -/
theorem ret_getAs {α β : Type} {Q : β → Prop} (name : String) (x : Option α) (f : α → SubM β)
    (h : ∀ a, x = some a → Ret Q (f a)) :
    Ret Q ((liftM (Head.getAs name x) : SubM α) >>= f) := by
  intro F c b F' c' hr
  obtain ⟨a, F1, c1, h1, h2⟩ := (Port.bind_ok _ f F c _).1 hr
  have h3 := ((Port.lift_ok _ F F1 c c1 a).1 h1).1
  cases x with
  | none => cases h3
  | some a' =>
    cases h3
    exact h _ rfl F1 _ b F' c' h2

/-- Every success of tablesOf, dry or on a view, lays out tables with the term's shapes. -/
theorem tablesOf_ret (h : Head.Shape) (L : Head.HL) (hp : Head.HPlanH2) (cov : Head.Covered)
    (x : Head.Heard) :
    Ret (fun t : Head.Tables =>
        shapesOf t.funs = headShapes h hp.tl.mats ∧ ∀ Fn ∈ t.funs.toList, Fn.tree = 2)
      (Head.tablesOf h L hp cov x) := by
  unfold Head.tablesOf
  repeat' first
    | refine ret_getAs _ _ _ fun _ _ => ?_
    | refine ret_bind _ _ fun _ => ?_
  refine ret_pure _ ?_
  rename_i t ht _
  obtain ⟨s1, s2⟩ := foldAsks _ _ _ _ ht
  exact ⟨s1, s2 fun _ k => absurd k List.not_mem_nil⟩

/-- The same, of one success. -/
theorem tablesOf_shapes {h : Head.Shape} {L : Head.HL} {hp : Head.HPlanH2} {cov : Head.Covered}
    {x : Head.Heard} {F F' : Fork} {c c' : Ctx} {t : Head.Tables}
    (hr : Head.tablesOf h L hp cov x F c = .ok ((t, F'), c')) :
    shapesOf t.funs = headShapes h hp.tl.mats ∧ ∀ Fn ∈ t.funs.toList, Fn.tree = 2 :=
  tablesOf_ret h L hp cov x F c t F' c' hr

/-! ## The dry run on zeros, and the debt -/

/-- The dry run on zeros, where it returns, has the term's shapes. -/
theorem shAt_head {c : Plan.Chain1} {n : Plan.LinkNums} {x : Array HFun × Nat}
    (hA : (n.kind == "A") = false) (hH : (n.kind == "H") = true)
    (h : Plan.funsOf c n = .ok x) : shAt c n = headShapes c.X.hS c.X.H.tl.mats := by
  rw [shAt_ok h]
  unfold Plan.funsOf at h
  simp only [hA, hH, Bool.false_eq_true, if_false, if_true] at h
  have q : Ret (fun f : Array HFun => shapesOf f = headShapes c.X.hS c.X.H.tl.mats)
      (do
        let x ← Head.hear c.X.hS c.X.HLy c.X.H default #[zeroE]
        let t ← Head.tablesOf c.X.hS c.X.HLy c.X.H default x
        pure t.funs) := by
    refine ret_bind _ _ fun y => ?_
    intro F d f F' d' hr
    obtain ⟨t, F1, d1, h1, h2⟩ := (Port.bind_ok _ _ F d _).1 hr
    have e := (HasRuns.runs_pure (m := SubM) (a := t.funs) (b := f) (s := (F1, d1))
      (s' := (F', d')) h2).1
    rw [e]
    exact (tablesOf_shapes h1).1
  exact dry_ret q h

/-- At the head's link of a chain whose dry run returns: every success of tablesOf at the chain's
public numbers and plan record lays out tables with the dry run's shapes. -/
theorem run_shapes_head {c : Plan.Chain1} {n : Plan.LinkNums} {x : Array HFun × Nat}
    (hA : (n.kind == "A") = false) (hH : (n.kind == "H") = true) (h : Plan.funsOf c n = .ok x)
    {L : Head.HL} {cov : Head.Covered} {y : Head.Heard} {F F' : Fork} {d d' : Ctx}
    {t : Head.Tables} (hr : Head.tablesOf c.X.hS L c.X.H cov y F d = .ok ((t, F'), d')) :
    shapesOf t.funs = shAt c n ∧
      t.funs = funsOf (shAt c n) fun k => (t.funs.toList.getD k {}).phi := by
  obtain ⟨s1, s2⟩ := tablesOf_shapes hr
  have e : shapesOf t.funs = shAt c n := s1.trans (shAt_head hA hH h).symm
  exact ⟨e, by rw [← e]; exact (funsOf_self t.funs s2).symm⟩

/-- So the run's tables have the closed record's shapes. -/
theorem head_same {c : Plan.Chain1} {n : Plan.LinkNums} {x : Array HFun × Nat}
    (hA : (n.kind == "A") = false) (hH : (n.kind == "H") = true) (h : Plan.funsOf c n = .ok x)
    {L : Head.HL} {cov : Head.Covered} {y : Head.Heard} {F F' : Fork} {d d' : Ctx}
    {t : Head.Tables} (hr : Head.tablesOf c.X.hS L c.X.H cov y F d = .ok ((t, F'), d')) :
    SameShapes (recAt c n) t.funs :=
  (run_shapes_head hA hH h hr).1.trans (funsL_shapes (shAt c n) _).symm

end OnBytes.Tie.Pv.Tail.Closed

#print axioms OnBytes.Tie.Pv.Tail.Closed.foldParts
#print axioms OnBytes.Tie.Pv.Tail.Closed.addFun_shapes
#print axioms OnBytes.Tie.Pv.Tail.Closed.foldAsks
#print axioms OnBytes.Tie.Pv.Tail.Closed.ret_getAs
#print axioms OnBytes.Tie.Pv.Tail.Closed.tablesOf_shapes
#print axioms OnBytes.Tie.Pv.Tail.Closed.shAt_head
#print axioms OnBytes.Tie.Pv.Tail.Closed.run_shapes_head
#print axioms OnBytes.Tie.Pv.Tail.Closed.head_same
