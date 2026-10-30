-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Tail/ShapesLay.lean: the shapes of the tables of a layers' sub-proof (of each table
its matrix, the rows in a block and the first entry in the vector of reads) are a term of the public
record; so the tables of every run have the shapes of the dry run on zeros.

The closed record of a smallness test at a link (`recAt`, ClosedPlace.lean) takes its list of shapes
from a dry run on zeros (`Plan.funsOf`, OnBytes/Tie/Pv/Plan/PlaceTabs.lean). By the verifier's text
(`hearOwn`, OnBytes/Model/Layer.lean) the tables are placed by `layTables` at the matrices' sizes
and the group's families of tables, which are plain functions of the public record
(OnBytes/Model/LayerForms.lean); `Layer.funsOf` then gives each placed table its weights and copies
matrix, block and first entry. Of a table the weights alone hang on what was heard.

Main names (namespace OnBytes.Tie.Pv.Tail.Closed):
  `laidShapes`, `layShapes P g`: the term. `layShapes_tokens`: it does not read the tokens.
  `funs_shapes`: where `Layer.funsOf` returns tables, they have the placed families' shapes and lie
    in the third vector.
  `Ret Q x`: every success of the routine x, from every state and every context, returns a value
    with Q. `ret_bind`, `ret_form`, `ret_ite`, `ret_pure`: its four laws. No law on what a called
    routine does is needed: `ret_bind` asks nothing of the first routine.
  `hearOwn_shapes`: every success of `hearOwn`, in a dry run or on a view, lays out tables with the
    shapes `layShapes P g`, in the third vector. No hypothesis but the success.
  `runNamed_ok`, `dry_ret`: what a dry run returns is the value of a success.
  `shAt_lay`: the dry run on zeros, where it returns, has the term's shapes.
  `run_shapes_lay`: at a layers' link of a chain whose dry run returns: every success of `hearOwn`
    at the chain's public record with any tokens, at any plan record, from every state and context:
    its tables have the shapes `shAt c n`, and they are `funsOf (shAt c n)` at their own weights.
  `layCut_same`: so at the cut of a run of the link's check (`LayCut`,
    OnBytes/Tie/Pv/Keeps/LayerCut.lean): `SameShapes (recAt c n) o.funs`.
The hypotheses of the last three: hA, hH: the link's kind is neither "A" nor "H"; hG: the chain's
public record has a plan record hp for the link's group; h: the dry run returns (hG follows from h;
it names hp). Besides, in `run_shapes_lay`: hr, the success; in `layCut_same`: cut.

Limits: where the dry run fails `shAt` is empty and nothing is said. Nothing on the weights: the
second half of `run_shapes_lay` has the run's own weights on its right side. It is not the equation
on the tables of a typed statement that a later file's theorem asks as a premise, which is met by
unfolding: it serves where a typed statement's weights are shown to be the run's, below the list's
length; that is shown nowhere. Not said: that the link's record `n.tail` is `hp.tl`; that the
public record of an accepted run is the chain's with the request's tokens (by the verifier's text,
OnBytes/Model/VerifyLinks.lean, it is); anything on the first columns or the drawn matrix. The
layers alone: by the text the head's tables are placed at public numbers too (`addFun`,
OnBytes/Model/HeadTables.lean); attention's hang besides on the number of score units that were
heard (`placeAll`, OnBytes/Model/AttentionTables.lean). Neither is shown here.

-/
import OnBytes.Tie.Pv.Keeps.LayerCut
import OnBytes.Tie.Pv.Tail.EndRun
import OnBytes.Tie.Pv.Tail.ClosedPlace

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Tail.Closed
open OnBytes OnBytes.Model OnBytes.Tie.Pv.Tail Cb.Pv.Tail OnBytes.L5 OnBytes.L5.LayerCut

/-! ## The term -/

/-- The shapes of the tables of a list of laid families: for each family, for each of its parts, the
part's matrix, the family's rows in a block, the part's first entry. -/
def laidShapes (laid : List (Layer.TableAsk × List (Nat × Nat))) : List Tab :=
  laid.flatMap fun x => x.2.map fun m => (⟨m.1, x.1.L, m.2⟩ : Tab)

/-- The shapes of the tables of the layers' sub-proof of group g: a term of the public record. -/
def layShapes (P : Layer.Pub) (g : Nat) : List Tab :=
  match Layer.layTables ((P.tails.getD g {}).mats.map fun M => (M.m, M.k))
      (Layer.tableAsks P.y P.rd g) 0 with
  | some x => laidShapes x.2.1
  | none => []

/-- It does not read the tokens. -/
theorem layShapes_tokens (P : Layer.Pub) (z : Array Nat) (g : Nat) :
    layShapes { P with tokv := z } g = layShapes P g := rfl

/-! ## The plain routine -/

/-- The tables of one family. -/
def famFuns (y : Layer.Lay) (fo : Forest.Heard) (pt : List (String × Array E))
    (x : Layer.TableAsk × List (Nat × Nat)) : Option (List HFun) := do
  let phi ← Layer.phiOf y fo pt x.1
  pure (x.2.map fun m => ({ mat := m.1, len := x.1.L, phi, tree := 2, start := m.2 } : HFun))

/-- They have the family's shapes and lie in the third vector. -/
theorem famFuns_shapes {y : Layer.Lay} {fo : Forest.Heard} {pt : List (String × Array E)}
    {x : Layer.TableAsk × List (Nat × Nat)} {b : List HFun} (h : famFuns y fo pt x = some b) :
    (b.map fun Fn : HFun => (⟨Fn.mat, Fn.len, Fn.start⟩ : Tab)) =
        x.2.map (fun m => (⟨m.1, x.1.L, m.2⟩ : Tab)) ∧ ∀ Fn ∈ b, Fn.tree = 2 := by
  unfold famFuns at h
  cases hp : Layer.phiOf y fo pt x.1 with
  | none =>
    rw [hp] at h
    cases h
  | some phi =>
    rw [hp] at h
    obtain rfl := Option.some.inj h
    refine ⟨?_, ?_⟩
    · rw [List.map_map]
      rfl
    · intro Fn hFn
      obtain ⟨m, _, rfl⟩ := List.mem_map.1 hFn
      rfl

/-- The same of all families, one after the other. -/
theorem mapM_shapes (y : Layer.Lay) (fo : Forest.Heard) (pt : List (String × Array E)) :
    ∀ (laid : List (Layer.TableAsk × List (Nat × Nat))) (l : List (List HFun)),
      laid.mapM (famFuns y fo pt) = some l →
      (l.flatten.map fun Fn : HFun => (⟨Fn.mat, Fn.len, Fn.start⟩ : Tab)) = laidShapes laid ∧
        ∀ Fn ∈ l.flatten, Fn.tree = 2
  | [], l, h => by
    rw [List.mapM_nil] at h
    obtain rfl := Option.some.inj h
    exact ⟨rfl, fun _ hh => absurd hh List.not_mem_nil⟩
  | x :: laid, l, h => by
    rw [List.mapM_cons] at h
    cases hb : famFuns y fo pt x with
    | none =>
      rw [hb] at h
      cases h
    | some b =>
      rw [hb] at h
      cases hbs : laid.mapM (famFuns y fo pt) with
      | none =>
        have h' : (laid.mapM (famFuns y fo pt) >>= fun bs => pure (b :: bs)) = some l := h
        rw [hbs] at h'
        cases h'
      | some bs =>
        have h' : (laid.mapM (famFuns y fo pt) >>= fun bs => pure (b :: bs)) = some l := h
        rw [hbs] at h'
        obtain rfl := Option.some.inj h'
        obtain ⟨i1, i2⟩ := mapM_shapes y fo pt laid bs hbs
        obtain ⟨j1, j2⟩ := famFuns_shapes hb
        refine ⟨?_, ?_⟩
        · rw [List.flatten_cons, List.map_append, i1, j1]
          unfold laidShapes
          rw [List.flatMap_cons]
        · intro Fn hFn
          rw [List.flatten_cons, List.mem_append] at hFn
          rcases hFn with h1 | h1
          · exact j2 Fn h1
          · exact i2 Fn h1

/-- The routine that gives the laid families their weights keeps their shapes. -/
theorem funs_shapes {y : Layer.Lay} {fo : Forest.Heard} {pt : List (String × Array E)}
    {laid : List (Layer.TableAsk × List (Nat × Nat))} {funs : Array HFun}
    (h : Layer.funsOf y fo pt laid = some funs) :
    shapesOf funs = laidShapes laid ∧ ∀ Fn ∈ funs.toList, Fn.tree = 2 := by
  have h' : (laid.mapM (famFuns y fo pt) >>= fun l => pure l.flatten.toArray) = some funs := h
  cases hl : laid.mapM (famFuns y fo pt) with
  | none =>
    rw [hl] at h'
    cases h'
  | some l =>
    rw [hl] at h'
    obtain rfl := Option.some.inj h'
    exact mapM_shapes y fo pt laid l hl

/-! ## Every success's value -/

/-- Every success of x, from every state and every context, returns a value with Q. -/
def Ret {α : Type} (Q : α → Prop) (x : SubM α) : Prop :=
  ∀ (F : Fork) (c : Ctx) (a : α) (F' : Fork) (c' : Ctx), x F c = .ok ((a, F'), c') → Q a

/-- One routine after another: nothing is asked of the first. -/
theorem ret_bind {α β : Type} {Q : β → Prop} (x : SubM α) (f : α → SubM β)
    (h : ∀ a, Ret Q (f a)) : Ret Q (x >>= f) := by
  intro F c b F' c' hr
  obtain ⟨a, F1, c1, _, h2⟩ := (Port.bind_ok x f F c _).1 hr
  exact h a F1 c1 b F' c' h2

/-- Behind a value that must be there: it was there. -/
theorem ret_form {α β : Type} {Q : β → Prop} (x : Option α) (f : α → SubM β)
    (h : ∀ a, x = some a → Ret Q (f a)) : Ret Q (Layer.form x >>= f) := by
  intro F c b F' c' hr
  obtain ⟨a, F1, c1, h1, h2⟩ := (Port.bind_ok _ f F c _).1 hr
  exact h a ((Port.get_ok x F F1 c c1 a).1 h1).1 F1 c1 b F' c' h2

/-- A routine that only returns a value. -/
theorem ret_pure {α : Type} {Q : α → Prop} (a : α) (h : Q a) : Ret Q (pure a : SubM α) := by
  intro F c b F' c' hr
  have e := (HasRuns.runs_pure (m := SubM) (a := a) (b := b) (s := (F, c)) (s' := (F', c')) hr).1
  rw [e]
  exact h

/-- Either of two routines. -/
theorem ret_ite {α : Type} {Q : α → Prop} (c : Prop) [Decidable c] (x y : SubM α) (hx : Ret Q x)
    (hy : Ret Q y) : Ret Q (if c then x else y) := by
  split
  · exact hx
  · exact hy

/-- Every success of hearOwn, dry or on a view, lays out tables with the term's shapes. -/
theorem hearOwn_ret (P : Layer.Pub) (hp : Layer.HPlan2) (g : Nat) (fo : Forest.Heard) :
    Ret (fun o : Layer.Own => shapesOf o.funs = layShapes P g ∧ ∀ Fn ∈ o.funs.toList, Fn.tree = 2)
      (Layer.hearOwn P hp g fo) := by
  unfold Layer.hearOwn
  refine ret_bind _ _ fun iU3 => ?_
  refine ret_bind _ _ fun H0 => ?_
  refine ret_bind _ _ fun H => ?_
  refine ret_bind _ _ fun _ => ?_
  refine ret_form _ _ ?_
  rintro ⟨tab, laid, nU3⟩ hx
  refine ret_bind _ _ fun _ => ?_
  refine ret_bind _ _ fun K => ?_
  refine ret_bind _ _ ?_
  rintro ⟨hd, hd2⟩
  repeat' first
    | refine ret_form _ _ fun _ _ => ?_
    | refine ret_ite _ _ _ ?_ ?_
    | refine ret_bind _ _ fun _ => ?_
  all_goals
    refine ret_pure _ ?_
    rename_i funs hf
    obtain ⟨s1, s2⟩ := funs_shapes hf
    refine ⟨s1.trans ?_, s2⟩
    unfold layShapes
    rw [show Layer.layTables ((P.tails.getD g {}).mats.map fun M => (M.m, M.k))
      (Layer.tableAsks P.y P.rd g) 0 = some (tab, laid, nU3) from hx]

/-- The same, of one success. -/
theorem hearOwn_shapes {P : Layer.Pub} {hp : Layer.HPlan2} {g : Nat} {fo : Forest.Heard}
    {F F' : Fork} {c c' : Ctx} {o : Layer.Own}
    (h : Layer.hearOwn P hp g fo F c = .ok ((o, F'), c')) :
    shapesOf o.funs = layShapes P g ∧ ∀ Fn ∈ o.funs.toList, Fn.tree = 2 :=
  hearOwn_ret P hp g fo F c o F' c' h

/-! ## The dry run on zeros -/

/-- A run from a start that has returned is a success of the block from some context. -/
theorem runNamed_ok {α : Type} {b : Blk α} {s : Start} {dry : Bool} {rounds : List Fmt.RoundView}
    {opened : List (Nat × Nat × List UInt64)} {r : α × Ctx}
    (h : b.runNamed s dry rounds opened = .ok r) : ∃ c0, b c0 = .ok r := by
  unfold Blk.runNamed at h
  split at h
  · exact ⟨_, h⟩
  · cases h

/-- What a dry run of a sub-proof's routine returns has every property of all its successes. -/
theorem dry_ret {α : Type} {Q : α → Prop} {x : SubM α} (hQ : Ret Q x) {F0 : Fork}
    {l : List Params.PlanRound} {r : α × Nat} (h : Plan.dry x F0 l = .ok r) : Q r.1 := by
  unfold Plan.dry at h
  split at h
  · cases h
  · rename_i a G c hr
    obtain ⟨c0, h0⟩ := runNamed_ok hr
    obtain rfl := Except.ok.inj h
    exact hQ F0 c0 a G c h0

/-- The dry run on zeros, where it returns, has the term's shapes. -/
theorem shAt_lay {c : Plan.Chain1} {n : Plan.LinkNums} {hp : Layer.HPlan2} {x : Array HFun × Nat}
    (hA : (n.kind == "A") = false) (hH : (n.kind == "H") = false)
    (hG : c.X.G[n.group]? = some hp) (h : Plan.funsOf c n = .ok x) :
    shAt c n = layShapes c.X.layers n.group := by
  rw [shAt_ok h]
  unfold Plan.funsOf at h
  simp only [hA, hH, hG, Bool.false_eq_true, if_false] at h
  have q : Ret (fun f : Array HFun => shapesOf f = layShapes c.X.layers n.group)
      (do
        let o ← Layer.hearOwn { c.X.layers with tokv := Array.replicate c.X.T 0 } hp n.group
          (← Layer.hearLook c.X.y n.group)
        pure o.funs) := by
    refine ret_bind _ _ fun fo => ?_
    intro F d f F' d' hr
    obtain ⟨o, F1, d1, h1, h2⟩ := (Port.bind_ok _ _ F d _).1 hr
    have e := (HasRuns.runs_pure (m := SubM) (a := o.funs) (b := f) (s := (F1, d1))
      (s' := (F', d')) h2).1
    rw [e]
    exact (hearOwn_shapes h1).1
  exact dry_ret q h

/-! ## The debt -/

/-- At a layers' link of a chain whose dry run returns: every success of hearOwn at the chain's
public record with any tokens lays out tables with the dry run's shapes. -/
theorem run_shapes_lay {c : Plan.Chain1} {n : Plan.LinkNums} {hp : Layer.HPlan2}
    {x : Array HFun × Nat} (hA : (n.kind == "A") = false) (hH : (n.kind == "H") = false)
    (hG : c.X.G[n.group]? = some hp) (h : Plan.funsOf c n = .ok x) {t : Array Nat}
    {hp' : Layer.HPlan2} {fo : Forest.Heard} {F F' : Fork} {d d' : Ctx} {o : Layer.Own}
    (hr : Layer.hearOwn { c.X.layers with tokv := t } hp' n.group fo F d = .ok ((o, F'), d')) :
    shapesOf o.funs = shAt c n ∧
      o.funs = funsOf (shAt c n) fun k => (o.funs.toList.getD k {}).phi := by
  obtain ⟨s1, s2⟩ := hearOwn_shapes hr
  have e : shapesOf o.funs = shAt c n := s1.trans (shAt_lay hA hH hG h).symm
  exact ⟨e, by rw [← e]; exact (funsOf_self o.funs s2).symm⟩

/-- At the cut of an accepted run: the run's tables have the closed record's shapes. -/
theorem layCut_same {c : Plan.Chain1} {n : Plan.LinkNums} {hp : Layer.HPlan2}
    {x : Array HFun × Nat} (hA : (n.kind == "A") = false) (hH : (n.kind == "H") = false)
    (hG : c.X.G[n.group]? = some hp) (h : Plan.funsOf c n = .ok x) {t : Array Nat} {L : LinkCtx}
    {F : Fork} {d : Ctx} {iU3 : Nat} {fo : Forest.Heard} {o : Layer.Own} {F0 F1 F2 F3 : Fork}
    {L3 : LinkCtx} {c1 c2 c3 : Ctx}
    (cut : LayCut { c.X.layers with tokv := t } hp n.group L F d iU3 fo o F0 F1 F2 F3 L3 c1 c2 c3) :
    SameShapes (recAt c n) o.funs :=
  (run_shapes_lay hA hH hG h cut.own).1.trans (funsL_shapes (shAt c n) _).symm

end OnBytes.Tie.Pv.Tail.Closed

#print axioms OnBytes.Tie.Pv.Tail.Closed.funs_shapes
#print axioms OnBytes.Tie.Pv.Tail.Closed.hearOwn_shapes
#print axioms OnBytes.Tie.Pv.Tail.Closed.shAt_lay
#print axioms OnBytes.Tie.Pv.Tail.Closed.run_shapes_lay
#print axioms OnBytes.Tie.Pv.Tail.Closed.layCut_same
