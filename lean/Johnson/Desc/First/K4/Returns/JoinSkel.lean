-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/K4/Returns/JoinSkel.lean: THE LAYERS' OWN ROUNDS (K4): JoinPub FOLLOWS FROM A
TEST ON THE PLAN, AN EQUATION ON THE PADDING KEYS' COUNTS AND FOUR FACTS ON THE LOOKUP's RECORD.
JoinPub (Johnson/Desc/First/K4/Returns/Stack.lean) gathers what the start form of the batched
sumcheck wants of pure functions: the columns' marks, each call's factor and the padding keys'
counts are returned; there are as many factors, and as many weights, as the lookup's shape has
calls; the counts are the shape's own; no factor names a slot. The law that the hearing returns
(hear_returns, Johnson/Desc/First/K4/Returns/Whole.lean) asks it inside its premise HearPub, by way
of StackPub. General laws: nothing is evaluated.

  seq_both, seq_same, map_both, pure_alike, some_alike, foldlM_both   two computations in Option of
                  one build: both return or neither does.
  isMoe_skel, SA_skel, SBA_skel, site_skel, lineGU_skel, lineGUH_skel, lineQK_skel, lineROW_skel,
  lineDD_skel     the like for the functions that Env.line calls, over the library's laws on the
                  readers of the tables (Johnson/Road/K4/Total/SkelReaders.lean), three laws on
                  Option (Johnson/Road/K4/Total/IsSomeKit.lean) and three laws of
                  Johnson/Desc/First/K4/Returns/Pub/Kit.lean.
  **line_skel**   whether the form of a segment's keys is there (Env.line,
                  OnBytes/Model/LayerForms.lean, at any string) hangs on the environment's skeleton
                  (the layout; the tables' places; the columns of the array of the reads) and the
                  two arrays' sizes alone.
  **joinPart_skel**   whether a call's factor in the join is there hangs on the skeleton alone: not
                  on the lookup's points, not on its two elements, not on the columns' marks.
  weighedOf_y, laidOf_y   each of the functions weighedOf and laidOf has one value at two
                  environments of one layout.
  mapM_length     a list that mapM returns is as long as the list that was mapped.
  (envBlank, joinB: THE TEST ON THE PLAN, a function with values in Bool: each call's factor is
                  there, at no point, at the elements 0 and with the array of the columns' marks
                  left empty: their two definitions stand in
                  Johnson/Desc/First/K4/Returns/JoinB.lean.)
  **join_pay**    JoinPub, from: the count of the padding keys that laidLayers makes from the plan
                  (Johnson/Desc/First/Look/Laid.lean, which calls it the host's count) is the
                  layout's own; joinB; and four facts on the lookup's record: its shape has as many
                  calls as the layout; it has as many weights as the layout has calls; its shape's
                  number of trees and its padding counts are the layout's.

Limits. That joinB is true at a plan, and that laidLayers' count is the layout's, are not shown
here. The four facts on the lookup's record are premises. Nothing on soundness, completeness or
hiding.
-/
import Johnson.Desc.First.K4.Returns.Pub.Kit
import Johnson.Desc.First.K4.Returns.JoinB
import Johnson.Desc.First.K4.Returns.JoinSlots
import Johnson.Desc.First.K4.Returns.Points
import Johnson.Desc.First.Look.Laid

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- The library's default instance Scl.ref (the reference scales, Inst/Model/Scl.lean) is switched
off in this file, as in its neighbours: so no statement can take that table of scales unsaid. -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Desc.First.K4.Rt

open OnBytes OnBytes.Model OnBytes.Model.Layer
open OnBytes.Desc.First.K4.Total (EnvSkel bind_same bind_both sumForms_same tabAt_skel U3at_skel
  longA_skel tensorAt_skel shA_skel)
open OnBytes.Desc.First.K4.RtPub (ite_isSome SxsA_skel shSum_skel)

variable {v v₀ : Env}

/-- Two binds in Option return alike, where their first parts return alike and their second parts
return alike at all pairs of arguments. It is bind_both, spelled with >>= as a do-block unfolds. -/
theorem seq_both {α α' β β' : Type} {x : Option α} {y : Option α'} {f : α → Option β}
    {g : α' → Option β'} (hx : x.isSome = y.isSome) (h : ∀ a b, (f a).isSome = (g b).isSome) :
    (x >>= f).isSome = (y >>= g).isSome := bind_both hx h

/-- Two pure values in Option return alike: both are there. -/
theorem pure_alike {α β : Type} (a : α) (b : β) :
    (pure a : Option α).isSome = (pure b : Option β).isSome := rfl

/-- The like for two values under some. -/
theorem some_alike {α β : Type} (a : α) (b : β) : (some a).isSome = (some b).isSome := rfl

/-- At two environments of one skeleton isMoe has one value at every layer. -/
theorem isMoe_skel (S : EnvSkel v v₀) (lam : ℕ) : v.isMoe lam = v₀.isMoe lam := by
  unfold Env.isMoe
  rw [S.y]

/-- Two calls of Env.SA, at two environments of one skeleton and two arrays of weights of one size,
return alike. -/
theorem SA_skel (S : EnvSkel v v₀) {wh wh₀ : Array E} (hw : wh.size = wh₀.size) (X : String)
    (i : ℕ) (Z : String) : (v.SA wh X i Z).isSome = (v₀.SA wh₀ X i Z).isSome := by
  unfold Env.SA
  rw [tensorAt_skel S, hw]
  refine bind_same _ fun x => sumForms_same _ fun xh _ => ?_
  rw [Option.isSome_map, Option.isSome_map]
  exact longA_skel S _ _ _ _

/-- Two calls of Env.SBA, at two environments of one skeleton, return alike, whatever the two arrays
of weights. -/
theorem SBA_skel (S : EnvSkel v v₀) (wh wh₀ : Array E) (a b : ℕ) (X : String) (i : ℕ) (Z : String)
    (x0 : ℕ) : (v.SBA wh a b X i Z x0).isSome = (v₀.SBA wh₀ a b X i Z x0).isSome := by
  unfold Env.SBA
  rw [tensorAt_skel S, S.y]
  refine bind_same _ fun x => sumForms_same _ fun k _ => ?_
  rw [Option.isSome_map, Option.isSome_map]
  exact longA_skel S _ _ _ _

/-- Two calls of Env.site at one and the same digit form return alike, where their two readings of
the high digits return alike: the weight, the quotient and the shift may differ. -/
theorem site_skel (w w' : E) (SQ SQ' : Aff) (k k' form : ℕ) {Srh Srh' : Unit → Option Aff}
    (h : (Srh ()).isSome = (Srh' ()).isSome) :
    (Env.site w SQ k form Srh).isSome = (Env.site w' SQ' k' form Srh').isSome := by
  unfold Env.site
  dsimp only
  exact ite_isSome (pure_alike _ _) (seq_both h fun _ _ => pure_alike _ _)

/-- Two binds in Option with one and the same first part return alike, where their second parts
return alike at every argument. It is bind_same, spelled with >>= as a do-block unfolds. -/
theorem seq_same {α β β' : Type} (x : Option α) {f : α → Option β} {g : α → Option β'}
    (h : ∀ a, (f a).isSome = (g a).isSome) : (x >>= f).isSome = (x >>= g).isSome := bind_same x h

/-- Two maps in Option return alike, where what they map returns alike. -/
theorem map_both {α α' β β' : Type} {x : Option α} {y : Option α'} (f : α → β) (g : α' → β')
    (h : x.isSome = y.isSome) : (x.map f).isSome = (y.map g).isSome := by
  rw [Option.isSome_map, Option.isSome_map]
  exact h

/-- Two folds in Option over one list return alike, where at every member of the list the two steps
return alike at all pairs of states. -/
theorem foldlM_both {α σ σ' : Type} {f : σ → α → Option σ} {g : σ' → α → Option σ'} :
    ∀ (l : List α) (s : σ) (s' : σ'), (∀ x ∈ l, ∀ s s', (f s x).isSome = (g s' x).isSome) →
      (l.foldlM f s).isSome = (l.foldlM g s').isSome
  | [], _, _, _ => rfl
  | x :: l, s, s', h => by
    rw [List.foldlM_cons, List.foldlM_cons]
    exact seq_both (h x (List.mem_cons_self ..) s s') fun a b =>
      foldlM_both l a b fun y hy => h y (List.mem_cons_of_mem _ hy)

/-- A tactic for goals "these two do-blocks in Option return alike", where the two are of one build
and stand at two environments of one skeleton: it tries the laws above and the library's, over and
over. -/
local macro "alike " S:term ", " hw:term : tactic => `(tactic| repeat' first
  | with_reducible exact pure_alike _ _
  | with_reducible exact SA_skel $S $hw _ _ _
  | with_reducible exact SBA_skel $S _ _ _ _ _ _ _ _
  | with_reducible exact SxsA_skel $S _ _ _ _
  | with_reducible exact shSum_skel $S _ _ _ _ _ _
  | with_reducible exact shA_skel $S _ _ _ _
  | with_reducible exact U3at_skel $S _ _
  | with_reducible exact Eq.refl _
  | with_reducible refine ite_isSome ?_ ?_
  | with_reducible refine site_skel _ _ _ _ _ _ _ ?_
  | with_reducible refine sumForms_same _ fun _ _ => ?_
  | with_reducible refine map_both _ _ ?_
  | with_reducible refine seq_same _ fun _ => ?_
  | with_reducible refine seq_both ?_ fun _ _ => ?_)

/-- Two calls of Env.lineGU, at two environments of one skeleton, return alike, where the second
arrays of weights have one size; the first arrays may differ. -/
theorem lineGU_skel (S : EnvSkel v v₀) (up : Bool) (lam : ℕ) (ew ew₀ : Array E) {wh wh₀ : Array E}
    (hw : wh.size = wh₀.size) :
    (v.lineGU up lam ew wh).isSome = (v₀.lineGU up lam ew₀ wh₀).isSome := by
  unfold Env.lineGU
  dsimp only
  rw [isMoe_skel S, S.y]
  alike S, hw

/-- The like for Env.lineGUH. -/
theorem lineGUH_skel (S : EnvSkel v v₀) (up : Bool) (lam : ℕ) (ew ew₀ : Array E)
    {wh wh₀ : Array E} (hw : wh.size = wh₀.size) :
    (v.lineGUH up lam ew wh).isSome = (v₀.lineGUH up lam ew₀ wh₀).isSome := by
  unfold Env.lineGUH
  dsimp only
  rw [isMoe_skel S, S.y]
  alike S, hw

/-- Two calls of Env.lineQK, at two environments of one skeleton, return alike, whatever the four
arrays of weights. -/
theorem lineQK_skel (S : EnvSkel v v₀) (hi : Bool) (lam : ℕ) (ew ew₀ wh wh₀ : Array E) :
    (v.lineQK hi lam ew wh).isSome = (v₀.lineQK hi lam ew₀ wh₀).isSome := by
  unfold Env.lineQK
  dsimp only
  rw [S.y]
  alike S, rfl

/-- Two calls of Env.lineROW, at two environments of one skeleton and two arrays of weights of one
size, return alike. -/
theorem lineROW_skel (S : EnvSkel v v₀) (lam : ℕ) {ew ew₀ : Array E} (he : ew.size = ew₀.size) :
    (v.lineROW lam ew).isSome = (v₀.lineROW lam ew₀).isSome := by
  unfold Env.lineROW
  dsimp only
  rw [tabAt_skel S, S.y, he]
  alike S, he

/-- Two calls of Env.lineDD, at two environments of one skeleton, return alike, whatever the two
arrays of weights. -/
theorem lineDD_skel (S : EnvSkel v v₀) (lamM : ℕ) (ew ew₀ : Array E) :
    (v.lineDD lamM ew).isSome = (v₀.lineDD lamM ew₀).isSome := by
  unfold Env.lineDD
  dsimp only
  rw [S.y]
  refine seq_both (foldlM_both _ _ _ fun x _ s s' => ?_) fun _ _ => pure_alike _ _
  exact seq_both (shA_skel S _ _ _ _) fun _ _ =>
    seq_both (shA_skel S _ _ _ _) fun _ _ => pure_alike _ _

set_option maxRecDepth 8000 in
/-- **Whether the form of a segment's keys is there hangs on the skeleton and two sizes alone.** -/
theorem line_skel (S : EnvSkel v v₀) (sn : String) (lam : ℕ) {ew ew₀ wh wh₀ : Array E}
    (he : ew.size = ew₀.size) (hw : wh.size = wh₀.size) :
    (v.line sn lam ew wh).isSome = (v₀.line sn lam ew₀ wh₀).isSome := by
  unfold Env.line
  dsimp only
  rw [S.y]
  repeat' first
    | with_reducible exact lineGU_skel S _ _ _ _ hw
    | with_reducible exact lineGUH_skel S _ _ _ _ hw
    | with_reducible exact lineQK_skel S _ _ _ _ _ _
    | with_reducible exact lineROW_skel S _ he
    | with_reducible exact lineDD_skel S _ _ _
    | with_reducible refine ite_isSome ?_ ?_
  all_goals alike S, hw

/-- **Whether a call's factor in the join is there hangs on the skeleton alone.** -/
theorem joinPart_skel (S : EnvSkel v v₀) (alpha theta alpha₀ theta₀ : E) (q : ℕ) (c : CallD)
    (weighed weighed₀ : Array Bool) :
    (v.joinPart alpha theta q c weighed).isSome =
      (v₀.joinPart alpha₀ theta₀ q c weighed₀).isSome := by
  unfold Env.joinPart
  dsimp only
  rw [S.y]
  refine seq_both (foldlM_both _ _ _ fun s _ a a' => foldlM_both _ _ _ fun lam _ b b' => ?_)
    fun _ _ => pure_alike _ _
  rw [isMoe_skel S]
  refine ite_isSome (some_alike _ _) (map_both _ _ (line_skel S _ _ ?_ ?_))
  · simp [Env.ewFrom]
  · split <;> simp [Env.ewhFrom]

/-! ## JoinPub -/

/-- Which columns a call's segments list hangs on the layout alone. -/
theorem weighedOf_y (hy : v.y = v₀.y) (c : CallD) : v.weighedOf c = v₀.weighedOf c := by
  unfold Env.weighedOf Env.isMoe
  rw [hy]

/-- The padding keys that a call's unlisted columns hold hang on the layout alone. -/
theorem laidOf_y (hy : v.y = v₀.y) (q : ℕ) (w : Array Bool) (laid : Array ℕ) :
    v.laidOf q w laid = v₀.laidOf q w laid := by
  unfold Env.laidOf
  rw [hy]

/-- What a list's members return one by one are as many as the members. -/
theorem mapM_length {α β : Type} {f : α → Option β} : ∀ (l : List α) (bs : List β),
    l.mapM f = some bs → bs.length = l.length
  | [], bs, h => by
    obtain rfl : [] = bs := by simpa using h
    rfl
  | x :: l, bs, h => by
    rw [List.mapM_cons] at h
    obtain ⟨y, _, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨ys, hys, h⟩ := Option.bind_eq_some_iff.mp h
    obtain rfl : y :: ys = bs := Option.some.inj h
    rw [List.length_cons, List.length_cons, mapM_length l ys hys]

/-- **JoinPub holds**, where laidLayers' count of the padding keys is the layout's own, the test on
the plan is true, and four facts hold of the lookup's record: its shape has as many calls as the
layout, it has as many weights as the layout has calls, and its shape's number of trees and padding
counts are the layout's. -/
theorem join_pay {P : Pub} {hp : HPlan2} {g iU3 : ℕ} {tab : List TableAt} {fo : Forest.Heard}
    (hL : VerifiableInference.Desc.First.Look.laidLayers P = some P.y.fo.pub)
    (hJ : joinB P hp g iU3 tab = true) (d1 : fo.shape.calls.size = P.y.calls.size)
    (d2 : fo.e.size = P.y.calls.size) (d3 : Forest.noPub fo.shape = Forest.noPub P.y.fo)
    (d4 : fo.shape.pub = P.y.fo.pub) : JoinPub (envOf P hp g fo iU3 tab) fo := by
  unfold VerifiableInference.Desc.First.Look.laidLayers at hL
  dsimp only at hL
  obtain ⟨weighed, hw, hl⟩ := Option.bind_eq_some_iff.mp hL
  have e1 : (envOf P hp g fo iU3 tab).y.calls.mapM (envOf P hp g fo iU3 tab).weighedOf =
      some weighed := by
    rw [← hw]
    exact congrArg (fun f => P.y.calls.mapM f) (funext fun c => weighedOf_y rfl c)
  unfold joinB at hJ
  have hJ' := List.all_eq_true.1 hJ
  obtain ⟨parts, hp'⟩ := mapM_some (fun x : (CallD × Array Bool) × ℕ =>
      (envOf P hp g fo iU3 tab).joinPart fo.alpha fo.theta x.2 x.1.1 x.1.2)
    (P.y.calls.zip weighed).toList.zipIdx fun x hx => by
      obtain ⟨⟨c, w⟩, q⟩ := x
      obtain ⟨hq, e⟩ := List.mem_zipIdx' hx
      have hq' : q < P.y.calls.size := by
        have : q < min P.y.calls.size weighed.size := by simpa using hq
        omega
      have hc : c = P.y.calls.getD q default := by
        have e' := congrArg Prod.fst e
        simp only [Array.toList_zip, List.getElem_zip, Array.getElem_toList] at e'
        rw [e']
        simp [Array.getD, hq']
      have h1 := hJ' q (List.mem_range.2 hq')
      rw [← hc, ← joinPart_skel (v := envOf P hp g fo iU3 tab) (v₀ := envBlank P hp g iU3 tab)
        ⟨rfl, rfl, rfl⟩ fo.alpha fo.theta zeroE zeroE q c w #[]] at h1
      exact Option.isSome_iff_exists.1 h1
  have hsz : weighed.size = P.y.calls.size := by
    rw [Array.mapM_eq_mapM_toList] at hw
    obtain ⟨l, hl', e⟩ := Option.map_eq_some_iff.mp hw
    rw [← e]
    simpa using mapM_length _ _ hl'
  have hlen : parts.length = P.y.calls.size := by
    rw [mapM_length _ _ hp']
    simp [hsz]
  refine ⟨⟨weighed, parts, P.y.fo.pub, e1, hp', ?_, ?_, ?_, join_no_slot hp'⟩⟩
  · rw [hlen, d1, d2]
    simp
  · rw [d3, ← hl]
    exact congrArg (fun f => weighed.toList.zipIdx.foldlM f (Forest.noPub P.y.fo))
      (funext fun laid => funext fun x => laidOf_y rfl _ _ _)
  · rw [d4]
    simp

end OnBytes.Desc.First.K4.Rt

#print axioms OnBytes.Desc.First.K4.Rt.seq_both
#print axioms OnBytes.Desc.First.K4.Rt.pure_alike
#print axioms OnBytes.Desc.First.K4.Rt.some_alike
#print axioms OnBytes.Desc.First.K4.Rt.isMoe_skel
#print axioms OnBytes.Desc.First.K4.Rt.SA_skel
#print axioms OnBytes.Desc.First.K4.Rt.SBA_skel
#print axioms OnBytes.Desc.First.K4.Rt.site_skel
#print axioms OnBytes.Desc.First.K4.Rt.seq_same
#print axioms OnBytes.Desc.First.K4.Rt.map_both
#print axioms OnBytes.Desc.First.K4.Rt.foldlM_both
#print axioms OnBytes.Desc.First.K4.Rt.lineGU_skel
#print axioms OnBytes.Desc.First.K4.Rt.lineGUH_skel
#print axioms OnBytes.Desc.First.K4.Rt.lineQK_skel
#print axioms OnBytes.Desc.First.K4.Rt.lineROW_skel
#print axioms OnBytes.Desc.First.K4.Rt.lineDD_skel
#print axioms OnBytes.Desc.First.K4.Rt.line_skel
#print axioms OnBytes.Desc.First.K4.Rt.joinPart_skel
#print axioms OnBytes.Desc.First.K4.Rt.weighedOf_y
#print axioms OnBytes.Desc.First.K4.Rt.laidOf_y
#print axioms OnBytes.Desc.First.K4.Rt.mapM_length
#print axioms OnBytes.Desc.First.K4.Rt.join_pay
