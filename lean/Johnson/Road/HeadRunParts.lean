-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/HeadRunParts.lean: the check of the output head's sub-proof, taken apart.

The check of the output head's sub-proof is one routine (runForkHidH2 in OnBytes/Model/Head.lean).
It tests what its caller hands in, sets up the state, receives the messages (hear), fixes the tables
of the reads (tablesOf), runs the messages of the smallness test and of the merge, draws the
batching element, adds all claims (walk), and closes. The files beside this one have theorems on
hear, on tablesOf, on weightsClaim and on the routines of the walk, each under the hypothesis that
the routine in question succeeds from some state. This file shows that, if the whole routine
succeeds, each of these routines has succeeded, on one record of the run, each from the state and
the context that the one before has left.

Main definitions: KeepsL (a routine of a link keeps the state's shape); runOf (the record of the run
that the routine builds); fresh (the state from which the routine starts its work); Chained (what
run_whole says, with the record, the state in which the walk begins and the claim on the weights as
letters).
Main theorems: cols_modify, cols_map, cols_fill, kept_fresh (steps that change an array's rows or
marks leave its number of columns); instances, each a named theorem, up to keeps_tablesOf,
keeps_weightsClaim, keeps_rootInH, keeps_transcript, keeps_t2Batch; okL_liftB, okL_get, okL_sub,
okL_map; stepL, stepB, stepS, stepSub, stepGet, stepFork (how a routine of a link is walked);
run_whole (the routine taken apart, to its last line), run_chained (the same in the word Chained),
chained_unique (what the caller hands in fixes the record, the state and the claim), run_chain (its
part up to the walk), run_parts (a shorter form); cols_of_handed, run_cols (the caller's arrays have
the plan's numbers of columns); transcript_keeps (the messages of the smallness test leave its list
of matrices).

What is not claimed. Of what follows the walk in the routine (the tests of the walk and the step
that hands the one equation on) only that it has succeeded, and from which states: nothing on what
these routines test or hand on. Nothing on the arguments: that the layout, the plan and the covered
positions are the results of the verifier's own functions is the caller's matter. Nothing on values
or on what a verifier's acceptance shows. Every theorem begins "if the routine succeeds": none says
that it does. The program does not import this file.
-/
import Johnson.Road.HeadKeeps

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.Hd.Parts

open OnBytes.Model (Fork SubM)
open OnBytes.Road.Hd.Walk (Kept OkL okL_pure okL_bind okL_lift)

/-! ## Steps that leave the numbers of columns -/

/-- Changing one array by a function that keeps its number of columns. -/
theorem cols_modify (trees : Array Model.HTree) (i : ℕ) (f : Model.HTree → Model.HTree)
    (hf : ∀ X, (f X).K = X.K) (t : ℕ) :
    ((trees.modify i f)[t]?).map (·.K) = (trees[t]?).map (·.K) := by
  rw [Array.getElem?_modify]
  split
  · cases trees[t]? with
    | none => rfl
    | some X => exact congrArg some (hf X)
  · rfl

/-- Changing every array by a function that keeps its number of columns. -/
theorem cols_map (trees : Array Model.HTree) (f : Model.HTree → Model.HTree)
    (hf : ∀ X, (f X).K = X.K) (t : ℕ) :
    ((trees.map f)[t]?).map (·.K) = (trees[t]?).map (·.K) := by
  rw [Array.getElem?_map]
  cases trees[t]? with
  | none => rfl
  | some X => exact congrArg some (hf X)

/-- Two states whose arrays have the same numbers of columns. -/
theorem colsOf_of {F G : Fork}
    (h : ∀ t : ℕ, (G.trees[t]?).map (fun X : Model.HTree => X.K) =
      (F.trees[t]?).map (fun X : Model.HTree => X.K)) (t : ℕ) :
    colsOf G t = colsOf F t := by
  unfold colsOf
  rw [h t]

/-- The state from which the check starts: the caller's arrays with their weights set up, no slot,
no claim. It has one coefficient for each slot, namely none, and the caller's numbers of columns. -/
theorem kept_fresh (F : Fork) :
    (({ trees := F.trees } : Fork).fillL).LS.size = (({ trees := F.trees } : Fork).fillL).ns ∧
      ∀ t, colsOf (({ trees := F.trees } : Fork).fillL) t = colsOf F t :=
  ⟨rfl, colsOf_of fun t => cols_map F.trees
    (fun X => { X with rows := X.rows.map fun r => { r with L := Array.replicate X.K zeroE } })
    (fun _ => rfl) t⟩

/-- Marking an array as committed keeps the state's shape. -/
instance keeps_rootTaken (t w : ℕ) : KeepsS (SubM.rootTaken t w) :=
  ⟨fun F C a G D hs h => by
    unfold SubM.rootTaken at h
    rw [Walk.ok_change] at h
    have e : F.rootTaken t w = G := Option.some.inj h.1
    rw [← e]
    exact ⟨hs, colsOf_of fun j =>
      cols_modify F.trees t (fun X => { X with root := some w }) (fun _ => rfl) j⟩⟩

/-- Setting up the weights of the listed arrays leaves the numbers of columns. -/
theorem cols_fill (fill : Model.HTree → Model.HTree) (hf : ∀ X, (fill X).K = X.K) :
    ∀ (l : List ℕ) (trees : Array Model.HTree) (t : ℕ),
      ((l.foldl (fun tr ti => tr.modify ti fill) trees)[t]?).map (·.K) = (trees[t]?).map (·.K)
  | [], _, _ => rfl
  | i :: l, trees, t => by
    rw [List.foldl_cons, cols_fill fill hf l _ t, cols_modify trees i fill hf t]

/-- The step that sets up the weights of the listed arrays keeps the state's shape. -/
instance keeps_t2FillL (T : Model.Tail2) :
    KeepsS (SubM.change fun F => some (Model.t2FillL F T)) :=
  ⟨fun F C a G D hs h => by
    rw [Walk.ok_change] at h
    have e : Model.t2FillL F T = G := Option.some.inj h.1
    rw [← e]
    exact ⟨hs, colsOf_of fun j => cols_fill
      (fun X => { X with rows := X.rows.map fun r =>
        if r.L.size != X.K then { r with L := Array.replicate X.K zeroE } else r })
      (fun _ => rfl) (List.range T.nt.size) F.trees j⟩⟩

/-- Taking the batching element keeps the state's shape. -/
instance keeps_batchBy (x : E) : KeepsS (SubM.batchBy x) :=
  ⟨fun F C a G D hs h => by
    unfold SubM.batchBy at h
    rw [Walk.ok_change] at h
    have h1 : F.batchBy x = some G := h.1
    unfold Fork.batchBy at h1
    split at h1
    · cases h1
    · cases h1
      exact ⟨hs, fun _ => rfl⟩⟩

/-- Setting the number of claims in the plan keeps the state's shape. -/
instance keeps_setPlanClaims (n : ℕ) : KeepsS (SubM.setPlanClaims n) :=
  ⟨fun F C a G D hs h => by
    unfold SubM.setPlanClaims at h
    rw [Walk.ok_change] at h
    have e : { F with planClaimsF := n } = G := Option.some.inj h.1
    rw [← e]
    exact ⟨hs, fun _ => rfl⟩⟩

/-- Setting up the marks of the claims' weights keeps the state's shape. -/
instance keeps_kapMap : KeepsS (SubM.change fun F =>
    some { F with kapMapF := Array.replicate F.planClaimsF false }) :=
  ⟨fun F C a G D hs h => by
    rw [Walk.ok_change] at h
    have e : { F with kapMapF := Array.replicate F.planClaimsF false } = G :=
      Option.some.inj h.1
    rw [← e]
    exact ⟨hs, fun _ => rfl⟩⟩

/-! ## Loops -/

/-- A loop over a list, if every step keeps the state. -/
theorem keeps_forInL {γ σ : Type} (f : γ → σ → SubM (ForInStep σ))
    (hf : ∀ x s, KeepsS (f x s)) : ∀ (l : List γ) (s : σ), KeepsS (forIn l s f)
  | [], s => by
    rw [List.forIn_nil]
    infer_instance
  | x :: l, s =>
    ⟨fun F C a G D hs h => by
      have hd := Kept.refl hs
      haveI := hf x s
      rw [List.forIn_cons] at h
      obtain ⟨r, _, _, hd, h⟩ := st_step hd h
      cases r with
      | done c => exact st_end hd h
      | yield c => exact hd.trans ((keeps_forInL f hf l c).keep _ _ _ _ _ hd.1 h)⟩

/-- A loop over a list keeps the state's shape, if every step does: as an instance. -/
instance keeps_forIn_list {γ σ : Type} (l : List γ) (s : σ) (f : γ → σ → SubM (ForInStep σ))
    [hf : ∀ x s, KeepsS (f x s)] : KeepsS (forIn l s f) := keeps_forInL f hf l s

/-- A loop over the numbers below n keeps the state's shape, if every step does. -/
instance keeps_forIn_range {σ : Type} (n : ℕ) (s : σ) (f : ℕ → σ → SubM (ForInStep σ))
    [hf : ∀ x s, KeepsS (f x s)] : KeepsS (forIn [:n] s f) := by
  have e : forIn [:n] s f = forIn (List.range' 0 n) s f := by
    rw [Std.Legacy.Range.forIn_eq_forIn_range', range_list]
  rw [e]
  infer_instance

/-- The rules for one routine after another, a choice and the two loops, with the facts on the parts
given by hand: for routines that are too long for Lean's search. -/
theorem kb {α β : Type} {m : SubM α} {f : α → SubM β} (hm : KeepsS m) (hf : ∀ a, KeepsS (f a)) :
    KeepsS (m >>= f) := keeps_bind m f

/-- A choice between two routines, with the facts on the two given by hand. -/
theorem ki {α : Type} {p : Prop} [Decidable p] {a b : SubM α} (ha : KeepsS a) (hb : KeepsS b) :
    KeepsS (if p then a else b) := keeps_ite p a b

/-- A loop over a list, with the fact on its steps given by hand. -/
theorem kfl {γ σ : Type} {l : List γ} {s : σ} {f : γ → σ → SubM (ForInStep σ)}
    (hf : ∀ x s, KeepsS (f x s)) : KeepsS (forIn l s f) := keeps_forInL f hf l s

/-- A loop over the numbers below n, with the fact on its steps given by hand. -/
theorem kfr {σ : Type} {n : ℕ} {s : σ} {f : ℕ → σ → SubM (ForInStep σ)}
    (hf : ∀ x s, KeepsS (f x s)) : KeepsS (forIn [:n] s f) := keeps_forIn_range n s f

/-! ## The tables and the claim on the weights -/

/-- The routine that fixes the tables of the reads keeps the state's shape. -/
instance keeps_tablesOf (h0 : Model.Head.Shape) (L : Model.Head.HL) (hp : Model.Head.HPlanH2)
    (cov : Model.Head.Covered) (x : Model.Head.Heard) :
    KeepsS (Model.Head.tablesOf h0 L hp cov x) :=
  ⟨fun F C a G D hs h => by
    have hd := Kept.refl hs
    unfold Model.Head.tablesOf at h
    obtain ⟨_, _, _, hd, h⟩ := st_step hd h
    obtain ⟨_, _, _, hd, h⟩ := st_step hd h
    obtain ⟨_, _, _, hd, h⟩ := st_step hd h
    obtain ⟨_, _, _, hd, h⟩ := st_step hd h
    obtain ⟨_, _, _, hd, h⟩ := st_step hd h
    obtain ⟨_, _, _, hd, h⟩ := st_step hd h
    obtain ⟨_, _, _, hd, h⟩ := st_step hd h
    obtain ⟨_, _, _, hd, h⟩ := st_step hd h
    obtain ⟨_, _, _, hd, h⟩ := st_step hd h
    obtain ⟨_, _, _, hd, h⟩ := st_step hd h
    exact st_end hd h⟩

/-- The routine that returns the weights of a segment's entries keeps the state's shape. -/
instance keeps_ewOf (R : Model.Head.Run) (sn : String) : KeepsS (Model.Head.ewOf R sn) :=
  ⟨(Walk.leaves_ewOf R sn).keeps⟩

/-- The routine that makes the claim on the weights keeps the state's shape. -/
instance keeps_weightsClaim (R : Model.Head.Run) (lay : Model.WsLay) :
    KeepsS (Model.Head.weightsClaim R lay) := by
  unfold Model.Head.weightsClaim
  dsimp only
  refine kb (keeps_ewOf _ _) fun ew0 => kb (keeps_liftM _) fun _ =>
    kb (kfl fun G r => ?_) fun _ => keeps_pure _
  refine ki ?_ (ki ?_ ?_)
  · refine kb (kfr fun t r2 => ki ?_ ?_) fun _ => kb (keeps_pure _) fun _ => keeps_pure _
    · exact kb (keeps_liftM _) fun _ => kb (keeps_pure _) fun _ => keeps_pure _
    · exact kb (keeps_pure _) fun _ => keeps_pure _
  · exact kb (keeps_pure _) fun _ => keeps_pure _
  · exact kb (keeps_liftM _) fun _ => keeps_pure _

/-! ## Routines of a link -/

/-- The routine of a link keeps the state's shape, whatever the link's state. -/
class KeepsL {α : Type} (m : Model.LinkM α) : Prop where
  keep : ∀ Lc, KeepsS (m Lc)

section Link
variable {α β : Type}

/-- A routine of a link that only returns a value keeps the state's shape. -/
instance keepsL_pure (a : α) : KeepsL (pure a : Model.LinkM α) :=
  ⟨fun Lc => (inferInstance : KeepsS (pure (a, Lc) : SubM (α × Model.LinkCtx)))⟩

/-- One routine of a link after another keeps the state's shape, if each of the two does. -/
instance keepsL_bind (m : Model.LinkM α) (f : α → Model.LinkM β) [hm : KeepsL m]
    [hf : ∀ a, KeepsL (f a)] : KeepsL (m >>= f) :=
  ⟨fun Lc => by
    have e : (m >>= f) Lc = (m Lc >>= fun p => f p.1 p.2) := rfl
    rw [e]
    haveI := hm.keep Lc
    haveI : ∀ p : α × Model.LinkCtx, KeepsS (f p.1 p.2) := fun p => (hf p.1).keep p.2
    infer_instance⟩

/-- The same rule with the facts on the parts given by hand. -/
theorem kbL (m : Model.LinkM α) (f : α → Model.LinkM β) (hm : KeepsL m)
    (hf : ∀ a, KeepsL (f a)) : KeepsL (m >>= f) := keepsL_bind m f

/-- A choice between two routines of a link that keep the state's shape keeps it. -/
instance keepsL_ite (p : Prop) [Decidable p] (a b : Model.LinkM α) [KeepsL a] [KeepsL b] :
    KeepsL (if p then a else b) := by
  split <;> infer_instance

/-- A routine of the sub-proof inside a link. -/
instance keepsL_sub (x : SubM α) [KeepsS x] : KeepsL (Model.LinkM.sub x) :=
  ⟨fun Lc => (inferInstance : KeepsS (x >>= fun a => (pure (a, Lc) : SubM (α × Model.LinkCtx))))⟩

/-- A routine of the sub-proof that is lifted into a link keeps the state's shape, if it does so by
itself. -/
instance keepsL_liftS (x : SubM α) [KeepsS x] : KeepsL (liftM x : Model.LinkM α) :=
  ⟨fun Lc => (inferInstance : KeepsS (x >>= fun a => (pure (a, Lc) : SubM (α × Model.LinkCtx))))⟩

/-- A block inside a link. -/
instance keepsL_liftB (x : Blk α) : KeepsL (liftM x : Model.LinkM α) :=
  ⟨fun Lc => (inferInstance :
    KeepsS ((liftM x : SubM α) >>= fun a => (pure (a, Lc) : SubM (α × Model.LinkCtx))))⟩

/-- Reading the link's state keeps the state's shape. -/
instance keepsL_get : KeepsL (get : Model.LinkM Model.LinkCtx) :=
  ⟨fun Lc => (inferInstance : KeepsS (pure (Lc, Lc) : SubM (Model.LinkCtx × Model.LinkCtx)))⟩

/-- Setting the link's state keeps the state's shape. -/
instance keepsL_set (s : Model.LinkCtx) : KeepsL (set s : Model.LinkM PUnit) :=
  ⟨fun _ => (inferInstance : KeepsS (pure (PUnit.unit, s) : SubM (PUnit × Model.LinkCtx)))⟩

/-- Changing the link's state keeps the state's shape. -/
instance keepsL_modify (f : Model.LinkCtx → Model.LinkCtx) :
    KeepsL (modify f : Model.LinkM PUnit) :=
  ⟨fun Lc => (inferInstance : KeepsS (pure (PUnit.unit, f Lc) : SubM (PUnit × Model.LinkCtx)))⟩

/-- A public condition in a link keeps the state's shape. -/
instance keepsL_mustAs (n : String) (b : Bool) : KeepsL (Model.LinkM.mustAs n b) := by
  unfold Model.LinkM.mustAs
  infer_instance

/-- Reading the sub-proof's state in a link keeps the state's shape. -/
instance keepsL_fork : KeepsL Model.LinkM.fork := by
  unfold Model.LinkM.fork
  infer_instance

/-- A call of the chain does not see the sub-proof's state, so it keeps its shape. -/
instance keepsL_call (f : Model.ChainCheck → Blk Model.ChainCheck) :
    KeepsL (Model.LinkM.call f) :=
  ⟨fun Lc => by
    unfold Model.LinkM.call
    infer_instance⟩

end Link

/-! ## How a routine of a link succeeds -/

/-- A block inside a link sees neither the link's state nor the sub-proof's. -/
theorem okL_liftB {α : Type} (x : Blk α) (Lc Lc' : Model.LinkCtx) (F G : Fork) (C D : Ctx)
    (a : α) : OkL (liftM x : Model.LinkM α) Lc F C a Lc' G D ↔
      x C = .ok (a, D) ∧ G = F ∧ Lc' = Lc := by
  have e : (liftM x : Model.LinkM α) = liftM (liftM x : SubM α) := rfl
  rw [e, okL_lift, ok_lift, and_assoc]

/-- Reading the link's state. -/
theorem okL_get (Lc Lc' L : Model.LinkCtx) (F G : Fork) (C D : Ctx) :
    OkL (get : Model.LinkM Model.LinkCtx) Lc F C L Lc' G D ↔
      L = Lc ∧ Lc' = Lc ∧ G = F ∧ D = C := by
  have e : (get : Model.LinkM Model.LinkCtx) Lc =
      (pure (Lc, Lc) : SubM (Model.LinkCtx × Model.LinkCtx)) := rfl
  unfold OkL
  rw [e, ok_pure]
  constructor
  · rintro ⟨h1, h2, h3⟩
    cases h1
    exact ⟨rfl, rfl, h2, h3⟩
  · rintro ⟨rfl, rfl, h2, h3⟩
    exact ⟨rfl, h2, h3⟩

/-- LinkM.sub is the lift. -/
theorem okL_sub {α : Type} (x : SubM α) (Lc Lc' : Model.LinkCtx) (F G : Fork) (C D : Ctx)
    (a : α) : OkL (Model.LinkM.sub x) Lc F C a Lc' G D ↔ Ok x F C a G D ∧ Lc' = Lc :=
  okL_lift x Lc Lc' F G C D a

/-- A routine of a link whose value is changed by a function. -/
theorem okL_map {α β : Type} (f : α → β) (m : Model.LinkM α) (Lc Lc' : Model.LinkCtx)
    (F G : Fork) (C D : Ctx) (b : β) :
    OkL (f <$> m) Lc F C b Lc' G D ↔ ∃ a, OkL m Lc F C a Lc' G D ∧ b = f a := by
  have e : (f <$> m) Lc = (m Lc >>= fun p => (pure (f p.1, p.2) : SubM (β × Model.LinkCtx))) := rfl
  unfold OkL
  rw [e, ok_bind]
  constructor
  · rintro ⟨⟨a, L1⟩, F1, C1, h1, h2⟩
    rw [ok_pure] at h2
    obtain ⟨e1, e2, e3⟩ := h2
    cases e1
    rw [e2, e3]
    exact ⟨a, h1, rfl⟩
  · rintro ⟨a, h1, rfl⟩
    exact ⟨(a, Lc'), G, D, h1, (ok_pure _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩⟩

/-- A routine of a link that keeps the state's shape, said of a run. -/
theorem KeepsL.kept {α : Type} {m : Model.LinkM α} [hm : KeepsL m] {Lc Lc' : Model.LinkCtx}
    {F0 F G : Fork} {C D : Ctx} {a : α} (hd : Kept F0 F) (h : OkL m Lc F C a Lc' G D) :
    Kept F0 G :=
  hd.trans ((hm.keep Lc).keep _ _ _ _ _ hd.1 h)

/-- The same for a routine of the sub-proof. -/
theorem KeepsS.kept {α : Type} {m : SubM α} [hm : KeepsS m] {F0 F G : Fork} {C D : Ctx} {a : α}
    (hd : Kept F0 F) (h : Ok m F C a G D) : Kept F0 G :=
  hd.trans (hm.keep _ _ _ _ _ hd.1 h)

/-! ## One step of a routine of a link, and what follows it -/

section Steps
variable {α β : Type} {Lc Lc' : Model.LinkCtx} {F G : Fork} {C D : Ctx} {b : β}

/-- Any routine of a link. -/
theorem stepL {m : Model.LinkM α} {f : α → Model.LinkM β} (H : OkL (m >>= f) Lc F C b Lc' G D) :
    ∃ a L1 F1 C1, OkL m Lc F C a L1 F1 C1 ∧ OkL (f a) L1 F1 C1 b Lc' G D :=
  (okL_bind m f Lc Lc' F G C D b).mp H

/-- A block. -/
theorem stepB {x : Blk α} {f : α → Model.LinkM β}
    (H : OkL ((liftM x : Model.LinkM α) >>= f) Lc F C b Lc' G D) :
    ∃ a C1, x C = .ok (a, C1) ∧ OkL (f a) Lc F C1 b Lc' G D := by
  obtain ⟨a, L1, F1, C1, h1, h2⟩ := stepL H
  rw [okL_liftB] at h1
  obtain ⟨e1, e2, e3⟩ := h1
  rw [e2, e3] at h2
  exact ⟨a, C1, e1, h2⟩

/-- A routine of the sub-proof. -/
theorem stepS {x : SubM α} {f : α → Model.LinkM β}
    (H : OkL ((liftM x : Model.LinkM α) >>= f) Lc F C b Lc' G D) :
    ∃ a F1 C1, Ok x F C a F1 C1 ∧ OkL (f a) Lc F1 C1 b Lc' G D := by
  obtain ⟨a, L1, F1, C1, h1, h2⟩ := stepL H
  rw [okL_lift] at h1
  rw [h1.2] at h2
  exact ⟨a, F1, C1, h1.1, h2⟩

/-- The same, where the routine is lifted by LinkM.sub. -/
theorem stepSub {x : SubM α} {f : α → Model.LinkM β}
    (H : OkL (Model.LinkM.sub x >>= f) Lc F C b Lc' G D) :
    ∃ a F1 C1, Ok x F C a F1 C1 ∧ OkL (f a) Lc F1 C1 b Lc' G D := stepS H

/-- Reading the link's state. -/
theorem stepGet {f : Model.LinkCtx → Model.LinkM β}
    (H : OkL ((get : Model.LinkM Model.LinkCtx) >>= f) Lc F C b Lc' G D) :
    OkL (f Lc) Lc F C b Lc' G D := by
  obtain ⟨a, L1, F1, C1, h1, h2⟩ := stepL H
  rw [okL_get] at h1
  obtain ⟨e1, e2, e3, e4⟩ := h1
  rw [e1, e2, e3, e4] at h2
  exact h2

/-- Reading the sub-proof's state. -/
theorem stepFork {f : Fork → Model.LinkM β}
    (H : OkL (Model.LinkM.fork >>= f) Lc F C b Lc' G D) : OkL (f F) Lc F C b Lc' G D := by
  obtain ⟨a, F1, C1, h1, h2⟩ := stepSub (x := SubM.ask fun F => some F) H
  rw [ok_ask] at h1
  obtain ⟨e1, e2, e3⟩ := h1
  have e4 : F = a := Option.some.inj e1
  rw [← e4, e2, e3] at h2
  exact h2

end Steps

/-! ## Loops and routines of a link -/

/-- A loop over a list in a link, if every step keeps the state. -/
theorem keepsL_forInL {γ σ : Type} (f : γ → σ → Model.LinkM (ForInStep σ))
    (hf : ∀ x s, KeepsL (f x s)) : ∀ (l : List γ) (s : σ), KeepsL (forIn l s f)
  | [], s => by
    rw [List.forIn_nil]
    infer_instance
  | x :: l, s =>
    ⟨fun Lc => ⟨fun F C a G D hs h => by
      obtain ⟨u, Lc'⟩ := a
      have H : OkL (forIn (x :: l) s f) Lc F C u Lc' G D := h
      rw [List.forIn_cons] at H
      obtain ⟨r, L1, F1, C1, h1, H⟩ := stepL H
      haveI := hf x s
      have k1 : Kept F F1 := KeepsL.kept (Kept.refl hs) h1
      cases r with
      | done c =>
        have H' : OkL (pure c : Model.LinkM σ) L1 F1 C1 u Lc' G D := H
        rw [okL_pure] at H'
        rw [H'.2.2.1]
        exact k1
      | yield c =>
        haveI := keepsL_forInL f hf l c
        exact KeepsL.kept k1 H⟩⟩

/-- A loop over a list in a link keeps the state's shape, if every step does: as an instance. -/
instance keepsL_forIn {γ σ : Type} (l : List γ) (s : σ) (f : γ → σ → Model.LinkM (ForInStep σ))
    [hf : ∀ x s, KeepsL (f x s)] : KeepsL (forIn l s f) := keepsL_forInL f hf l s

/-- Receiving the commitments of a moment keeps the state's shape. -/
instance keeps_rootInH (trees : List ℕ) : KeepsL (Model.rootInH trees) := by
  unfold Model.rootInH
  dsimp only
  refine kbL _ _ keepsL_get fun L => kbL _ _ (keepsL_mustAs _ _) fun _ =>
    kbL _ _ (keepsL_call _) fun _ => kbL _ _ (keepsL_modify _) fun _ =>
    kbL _ _ (keepsL_forInL _ (fun t r => ?_) _ _) fun _ => keepsL_mustAs _ _
  exact kbL _ _ keepsL_fork fun F => kbL _ _ (keepsL_mustAs _ _) fun _ =>
    kbL _ _ (keepsL_sub _) fun _ => keepsL_pure _

/-- The test of the order on which the draw of the smallness test's matrix relies keeps the state's
shape. -/
instance keeps_fixedBefore (tl : Model.HTailF2) : KeepsL tl.fixedBeforeTheMatrixF := by
  unfold Model.HTailF2.fixedBeforeTheMatrixF
  infer_instance

/-- The messages of the smallness test keep the state's shape. -/
instance keeps_transcript (tl : Model.HTailF2) : KeepsL tl.transcript := by
  unfold Model.HTailF2.transcript Model.HTailF2.transcriptF
  exact kbL _ _ (keepsL_mustAs _ _) fun _ => kbL _ _ (keepsL_mustAs _ _) fun _ =>
    kbL _ _ (keepsL_sub _) fun _ => kbL _ _ (keeps_fixedBefore _) fun _ =>
    kbL _ _ (keepsL_sub _) fun _ => kbL _ _ (keeps_rootInH _) fun _ =>
    kbL _ _ (keepsL_sub _) fun _ => kbL _ _ (keepsL_sub _) fun _ => keepsL_pure _

/-- The draw of the batching element keeps the state's shape. -/
instance keeps_t2Batch (used : ℕ) : KeepsL (Model.t2Batch used) := by
  unfold Model.t2Batch
  refine kbL _ _ keepsL_get fun L => kbL _ _ (keepsL_sub _) fun ⟨ns, pc⟩ => ?_
  exact kbL _ _ (keepsL_mustAs _ _) fun _ => kbL _ _ (keepsL_mustAs _ _) fun _ =>
    kbL _ _ (keepsL_sub _) fun _ => kbL _ _ (keepsL_sub _) fun _ =>
    kbL _ _ (keepsL_sub _) fun _ => kbL _ _ (keepsL_mustAs _ _) fun _ =>
    kbL _ _ (keepsL_sub _) fun _ => keepsL_set _

/-! ## The whole routine -/

/-- The record of the run that the routine builds from its arguments, from what hear returns, from
the tables and from the number of the array of the reads. -/
def runOf (h : Model.Head.Shape) (L : Model.Head.HL) (b : Model.Head.Border)
    (hp : Model.Head.HPlanH2) (cov : Model.Head.Covered) (x : Model.Head.Heard)
    (t : Model.Head.Tables) (iU3 : ℕ) : Model.Head.Run :=
  { h := h, L := L, b := b, hp := hp, cov := cov, x := x, t := t, iU3 := iU3 }

/-- The state from which the routine starts its work: the caller's arrays with their weights set
up, no slot, no claim. -/
def fresh (F : Fork) : Fork := ({ trees := F.trees } : Fork).fillL

/-- If the check of the head's sub-proof succeeds, all its routines have succeeded, on one record of
the run, each from the state, the context and the link's state that the one before has left: hear,
from the fresh state and the caller's context; the commitment to the reads; tablesOf; the messages
of the smallness test; weightsClaim; the merge's messages; the number of claims and the draw of the
batching element; the walk; the tests of the walk; the step that hands the one equation on (doorH);
the test that every weight of a claim was taken, which leaves the state and the context that the
whole routine leaves. The public tests on the way have passed. Each of six states up to the walk's
first has one coefficient for each slot, and in it every array has as many columns as in the state F
that the caller handed in. The value that the routine returns is what the merge's messages left. -/
theorem run_whole {h : Model.Head.Shape} {L : Model.Head.HL} {b : Model.Head.Border}
    {hp : Model.Head.HPlanH2} {O : Model.Head.Owner} {cov : Model.Head.Covered}
    {lay : Model.WsLay} {Lc Lc' : Model.LinkCtx} {F G : Fork} {C D : Ctx} {wo : Model.WsForkOut}
    (H : OkL (Model.Head.runForkHidH2 h L b hp O cov lay) Lc F C wo Lc' G D) :
    cov.sized h.T = true ∧ Model.Head.planHanded hp Lc.list F = true ∧
    (!O.tl.ix.TX.isEmpty && O.tl.kTX.back? == some b.kxb) = true ∧ (hp.NCL == 1) = true ∧
    ∃ (iU3 : ℕ) (x : Model.Head.Heard) (t : Model.Head.Tables)
      (tl0 tl1 tl2 : Model.HTailF2) (claim : Model.WsClaim) (nE : ℕ)
      (Lt Lt' Lw Lw' Ls : Model.LinkCtx)
      (Fh' Ft Ft' Fc Fc' Fm' Fp Fw Fw' Fs Fd : Fork)
      (Ch' Ct Ct' Cc Cc' Cm' Cp Cw Cw' Cs Cd : Ctx),
      hp.tl.ix.U.getD 2 none = some iU3 ∧
      Ok (Model.Head.hear h L hp cov Lc.check.plain) (fresh F) C x Fh' Ch' ∧
      OkL (Model.rootInH [iU3]) Lc Fh' Ch' () Lt Ft Ct ∧
      Ok (Model.Head.tablesOf h L hp cov x) Ft Ct t Ft' Ct' ∧
      hp.tl.closeFuns t.funs = some tl0 ∧
      OkL tl0.transcript Lt Ft' Ct' tl1 Lt' Fc Cc ∧
      Ok (Model.Head.weightsClaim (runOf h L b hp cov x t iU3) lay) Fc Cc claim Fc' Cc' ∧
      Ok (Model.wsForkEnd lay #[claim] #[x.sV]) Fc' Cc' wo Fm' Cm' ∧
      (Fm'.next == hp.nMsg) = true ∧
      Ok (SubM.setPlanClaims hp.nLin) Fm' Cm' () Fp Cp ∧
      OkL (Model.t2Batch Fm'.next) Lt' Fp Cp () Lw Fw Cw ∧
      OkL (Model.Head.walk (runOf h L b hp cov x t iU3) tl1 wo) Lw Fw Cw tl2 Lw' Fw' Cw' ∧
      OkL (Model.Head.selfTests (runOf h L b hp cov x t iU3) tl2 wo) Lw' Fw' Cw' () Ls Fs Cs ∧
      tl2.equationsLaidF = some nE ∧
      OkL (Model.doorH nE) Ls Fs Cs () Lc' Fd Cd ∧
      (Fd.nClaim == Fd.planClaimsF) = true ∧
      Ok SubM.allTaken Fd Cd () G D ∧
      tl2.foldAllTakenF = true ∧
      Kept F (fresh F) ∧ Kept F Ft ∧ Kept F Ft' ∧ Kept F Fc ∧ Kept F Fc' ∧ Kept F Fw := by
  unfold Model.Head.runForkHidH2 at H
  obtain ⟨_, C1, s1, H⟩ := stepB H
  obtain ⟨hcov, c1⟩ := (mustAs_ok _ _ _ _ _).mp s1
  have H := stepGet H
  have H := stepFork H
  obtain ⟨_, C2, s2, H⟩ := stepB H
  obtain ⟨hpl, c2⟩ := (mustAs_ok _ _ _ _ _).mp s2
  obtain ⟨_, Fh, C3, s3, H⟩ := stepSub H
  rw [Walk.ok_change] at s3
  have eFh : fresh F = Fh := Option.some.inj s3.1
  obtain ⟨_, C4, s4, H⟩ := stepB H
  obtain ⟨hown, c4⟩ := (mustAs_ok _ _ _ _ _).mp s4
  obtain ⟨iU3, C5, s5, H⟩ := stepB H
  obtain ⟨hU, c5⟩ := (getAs_ok _ _ _ _ _).mp s5
  have e5 : C5 = C := c5.trans (c4.trans (s3.2.trans (c2.trans c1)))
  rw [e5, ← eFh] at H
  have kh : Kept F (fresh F) := kept_fresh F
  obtain ⟨x, Fh', Ch', sx, H⟩ := stepS H
  have k1 : Kept F Fh' := KeepsS.kept kh sx
  obtain ⟨_, Lt, Ft, Ct, s7, H⟩ := stepL H
  have kt : Kept F Ft := KeepsL.kept k1 s7
  obtain ⟨t, Ft', Ct', st, H⟩ := stepS H
  have k2 : Kept F Ft' := KeepsS.kept kt st
  obtain ⟨tl0, C9, s9, H⟩ := stepB H
  obtain ⟨hcl, c9⟩ := (getAs_ok _ _ _ _ _).mp s9
  rw [c9] at H
  obtain ⟨tl1, Lt', Fc, Cc, s10, H⟩ := stepL H
  have kc : Kept F Fc := KeepsL.kept k2 s10
  obtain ⟨claim, Fc', Cc', sc, H⟩ := stepS H
  have k3 : Kept F Fc' := KeepsS.kept kc sc
  obtain ⟨_, C12, s12, H⟩ := stepB H
  obtain ⟨hncl, c12⟩ := (mustAs_ok _ _ _ _ _).mp s12
  rw [c12] at H
  obtain ⟨wo', Fm', Cm', sm, H⟩ := stepS H
  have k4 : Kept F Fm' := KeepsS.kept k3 sm
  obtain ⟨slot, F14, C14, s14, H⟩ := stepS H
  unfold SubM.slot at s14
  rw [ok_ask] at s14
  obtain ⟨e14, f14, c14⟩ := s14
  have eslot : Fm'.next = slot := Option.some.inj e14
  rw [f14, c14, ← eslot] at H
  obtain ⟨_, C15, s15, H⟩ := stepB H
  obtain ⟨hslot, c15⟩ := (mustAs_ok _ _ _ _ _).mp s15
  rw [c15] at H
  obtain ⟨_, Fp, Cp, s16, H⟩ := stepS H
  have k6 : Kept F Fp := KeepsS.kept k4 s16
  obtain ⟨_, Lw, Fw, Cw, s17, H⟩ := stepL H
  have kw : Kept F Fw := KeepsL.kept k6 s17
  obtain ⟨tl2, Lw', Fw', Cw', sw, H⟩ := stepL H
  obtain ⟨_, Ls, Fs, Cs, s19, H⟩ := stepL H
  obtain ⟨nE, C20, s20, H⟩ := stepB H
  obtain ⟨hE, c20⟩ := (getAs_ok _ _ _ _ _).mp s20
  rw [c20] at H
  obtain ⟨_, Ld, Fd, Cd, s21, H⟩ := stepL H
  have H := stepFork H
  obtain ⟨_, C22, s22, H⟩ := stepB H
  obtain ⟨hnc, c22⟩ := (mustAs_ok _ _ _ _ _).mp s22
  rw [c22] at H
  obtain ⟨_, F23, C23, s23, H⟩ := stepS H
  obtain ⟨_, C24, s24, H⟩ := stepB H
  obtain ⟨hfa, c24⟩ := (mustAs_ok _ _ _ _ _).mp s24
  rw [okL_pure] at H
  obtain ⟨e1, e2, e3, e4⟩ := H
  have eD : C23 = D := (e4.trans c24).symm
  rw [← e2] at s21
  rw [← e3, eD] at s23
  rw [e1]
  exact ⟨hcov, hpl, hown, hncl, iU3, x, t, tl0, tl1, tl2, claim, nE, Lt, Lt', Lw, Lw', Ls,
    Fh', Ft, Ft', Fc, Fc', Fm', Fp, Fw, Fw', Fs, Fd,
    Ch', Ct, Ct', Cc, Cc', Cm', Cp, Cw, Cw', Cs, Cd,
    hU, sx, s7, st, hcl, s10, sc, sm, hslot, s16, s17, sw, s19, hE, s21, hnc, s23, hfa,
    kh, kt, k2, kc, k3, kw⟩

/-- The part of run_whole up to the walk. -/
theorem run_chain {h : Model.Head.Shape} {L : Model.Head.HL} {b : Model.Head.Border}
    {hp : Model.Head.HPlanH2} {O : Model.Head.Owner} {cov : Model.Head.Covered}
    {lay : Model.WsLay} {Lc Lc' : Model.LinkCtx} {F G : Fork} {C D : Ctx} {wo : Model.WsForkOut}
    (H : OkL (Model.Head.runForkHidH2 h L b hp O cov lay) Lc F C wo Lc' G D) :
    cov.sized h.T = true ∧ Model.Head.planHanded hp Lc.list F = true ∧
    (!O.tl.ix.TX.isEmpty && O.tl.kTX.back? == some b.kxb) = true ∧ (hp.NCL == 1) = true ∧
    ∃ (iU3 : ℕ) (x : Model.Head.Heard) (t : Model.Head.Tables)
      (tl0 tl1 tl2 : Model.HTailF2) (claim : Model.WsClaim)
      (Lt Lt' Lw Lw' : Model.LinkCtx)
      (Fh' Ft Ft' Fc Fc' Fm' Fp Fw Fw' : Fork) (Ch' Ct Ct' Cc Cc' Cm' Cp Cw Cw' : Ctx),
      hp.tl.ix.U.getD 2 none = some iU3 ∧
      Ok (Model.Head.hear h L hp cov Lc.check.plain) (fresh F) C x Fh' Ch' ∧
      OkL (Model.rootInH [iU3]) Lc Fh' Ch' () Lt Ft Ct ∧
      Ok (Model.Head.tablesOf h L hp cov x) Ft Ct t Ft' Ct' ∧
      hp.tl.closeFuns t.funs = some tl0 ∧
      OkL tl0.transcript Lt Ft' Ct' tl1 Lt' Fc Cc ∧
      Ok (Model.Head.weightsClaim (runOf h L b hp cov x t iU3) lay) Fc Cc claim Fc' Cc' ∧
      Ok (Model.wsForkEnd lay #[claim] #[x.sV]) Fc' Cc' wo Fm' Cm' ∧
      (Fm'.next == hp.nMsg) = true ∧
      Ok (SubM.setPlanClaims hp.nLin) Fm' Cm' () Fp Cp ∧
      OkL (Model.t2Batch Fm'.next) Lt' Fp Cp () Lw Fw Cw ∧
      OkL (Model.Head.walk (runOf h L b hp cov x t iU3) tl1 wo) Lw Fw Cw tl2 Lw' Fw' Cw' ∧
      Kept F (fresh F) ∧ Kept F Ft ∧ Kept F Ft' ∧ Kept F Fc ∧ Kept F Fc' ∧ Kept F Fw := by
  obtain ⟨a1, a2, a3, a4, iU3, x, t, tl0, tl1, tl2, claim, _, Lt, Lt', Lw, Lw', _,
    Fh', Ft, Ft', Fc, Fc', Fm', Fp, Fw, Fw', _, _, Ch', Ct, Ct', Cc, Cc', Cm', Cp, Cw, Cw', _, _,
    hU, sx, sr, st, hcl, ss, sc, sm, hn, sp, sb, sw, _, _, _, _, _, _, k⟩ := run_whole H
  exact ⟨a1, a2, a3, a4, iU3, x, t, tl0, tl1, tl2, claim, Lt, Lt', Lw, Lw',
    Fh', Ft, Ft', Fc, Fc', Fm', Fp, Fw, Fw', Ch', Ct, Ct', Cc, Cc', Cm', Cp, Cw, Cw',
    hU, sx, sr, st, hcl, ss, sc, sm, hn, sp, sb, sw, k⟩

/-- What run_whole says of a run, with the record R of the run, the state Fw in which the walk
begins and the claim cl on the weights as letters: the four public tests on the arguments have
passed; the public parts of R are the routine's arguments; its other parts are what hear and
tablesOf have returned and the number of the array of the reads; and the routines have succeeded,
each from what the one before has left, from the fresh state and the caller's context C to the
link's state Lc', the state G and the context D that the whole routine leaves. -/
def Chained (h : Model.Head.Shape) (L : Model.Head.HL) (b : Model.Head.Border)
    (hp : Model.Head.HPlanH2) (O : Model.Head.Owner) (cov : Model.Head.Covered)
    (lay : Model.WsLay) (Lc : Model.LinkCtx) (F : Fork) (C : Ctx) (wo : Model.WsForkOut)
    (Lc' : Model.LinkCtx) (G : Fork) (D : Ctx) (R : Model.Head.Run) (Fw : Fork)
    (cl : Model.WsClaim) : Prop :=
  ∃ (tl0 tl1 tl2 : Model.HTailF2) (nE : ℕ) (Lt Lt' Lw Lw' Ls : Model.LinkCtx)
    (Fh' Ft Ft' Fc Fc' Fm' Fp Fw' Fs Fd : Fork)
    (Ch' Ct Ct' Cc Cc' Cm' Cp Cw Cw' Cs Cd : Ctx),
    cov.sized h.T = true ∧ Model.Head.planHanded hp Lc.list F = true ∧
    (!O.tl.ix.TX.isEmpty && O.tl.kTX.back? == some b.kxb) = true ∧ (hp.NCL == 1) = true ∧
    R.h = h ∧ R.L = L ∧ R.b = b ∧ R.hp = hp ∧ R.cov = cov ∧
    hp.tl.ix.U.getD 2 none = some R.iU3 ∧
    Ok (Model.Head.hear h L hp cov Lc.check.plain) (fresh F) C R.x Fh' Ch' ∧
    OkL (Model.rootInH [R.iU3]) Lc Fh' Ch' () Lt Ft Ct ∧
    Ok (Model.Head.tablesOf h L hp cov R.x) Ft Ct R.t Ft' Ct' ∧
    hp.tl.closeFuns R.t.funs = some tl0 ∧
    OkL tl0.transcript Lt Ft' Ct' tl1 Lt' Fc Cc ∧
    Ok (Model.Head.weightsClaim R lay) Fc Cc cl Fc' Cc' ∧
    Ok (Model.wsForkEnd lay #[cl] #[R.x.sV]) Fc' Cc' wo Fm' Cm' ∧
    (Fm'.next == hp.nMsg) = true ∧
    Ok (SubM.setPlanClaims hp.nLin) Fm' Cm' () Fp Cp ∧
    OkL (Model.t2Batch Fm'.next) Lt' Fp Cp () Lw Fw Cw ∧
    OkL (Model.Head.walk R tl1 wo) Lw Fw Cw tl2 Lw' Fw' Cw' ∧
    OkL (Model.Head.selfTests R tl2 wo) Lw' Fw' Cw' () Ls Fs Cs ∧
    tl2.equationsLaidF = some nE ∧
    OkL (Model.doorH nE) Ls Fs Cs () Lc' Fd Cd ∧
    (Fd.nClaim == Fd.planClaimsF) = true ∧
    Ok SubM.allTaken Fd Cd () G D ∧
    tl2.foldAllTakenF = true ∧
    Kept F (fresh F) ∧ Kept F Ft ∧ Kept F Ft' ∧ Kept F Fc ∧ Kept F Fc' ∧ Kept F Fw

/-- run_whole in that word. -/
theorem run_chained {h : Model.Head.Shape} {L : Model.Head.HL} {b : Model.Head.Border}
    {hp : Model.Head.HPlanH2} {O : Model.Head.Owner} {cov : Model.Head.Covered}
    {lay : Model.WsLay} {Lc Lc' : Model.LinkCtx} {F G : Fork} {C D : Ctx} {wo : Model.WsForkOut}
    (H : OkL (Model.Head.runForkHidH2 h L b hp O cov lay) Lc F C wo Lc' G D) :
    ∃ R Fw cl, Chained h L b hp O cov lay Lc F C wo Lc' G D R Fw cl := by
  obtain ⟨a1, a2, a3, a4, iU3, x, t, tl0, tl1, tl2, claim, nE, Lt, Lt', Lw, Lw', Ls,
    Fh', Ft, Ft', Fc, Fc', Fm', Fp, Fw, Fw', Fs, Fd,
    Ch', Ct, Ct', Cc, Cc', Cm', Cp, Cw, Cw', Cs, Cd, hU, rest⟩ := run_whole H
  exact ⟨runOf h L b hp cov x t iU3, Fw, claim, tl0, tl1, tl2, nE, Lt, Lt', Lw, Lw', Ls,
    Fh', Ft, Ft', Fc, Fc', Fm', Fp, Fw', Fs, Fd, Ch', Ct, Ct', Cc, Cc', Cm', Cp, Cw, Cw', Cs, Cd,
    a1, a2, a3, a4, rfl, rfl, rfl, rfl, rfl, hU, rest⟩

/-- A routine is a function: from one state and one context it returns one value and leaves one
state and one context. -/
theorem ok_unique {α : Type} {m : SubM α} {F G G' : Fork} {C D D' : Ctx} {a a' : α}
    (h : Ok m F C a G D) (h' : Ok m F C a' G' D') : a = a' ∧ G = G' ∧ D = D' := by
  unfold Ok at h h'
  rw [h] at h'
  cases h'
  exact ⟨rfl, rfl, rfl⟩

/-- The same for a routine of a link. -/
theorem okL_unique {α : Type} {m : Model.LinkM α} {Lc L1 L1' : Model.LinkCtx} {F G G' : Fork}
    {C D D' : Ctx} {a a' : α} (h : OkL m Lc F C a L1 G D) (h' : OkL m Lc F C a' L1' G' D') :
    a = a' ∧ L1 = L1' ∧ G = G' ∧ D = D' := by
  obtain ⟨e, f, c⟩ := ok_unique h h'
  cases e
  exact ⟨rfl, rfl, f, c⟩

/-- Two records of a run with the same eight parts are one. -/
theorem run_ext {R R' : Model.Head.Run} (a : R.h = R'.h) (b : R.L = R'.L) (c : R.b = R'.b)
    (d : R.hp = R'.hp) (e : R.cov = R'.cov) (f : R.x = R'.x) (g : R.t = R'.t)
    (i : R.iU3 = R'.iU3) : R = R' := by
  obtain ⟨h1, L1, b1, p1, c1, x1, t1, i1⟩ := R
  obtain ⟨h2, L2, b2, p2, c2, x2, t2, i2⟩ := R'
  dsimp only at a b c d e f g i
  subst a b c d e f g i
  rfl

/-- The arguments, the link's state, the state and the context that the caller hands in fix the
record of the run, the state in which the walk begins and the claim on the weights. -/
theorem chained_unique {h : Model.Head.Shape} {L : Model.Head.HL} {b : Model.Head.Border}
    {hp : Model.Head.HPlanH2} {O : Model.Head.Owner} {cov : Model.Head.Covered}
    {lay : Model.WsLay} {Lc Lc' : Model.LinkCtx} {F G : Fork} {C D : Ctx} {wo : Model.WsForkOut}
    {R R' : Model.Head.Run} {Fw Fw' : Fork} {cl cl' : Model.WsClaim}
    (A : Chained h L b hp O cov lay Lc F C wo Lc' G D R Fw cl)
    (B : Chained h L b hp O cov lay Lc F C wo Lc' G D R' Fw' cl') :
    R = R' ∧ Fw = Fw' ∧ cl = cl' := by
  obtain ⟨tl0, tl1, _, _, Lt, Lt', Lw, _, _, Fh, Ft, Ft', Fc, Fc', Fm, Fp, _, _, _,
    Ch, Ct, Ct', Cc, Cc', Cm, Cp, Cw, _, _, _, _, _, _, _, e1, e2, e3, e4, e5, hU,
    sx, sr, st, hcl, ss, sc, sm, _, sp, sb, _⟩ := A
  obtain ⟨ul0, ul1, _, _, Mt, Mt', Mw, _, _, Gh, Gt, Gt', Gc, Gc', Gm, Gp, _, _, _,
    Dh, Dt, Dt', Dc, Dc', Dm, Dp, Dw, _, _, _, _, _, _, _, f1, f2, f3, f4, f5, hV,
    tx, tr, tt, hdl, ts, tc, tm, _, tp, tb, _⟩ := B
  have eU : R.iU3 = R'.iU3 := Option.some.inj (hU.symm.trans hV)
  obtain ⟨ex, rfl, rfl⟩ := ok_unique sx tx
  rw [← eU] at tr
  obtain ⟨_, rfl, rfl, rfl⟩ := okL_unique sr tr
  rw [← ex] at tt
  obtain ⟨et, rfl, rfl⟩ := ok_unique st tt
  rw [← et] at hdl
  obtain rfl : tl0 = ul0 := Option.some.inj (hcl.symm.trans hdl)
  obtain ⟨rfl, rfl, rfl, rfl⟩ := okL_unique ss ts
  have eR : R = R' := run_ext (e1.trans f1.symm) (e2.trans f2.symm) (e3.trans f3.symm)
    (e4.trans f4.symm) (e5.trans f5.symm) ex et eU
  subst eR
  obtain ⟨rfl, rfl, rfl⟩ := ok_unique sc tc
  obtain ⟨_, rfl, rfl⟩ := ok_unique sm tm
  obtain ⟨_, rfl, rfl⟩ := ok_unique sp tp
  obtain ⟨_, _, rfl, _⟩ := okL_unique sb tb
  exact ⟨rfl, rfl, rfl⟩

/-- A shorter and weaker form of run_chain: six of the routines, each with states and contexts of
its own, which nothing ties to each other, and without the tests. -/
theorem run_parts {h : Model.Head.Shape} {L : Model.Head.HL} {b : Model.Head.Border}
    {hp : Model.Head.HPlanH2} {O : Model.Head.Owner} {cov : Model.Head.Covered}
    {lay : Model.WsLay} {Lc Lc' : Model.LinkCtx} {F G : Fork} {C D : Ctx} {wo : Model.WsForkOut}
    (H : OkL (Model.Head.runForkHidH2 h L b hp O cov lay) Lc F C wo Lc' G D) :
    cov.sized h.T = true ∧ ∃ (iU3 : ℕ) (x : Model.Head.Heard) (t : Model.Head.Tables)
      (tl0 tl1 tl2 : Model.HTailF2) (claim : Model.WsClaim)
      (Lt Lt' Lw Lw' : Model.LinkCtx)
      (Fh Fh' Ft Ft' Fs Fs' Fc Fc' Fm Fm' Fw Fw' : Fork)
      (Ch Ch' Ct Ct' Cs Cs' Cc Cc' Cm Cm' Cw Cw' : Ctx),
      hp.tl.ix.U.getD 2 none = some iU3 ∧
      Fh = ({ trees := F.trees } : Fork).fillL ∧
      Ok (Model.Head.hear h L hp cov Lc.check.plain) Fh Ch x Fh' Ch' ∧
      Ok (Model.Head.tablesOf h L hp cov x) Ft Ct t Ft' Ct' ∧
      hp.tl.closeFuns t.funs = some tl0 ∧
      OkL tl0.transcript Lt Fs Cs tl1 Lt' Fs' Cs' ∧
      Ok (Model.Head.weightsClaim (runOf h L b hp cov x t iU3) lay) Fc Cc claim Fc' Cc' ∧
      Ok (Model.wsForkEnd lay #[claim] #[x.sV]) Fm Cm wo Fm' Cm' ∧
      OkL (Model.Head.walk (runOf h L b hp cov x t iU3) tl1 wo) Lw Fw Cw tl2 Lw' Fw' Cw' ∧
      Kept F Fh ∧ Kept F Ft ∧ Kept F Fs ∧ Kept F Fc ∧ Kept F Fm ∧ Kept F Fw := by
  obtain ⟨hcov, _, _, _, iU3, x, t, tl0, tl1, tl2, claim, Lt, Lt', Lw, Lw', Fh', Ft, Ft', Fc, Fc',
    Fm', Fp, Fw, Fw', Ch', Ct, Ct', Cc, Cc', Cm', Cp, Cw, Cw',
    hU, sx, _, st, hcl, ss, sc, sm, _, _, _, sw, kh, kt, k2, kc, k3, kw⟩ := run_chain H
  exact ⟨hcov, iU3, x, t, tl0, tl1, tl2, claim, Lt, Lt', Lw, Lw',
    fresh F, Fh', Ft, Ft', Ft', Fc, Fc, Fc', Fc', Fm', Fw, Fw',
    C, Ch', Ct, Ct', Ct', Cc, Cc, Cc', Cc', Cm', Cw, Cw',
    hU, rfl, sx, st, hcl, ss, sc, sm, sw, kh, kt, k2, kc, k3, kw⟩

/-! ## What the plan says of the caller's arrays and of the smallness test's record -/

/-- The routine's test on what the caller hands in: if it passes, every array has as many columns in
the caller's state as in the plan's. -/
theorem cols_of_handed {hp : Model.Head.HPlanH2} {list : Model.Tail2} {F : Fork}
    (h : Model.Head.planHanded hp list F = true) (t : ℕ) : colsOf F t = colsOf hp.Fp t := by
  unfold Model.Head.planHanded at h
  rw [Bool.and_eq_true] at h
  have e : (F.trees.map fun X => (X.name, X.R, X.K, X.rows.size)) =
      hp.Fp.trees.map fun X => (X.name, X.R, X.K, X.rows.size) := by
    simpa using h.2
  have e2 := congrArg
    (fun a : Array (String × ℕ × ℕ × ℕ) => ((a[t]?).map (·.2.2.1)).getD 0) e
  unfold colsOf
  simpa [Array.getElem?_map, Option.map_map, Function.comp_def] using e2

/-- A state that is kept from F is kept from every state with the same numbers of columns. -/
theorem kept_of_cols {F F' X : Fork} (e : ∀ t, colsOf F t = colsOf F' t) (k : Kept F X) :
    Kept F' X := ⟨k.1, fun t => (k.2 t).trans (e t)⟩

/-- If the check of the head's sub-proof succeeds, every array has as many columns in the state that
the caller handed in as in the plan's state, which is public. -/
theorem run_cols {h : Model.Head.Shape} {L : Model.Head.HL} {b : Model.Head.Border}
    {hp : Model.Head.HPlanH2} {O : Model.Head.Owner} {cov : Model.Head.Covered}
    {lay : Model.WsLay} {Lc Lc' : Model.LinkCtx} {F G : Fork} {C D : Ctx} {wo : Model.WsForkOut}
    (H : OkL (Model.Head.runForkHidH2 h L b hp O cov lay) Lc F C wo Lc' G D) (t : ℕ) :
    colsOf F t = colsOf hp.Fp t := cols_of_handed (run_chain H).2.1 t

/-- The draw of the smallness test's matrix leaves the list of matrices and their number. -/
theorem drawMatrixF_keeps {tl tl' : Model.HTailF2} {F G : Fork} {C D : Ctx}
    (h : Ok tl.drawMatrixF F C tl' G D) : tl'.mats = tl.mats ∧ tl'.NM = tl.NM := by
  unfold Model.HTailF2.drawMatrixF at h
  obtain ⟨_, _, _, _, h⟩ := (ok_bind _ _ _ _ _ _ _).mp h
  obtain ⟨_, _, _, _, h⟩ := (ok_bind _ _ _ _ _ _ _).mp h
  obtain ⟨e, _, _⟩ := (ok_pure _ _ _ _ _ _).mp h
  rw [e]
  exact ⟨rfl, rfl⟩

/-- The messages of the smallness test leave the list of matrices and their number. -/
theorem transcript_keeps {tl0 tl1 : Model.HTailF2} {Lc Lc' : Model.LinkCtx} {F G : Fork}
    {C D : Ctx} (h : OkL tl0.transcript Lc F C tl1 Lc' G D) :
    tl1.mats = tl0.mats ∧ tl1.NM = tl0.NM := by
  unfold Model.HTailF2.transcript Model.HTailF2.transcriptF at h
  obtain ⟨_, _, _, _, _, h⟩ := stepL h
  obtain ⟨_, _, _, _, _, h⟩ := stepL h
  obtain ⟨_, _, _, _, _, h⟩ := stepL h
  obtain ⟨_, _, _, _, _, h⟩ := stepL h
  obtain ⟨tl', _, _, s5, h⟩ := stepSub h
  obtain ⟨_, _, _, _, _, h⟩ := stepL h
  obtain ⟨_, _, _, _, _, h⟩ := stepL h
  obtain ⟨_, _, _, _, _, h⟩ := stepL h
  rw [okL_pure] at h
  have e := drawMatrixF_keeps s5
  rw [h.1]
  exact ⟨e.1, e.2⟩

#print axioms keeps_rootInH
#print axioms keeps_transcript
#print axioms keeps_t2Batch
#print axioms keeps_tablesOf
#print axioms keeps_weightsClaim
#print axioms okL_map
#print axioms run_whole
#print axioms run_chain
#print axioms run_chained
#print axioms chained_unique
#print axioms run_parts
#print axioms cols_of_handed
#print axioms run_cols
#print axioms transcript_keeps

end OnBytes.Road.Hd.Parts
