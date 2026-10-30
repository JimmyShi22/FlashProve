-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LateSide/Run.lean: ONE COMPILED RUN: MODE I OF THE TOKEN PROGRAM (proveC,
Johnson/TokenRules/Chunks.lean) IS THE RUN THAT IS LAID LATE (lateProof,
Johnson/LateWorld/Defs.lean), at coins that are drawn first. Definitions, and one theorem with its
proof, at letters.

Lemmas of one step of a proof. This file states no goal of the release.
The definitions of this file are a device of one step of a proof of index privacy. They stand in no
statement on the scheme.

  outLate       what is handed out, and the table, out of (the three things that handOut reads, the
                table, the run's log).
  lateProof_eq  lateProof in these terms.
  allLeaf_handDataT   what the token side reads off as the run's own leaves are leaves' entries.
  outLate_ghost the exchange of queries goes through outLate.
  RunGood       what is asked of the state before a run: the premises of the rule of release.
  end_eq        the end of the token program in mode I, in these terms: from the rule of release.
  runLate       THE THEOREM. Its way:
      the token program is "all hashing, then the end";
      the end is one outcome, a function of what is kept of the hashing (end_eq);
      mode I of the hashing is the run of its erasure with a log (modeI_defer_at,
        Compile/DeferRun/Proof.lean), the log taken from the empty one (interp_defer_shift);
      the names of later tries are written back (runDefer_plainOf, Johnson/GhostSide/Back.lean;
        runDefer_plain_run, Johnson/LateSide/Names.lean; outLate_ghost);
      the token side's hashing does what the compiled prover's chain does (sameHand,
        Johnson/LateSide/Hand.lean), under the rule that defers.

THE RULE OF RELEASE (Spec.release, Johnson/TokenRules/ReleaseSpec.lean) IS A HYPOTHESIS of end_eq
and runLate. It is proved in Johnson/TokenRel/Release.lean and laid in where runLate is called
(runStep, Johnson/LateSide/Units.lean).
Terms: lean/GLOSSARY.md.

-/
import Johnson.LateSide.Hand
import Johnson.LateSide.Names
import Johnson.HopSide.Proof
import Johnson.LateWorld.Defs
import Johnson.TokenRules.ReleaseSpec
import Johnson.TokenRules.Marks
import Compile.DeferRun.Proof

set_option autoImplicit false

noncomputable section

namespace OnBytes.LateSide
open _root_.Compile hiding ON
open TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch Rom Prob
open OnBytes.Prover OnBytes.WholeKey OnBytes.TokenSide OnBytes.GhostSide OnBytes.TokenRules
open OnBytes.LateWorld
open _root_.Compile.Batch.Disc (TidyO)
open _root_.Compile.DeferRun (Marks qa keep)
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout Marks

variable {I X : Type} {lam : ℕ} {L : BatchProtocolWithLeafBody I X}

section Out
variable {K : ℕ} {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E) (wq : ProtocolQueryLayout lam K Q) (x : Y)

/-- What is handed out, and the table. d: the verifier messages, the string, the entries of the
run's own leaves that are read; or no value. T, lg: the table and the run's log behind the hashing.
-/
def outLate (stop : Rho Q.loc.shape → Bool) (xt : ℕ → TreeK lam L)
    (d : Res (Rho Q.loc.shape × OneProtocolProof lam Q × Trace (typedOracleFamily lam K L))) (T : Table (typedOracleFamily lam K L))
    (lg : Trace (typedOracleFamily lam K L)) : Option (OneProtocolProof lam Q) × Table (typedOracleFamily lam K L) :=
  match d with
  | .ok d =>
      if stop d.1 then (none, T)
      else (some d.2.1, ((T.lay (lg.filter notLeaf)).lay d.2.2).lay (extLaid Q wq x xt d.1))
  | _ => (none, T)

end Out

section Plain
variable {K : ℕ} (t : Tag) {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E) (wq : ProtocolQueryLayout lam K Q)
  (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L)
  (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X)
  (cms : List (Dig lam)) (x : Y) (y : E.Str) (xt : ℕ → TreeK lam L) (cap : ℕ → ℕ)

theorem lateProof_eq (stop : Rho Q.loc.shape → Bool) (σ : Strat Q.loc.shape Unit)
    (co : Coins lam L) (T : Table (typedOracleFamily lam K L)) :
    lateProof t Q wq embS embP xin cms x y xt cap stop σ co T =
      ((chainX t Q wq embS embP xin cms x cap σ co).runDefer mkRun T []).map fun o =>
        outLate Q wq x stop xt (handData Q wq x y xt co o.1) o.2.1 o.2.2 := by
  unfold lateProof
  refine congrArg (fun f => PMF.map f _) (funext fun o => ?_)
  obtain ⟨r, T', lg⟩ := o
  cases r with
  | ok z =>
    have key : ∀ b : Bool, stop z.1 = b →
        handOut Q wq x y xt (!b) co (Res.ok z, ⟨T', lg, [], false⟩) =
          outLate Q wq x stop xt (handData Q wq x y xt co (Res.ok z)) T' lg := by
      intro b hb
      cases b
      · show _ = if stop z.1 = true then _ else _
        rw [if_neg (by rw [hb]; exact Bool.false_ne_true)]
        rfl
      · show _ = if stop z.1 = true then _ else _
        rw [if_pos hb]
        rfl
    exact key _ rfl
  | noFormat => rfl
  | ranOut j => rfl

end Plain

/-- What the token side reads off as the run's own leaves are leaves' entries. -/
theorem allLeaf_handDataT {K : ℕ} {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E)
    (wq : ProtocolQueryLayout lam K Q) (x : Y) (y : E.Str) (xt : ℕ → TreeT lam L) (preX : Bits)
    (pre : ℕ → Bool → Bits → Bits) (a : Tok × CoinsD lam L × Res (OutT lam L Q.loc.shape))
    (vs : List Bits) (d' : Rho Q.loc.shape × OneProtocolProof lam Q × Trace (typedOracleFamily lam K L))
    (h : handDataT Q wq x y xt preX pre a vs = .ok d') : AllLeaf d'.2.2 := by
  obtain ⟨salt, cd, r⟩ := a
  cases r with
  | ok z =>
    have h' : Res.ok _ = Res.ok d' := h
    obtain rfl := Res.ok.inj h'
    exact allLeaf_laidK _ _ _ _ _
  | noFormat =>
    have h' : (Res.noFormat : Res (Rho Q.loc.shape × OneProtocolProof lam Q × Trace (typedOracleFamily lam K L))) =
        Res.ok d' := h
    cases h'
  | ranOut j =>
    have h' : (Res.ranOut j : Res (Rho Q.loc.shape × OneProtocolProof lam Q × Trace (typedOracleFamily lam K L))) =
        Res.ok d' := h
    cases h'

variable (W : QueryLayout lam L)

section Ghost
variable {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E) (wq : ProtocolQueryLayout lam W.K Q) (x : Y)

/-- The exchange of queries goes through outLate. -/
theorem outLate_ghost (stop : Rho Q.loc.shape → Bool) (xt : ℕ → TreeK lam L)
    (d : Res (Rho Q.loc.shape × OneProtocolProof lam Q × Trace (typedOracleFamily lam W.K L)))
    (hd : ∀ d', d = .ok d' → AllLeaf d'.2.2) (T : Table (typedOracleFamily lam W.K L))
    (lg : Trace (typedOracleFamily lam W.K L)) :
    ((outLate Q wq x stop xt d (Table.via (ghost W) T) (lg.map (ghostQA W))).1,
      Table.via (ghost W)
        (outLate Q wq x stop xt d (Table.via (ghost W) T) (lg.map (ghostQA W))).2) =
      outLate Q wq x stop xt d T lg := by
  cases d with
  | ok d' =>
    by_cases hs : stop d'.1 = true
    · simp only [outLate, if_pos hs, via_via_ghost]
    · simp only [outLate, if_neg hs, lay_ghost, via_via_ghost, filter_notLeaf_ghost,
        map_ghostQA_allLeaf W (hd d' rfl), map_ghostQA_allLeaf W (allLeaf_extLaid Q wq x xt d'.1)]
  | noFormat => simp only [outLate, via_via_ghost]
  | ranOut j => simp only [outLate, via_via_ghost]

end Ghost

section Run
variable (t : Tag) {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E) (wq : ProtocolQueryLayout lam W.K Q)
  (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L)
  (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X)
  (cms : List (Dig lam)) (x : Y) (y : E.Str) (xt : ℕ → TreeT lam L) (preX : Bits)
  (σ : Strat Q.loc.shape Unit) (ln : RunLen lam L) (pre : ℕ → Bool → Bits → Bits) (cap : ℕ → ℕ)
  (stop : Rho Q.loc.shape → Bool)

/-- What is asked of the state before a run: the premises of the rule of release. -/
structure RunGood (bl bf : ℕ) (sd : (t : Tag) → FbIn lam L t → Prop)
    (D : DSt (typedOracleFamily lam W.K L)) : Prop where
  fr : bl ≤ ln.fr
  sFS : bf ≤ ln.sFS
  dig : bf ≤ lam
  ext : ∀ p, wq.ext.leaf p < (xt (wq.ext.which p)).tok.length
  tidy : TidyO (rulesT W.K L lam bl bf sd) D
  laid : Laid D
  tree : ∀ k, TreeOKT D [] (xt k)
  leaf : ∀ k, LeafAt D (xt k) preX

/-- The end of the token program in mode I is one outcome: what outLate gives at what is read off
the hashing's outcome, the store, the table and the new evaluations. -/
theorem end_eq (hRel : TokenRules.Spec.release) {bl bf : ℕ}
    {sd : (t : Tag) → FbIn lam L t → Prop} {D : DSt (typedOracleFamily lam W.K L)}
    (hD : RunGood W Q wq xt preX ln bl bf sd D)
    (u : (Tok × CoinsD lam L × Res (OutT lam L Q.loc.shape)) × DSt (typedOracleFamily lam W.K L))
    (hu : u ∈ ((hashT t Q wq embS embP xin cms x σ ln pre cap).run true D).support) :
    ((endC Q wq x y xt preX pre stop u.1).run true u.2).map (fun v => (v.1, v.2.table)) =
      PMF.pure (outLate Q wq x stop (fun k => (xt k).toK (fun w => u.2.vals.getD w []) preX)
        (handDataT Q wq x y xt preX pre u.1 u.2.vals) u.2.table
        ((u.2.evs.map qa).drop D.evs.length)) := by
  obtain ⟨⟨salt, cd, r⟩, D₁⟩ := u
  have hN := fun hz => TokenRules.releaseNone I X lam W.K L Y E Q wq x y xt preX pre stop true D₁
    (salt, cd, r) hz
  cases r with
  | noFormat =>
    rw [hN (fun z hz => by cases hz), PMF.pure_map]
    rfl
  | ranOut j =>
    rw [hN (fun z hz => by cases hz), PMF.pure_map]
    rfl
  | ok z =>
    by_cases hs : stop z.rho = true
    · rw [hN (fun z' hz => by cases hz; exact hs), PMF.pure_map]
      show PMF.pure (none, D₁.table) = PMF.pure (if stop z.rho then _ else _)
      rw [if_pos hs]
    · obtain ⟨D₂, e1, e2, -⟩ := hRel I X lam W.K L bl bf sd t Y E Q wq embS embP xin cms x y xt preX
        σ ln pre cap stop D D₁ (salt, cd, Res.ok z) z hD.fr hD.sFS hD.dig hD.ext hD.tidy hD.laid
        hD.tree hD.leaf hu rfl (by simpa using hs)
      rw [e1, PMF.pure_map, e2, ← List.map_drop]
      show _ = PMF.pure (if stop z.rho then _ else _)
      rw [if_neg hs]
      rfl

variable {Ω : Type} {μ : PMF Ω} {Z : RunCo → Prop} (rl : RunLens Ω μ ln Z)

/-- **One compiled run: mode I of the token program is the run that is laid late**, its coins drawn
first; the tables exchanged. -/
theorem runLate (hRel : TokenRules.Spec.release) {bl bf : ℕ}
    {sd : (t : Tag) → FbIn lam L t → Prop} {D : DSt (typedOracleFamily lam W.K L)}
    (hD : RunGood W Q wq xt preX ln bl bf sd D)
    (hR : RoutedT W (hashT t Q wq embS embP xin cms x σ ln pre cap)) (hW : wq.OKG)
    (hC : CoversRun Z ln Q.loc.shape Q.ann wq.sh)
    (hX : ExtTie wq.ext (fun k => (xt k).toK (fun w => D.vals.getD w []) preX) xt preX D.vals) :
    ((proveC t Q wq embS embP xin cms x y xt preX σ ln pre cap stop).run true D).map
        (fun v => (v.1, Table.via (ghost W) v.2.table)) =
      μ.bind fun ω => lateProof t Q wq embS embP xin cms x y
        (fun k => (xt k).toK (fun w => D.vals.getD w []) preX) cap stop σ (coRun rl pre ω)
        (Table.via (ghost W) D.table) := by
  -- the token program: all hashing, then the end, which is one outcome
  have eA : ((proveC t Q wq embS embP xin cms x y xt preX σ ln pre cap stop).run true D).map
      (fun v => (v.1, Table.via (ghost W) v.2.table)) =
      (((hashT t Q wq embS embP xin cms x σ ln pre cap).run true D).map keep).map fun k =>
        ((outLate Q wq x stop (fun j => (xt j).toK (fun w => k.1.2.getD w []) preX)
          (handDataT Q wq x y xt preX pre k.1.1 k.1.2) k.2.1 (k.2.2.drop D.evs.length)).1,
        Table.via (ghost W) (outLate Q wq x stop
          (fun j => (xt j).toK (fun w => k.1.2.getD w []) preX)
          (handDataT Q wq x y xt preX pre k.1.1 k.1.2) k.2.1 (k.2.2.drop D.evs.length)).2) := by
    unfold proveC
    rw [Life2.run_bind, PMF.map_bind, PMF.map_comp]
    refine Rom.bind_congr_support _ fun u hu => ?_
    have e := congrArg (PMF.map fun o : Option (OneProtocolProof lam Q) × Table (typedOracleFamily lam W.K L) =>
      (o.1, Table.via (ghost W) o.2))
      (end_eq W t Q wq embS embP xin cms x y xt preX σ ln pre cap stop hRel hD u hu)
    rw [PMF.map_comp, PMF.pure_map] at e
    exact e
  rw [eA, DeferRun.modeI_defer_at mkHash _ D
    (TokenRules.marksHash I X lam W.K L t Y E Q wq embS embP xin cms x σ ln pre cap D.vals)]
  -- the log from the empty one
  have eC : (erase (hashT t Q wq embS embP xin cms x σ ln pre cap) D.vals).runDefer mkHash D.table
      (D.evs.map qa) =
      ((erase (hashT t Q wq embS embP xin cms x σ ln pre cap) D.vals).runDefer mkHash D.table
        []).map fun o => (o.1, (o.2.1, D.evs.map qa ++ o.2.2)) := by
    have := OComp.interp_defer_shift mkHash Handler.lazy
      (erase (hashT t Q wq embS embP xin cms x σ ln pre cap) D.vals) D.table (D.evs.map qa) []
    rwa [List.append_nil] at this
  -- the names of later tries written back
  have eD := runDefer_plainOf W mkHash hR D.vals (Table.via (ghost W) D.table) []
  rw [via_via_ghost, List.map_nil, runDefer_plain_run] at eD
  rw [eC, ← eD, PMF.map_comp, PMF.map_comp]
  -- the token side's hashing does what the chain does, under the rule that defers
  have eG := (sameHand t Q wq embS embP xin cms x y
    (fun k => (xt k).toK (fun w => D.vals.getD w []) preX) xt preX σ ln pre cap rl D.vals hW hC
    hX).sound_const (Handler.defer mkRun Handler.lazy) (Table.via (ghost W) D.table, [])
  have eH : (μ.bind fun ω => lateProof t Q wq embS embP xin cms x y
      (fun k => (xt k).toK (fun w => D.vals.getD w []) preX) cap stop σ (coRun rl pre ω)
      (Table.via (ghost W) D.table)) =
      (μ.bind fun ω => ((chainX t Q wq embS embP xin cms x cap σ (coRun rl pre ω)).bind fun r =>
        OComp.pure (handData Q wq x y (fun k => (xt k).toK (fun w => D.vals.getD w []) preX)
          (coRun rl pre ω) r)).interp (Handler.defer mkRun Handler.lazy)
          (Table.via (ghost W) D.table, [])).map fun o =>
        outLate Q wq x stop (fun k => (xt k).toK (fun w => D.vals.getD w []) preX) o.1 o.2.1
          o.2.2 := by
    rw [PMF.map_bind]
    refine congrArg _ (funext fun ω => ?_)
    rw [lateProof_eq, OComp.interp_bind]
    simp only [OComp.interp_pure]
    rw [PMF.map_bind]
    simp only [PMF.pure_map]
    rfl
  rw [eH, eG, PMF.map_comp]
  refine HopSide.map_congr_support _ fun o ho => ?_
  have hp : D.vals <+: o.1.2 :=
    HopSide.post_interp (Handler.defer mkRun Handler.lazy) (plainOf_grows _ D.vals) _ o ho
  have hk : (fun j => (xt j).toK (fun w => o.1.2.getD w []) preX) =
      fun k => (xt k).toK (fun w => D.vals.getD w []) preX :=
    funext fun j => HopSide.toK_prefix hp preX (xt j) fun a ha => ((hD.tree j) a ha).1
  have hl : (D.evs.map qa ++ o.2.2.map (ghostQA W)).drop D.evs.length = o.2.2.map (ghostQA W) := by
    have := List.drop_left (l₁ := D.evs.map qa) (l₂ := o.2.2.map (ghostQA W))
    rwa [List.length_map] at this
  show ((outLate Q wq x stop (fun j => (xt j).toK (fun w => o.1.2.getD w []) preX)
      (handDataT Q wq x y xt preX pre o.1.1 o.1.2) (Table.via (ghost W) o.2.1)
      ((D.evs.map qa ++ o.2.2.map (ghostQA W)).drop D.evs.length)).1,
    Table.via (ghost W) (outLate Q wq x stop (fun j => (xt j).toK (fun w => o.1.2.getD w []) preX)
      (handDataT Q wq x y xt preX pre o.1.1 o.1.2) (Table.via (ghost W) o.2.1)
      ((D.evs.map qa ++ o.2.2.map (ghostQA W)).drop D.evs.length)).2) =
    outLate Q wq x stop (fun k => (xt k).toK (fun w => D.vals.getD w []) preX)
      (handDataT Q wq x y xt preX pre o.1.1 o.1.2) o.2.1 o.2.2
  rw [hk, hl]
  exact outLate_ghost W Q wq x stop _ _
    (fun d' hd' => allLeaf_handDataT Q wq x y xt preX pre o.1.1 o.1.2 d' hd') _ _

end Run

end OnBytes.LateSide

#print axioms OnBytes.LateSide.end_eq
#print axioms OnBytes.LateSide.runLate
