-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/EqSetup.lean: given `Spec.eqProveB` and under the hypotheses of `Spec.eqSetupB`, the
honest setup has the distribution of the samples of the lifetime game's setup, then the reduction's
setup program. Of the true key only the index, `keyOf` and the encoding randomness of the copies are
compared (Compile/Batch/SpecEq.lean).

The programs: the honest setup is `CpL` (a program of `LStep`, Rom/DeferLate.lean), the reduction's
setup program is `CpW` (both: Compile/Batch/Mirror.lean); the game's setup:
Compile/Batch/SpecLifeStar.lean. The hypotheses of `Spec.eqSetupB`: `L.Wired`, `W.OKG`, `GrFitPB W`,
`WP.OK`.

  `eqSetupB`  Spec.eqProveB → Spec.eqSetupB (Compile/Batch/SpecEqProve.lean,
              Compile/Batch/SpecEq.lean).

Test and Link are executions with one slot (`bsess_one_bind`). The proof moves the game's samples to
the front: they do not depend on the runs of the hash work, so the order can be changed
(`PMF.bind_comm`). (words of this library: lean/GLOSSARY.md)

Notation: the reduction: `theWrapBP` (Compile/Batch/PubWr.lean); names that end in L (`CpL`,
`proveTL`, `leavesCL`): programs of the honest parties in `LStep`; in W (`CpW`, `proveTW`,
`leavesW`): the reduction's (Compile/Batch/Mirror.lean); `W`: a `QueryLayout lam L` (Iop/BatchWire.lean),
the wire record; `WP`: a `WireBP L` (Iop/BatchWireP.lean): the prover's data for the three
protocols, and the enumeration of the encoding randomness; `p`: a `Params` (Compile/Star.lean): the
number of copies is `p.M + 1`; `st`: an `LSt` (Rom/DeferLate.lean): the state of the experiment
beside the challenger's own.
-/
import Compile.Batch.SpecEq
import Compile.Batch.SpecEqProve
import Compile.Step1_defc_EqSetup
import Iop.BatchOne
import Iop.BatchUnif

noncomputable section

namespace Compile.Batch
open Iop Rom Prob
open Compile.BatchLife (linksGB bsess BSess)
open Compile.Lifetime (Sess)
open Compile.DefC (virtL lbind_assoc)
open Compile.DefC.EqSetup (virtL_zero)

namespace EqSetupB

/-! ## One slot -/

section One

variable {Y : Type} {E : ExtSpec} {Q : InteractiveOracleProof Y E} {Wt : Type} (H : Honest Q Wt)

/-- A session of an IOP, taken as a batch IOP with one slot and local rounds only, is a session of
the IOP. -/
theorem bsess_one_bind {γ : Type} (w : Wt) (y : Y) (F : Sess Q → PMF γ) :
    ((bsess (BatchHonestProver.ofHonest H) w (fun _ : Fin 1 => some y) {0}).bind fun so =>
        F (so.1 BatchOne.slot0, so.2 BatchOne.slot0)) =
      (Lifetime.sess H w y).bind F := by
  unfold bsess Lifetime.sess
  rw [← BRho.map_slot_unif (0 : Fin 1) Q.shape (RoundSplits.allLocal Q.shape), PMF.bind_bind,
    PMF.bind_map, PMF.bind_bind]
  refine congrArg _ (funext fun ρ => ?_)
  rw [BatchOne.output_one, PMF.map_comp, PMF.bind_map]
  show _ = ((H.output w y (BRho.slot 0 ρ)).map _).bind F
  rw [PMF.bind_map]
  rfl

theorem ownSlots_one (y : Y) : ownSlots (fun _ : Fin 1 => some y) (fun _ => true) = {0} := by
  ext s
  simp [ownSlots, Subsingleton.elim s 0]

open Classical in
theorem osOf_one (y : Y) (so : BSess (BatchInteractiveOracleProof.ofProto Q) ({0} : Finset (Fin 1))) :
    osOf (fun _ : Fin 1 => some y) {0} so =
      [some (y, so.1 BatchOne.slot0, so.2 BatchOne.slot0)] := by
  unfold osOf
  rw [show List.finRange 1 = [0] from rfl, List.map_singleton,
    dif_pos (Finset.mem_singleton_self 0)]
  rfl

end One

/-! ## Test and Link -/

section TL

variable {I X : Type} {lam : ℕ} {L : BatchProtocol I X}

theorem lpure_eq {K : ℕ} {β : Type} (a : β) : (pure a : Lp lam K L β) = LStep.pure a := rfl

theorem run_draw_bind {K : ℕ} {β γ : Type} [Fintype β] [Nonempty β] (e : Enum β) (he : e.OK)
    (g : β → Lp lam K L γ) (st : LSt (spec lam K L)) :
    ((drawL e).bind g).run st = (unif β).bind fun b => (g b).run st := by
  rw [← map_unif_equiv (Equiv.ofBijective e.e he), PMF.bind_map]
  rfl

variable (hP : Spec.eqProveB)
  (W : QueryLayout lam L) (WP : WireBP L) (p : Params) (hW : W.OKG) (hG : GrFitPB W) (hWP : WP.OK)
include hP hW hG hWP

theorem run_proveTL (tree : TreeH lam) (i : I) (r : L.EncodingRandomness) (st : LSt (spec lam W.K L)) :
    (proveTL W WP p tree i r).run st =
      (Lifetime.sess L.honestOfflineProver (i, r) ()).bind fun s => (proveTW W p tree s).run st := by
  have h1 := hP I X lam W.K L p.sMT p.sFS Tag.test Unit _ (BatchInteractiveOracleProof.ofProto L.offline) _
    (BatchHonestProver.ofHonest L.honestOfflineProver) W.T WP.T (fun q a => some (.inr ⟨Tag.test, ⟨q, a⟩⟩)) id
    (fun _ => none) embSg W.depthReq [tree] 0 0 1 (i, r) (fun _ => true) (fun _ => some ())
    st hW.T.sh hG.T hWP.T (RoundSplits.fmt_allLocal _)
  simp only [virtL_zero] at h1
  rw [ownSlots_one] at h1
  simp only [osOf_one] at h1
  unfold proveTL proveTW
  simp only [DefC.run_bind]
  rw [show ([some ()] : List (Option Unit)) = (List.finRange 1).map fun _ => some () from rfl, h1,
    PMF.bind_bind]
  exact bsess_one_bind L.honestOfflineProver (i, r) () fun s =>
    ((proveBW p.sMT p.sFS Tag.test (BatchInteractiveOracleProof.ofProto L.offline) W.T
        (fun q a => some (.inr ⟨Tag.test, ⟨q, a⟩⟩)) id (fun _ => none) embSg W.depthReq
        [tree] [some ((), s.1, s.2)]).run st).bind
      fun x => (pure (x.1.headD none) : Lp lam W.K L _).run x.2

theorem run_proveLkL (root tree : TreeH lam) (i : I) (r₀ r : L.EncodingRandomness) (st : LSt (spec lam W.K L)) :
    (proveLkL W WP p root tree i r₀ r).run st =
      (Lifetime.sess L.honestLinkProver (i, r₀, r) ()).bind fun s => (proveLkW W p root tree s).run st := by
  have h1 := hP I X lam W.K L p.sMT p.sFS Tag.link Unit _ (BatchInteractiveOracleProof.ofProto L.link) _
    (BatchHonestProver.ofHonest L.honestLinkProver) W.Lk WP.Lk (fun q a => some (.inr ⟨Tag.link, ⟨q, a⟩⟩)) id
    (fun _ => none) embSg W.depthReq [root, tree] 0 0 1 (i, r₀, r) (fun _ => true)
    (fun _ => some ()) st hW.Lk.sh hG.Lk hWP.Lk (RoundSplits.fmt_allLocal _)
  simp only [virtL_zero] at h1
  rw [ownSlots_one] at h1
  simp only [osOf_one] at h1
  unfold proveLkL proveLkW
  simp only [DefC.run_bind]
  rw [show ([some ()] : List (Option Unit)) = (List.finRange 1).map fun _ => some () from rfl, h1,
    PMF.bind_bind]
  exact bsess_one_bind L.honestLinkProver (i, r₀, r) () fun s =>
    ((proveBW p.sMT p.sFS Tag.link (BatchInteractiveOracleProof.ofProto L.link) W.Lk
        (fun q a => some (.inr ⟨Tag.link, ⟨q, a⟩⟩)) id (fun _ => none) embSg W.depthReq
        [root, tree] [some ((), s.1, s.2)]).run st).bind
      fun x => (pure (x.1.headD none) : Lp lam W.K L _).run x.2

/-- the recursion over the copies, with any continuation -/
theorem run_leaves {γ : Type} (i : I) (root : Node lam L) : ∀ (m : ℕ) (st : LSt (spec lam W.K L))
    (Kc : WKey lam L × List L.EncodingRandomness → LSt (spec lam W.K L) → PMF γ),
    ((leavesCL W WP p i root m).run st).bind (fun y =>
        Kc (y.1.map fun lf => (lf.node.tree, lf.piL), y.1.map fun lf => lf.node.r) y.2)
      = (linksGB (fun r r' => Lifetime.sess L.honestLinkProver (i, r, r') ()) root.r m).bind fun ls =>
          ((leavesW W p root.tree (ls.map Prod.snd)).run st).bind fun y =>
              Kc (y.1, ls.map Prod.fst) y.2 := by
  intro m
  induction m with
  | zero =>
    intro st Kc
    simp only [leavesCL, linksGB, leavesW, lpure_eq, LStep.run, PMF.pure_bind, List.map_nil]
  | succ m ih =>
    intro st Kc
    simp only [leavesCL, nodeLL, linksGB, lbind_assoc]
    rw [run_draw_bind WP.ri hWP.ri, PMF.bind_bind, PMF.bind_bind]
    refine congrArg _ (funext fun r => ?_)
    simp only [DefC.run_bind, lpure_eq, LStep.bind, LStep.run, PMF.bind_bind, PMF.pure_bind,
      PMF.bind_map, Function.comp_def, run_proveLkL hP W WP p hW hG hWP, List.map_cons, leavesW]
    rw [PMF.bind_comm]
    refine congrArg _ (funext fun s => ?_)
    have e1 : ∀ ytr : TreeH lam × LSt (spec lam W.K L),
        ((proveLkW W p root.tree ytr.1 s).run ytr.2).bind (fun yπ =>
            ((leavesCL W WP p i root m).run yπ.2).bind fun yr =>
              Kc ((ytr.1, yπ.1) :: yr.1.map (fun lf => (lf.node.tree, lf.piL)),
                  r :: yr.1.map fun lf => lf.node.r) yr.2) =
          (linksGB (fun r r' => Lifetime.sess L.honestLinkProver (i, r, r') ()) root.r m).bind
            fun ls => ((proveLkW W p root.tree ytr.1 s).run ytr.2).bind fun yπ =>
          ((leavesW W p root.tree (ls.map Prod.snd)).run yπ.2).bind fun yk =>
            Kc ((ytr.1, yπ.1) :: yk.1, r :: ls.map Prod.fst) yk.2 := by
      intro ytr
      rw [PMF.bind_comm]
      refine congrArg _ (funext fun yπ => ?_)
      exact ih yπ.2 fun z st' => Kc ((ytr.1, yπ.1) :: z.1, r :: z.2) st'
    simp only [e1]
    rw [PMF.bind_comm]

end TL

end EqSetupB

open EqSetupB in
/-- From `Spec.eqProveB`: `Spec.eqSetupB` (Compile/Batch/SpecEq.lean). -/
theorem eqSetupB (hP : Spec.eqProveB) : Spec.eqSetupB := by
  intro I X lam L W WP p i st _ hW hG hWP
  rw [← PMF.bind_pure_comp]
  simp only [CpL, nodeLL, lbind_assoc]
  rw [run_draw_bind WP.ri hWP.ri, PMF.bind_bind]
  refine congrArg _ (funext fun r₀ => ?_)
  simp only [DefC.run_bind, lpure_eq, LStep.bind, LStep.run, PMF.bind_bind, PMF.pure_bind,
    Function.comp_def, run_proveTL hP W WP p hW hG hWP, CpW, ← PMF.bind_pure_comp, keyOf]
  rw [PMF.bind_comm]
  refine congrArg _ (funext fun sT => ?_)
  have e1 : ∀ ytr : TreeH lam × LSt (spec lam W.K L),
      ((proveTW W p ytr.1 sT).run ytr.2).bind (fun yπ =>
          ((leavesCL W WP p i ⟨r₀, ytr.1⟩ (p.M + 1)).run yπ.2).bind fun yr =>
            PMF.pure (((⟨ytr.1.root, yπ.1⟩ : IVK lam L), i,
                  yr.1.map (fun lf => (lf.node.tree, lf.piL)), yr.1.map fun lf => lf.node.r),
                yr.2)) =
        (linksGB (fun r r' => Lifetime.sess L.honestLinkProver (i, r, r') ()) r₀ (p.M + 1)).bind
          fun ls => ((proveTW W p ytr.1 sT).run ytr.2).bind fun yπ =>
        ((leavesW W p ytr.1 (ls.map Prod.snd)).run yπ.2).bind fun yk =>
          PMF.pure (((⟨ytr.1.root, yπ.1⟩ : IVK lam L), i, yk.1, ls.map Prod.fst), yk.2) := by
    intro ytr
    rw [PMF.bind_comm]
    refine congrArg _ (funext fun yπ => ?_)
    exact run_leaves hP W WP p hW hG hWP i ⟨r₀, ytr.1⟩ (p.M + 1) yπ.2
      fun z st' => PMF.pure (((⟨ytr.1.root, yπ.1⟩ : IVK lam L), i, z.1, z.2), st')
  simp only [e1]
  rw [PMF.bind_comm]

end Compile.Batch
