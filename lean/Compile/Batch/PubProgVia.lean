-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/PubProgVia.lean: the scheme with any program in the place of the prover's (`argBPG`,
Compile/Batch/PubProg.lean) and its token form, without `realQ` (`argBPGT`): their tie by the
exchange of queries `ghost W` (`argBPG_via`: see its statement), and a sanity lemma (words of this
library: lean/GLOSSARY.md).

  `RoutedF W pq`  The program pq is routed, for all keys, flags and instances (`RoutedT`,
                  Compile/Batch/SpecGhost.lean): it queries `fb t` only with the nonce for attempt
                  0, or where the component that the query holds has no proof-of-work record, and
                  `fbw t k` only with the nonce for attempt k + 1.
  `argBPG_via`  For a routed program and under `W.OKG`: `argBPG` is `argBPGT` with C and P
                translated by the exchange of queries `ghost W` ((fb t, q) with the nonce for k + 1
                against (fbw t k, q)).
  `noGhostPubG`  C and P of `argBPG` never query a ghost name, for every program pq (they are
                 `realQ` of something). Its V is the given verifier.
  `routedF_Pp`, `routedF_PpU`  Under `W.OKG`, the prover's program `Pp`, and `PpU` (no query for an
                               empty slot), are routed (Compile/Batch/GhostRouted.lean,
                               Compile/Batch/GhostRoutedU.lean).

Notation:
  `W.OKG`: `QueryLayout.OKG` (Iop/BatchWire.lean): the laws of a wire whose rounds may have tests
  `pq`: an `FProg`: a prover's program with flags: pq k fr xs: the key with tokens, for which
    requests a proof string is made, the instances (Compile/Batch/PubProg.lean); P of `argBPG` runs
    pq at the flags fun _ => true: all flags true

Limits: it does not say any of the three properties of a scheme. That a given program is routed has
to be shown beside it (for `PpU`: Compile/Batch/GhostRoutedU.lean).
-/
import Compile.Batch.PubProg
import Compile.Batch.GhostRouted
import Compile.Batch.GhostRoutedU
import Compile.Batch.GhostGuards

noncomputable section

namespace Compile.Batch
open Iop Rom ZKCP
open Compile.GlueB (viaCP)

variable {I X V : Type} {lam : ℕ} {L : BatchProtocol I X}

/-- The program is routed, for all keys, flags and instances. -/
def RoutedF (W : QueryLayout lam L) (pq : FProg lam L W.K) : Prop := ∀ k fr xs, RoutedT W (pq k fr xs)

theorem routedF_Pp (W : QueryLayout lam L) (WP : WireBP L) (p : Params) (hW : W.OKG) :
    RoutedF W (Pp W WP p) :=
  fun k fr xs => routedPp I X lam L W WP p k fr xs hW

theorem routedF_PpU (W : QueryLayout lam L) (WP : WireBP L) (p : Params) (hW : W.OKG) :
    RoutedF W (PpU W WP p) :=
  fun k fr xs => routedPpU I X lam L W WP p k fr xs hW

variable (W : QueryLayout lam L) (WP : WireBP L) (p : Params) (pw : IVK lam L → WKey lam L → V)
  (pq : FProg lam L W.K) (Vf : V → X → Prf lam L → TypedOracleComputation lam W.K L Bool)

/-- Under `W.OKG`, for a routed program: the scheme is `argBPGT` with C and P translated by the
exchange of queries `ghost W`. -/
theorem argBPG_via (hW : W.OKG) (hR : RoutedF W pq) :
    argBPG W WP p pw pq Vf = viaCP (ghost W) (argBPGT W WP p pw pq Vf) := by
  have hv := argB_via I X lam L W WP p hW
  have eC : ∀ i, C W WP p i = (Ctok W WP p i).via (ghost W) := fun i =>
    congrFun (congrArg Gen.Arg.C hv) i
  have e1 : (argBPG W WP p pw pq Vf).C =
      (viaCP (ghost W) (argBPGT W WP p pw pq Vf)).C := funext fun i => by
    show (C W WP p i).bind (fun o => OComp.pure (pw o.1 (keyOf o.2.1), o.2)) =
      ((Ctok W WP p i).bind fun o => OComp.pure (pw o.1 (keyOf o.2.1), o.2)).via (ghost W)
    rw [OComp.via_bind, eC i]
    rfl
  have e2 : (argBPG W WP p pw pq Vf).P =
      (viaCP (ghost W) (argBPGT W WP p pw pq Vf)).P := funext fun k => funext fun b =>
    realQ_via I X lam L W _ _
      (Routed.bind (routedErase I X lam L W _ _ k.2 (hR k.1 (fun _ => true) (b.map Prod.fst)))
        fun _ => trivial)
  show (⟨(argBPG W WP p pw pq Vf).C, (argBPG W WP p pw pq Vf).P, Vf⟩ : Gen.Arg _ _ _ _ _ _ _) =
    ⟨(viaCP (ghost W) (argBPGT W WP p pw pq Vf)).C,
      (viaCP (ghost W) (argBPGT W WP p pw pq Vf)).P,
      Vf⟩
  rw [e1, e2]

/-- Sanity lemma: C and P never query a ghost name, whatever the program is. -/
theorem noGhostPubG :
    (∀ i, NoGhost ((argBPG W WP p pw pq Vf).C i)) ∧
    ∀ k b, NoGhost ((argBPG W WP p pw pq Vf).P k b) :=
  ⟨fun i => NoGhost.bind (noGhost_C W WP p i) fun _ => trivial, fun _ _ => noGhost_realQ _⟩

end Compile.Batch
