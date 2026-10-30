-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/PlanPullWqProofs.lean: the proof of Run/PlanPullWq.lean's statement.
`planPull_wq`: the generic construction's protocol and wiring with whole paths against the library's
pair (statement and hypotheses: Run/PlanPullWq.lean). (The generic construction: Run/PlanQ*.lean:
makes, from a description, the typed protocol, its wiring and the run functions.)
The words are explained in the heads of Run/PlanPull.lean, Run/PlanPullWire.lean. Limits: the head
of Run/PlanPullWq.lean.

Why the proof has this form: as in Run/PlanPullProtoProofs.lean, with a larger record (`PullW.Pz`):
beside the functions on the rounds after the round in front it holds their annotation and their
wirings. The generic construction's record (`PullW.Z1`) and the library's (`PullW.Z2`) are made by
one step a round (`PullW.stepZ`); a round's wiring: Run/PlanPullWireT.lean. A pair (protocol with
annotation, wiring) is made from a record (`PullW.GZ`): the generic construction's is `GZ` of `Z1`
by definition; the library's is `GZ` of `Z2` by the facts of Run/PlanPullProtoProofs.lean and three
more: the front round's wiring (`PullW.front_wire`); the wiring of the empty external oracle
(`PullW.we0_one`); the greatest depth, a fold from the left in the generic construction and from the
right in the library (`PullW.md_lib`, `PullW.md_fold`).

Terms: lean/GLOSSARY.md.
-/
/- Limits: that a proof file is accepted or refused is no theorem of this library. It is the outcome
   of a `#guard` line, or of an evaluation outside the library, such as a test by Lean's evaluator,
   which leaves no declaration. So nothing that is checked of declarations is checked of such an
   evaluation. No clause of a soundness theorem of Fmt/ and Run/ speaks of a run. -/
import Run.PlanPullWq
import Run.PlanPullProtoProofs

set_option autoImplicit false

namespace Run
open Prob Iop

namespace PullW
open PullP

/-- The record of Run/PlanPullProtoProofs.lean (`PullP.Pk`), with the annotation and the wirings. -/
structure Pz (K : ℕ) where
  s : Shape
  dq : DecidableEq (OPos s)
  drawn : Rho s → List _root_.Fmt.Drawn
  pass : Rho s → Bool
  rho : Iop.Tr s → Rho s
  rv : Iop.Tr s → List PQ.RV
  pos : ℕ → ℕ → Option (OPos s)
  col : Iop.Tr s → ℕ → ℕ → Option (List UInt64)
  A : RoundSplits s
  W : RoundsQueryLayout 256 (K + 1) s A

def Pz.pk {K : ℕ} (P : Pz K) : Pk := ⟨P.s, P.dq, P.drawn, P.pass, P.rho, P.rv, P.pos, P.col⟩

def ofPk {K : ℕ} (P : Pk) (A : RoundSplits P.s) (W : RoundsQueryLayout 256 (K + 1) P.s A) : Pz K :=
  ⟨P.s, P.dq, P.drawn, P.pass, P.rho, P.rv, P.pos, P.col, A, W⟩

theorem mkz_congr {K : ℕ} {s : Shape} {q q' : DecidableEq (OPos s)}
    {a a' : Rho s → List _root_.Fmt.Drawn} {b b' : Rho s → Bool} {c c' : Iop.Tr s → Rho s}
    {d d' : Iop.Tr s → List PQ.RV} {e e' : ℕ → ℕ → Option (OPos s)}
    {g g' : Iop.Tr s → ℕ → ℕ → Option (List UInt64)} {A : RoundSplits s}
    {W W' : RoundsQueryLayout 256 (K + 1) s A} (ha : a = a') (hb : b = b') (hc : c = c') (hd : d = d')
    (he : e = e') (hg : g = g') (hW : W = W') :
    Pz.mk s q a b c d e g A W = Pz.mk s q' a' b' c' d' e' g' A W' := by
  have hq : q = q' := Subsingleton.elim _ _
  subst hq ha hb hc hd he hg hW
  rfl

def stepZ (f : _root_.Fmt.Fld) (K : ℕ) (d : PQ.RD) (P : Pz K) : Pz K :=
  ofPk (step f d P.pk) ((PQ.roundS (ckP f) d).lo, P.A) (PQ.wireSF (ckP f) K (chalP f K) d, P.W)

def Z1 (f : _root_.Fmt.Fld) (K : ℕ) (ds : List PQ.RD) : Pz K :=
  ofPk (P1 f ds) (Twin.allLo (PQ.SL (ckP f) ds)) (PQ.wiresSLF (ckP f) K (chalP f K) ds)

abbrev wL (f : _root_.Fmt.Fld) (K : ℕ) (ds : List PQ.RD) :
    RoundsQueryLayout 256 K ((PQ.shapeL (ck f) ds).pull (sg f ds)) (RoundSplits.allLocal _) :=
  RoundsQueryLayout.ofLocalD 256 K (PQ.shapeL (ck f) ds) (ptL f ds) (drawsOf f _ (planL f ds)) (npL f ds)

def Z2 (f : _root_.Fmt.Fld) (K : ℕ) (ds : List PQ.RD) : Pz K :=
  ofPk (P2 f ds) (RoundSplits.allLocal _) (RoundsQueryLayout.grindLocal (wL f K ds) PQ.Dn (gv f ds))

theorem Z1_cons (f : _root_.Fmt.Fld) (K : ℕ) (d : PQ.RD) (ds : List PQ.RD) :
    Z1 f K (d :: ds) = stepZ f K d (Z1 f K ds) :=
  mkz_congr (s := (PQ.roundS (ckP f) d).up :: PQ.uL (ckP f) ds)
    (A := ((PQ.roundS (ckP f) d).lo, Twin.allLo (PQ.SL (ckP f) ds))) rfl rfl rfl rfl rfl rfl rfl

theorem Z2_cons (f : _root_.Fmt.Fld) (K : ℕ) (d : PQ.RD) (ds : List PQ.RD) :
    Z2 f K (d :: ds) = stepZ f K d (Z2 f K ds) :=
  mkz_congr (s := (PQ.roundS (ckP f) d).up :: (P2 f ds).s)
    (A := ((PQ.roundS (ckP f) d).lo, RoundSplits.allLocal (P2 f ds).s)) rfl rfl rfl rfl
    (funext fun n => funext fun x => by
      show (PQ.posAt (ck f) (d :: ds) n x).map (back f (d :: ds)) = (step f d (P2 f ds)).pos n x
      unfold PQ.posAt step
      dsimp only
      split
      · split
        · split <;> rfl
        · show _ = Option.map Sum.inr ((PQ.posAt (ck f) ds (n - 1) x).map (back f ds))
          cases PQ.posAt (ck f) ds (n - 1) x <;> rfl
      · show _ = Option.map Sum.inr ((PQ.posAt (ck f) ds n x).map (back f ds))
        cases PQ.posAt (ck f) ds n x <;> rfl)
    rfl
    (congrArg (fun w => (w, RoundsQueryLayout.grindLocal (wL f K ds) PQ.Dn (gv f ds)))
      (planPull_wireT f K d).symm)

theorem Z_eq (f : _root_.Fmt.Fld) (K : ℕ) : ∀ ds : List PQ.RD, Z1 f K ds = Z2 f K ds
  | [] => mkz_congr (s := []) (A := PUnit.unit) rfl rfl rfl rfl rfl rfl rfl
  | d :: ds => by rw [Z1_cons, Z2_cons, Z_eq f K ds]

/-- a protocol with its annotation, and its wiring, from a record -/
def GZ (f : _root_.Fmt.Fld) (K : ℕ) (ds : List PQ.RD) (dec : PQ.View → Bool) (P : Pz K) :
    Σ Q : BatchInteractiveOracleProof Unit PQ.E0, ProtocolQueryLayout 256 (K + 1) Q :=
  ⟨⟨G f ds dec P.pk, ((PQ.s0 (ckP f)).lo, P.A)⟩,
    ⟨(PQ.wire0S (ckP f) K (chalP f K), P.W),
      PQ.we0,
      (by haveI := P.dq; exact inferInstanceAs (DecidableEq (Empty ⊕ OPos P.s))),
      PQ.nOpen ds, PQ.maxDepth ds⟩⟩

theorem left (f : _root_.Fmt.Fld) (K : ℕ) (ds : List PQ.RD) (dec : PQ.View → Bool) :
    (⟨(PQ.PSof (ckP f) ds dec).up, PQ.wqSF (ckP f) K (chalP f K) ds dec⟩ :
        Σ Q : BatchInteractiveOracleProof Unit PQ.E0, ProtocolQueryLayout 256 (K + 1) Q) =
      GZ f K ds dec (Z1 f K ds) := rfl


theorem sig_congr {K : ℕ} {s : Shape} {A : RoundSplits s} {bl : OPos s → Bool}
    {er : Unit → Rho s → Finset PQ.E0.Pos} {r r' : Unit → Rho s → Plains s → Finset (OPos s)}
    {a a' : Unit → PQ.E0.Str → Iop.Tr s → Bool} {sh sh' : RoundsQueryLayout 256 (K + 1) s A}
    {e e' : WireE PQ.E0} {q q' : DecidableEq (OPos s)} {n m m' : ℕ} (hr : r = r') (ha : a = a')
    (hs : sh = sh') (he : e = e') (hm : m = m') :
    (⟨⟨⟨s, bl, er, r, a⟩, A⟩, ⟨sh, e, q, n, m⟩⟩ :
        Σ Q : BatchInteractiveOracleProof Unit PQ.E0, ProtocolQueryLayout 256 (K + 1) Q) =
      ⟨⟨⟨s, bl, er, r', a'⟩, A⟩, ⟨sh', e', q', n, m'⟩⟩ := by
  have hq : q = q' := Subsingleton.elim _ _
  subst hq hr ha hs he hm
  rfl

/-- The wiring of the empty external oracle is the library's at length 0. -/
theorem we0_one : WireE.one 0 Unit () = PQ.we0 := by
  unfold WireE.one PQ.we0
  congr 1
  · funext p; exact p.elim0
  · funext p; exact p.elim0

/-- The front round's wiring. -/
theorem front_wire (f : _root_.Fmt.Fld) (K : ℕ) :
    (WireRB.ofLocalD 256 K (PQ.s0 (ck f)).up (pt0 (ck f)) (bsRound f PQ.e0 .nothing) np0).grindLocal
        PQ.Dn 0 =
      PQ.wire0S (ckP f) K (chalP f K) := by
  unfold WireRB.grindLocal WireRB.ofLocalD PQ.wire0S
  congr 1
  funext p
  exact p.elim

/-- the greatest depth, from the right -/
def mdR : List PQ.RD → ℕ
  | [] => 0
  | d :: ds => max (max 0 (PQ.depthOf d.tree)) (mdR ds)

theorem md_lib (f : _root_.Fmt.Fld) (K : ℕ) :
    ∀ ds : List PQ.RD, RoundsQueryLayout.maxDepth _ _ (wL f K ds) = mdR ds
  | [] => rfl
  | d :: ds => by
      show max (max 0 (Nat.clog 2 (Fintype.card (Fin (PQ.posN d.tree)))))
          (RoundsQueryLayout.maxDepth _ _ (wL f K ds)) = _
      rw [(planPull_depth d.tree).1, md_lib f K ds]
      rfl

theorem md_fold :
    ∀ (ds : List PQ.RD) (a : ℕ), ds.foldl (fun a d => max a (PQ.depthOf d.tree)) a = max a (mdR ds)
  | [], a => (Nat.max_zero a).symm
  | d :: ds, a => by
      show ds.foldl (fun a d => max a (PQ.depthOf d.tree)) (max a (PQ.depthOf d.tree)) =
        max a (max (max 0 (PQ.depthOf d.tree)) (mdR ds))
      rw [md_fold ds, Nat.zero_max, Nat.max_assoc]

theorem right (f : _root_.Fmt.Fld) (K : ℕ) (ds : List PQ.RD) (dec : PQ.View → Bool) :
    (⟨BatchInteractiveOracleProof.ofProto
          (((Qv (ck f) ds dec).pull (Samplers.ofDraws _ (drOf f ds))).grind
            ℕ ((g0Of f ds).pull (Samplers.ofDraws _ (drOf f ds)))),
        (ProtocolQueryLayout.ofLocalD 256 K (Qv (ck f) ds dec) (ptOfv f ds) (drOf f ds) (npOfv f ds)
            (WireE.one 0 Unit ()) (PQ.nOpen ds) (Nat.clog 2 0)).grindLocal
          PQ.Dn ((g0Of f ds).pull (Samplers.ofDraws _ (drOf f ds)))⟩ :
        Σ Q : BatchInteractiveOracleProof Unit PQ.E0, ProtocolQueryLayout 256 (K + 1) Q) =
      GZ f K ds dec (Z2 f K ds) :=
  sig_congr (s := (PQ.s0 (ckP f)).up :: (P2 f ds).s)
    (A := ((PQ.s0 (ckP f)).lo, RoundSplits.allLocal (P2 f ds).s))
    (funext fun _ => funext fun ρ => funext fun _ => by
      refine map2 _ _ _ _ _ _ ?_
      refine (List.map_filterMap ..).trans ?_
      refine congrArg (fun F => List.filterMap F (PQ.wanted ds ((P2 f ds).drawn ρ.2)))
        (funext fun nx => ?_)
      show _ = Option.map _ ((PQ.posAt (ck f) ds nx.1 nx.2).map (back f ds))
      cases PQ.posAt (ck f) ds nx.1 nx.2 <;> rfl)
    (funext fun _ => funext fun _ => funext fun t => by
      show ((GChal.pass (b := 0) t.2.1 && Rho.pass (gv f ds) t.2.2.rho) &&
          dec ⟨PQ.rvL (ck f) ds (Iop.Tr.push (sg f ds) (Iop.Tr.strip (gv f ds) t.2.2)),
              (PQ.wanted ds
                (PQ.drawnL (ck f) ds
                  (Iop.Tr.push (sg f ds) (Iop.Tr.strip (gv f ds) t.2.2)).rho)).filterMap fun nx =>
                    (PQ.colAt (ck f) ds
                        (Iop.Tr.push (sg f ds) (Iop.Tr.strip (gv f ds) t.2.2)) nx.1 nx.2).map
                      fun c => (nx.1, nx.2, c)⟩) = _
      rw [pass0, Bool.true_and, Iop.Tr.rho_push, Iop.Tr.rho_strip]
      rfl)
    (congrArg (fun w => (w, RoundsQueryLayout.grindLocal (wL f K ds) PQ.Dn (gv f ds))) (front_wire f K))
    we0_one
    (by
      show max (Nat.clog 2 0)
          (max (max 0 (Nat.clog 2 (Fintype.card Empty))) (RoundsQueryLayout.maxDepth _ _ (wL f K ds))) =
        PQ.maxDepth ds
      rw [md_lib]
      unfold PQ.maxDepth
      rw [md_fold]
      simp)

end PullW

theorem planPull_wq : Spec.planPull_wq := fun f K ds dec => by
  rw [PullW.left, PullW.right, PullW.Z_eq]

end Run
