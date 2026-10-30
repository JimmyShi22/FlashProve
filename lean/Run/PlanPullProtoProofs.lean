-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/PlanPullProtoProofs.lean: the proof of Run/PlanPullProto.lean's statement, `planPull_proto`: the
protocol of the generic construction with challenges as hash blocks is, as a term, the protocol with
challenges as sampled values, without work, pulled back along the format's samplers and then given
its tests (the tests of the rounds' proof of work: a round's test bits must be zero), for every
field f, ds, dec. The words: the head of Run/PlanPull.lean. The limits: the head of
Run/PlanPullProto.lean.
Many statements of this library are written twice: a definition in the namespace `Spec` states a
proposition, and a theorem of the same name outside that namespace proves it (lean/GLOSSARY.md).

Why the proof has this form: what a protocol made from a plan needs of the rounds after the round in
front (what was drawn, the tests, the verifier messages off a transcript, the rounds' view,
positions, columns) is packed with its shape in one record (`PullP.Pk`). The generic construction's
functions with challenges as hash blocks (`PullP.P1`) and the library's composites with challenges
as sampled values (`PullP.P2`) are both made by one step a round (`PullP.step`): so the two records
are equal by induction, with no cast between their types. A protocol is made from a record
(`PullP.G`): the generic construction's is `G` of `P1` by definition (`PullP.left`); the library's
is `G` of `P2` (`PullP.right`).
-/
/- Limits: that a proof file is accepted or refused is no theorem of this library. It is the outcome
   of a `#guard` line, or of an evaluation outside the library, such as a test by Lean's evaluator,
   which leaves no declaration. So nothing that is checked of declarations is checked of such an
   evaluation. No clause of a soundness theorem of Fmt/ and Run/ speaks of a run. -/
import Run.PlanPullProto
import Iop.GrindProofs
import Iop.PullProofs

set_option autoImplicit false

namespace Run
open Prob Iop

namespace PullP

/-- What a protocol made from a plan needs of the rounds after the round in front, with their shape.
-/
structure Pk where
  s : Shape
  dq : DecidableEq (OPos s)
  drawn : Rho s → List _root_.Fmt.Drawn
  pass : Rho s → Bool
  rho : Iop.Tr s → Rho s
  rv : Iop.Tr s → List PQ.RV
  pos : ℕ → ℕ → Option (OPos s)
  col : Iop.Tr s → ℕ → ℕ → Option (List UInt64)

theorem mk_congr {s : Shape} {q q' : DecidableEq (OPos s)} {a a' : Rho s → List _root_.Fmt.Drawn}
    {b b' : Rho s → Bool} {c c' : Iop.Tr s → Rho s} {d d' : Iop.Tr s → List PQ.RV}
    {e e' : ℕ → ℕ → Option (OPos s)} {g g' : Iop.Tr s → ℕ → ℕ → Option (List UInt64)} (ha : a = a')
    (hb : b = b') (hc : c = c') (hd : d = d') (he : e = e') (hg : g = g') :
    Pk.mk s q a b c d e g = Pk.mk s q' a' b' c' d' e' g' := by
  have hq : q = q' := Subsingleton.elim _ _
  subst hq ha hb hc hd he hg
  rfl

/-- one round more in front of a record -/
def step (f : _root_.Fmt.Fld) (d : PQ.RD) (P : Pk) : Pk where
  s := (PQ.roundS (ckP f) d).up :: P.s
  dq := by
    haveI := P.dq
    exact inferInstanceAs (DecidableEq (Fin (PQ.posN d.tree) ⊕ OPos P.s))
  drawn := fun x => (ckP f).dr d.entry d.kind (GChal.old (b := d.entry.work) x.1) :: P.drawn x.2
  pass := fun x => GChal.pass (b := d.entry.work) x.1 && P.pass x.2
  rho := fun x => (x.2.1, P.rho x.2.2)
  rv := fun x =>
    ⟨PQ.PlainOf.gots d.items (GPlain.old (b := d.entry.work) x.1.2),
        (ckP f).dr d.entry d.kind (GChal.old (b := d.entry.work) x.2.1)⟩ :: P.rv x.2.2
  pos := fun n x =>
    if d.tree.isSome then
      if n = 0 then (if h : x < PQ.posN d.tree then some (.inl ⟨x, h⟩) else none)
      else (P.pos (n - 1) x).map .inr
    else (P.pos n x).map .inr
  col := fun t n x =>
    if d.tree.isSome then
      if n = 0 then (if h : x < PQ.posN d.tree then some (List.ofFn (t.1.1 ⟨x, h⟩)) else none)
      else P.col t.2.2 (n - 1) x
    else P.col t.2.2 n x

/-- The generic construction's functions with challenges as hash blocks. -/
def P1 (f : _root_.Fmt.Fld) (ds : List PQ.RD) : Pk :=
  ⟨PQ.uL (ckP f) ds, PQ.decSL (ckP f) ds, PQ.drawnSL (ckP f) ds, PQ.passSL (ckP f) ds,
    PQ.rhoSL (ckP f) ds, PQ.rvSL (ckP f) ds, PQ.posAtS (ckP f) ds, PQ.colAtS (ckP f) ds⟩

abbrev sg (f : _root_.Fmt.Fld) (ds : List PQ.RD) : Samplers (PQ.shapeL (ck f) ds) :=
  Samplers.ofDraws _ (drawsOf f _ (planL f ds))
abbrev gv (f : _root_.Fmt.Fld) (ds : List PQ.RD) : GBits ((PQ.shapeL (ck f) ds).pull (sg f ds)) :=
  (PQ.gL (ck f) ds).pull (sg f ds)

/-- A position of the shape with challenges as sampled values, as a position of the pulled shape
with tests. -/
def back (f : _root_.Fmt.Fld) (ds : List PQ.RD) (p : OPos (PQ.shapeL (ck f) ds)) :
    OPos (((PQ.shapeL (ck f) ds).pull (sg f ds)).grind ℕ (gv f ds)) :=
  (OPos.stripE (gv f ds)).symm ((OPos.pushEquiv (sg f ds)).symm p)

/-- The library's composites with challenges as sampled values. -/
def P2 (f : _root_.Fmt.Fld) (ds : List PQ.RD) : Pk where
  s := ((PQ.shapeL (ck f) ds).pull (sg f ds)).grind ℕ (gv f ds)
  dq := ((OPos.stripE (gv f ds)).trans (OPos.pushEquiv (sg f ds))).decidableEq
  drawn := fun ρ => PQ.drawnL (ck f) ds (Rho.push (sg f ds) (Rho.strip (gv f ds) ρ))
  pass := fun ρ => Rho.pass (gv f ds) ρ
  rho := fun t => t.rho
  rv := fun t => PQ.rvL (ck f) ds (Iop.Tr.push (sg f ds) (Iop.Tr.strip (gv f ds) t))
  pos := fun n x => (PQ.posAt (ck f) ds n x).map (back f ds)
  col := fun t n x => PQ.colAt (ck f) ds (Iop.Tr.push (sg f ds) (Iop.Tr.strip (gv f ds) t)) n x

theorem P1_cons (f : _root_.Fmt.Fld) (d : PQ.RD) (ds : List PQ.RD) :
    P1 f (d :: ds) = step f d (P1 f ds) :=
  mk_congr (s := (PQ.roundS (ckP f) d).up :: PQ.uL (ckP f) ds) rfl rfl rfl rfl rfl rfl

theorem P2_cons (f : _root_.Fmt.Fld) (d : PQ.RD) (ds : List PQ.RD) :
    P2 f (d :: ds) = step f d (P2 f ds) :=
  mk_congr (s := (PQ.roundS (ckP f) d).up :: (P2 f ds).s) rfl rfl rfl rfl
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

theorem P_eq (f : _root_.Fmt.Fld) : ∀ ds : List PQ.RD, P1 f ds = P2 f ds
  | [] => mk_congr (s := []) rfl rfl rfl rfl rfl rfl
  | d :: ds => by rw [P1_cons, P2_cons, P_eq f ds]

/-- a protocol from a record -/
def G (f : _root_.Fmt.Fld) (ds : List PQ.RD) (dec : PQ.View → Bool) (P : Pk) :
    InteractiveOracleProof Unit PQ.E0 where
  shape := (PQ.s0 (ckP f)).up :: P.s
  blinded := fun _ => true
  extReads := fun _ _ => ∅
  reads := fun _ ρ _ =>
    haveI := P.dq
    (((PQ.wanted ds (P.drawn ρ.2)).filterMap fun nx =>
      (P.pos nx.1 nx.2).map fun p => (Sum.inr p : Empty ⊕ OPos P.s))).toFinset
  accept := fun _ _ t =>
    P.pass (P.rho t.2.2) &&
      dec ⟨P.rv t.2.2,
          (PQ.wanted ds (P.drawn (P.rho t.2.2))).filterMap fun nx =>
            (P.col t.2.2 nx.1 nx.2).map fun c => (nx.1, nx.2, c)⟩

theorem left (f : _root_.Fmt.Fld) (ds : List PQ.RD) (dec : PQ.View → Bool) :
    (PQ.PSof (ckP f) ds dec).up.loc = G f ds dec (P1 f ds) := rfl


/-- The set of a list, mapped along two embeddings, whatever the instances of `DecidableEq` are. -/
theorem map2 {α β γ : Type} (iα : DecidableEq α) (iγ : DecidableEq γ) (e1 : α ↪ β) (e2 : β ↪ γ)
    (l : List α) (l' : List γ) (h : l.map (fun a => e2 (e1 a)) = l') :
    ((@List.toFinset α iα l).map e1).map e2 = @List.toFinset γ iγ l' := by
  subst h
  ext c
  simp

theorem pass0 {C : Type} (c : GChal 0 C) : GChal.pass (b := 0) c = true :=
  decide_eq_true fun i => i.elim0

theorem proto_congr {s : Shape} {bl : OPos s → Bool} {er : Unit → Rho s → Finset PQ.E0.Pos}
    {r r' : Unit → Rho s → Plains s → Finset (OPos s)} {a a' : Unit → PQ.E0.Str → Iop.Tr s → Bool}
    (hr : r = r') (ha : a = a') :
    (⟨s, bl, er, r, a⟩ : InteractiveOracleProof Unit PQ.E0) = ⟨s, bl, er, r', a'⟩ := by
  subst hr ha
  rfl

theorem right (f : _root_.Fmt.Fld) (ds : List PQ.RD) (dec : PQ.View → Bool) :
    ((Qv (ck f) ds dec).pull (Samplers.ofDraws _ (drOf f ds))).grind
        ℕ ((g0Of f ds).pull (Samplers.ofDraws _ (drOf f ds))) =
      G f ds dec (P2 f ds) :=
  proto_congr (s := (PQ.s0 (ckP f)).up :: (P2 f ds).s)
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

end PullP

theorem planPull_proto : Spec.planPull_proto := fun f ds dec => by
  rw [PullP.left, PullP.right, PullP.P_eq]

end Run
