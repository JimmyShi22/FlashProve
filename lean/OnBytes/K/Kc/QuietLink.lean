-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/K/Kc/QuietLink.lean: the merge's messages as a function on plain data; and the walk through
the claims of the output head's sub-proof, with the check's own tests, as functions on the link's
record and the ledger alone.

 - `flatForkEnd` (with `Fl.wsForkRounds`, `Fl.wsForkMerge`): the messages of the merge of a
   sub-proof's claims on the committed weights, the counterpart of `Model.wsForkEnd`
   (OnBytes/Model/Merge.lean), in the form of OnBytes/K/Kc/Flat.lean; its law `lawForkEnd` in the
   form of OnBytes/K/Kc/Laws.lean.
 - 'QuietL m', for a routine m that also holds the record of its link (`Model.LinkM`,
   OnBytes/Model/Trees.lean): from every such record the routine is quiet
   (OnBytes/K/Kc/Quiet.lean). The rules for pure, bind, if, a routine or a block used inside a link,
   reading the record, the named conditions.
 - `flatWalk`, `flatSelfTests`: `Model.Head.walk` and `Model.Head.selfTests`
   (OnBytes/Model/Head.lean) run from one fixed empty context, the context dropped. Their laws
   `lawWalk`, `lawSelfTests` hold in both directions, from any context of a run on a view.

A NAMED HYPOTHESIS. The walk and the tests call four routines of the smallness test
(OnBytes/Model/Tail.lean): `objectsF`, `selfTest`, `coefficients`, `rkSelfTest`. That these four are
quiet is `TailQuiet`, which `lawWalk` and `lawSelfTests` take as a hypothesis and this file does not
prove.

Not claimed. Nothing on the dry run. Nothing on soundness. WHICH claims the walk adds is not said in
closed form: the function is the program's text. The program does not import this file.
-/
import OnBytes.K.Kc.QuietHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.K.Kc

open OnBytes.Model (Fork SubM LinkM LinkCtx Aff Psc)

variable {α β : Type}

/-! ## The merge -/

section Merge

open OnBytes.Model (WsMerged WsForkOut WsLay WsClaim wsForkStart wsClaimShape wsRowPart wsEpsT)

/-- n plain rounds of degree 2. -/
def Fl.wsForkRounds : Nat → Array E → Psc → Fl (Array E × Psc)
  | 0, rm, p => pure (rm, p)
  | n + 1, rm, p => do
    let (r, p) ← Fl.roundIn .sum2 p
    Fl.wsForkRounds n (rm.push r) p

/-- The merge's messages. sv[a]: the slot of the a-th value. -/
def Fl.wsForkMerge (lk : Nat) (sv : Array Nat) : Fl (WsMerged × Array E) := do
  let rho ← Fl.batch sv.size
  let p ← Fl.pscBegin (wsForkStart sv rho)
  let (rm, p) ← Fl.wsForkRounds lk (Array.emptyWithCapacity lk) p
  let (sFv, p) ← Fl.pscEnds p 1 1
  let fvp ← Fl.shown sFv
  pure ({ fvp := fvp, beta := p.r.back?.getD zeroE, rm := rm, p := p, sFv := sFv }, rho)

/-- The tests on the claims' number and sizes, the merge, and what is left of each claim. -/
def flatForkEnd (lay : WsLay) (cl : Array WsClaim) (sv : Array Nat) : Fl WsForkOut := do
  Fl.must (!cl.isEmpty && cl.size ≤ 4096 && sv.size == cl.size)
  Fl.must (cl.all fun c => c.ui < lay.U.size)
  Fl.must (cl.all fun c => (wsClaimShape lay c).isOk)
  let (o, rho) ← Fl.wsForkMerge lay.lk sv
  pure {
    toWsMerged := o
    recs := (cl.zip rho).toList.map fun y => wsRowPart lay y.1 (mulE y.2 (wsEpsT lay y.1 o.rm)) }

theorem sim_wsForkRounds : ∀ (n : Nat) (rm : Array E) (p : Psc),
    Sim (Model.wsForkRounds n rm p) (Fl.wsForkRounds n rm p)
  | 0, rm, p => by
    unfold Model.wsForkRounds Fl.wsForkRounds
    exact Sim.pure _
  | n + 1, rm, p => by
    unfold Model.wsForkRounds Fl.wsForkRounds
    refine Sim.bind (sim_roundIn _ _ _ _) fun x => ?_
    obtain ⟨r, p'⟩ := x
    exact sim_wsForkRounds n _ p'

theorem sim_wsForkMerge (lk : Nat) (sv : Array Nat) :
    Sim (Model.wsForkMerge lk sv) (Fl.wsForkMerge lk sv) := by
  unfold Model.wsForkMerge Fl.wsForkMerge
  refine Sim.bind (sim_batch _) fun rho => ?_
  refine Sim.bind (sim_pscBegin _) fun p => ?_
  refine Sim.bind (sim_wsForkRounds _ _ p) fun x => ?_
  obtain ⟨rm, p1⟩ := x
  refine Sim.bind (sim_pscEnds p1 1 1) fun x => ?_
  obtain ⟨sFv, p2⟩ := x
  refine Sim.bind (sim_shown _) fun fvp => ?_
  exact Sim.pure _

/-- **The merge's messages.** -/
theorem lawForkEnd (lay : WsLay) (cl : Array WsClaim) (sv : Array Nat) :
    Sim (Model.wsForkEnd lay cl sv) (flatForkEnd lay cl sv) := by
  unfold Model.wsForkEnd flatForkEnd
  refine Sim.bind (Sim.mustAs _ _) fun _ => ?_
  refine Sim.bind (Sim.mustAs _ _) fun _ => ?_
  refine Sim.bind (Sim.mustAs _ _) fun _ => ?_
  refine Sim.bind (sim_wsForkMerge _ _) fun x => ?_
  obtain ⟨o, rho⟩ := x
  exact Sim.pure _

/-- Adding the merge's claim is quiet. -/
instance quiet_wsForkLin (o : WsMerged) : Quiet (Model.wsForkLin o) := by
  unfold Model.wsForkLin
  infer_instance

end Merge

/-! ## Routines that hold the record of their link -/

/-- From every record of a link the routine is quiet. -/
class QuietL (m : LinkM α) : Prop where
  quiet : ∀ L : LinkCtx, Quiet (m L)

instance quietL_pure (a : α) : QuietL (pure a : LinkM α) :=
  ⟨fun L => (inferInstance : Quiet (pure (a, L) : SubM (α × LinkCtx)))⟩

instance quietL_bind (m : LinkM α) (f : α → LinkM β) [QuietL m] [∀ a, QuietL (f a)] :
    QuietL (m >>= f) :=
  ⟨fun L => by
    haveI := QuietL.quiet (m := m) L
    haveI : ∀ p : α × LinkCtx, Quiet (f p.1 p.2) := fun p => QuietL.quiet (m := f p.1) p.2
    exact (inferInstance : Quiet (m L >>= fun p => f p.1 p.2))⟩

/-- One routine after another, with the facts on the parts given by hand. -/
theorem qbL {m : LinkM α} {f : α → LinkM β} (hm : QuietL m) (hf : ∀ a, QuietL (f a)) :
    QuietL (m >>= f) :=
  @quietL_bind α β m f hm hf

instance quietL_ite (p : Prop) [Decidable p] (a b : LinkM α) [QuietL a] [QuietL b] :
    QuietL (if p then a else b) := by
  split <;> infer_instance

instance quietL_lift (x : SubM α) [Quiet x] : QuietL (StateT.lift x : LinkM α) :=
  ⟨fun L => (inferInstance : Quiet (x >>= fun a => pure (a, L)))⟩

instance quietL_liftS (x : SubM α) [Quiet x] : QuietL (liftM x : LinkM α) :=
  quietL_lift x

instance quietL_liftB (b : Blk α) [QuietB b] : QuietL (liftM b : LinkM α) :=
  quietL_lift (StateT.lift b)

instance quietL_sub (x : SubM α) [Quiet x] : QuietL (LinkM.sub x) :=
  ⟨fun L => (inferInstance : Quiet (x >>= fun a => pure (a, L)))⟩

instance quietL_get : QuietL (get : LinkM LinkCtx) :=
  ⟨fun L => (inferInstance : Quiet (pure (L, L) : SubM (LinkCtx × LinkCtx)))⟩

instance quietL_must (b : Bool) : QuietL (LinkM.must b) := by
  unfold LinkM.must
  infer_instance

instance quietL_mustAs (n : String) (b : Bool) : QuietL (LinkM.mustAs n b) := by
  unfold LinkM.mustAs
  infer_instance

instance quietL_testAs (n : String) (b : Bool) : QuietL (LinkM.testAs n b) := by
  unfold LinkM.testAs
  infer_instance

instance quietL_fork : QuietL LinkM.fork := by
  unfold LinkM.fork
  infer_instance

/-! ## The walk and the check's own tests -/

/-- THE NAMED HYPOTHESIS: the four routines of the smallness test that the walk and the tests call
are quiet. -/
structure TailQuiet : Prop where
  objectsF : ∀ (tl : Model.HTailF2) (funs : Array Model.HFun), Quiet (tl.objectsF funs)
  selfTest : ∀ (tl : Model.HTailF2) (nU : Array Nat), Quiet (tl.selfTest nU)
  coefficients : ∀ tl : Model.HTailF2, Quiet tl.coefficients
  rkSelfTest : ∀ tl : Model.HTailF2, Quiet tl.rkSelfTest

theorem quietL_walk (T : TailQuiet) (R : Model.Head.Run) (tl : Model.HTailF2)
    (wo : Model.WsForkOut) : QuietL (Model.Head.walk R tl wo) := by
  haveI := T.objectsF
  unfold Model.Head.walk
  repeat' first
    | infer_instance
    | refine qbL ?_ ?_
    | intro _

theorem quietL_selfTests (T : TailQuiet) (R : Model.Head.Run) (tl : Model.HTailF2)
    (wo : Model.WsForkOut) : QuietL (Model.Head.selfTests R tl wo) := by
  haveI := T.selfTest
  haveI := T.coefficients
  haveI := T.rkSelfTest
  unfold Model.Head.selfTests
  repeat' first
    | infer_instance
    | refine qbL ?_ ?_
    | intro _

/-- The walk through the head's claims, on the link's record and the ledger. -/
def flatWalk (R : Model.Head.Run) (tl : Model.HTailF2) (wo : Model.WsForkOut) (L : LinkCtx) :
    Fork → Option ((Model.HTailF2 × LinkCtx) × Fork) :=
  still (Model.Head.walk R tl wo L)

/-- The check's own tests, on the link's record and the ledger. -/
def flatSelfTests (R : Model.Head.Run) (tl : Model.HTailF2) (wo : Model.WsForkOut) (L : LinkCtx) :
    Fork → Option ((Unit × LinkCtx) × Fork) :=
  still (Model.Head.selfTests R tl wo L)

/-- **The walk.** -/
theorem lawWalk (T : TailQuiet) (R : Model.Head.Run) (tl : Model.HTailF2) (wo : Model.WsForkOut)
    (L : LinkCtx) : LawStill (Model.Head.walk R tl wo L) (flatWalk R tl wo L) := by
  haveI := (quietL_walk T R tl wo).quiet L
  exact lawStill _

/-- **The check's own tests.** -/
theorem lawSelfTests (T : TailQuiet) (R : Model.Head.Run) (tl : Model.HTailF2)
    (wo : Model.WsForkOut) (L : LinkCtx) :
    LawStill (Model.Head.selfTests R tl wo L) (flatSelfTests R tl wo L) := by
  haveI := (quietL_selfTests T R tl wo).quiet L
  exact lawStill _

end OnBytes.K.Kc

#print axioms OnBytes.K.Kc.lawForkEnd
#print axioms OnBytes.K.Kc.lawWalk
#print axioms OnBytes.K.Kc.lawSelfTests
