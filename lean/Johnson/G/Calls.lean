-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/G/Calls.lean: the seven plans of the verifier on bytes as seven lists of calls of the
planner's routines, computed from the three public files.

The planner (OnBytes/Params/Planner.lean and the files above it) writes a chain's plan by routines
that call each other. Here the routines above the named ones are written once more, so that each
call of a named routine is noted with its arguments while it runs. Definitions only.
Main names:
  `Call`: one constructor for each named routine of the planner, with its arguments.
  `Call.plan`: the planner's own routine at these arguments. Three constructors are no routine of
    the planner but single lines of its bodies: `lkp` (the line `close "LKP"` of `planLookup`),
    `reply` (`closeNone "REPLY"` in `reqPlanFrom`), `scope` (the frame sets the scope again).
  `callsOf`: the seven lists, in the order key 0, 1, 2, entry 0, proof 0, 1, 2. It refuses unless,
    at each chain, (k1) the plan that is written while the calls are noted is the plan that
    `OnBytes.Model.Verify.planned` makes, round for round, and (k2) the list of calls alone, run
    from an empty plan (`replay`), gives that same plan, round for round.
Limits: no theorem is stated. That the bodies written once more are the planner's is held by (k1)
and (k2) only where `callsOf` is evaluated, at the public files handed in. A call says what is
planned: names, sizes, errors. It does not say which polynomial a sumcheck sums, which claims go in
and come out, or in which order variables are bound.

-/
import OnBytes.Model.Verify

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.G

open OnBytes OnBytes.Params

/-- Two rounds of a plan agree in the entry, the error, the argument and the scope. -/
def same (a b : PlanRound) : Bool :=
  a.entry == b.entry && a.error == b.error && a.why == b.why && a.scope == b.scope

/-- Two lists of rounds agree round for round. -/
def sameAll : List PlanRound → List PlanRound → Bool
  | [], [] => true
  | a :: l, b :: m => same a b && sameAll l m
  | _, _ => false

/-- A call of a named routine of the planner, with its arguments. -/
inductive Call where
  | scalars (n : Nat)
  | psc (x : PscSize)
  | line
  | zero (n : Nat)
  | join (n : Nat)
  | shift (n : Nat)
  | lkp (keys : Nat)
  | batSigma (n : Nat)
  | productTree (levels more : Nat)
  | productLayer (n : Nat)
  | tokenSumcheck (lt degreeY shown : Nat)
  | tokenSum (lt shown degreeInY more : Nat)
  | rng (columns : Nat)
  | batt (rows kCol : Nat)
  | bat (gs : List GroupSize) (rows : Nat)
  | fold (g : GroupSize) (roots : Nat)
  | cs (x y : GroupSize) (cube old symbols roots : Nat)
  | base (g : GroupSize) (roots : Nat)
  | loc (g : GroupSize)
  | send (o : List SampleSize) (roots : Nat) (answerRound : Bool)
  | record (T : TableSize)
  | seal
  | split
  | reply
  | linFirst (x : LinSize)
  | linShared (T : TableSize) (x : LinSize)
  | link (T : TableSize) (u : SampleSize)
  | scope (s : Scope)

/-- The planner's own routine at a call's arguments. -/
def Call.plan : Call → Planning Unit
  | .scalars n => planScalars n
  | .psc x => planPsc x
  | .line => planLine
  | .zero n => planZero n
  | .join n => planJoin n
  | .shift n => planShift n
  | .lkp keys => do
    close "LKP" .field (Bound.ratio (keys - 1) (← theSetting).cardE)
      { drawE := 1, priced := .callersWord }
  | .batSigma n => planBatSigma n
  | .productTree l m => planProductTree l m
  | .productLayer n => planProductLayer n
  | .tokenSumcheck a b c => planTokenSumcheck a b c
  | .tokenSum a b c d => planTokenSum a b c d
  | .rng c => planRng c
  | .batt r k => planBatt r k
  | .bat gs r => planBat gs r
  | .fold g r => planFold g r
  | .cs x y a b c d => do let _ ← planCs x y a b c d
  | .base g r => do let _ ← planBase g r
  | .loc g => do let _ ← planLoc g
  | .send o r a => planSend o r a
  | .record T => planRecord T
  | .seal => planSeal
  | .split => planSplit
  | .reply => closeNone "REPLY"
  | .linFirst x => planLinFirst x
  | .linShared T x => do let _ ← planLinShared T x
  | .link T u => do let _ ← planLink T u
  | .scope s => modify fun p => { p with scope := s }

/-- Notes calls while the planner's routines run. -/
abbrev N := StateT (Array Call) Planning

/-- Notes a call and runs it. -/
def note (c : Call) : N Unit := do modify (·.push c); (c.plan : Planning Unit)
/-- Notes a call and runs the routine that returns its value. -/
def noteV {α : Type} (c : Call) (x : Planning α) : N α := do modify (·.push c); x

/-- `planLookup`, each call noted. -/
def nLookup (x : LookupSize) : N Unit := do
  let s ← (theSetting : Planning Setting)
  let slots := 2 ^ min x.mu 6
  let w := if x.live != 0 then x.live else slots
  let parts := if x.parts.isEmpty then [x.v] else x.parts
  let keys := sumT (parts.map (2 ^ ·))
  (needs (decide (1 ≤ x.mu) && decide (x.mu ≤ 6) && decide (2 ≤ w) && decide (w ≤ slots)) :
    Planning Unit)
  (needs (decide (keys < 2 ^ w) && decide (2 ^ x.d * (2 ^ w - 1) < s.p)) : Planning Unit)
  if x.shifted then note (.shift (2 ^ x.d))
  note (.lkp keys)
  note (.psc { degreeY := 3, values := 3 })
  for _ in List.range (w - 2) do note (.psc { degreeY := 3, values := 2 })
  for _ in List.range (parts.length - 1) do note (.psc {})
  note (.join x.mu)
  for v in parts do note (.productTree v 0)
  note (.productTree x.d x.mu)
  note (.psc { degree := List.replicate x.d 3 ++ List.replicate x.mu 2, withY := false })
  note (.zero (x.mu + x.d))
  note (.psc { degree := List.replicate (x.mu + x.d) 3, degreeY := 2, values := 1 })

/-- `planForest`, each call noted. -/
def nForest (x : ForestSize) : N Unit :=
  nLookup { v := x.v, d := x.d, mu := 5, shifted := x.shifted }

/-- `planSmall`, each call noted. -/
def nSmall (x : SmallSize) (which : Nat) : N Unit := do
  if which == 0 then
    (do needs (rngCombinations (← theSetting) (← theScope) == x.tau) "plan-tau" : Planning Unit)
    note (.rng x.columns)
  else
    (needs (which == 1) : Planning Unit)
    nForest x.digits

/-- `planLayerOwn`, each call noted. -/
def nLayerOwn (x : LayerRounds) : N Unit := do
  note (.zero x.lt)
  if x.firstGroup then
    note (.zero (x.ls + x.lt))
    note (.zero (x.lPd - x.ls))
  note (.scalars (x.NS * x.NI))
  note (.batSigma x.NS)
  if x.lNI != 0 then note (.join x.lNI)
  note (.productLayer (x.lNI + x.lPd + x.lt))
  note (.scalars (x.NP * x.NI))
  note (.batSigma (x.NP * x.NI))
  note (.tokenSumcheck x.lt 2 (x.NO * x.NI))
  if x.withTerms then
    note (.tokenSumcheck x.lt 1 x.shownByTheTerms)
    note (.batSigma 2)
  note (.psc { degree := List.replicate x.lamS 3, degreeY := 2,
               values := 2 + x.neverSent + x.weightClaims })
  note (.productLayer (x.ll + x.lPf + x.lt))
  if x.routed then
    if 1 < x.ll then note (.join (x.ll - 1))
    note (.productLayer (x.ll - 1 + x.lfe + x.lt))
  if x.firstGroup then note (.scalars 1)
  note (.batSigma (x.weightClaims + (if x.firstGroup then 1 else 0)))
  note (.psc { degree := List.replicate x.lkW 3, degreeY := 1, values := 1 })

/-- `layerRounds`, each call noted. -/
def nLayer (look : ForestSize) (x : LayerRounds) (small : SmallSize) (claims moment : Nat) :
    N Unit := do
  if moment == 0 then
    nForest look
    nLayerOwn x
  else
    nSmall small (moment - 1)
    if moment == 2 then note (.batSigma claims)

/-- `planAttentionOwn`, each call noted. -/
def nAttentionOwn (x : AttentionRounds) : N Unit := do
  if x.planeMessages != 0 then note (.scalars (3 * x.planeMessages))
  for s in x.score do
    note (.scalars 7)
    note (.psc (attentionSc3 s.1 s.2))
  note (.scalars (5 + x.lt + 2))
  note (.psc (attentionSc3 x.e x.pairs))
  note (.batSigma 2)
  note (.scalars 2)
  note (.psc (attentionSc3 x.valueM x.pairs))
  note (.psc (attentionSc3 x.valueD x.pairs))
  note (.zero (2 * x.lgk + 2 * x.lt + 4))
  note (.scalars x.pairs)
  note (.batSigma x.pairs)
  note (.psc (attentionSc3 x.attained x.pairs))
  note (.batSigma x.pairs)
  note (.psc (attentionScd x.lt x.lgk x.pairs x.Lam))
  note (.batSigma x.pairs)
  note (.psc (attentionSc3 x.bits x.pairs))

/-- `attentionRounds`, each call noted. -/
def nAttention (look : ForestSize) (x : AttentionRounds) (small : SmallSize) (moment : Nat) :
    N Unit := do
  if moment == 0 then
    nForest look
    nAttentionOwn x
  if 1 ≤ moment then nSmall small (moment - 1)
  if moment == 2 then note (.batSigma x.rows)

/-- `headRounds` with `planHeadOwn` and `planHeadEnd`, each call noted. -/
def nHead (look : ForestSize) (x : HeadRounds) (small : SmallSize) (moment : Nat) : N Unit := do
  if moment == 0 then
    nForest look
    note (.zero x.lt)
    note (.scalars x.sums)
    note (.batSigma x.sums)
    note (.psc { degree := List.replicate (x.lPd + x.lt) 3, degreeY := 2, values := 2 })
    note .line
    note (.scalars x.products)
    note (.batSigma x.products)
    note (.tokenSum x.lt x.rowValues 2 0)
    note (.tokenSum x.lt 2 2 0)
    note (.tokenSum x.lt 2 2 x.lPd)
  if 1 ≤ moment then nSmall small (moment - 1)
  if moment == 2 then
    note (.batSigma 1)
    note (.psc { degree := List.replicate x.lkW 3, degreeY := 1, values := 1 })
    note (.batSigma x.rows)

open OnBytes.Model OnBytes.Model.Verify in
/-- `OnBytes.Model.Verify.linkRounds`, each call noted. -/
def nLink (X : Public) (link moment : Nat) : N Unit :=
  let step := if X.p4 then 2 else 1
  let g := link / step
  if link == step * X.NGr then nHead (forestSize X.HLy.fs) (X.H.own X.hS) (smallSize X.H.tl) moment
  else if link % step == 0 then
    match X.G[g]? with
    | some hp =>
      nLayer (forestSize X.y.fo) (layerNumbers X.layers hp g) (smallSize hp.tl) hp.nBatched moment
    | none => (needs false : Planning Unit)
  else
    match X.A[g]? with
    | some a => nAttention (forestSize a.fs) a.own (smallSize a.seam.tl) moment
    | none => (needs false : Planning Unit)

/-- `planStages`, each call noted. -/
def nStages (firstMaskRoots : Nat) (masksRide : Bool) : Bool → List StageSize → N Unit
  | first, x :: y :: rest => do
    note (.fold x.g (if first then firstMaskRoots else if masksRide then 0 else 1))
    let sym := x.g.slots + (if x.g.hasMask then 2 else 0)
    let n ← noteV (.cs x.g y.g (stageCubeBits y.g) 1 sym 1)
      (planCs x.g y.g (stageCubeBits y.g) 1 sym 1)
    (needs (decide (n ≤ x.t)) : Planning Unit)
    nStages firstMaskRoots masksRide false (y :: rest)
  | _, [x] => do
    let roots := if masksRide then 0 else 1
    let n ← noteV (.base x.g roots) (planBase x.g roots)
    (needs (decide (n ≤ x.t)) : Planning Unit)
  | _, [] => (refusePlan : Planning Unit)

/-- `planIopp`, each call noted. -/
def nIopp (st : List StageSize) (rows firstMaskRoots : Nat) (masksRide : Bool) : N Unit := do
  (needs (decide (2 ≤ st.length)) : Planning Unit)
  note (.bat (st.take 1 |>.map (·.g)) rows)
  nStages firstMaskRoots masksRide true st

/-- `reqSend`, down to its one call of `planSend`, which is noted. -/
def nReqSend (codes : Codes) (sent : List OracleNotice) (group atStart : GroupSize) (riders : Nat)
    (ownRound : Bool) : N Unit := do
  let own := sent.length - riders
  let sampled := (zipT (List.range sent.length) sent).filter (fun x => 0 < x.2.shape.answers) |>.map
    fun x => (⟨cubeBitsOf codes x.2.shape, [if x.1 < own then group else atStart]⟩ : SampleSize)
  let roots ← (must (treesOf codes sent.toArray) : Planning Nat)
  note (.send sampled roots ownRound)

/-- `reqMoments`, each call noted. -/
def nMoments (X : OnBytes.Model.Verify.Public) (z : ProofSized) (l : Nat) (msgs : List ReqMessage) :
    Nat → Nat → N Nat
  | 0, _ => pure 0
  | fuel + 1, moment => do
    let sent : List OracleNotice :=
      (msgs.filter fun m => m.moment == moment).map fun m => ⟨m.shape, m.leafClass⟩
    nReqSend z.codes sent z.link.group z.batch.own.first 0 true
    nLink X l moment
    note (.scope .request)
    let more ← nMoments X z l msgs fuel (moment + 1)
    pure (sumT (sent.map (·.shape.answers)) + more)

/-- `reqPlanFrom`, each call noted. -/
def nFrame (X : OnBytes.Model.Verify.Public) (z : ProofSized) :
    Nat → List ReqGroup → List ReqLink → List Nat → GroupSize → N Unit
  | _, [], _, _, _ => pure ()
  | l, g :: gs, links, open_, before => do
    let S := z.request
    let link := links.head?
    let msgs := (link.map (·.messages)).getD []
    let members : List OracleNotice :=
      (if 0 < l then [⟨g.target.shape, g.target.leafClass⟩] else []) ++
      (keptOf g).map (fun k => ⟨k.shape, k.leafClass⟩) ++
      (msgs.filter fun m => m.moment == 0).map (fun m => ⟨m.shape, m.leafClass⟩) ++
      [foldMaskNotice (ioppFoldShape ⟨S.code, S.maskCode, g.k, g.h⟩ {})]
    let sampleRows := sumT (members.map (·.shape.answers))
    let sent := if l == 0 then members ++ S.atStart else members
    if (link.map (·.plain)).getD 0 != 0 then
      note (.scalars ((link.map (·.plain)).getD 0))
      note .reply
    nReqSend z.codes sent (if link.isSome then z.link.group else z.last.first) z.batch.own.first
      (if l == 0 then S.atStart.length else 0) (l == 0)
    let carried ← if 0 < l then do
        let t ← noteV (.loc before) (planLoc before)
        pure (1 + sumT ((keptOf g).map (·.shape.answers)) +
          t * (3 + sumT ((keptOf g).map (·.shape.mainRows))))
      else pure 0
    match link with
    | none => nIopp z.last.stages (carried + sampleRows) 0 S.choice.masksRide
    | some _ =>
      nLink X l 0
      note (.scope .request)
      let moments := (msgs.getLast?.map (·.moment + 1)).getD 0
      let more ← nMoments X z l msgs (moments - 1) 1
      let keptRows := sumT (((gs.head?.map keptOf).getD []).map (·.shape.mainRows))
      let closed : GroupSize :=
        { z.link.group with k := g.k, h := g.h, slots := 2 ^ clog2 (1 + keptRows) }
      note (.bat [closed] (open_.headD 0 + carried + sampleRows + more))
      note (.fold closed 0)
      nFrame X z (l + 1) gs (links.drop 1) (open_.drop 1) closed

/-- `linPlanFirst`, its call noted. -/
def nLinFirst (codes : Codes) (x : LinSized) : N Unit := do
  note (.linFirst (← (must (linSizeOf codes x) : Planning LinSize)))

/-- `linPlanShared`, each call noted. -/
def nLinShared (codes : Codes) (x : LinSized) : N Unit := do
  let s ← (theSetting : Planning Setting)
  let S := x.shape
  let y ← (must (linSizeOf codes x) : Planning LinSize)
  let nu ← noteV (.linShared x.table y) (planLinShared x.table y)
  (needs (nu == S.fold.columns) : Planning Unit)
  let rows := S.fold.index.answers + nu + 1 + 2 * s.samples
  let ahead := if S.masksAhead then 0 else 1
  if S.sharedSplitNeeded then
    note .split
    nIopp x.folded.stages rows ahead S.choice.masksRide
    nIopp x.omega.stages (1 + 2 * s.samples) 1 S.choice.masksRide
  else nIopp x.folded.stages rows ahead S.choice.masksRide

/-- `linPlanSecond`, each call noted. -/
def nLinSecond (x : LinSized) : N Unit := do
  let s ← (theSetting : Planning Setting)
  nIopp x.own.stages (2 + 3 * s.samples) (if x.shape.masksAhead then 0 else 1)
    x.shape.choice.masksRide

/-- `linkPlan`, each call noted. -/
def nLinkPlan (x : LinkSized) : N Unit := do
  let s ← (theSetting : Planning Setting)
  note (.record x.table)
  let cube := clog2 x.shape.rows + clog2 x.linked.group.main.ell
  let nu ← noteV (.link x.table ⟨cube, [x.linked.group]⟩)
    (planLink x.table ⟨cube, [x.linked.group]⟩)
  (needs (nu.1 == x.shape.columnsFirst && nu.2 == x.shape.columnsFurther) : Planning Unit)
  nIopp x.linked.stages (2 * x.shape.table.answers + nu.1 + nu.2 + 1 + 2 * s.samples)
    (if x.shape.masksAhead then 0 else 1) x.shape.choice.masksRide

open OnBytes.Plan in
/-- `OnBytes.Plan.rangesPlan`, each call noted. -/
def nRanges (codes : Codes) (z : RangesSized) : N Unit := do
  let x := z.x
  let roots ← (must (treesOf codes (Wf.messageOf x)) : Planning Nat)
  note (.send [⟨cubeBitsOf codes x.message.shape, [z.test.first]⟩] roots true)
  for p in lookupSizes x z.matrix do nLookup p
  (needs (sizedFits codes x.stages z.test.stages) : Planning Unit)
  nIopp z.test.stages (Wf.rowsBatched x z.matrix) (if x.choice.masksRide then 0 else 1)
    x.choice.masksRide
  if 1 < z.pending then note (.batt z.pending z.matrix.kCol)

/-- Runs a noting routine from an empty plan: the calls, and the plan that was written meanwhile. -/
def noted (s : Setting) (scope : Scope) (x : N Unit) : Except String (List Call × Planned) := do
  -- `finish` wants a routine without a value: the run is made twice, for the plan and for the calls
  let P ← finish s scope (do let _ ← x.run #[])
  let r ← (x.run #[]) { set := s, scope := scope }
  pure (r.1.2.toList, P)

/-- The plan that a list of calls alone writes, from an empty plan. -/
def replay (s : Setting) (scope : Scope) (l : List Call) : Except String Planned :=
  finish s scope (forEach l Call.plan)

/-- A chain's list of calls, with the scope in which its plan begins. -/
structure Chain where
  file : String
  chain : Nat
  scope : Scope
  calls : List Call

/-- The setting and the seven lists of calls, from policy.txt, layout.txt and KL.bin. -/
def callsOf (pol lay KL : ByteArray) : Except String (Setting × List Chain) := do
  let p ← OnBytes.Model.Verify.planned pol KL (some lay)
  let c := p.chains.made
  let z := c.sized
  let (_, shapes) ← OnBytes.Model.Verify.shapesOf p.X (some lay)
  let sub := shapes.sub
  let one (file : String) (ch : Nat) (scope : Scope) (x : N Unit) (truth : Planned) :
      Except String Chain := do
    let (calls, P) ← noted z.set scope x
    unless sameAll P.rounds truth.rounds do
      throw s!"(k1) fails at {file} {ch}: the plan written while the calls were noted differs"
    let Q ← replay z.set scope calls
    unless sameAll Q.rounds truth.rounds do
      throw s!"(k2) fails at {file} {ch}: the list of calls, replayed alone, gives another plan"
    pure ⟨file, ch, scope, calls⟩
  let sc (x : LinSized) (other : Scope) : Scope := if x.lines.oneTime then .once else other
  match c.key, c.proof with
  | [k0, k1, k2], [p0, p1, p2] =>
    let l ← [
      one "key" 0 .once (do
        note (.record z.key.once.table)
        note (.send [⟨cubeBitsOf z.key.codes z.key.once.input.shape, [z.key.once.own.first]⟩] 1
          true)
        nRanges z.key.codes z.key.ranges
        nLinFirst z.key.codes z.key.once
        note .seal) k0,
      one "key" 1 (sc z.key.once .shared) (do nLinShared z.key.codes z.key.once; note .seal) k1,
      one "key" 2 (sc z.key.once .request) (nLinSecond z.key.once) k2,
      one "entry" 0 .once (nLinkPlan z.link) c.entry,
      one "proof" 0 .request (do
        nFrame p.X z.proof 0 (reqGroups z.proof.request).toList z.proof.request.link sub.openRows
          z.proof.link.group
        note (.scope .request)
        if 1 < sub.pendingRows then note (.batt sub.pendingRows z.proof.batch.shape.kCol)
        nLinFirst z.proof.codes z.proof.batch
        note .seal) p0,
      one "proof" 1 (sc z.proof.batch .shared)
        (do nLinShared z.proof.codes z.proof.batch; note .seal) p1,
      one "proof" 2 (sc z.proof.batch .request) (nLinSecond z.proof.batch) p2 ].mapM id
    pure (z.set, l)
  | _, _ => throw "the key or the proof has not three plans"

end Johnson.G
