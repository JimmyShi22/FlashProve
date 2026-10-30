-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Lot/K2OfPlan.lean: THE NUMBERS OF A PLACE OF THE KIND K2 (the code switch)
OUT OF THE PLAN's OWN PUBLIC RECORDS AND THE NUMBER OF THE GROUP INTO WHICH THE SWITCH LEADS: FOR
THE LINE «ROUNDS ARE THE PLAN's».
THE PUBLIC SIDE: NO PART OF A BLOCK's DECISION. IT STANDS OVER MATHLIB BY IMPORT LINES
(OnBytes.Plan.ReqFrames and, beneath it, the home of the planner's list functions): what a block
gets of it are plain numbers.
numsOfPlan names no record of the fold's harness; p2OfPlan, at the file's end, lays its numbers into
P2 over the fold's records Pub · Ground · Spot.
Nothing here reads an entry of the made plan, a declared round (Z.D), a view, or the program's
context; OF WHAT THE PLANNER HAS MADE IT READS THE SIZES ALONE. Of Z: p.chains.made.sized.proof ·
s₀.st.codes · s₀.check.frame.shape (for a tie alone) · P.samples (the same) · P.firstTree. Of G: W ·
first.
THE RULES HAVE BEEN RUN, in another form of this file with the same rules to the letter, in the fold
over another form of Johnson/Desc/Block.lean: that fold's own line on the rounds and the
oracles said true at all 5 places of the small stored plan; a file of evaluations,
not named here, said «rounds = the made plan's declared stretch, whole» at 5 of 5 and 25 of
25 places, with three controls a place that say false.
THE ROAD: THE PLANNER's OWN SIZES z (Params.ProofSized: the setting · the codes · the links' group ·
the request's shape): READ, NOT MADE ANEW: Z.p.chains.made.sized.proof: the record that
the planner keeps of what it
has sized out of the three public files: a public record of the plan; no entry, no round. REFUSED
unless z's shape and codes are the chain's and the first state's, and its number of samples the
start's (tied). sizedAnew makes
the same sizes anew (proofSized (the policy's lines) (subproofsWith W (the shape's links)): pure, a
search): for a look alone: at both written configurations the numbers over it are those over the
record that is read. Then the planner's record of group l, (framesOf z sub)[l]: what is sent there,
and the group that was closed last. The groups are made as ReqFrame.start makes them: reqGroups
shape (Iop/Req.lean:284).
THE RULES, EACH WITH ITS HOME IN THE LIBRARY:
  work₁ · work₂   the setting's bits of work for a round of samples | of queries, under the
  request's scope     Params/PlanningLaws.lean:58-61; PlanListsProx.lean:40;
  Plan/PlanListsReq.lean:164
  sent · roots    what group l's first message announces; a root for each tree that layTrees makes
  of it         Plan/ReqFrames.lean (frameAt: sent); Params/DeriveLin.lean:239-240;
  Iop/Ground.lean:1413
  seeds           samples × (the largest number of cube bits of a sampled message + 1)              
               Params/PlanListsProx.lean:41
  nonZero         samples                                                                           
              the same line
  answers         samples × the number of sampled messages                                          
              Plan/ReqFrames.lean (FrameN.rounds: locRound's last argument)
  positions       baseCount at the group that was closed last                                       
              Plan/PlanListsReq.lean:163-165; Params/PlanListsProx.lean:82-83
  logN            that group's main code's log-length                                               
              the same
  read            ALL TREES THAT THE LINK IN FRONT HAS SENT, in the order of sending, but for a tree
  that holds what rides at the start; a tree's number: how many trees the chain has sent before it;
  its depth: its
                  log-length; its width: its main and mask symbols. The announcements link by link
                  and moment by moment are typed after Iop/Req.lean:322-356; the trees are
                  layTrees'. The library's
                  Johnson/G/RoundsOfPlan.lean, which makes the declared rounds against which these
                  numbers are held, has the rule in its head's words; its text is not called.
WHAT THE TEST SHOWS, NUMBER BY NUMBER. read · sent: a road of their own: agreement is a finding. The
other eight are the planner's own formulas at the planner's own sizes made anew: agreement shows
(with the sizes READ) nothing on z itself; it shows that the numbers are laid into the right fields
with the right bytes, and that the right record is taken at each place; not that the formulas are
right by a measure outside the planner.
WHAT IS THE SAME AT EVERY PLACE IS MADE ONCE
(prepare: the sizes · the groups' records · every link's trees) AND READ AT EACH PLACE (numsAt ·
p2With · p2All).



LIMITS. At both stored plans work₁ = 0 and work₂ = 20: the rule for work₁ is held at 0 alone. A look
at two plans, no law.
-/
import Johnson.Top.H0.Tw.K2C.Kind
import Johnson.Desc.ProofFile.LotCore
import Johnson.Desc.ProofFile.Places
import OnBytes.Iop.Req
import OnBytes.Params.Chains
import OnBytes.Plan.ReqFrames
import OnBytes.Model.VerifySubproofs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K2
open OnBytes

/-- The ties: the sizes' shape and codes are the chain's and the first state's; their number of
samples the start's. codes₀, shape₀, samples₀: the first state's codes, its frame's shape, the
start's number of samples. -/
def tied (z : Params.ProofSized) (first : Params.First) (codes₀ : Codes) (shape₀ : Params.ReqShape)
    (samples₀ : Nat) : Bool :=
  decide (z.request = first.shape) && decide (z.codes = first.codes) && decide (codes₀ = z.codes) &&
      decide (shape₀ = z.request) &&
    z.set.samples == samples₀

/-- The planner's sizes MADE ANEW of the public record and the chain's links: a search (solveGroup ·
solveStages): FOR A LOOK ALONE. -/
def sizedAnew (W : Model.Verify.Public) (first : Params.First) : Option Params.ProofSized :=
  Params.proofSized W.P.frame (Model.Verify.subproofsWith W first.shape.link)

/-- What link k announces at its moment m. After Iop/Req.lean:326-329, :337 (through switchNotices:
Cs.lean:578-579) and :352-353. -/
def noticesAt (f₀ : ReqFrame) (k m : Nat) : Array OracleNotice :=
  let f := { f₀ with link := k }
  if m != 0 then ReqFrame.notices (f.atMoment m)
  else
    let others := ReqFrame.notices (f.atMoment 0) ++ #[foldMaskNotice (f.foldShape k {})] ++
      (if k == 0 then f.shape.atStart.toArray else #[])
    if k == 0 then others else _root_.Tw.K2.switchNotices (f.groups.getD k {}).target others

/-- The trees that link k sends, in order: depth, width, and whether the next switch reads it (not a
tree that holds what rides at the start). -/
def treesOfLink (codes : Codes) (f₀ : ReqFrame) (k : Nat) : Option (List (Nat × Nat × Bool)) :=
  (f₀.shape.link[k]?).bind fun L =>
    (List.range (_root_.OnBytes.reqMoments L)).foldlM (fun acc m =>
      (layTrees codes (noticesAt f₀ k m)).map fun lay =>
        let own := ({ f₀ with link := k }.atMoment 0).length
        let riders : List Nat :=
          if k == 0 && m == 0 then (List.range f₀.shape.atStart.length).map fun j =>
              lay.tree.getD (own + 1 + j) 0 else []
        acc ++ lay.shapes.toList.zipIdx.map fun t =>
            (t.1.logN, t.1.mainWidth + t.1.maskWidth, !riders.contains t.2)) []

/-- The own trees that the switch into group l reads: number in the chain, depth, width. all: the
trees of every link, in order (treesOfLink at 0, 1, …). -/
def readOf (all : List (List (Nat × Nat × Bool))) (l : Nat) : Option (List (Nat × Nat × Nat)) :=
  (all[l - 1]?).map fun ts =>
    let before := (all.take (l - 1)).foldl (fun n t => n + t.length) 0
    (ts.zipIdx.filter fun x => x.1.2.2).map fun x => (before + x.2, x.1.1, x.1.2.1)

/-- The numbers of the switch into a group. -/
structure Nums where
  /-- the group's number: the link's; at the finish the number of links -/
  grp : Nat
  samples : Nat
  work₁ : Nat
  roots : Nat
  seeds : Nat
  nonZero : Nat
  work₂ : Nat
  answers : Nat
  positions : Nat
  logN : Nat
  /-- the codes, and what the group's first message announces: for the sent trees with their tenants
  -/
  codes : Codes
  sent : Array OracleNotice
  read : List (Nat × Nat × Nat)

/-- WHAT IS MADE ONCE FOR ALL PLACES: the planner's sizes; the records of all groups; the trees of
every link. -/
structure Prep where
  z : Params.ProofSized
  frames : List Plan.FrameN
  trees : List (List (Nat × Nat × Bool))

/-- Made once, at given sizes z; nothing unless z is tied. WHOEVER WANTS THE NUMBERS OF MANY PLACES
CALLS THIS ONCE AND numsAt AT EACH. Of the sub-proofs' record the groups' records read the open rows
alone (Plan/ReqFrames.lean:141-142). -/
def prepareAt (z : Params.ProofSized) (W : Model.Verify.Public) (first : Params.First) (codes₀ :
    Codes) (shape₀ : Params.ReqShape) (samples₀ : Nat) :
    Option Prep := do
  if !tied z first codes₀ shape₀ samples₀ then none
  let trees ← (List.range z.request.link.length).mapM (treesOfLink z.codes { shape := z.request,
                                                                             groups :=
                                                                                 reqGroups z.request
                                                                                     })
  pure ⟨z, Plan.framesOf z (Model.Verify.subproofsWith W first.shape.link), trees⟩

/-- The same at the sizes made anew: FOR A LOOK ALONE: dear. -/
def prepare (W : Model.Verify.Public) (first : Params.First) (codes₀ : Codes) (shape₀ :
    Params.ReqShape) (samples₀ : Nat) : Option Prep :=
  (sizedAnew W first).bind fun z => prepareAt z W first codes₀ shape₀ samples₀

/-- **The numbers of the switch into group l, out of the plan's public records.** link: the place's
link; none: the finish, whose group follows the last link's. -/
def numsAt (P : Prep) (link : Option Nat) : Option Nums := do
  let z := P.z
  let l := link.getD z.request.link.length
  if l == 0 then none
  let f ← P.frames[l]?
  let lay ← layTrees z.codes f.sent.toArray
  let sampled := f.sent.filter fun n => decide (0 < n.shape.answers)
  let read ← readOf P.trees l
  pure
    { grp := l
      samples := z.set.samples
      work₁ := z.set.workOf .sample .request
      roots := lay.shapes.size
      seeds := z.set.samples * (sampled.foldl (fun c n =>
          max c (Params.cubeBitsOf z.codes n.shape)) 0 + 1)
      nonZero := z.set.samples
      work₂ := z.set.workOf .query .request
      answers := z.set.samples * sampled.length
      positions := Params.baseCount z.set .request f.before
      logN := f.before.main.logN
      codes := z.codes
      sent := f.sent.toArray
      read := read }

/-- The same at one place alone: prepare and numsAt in a row. -/
def numsOfPlan (W : Model.Verify.Public) (first : Params.First) (codes₀ : Codes) (shape₀ :
    Params.ReqShape) (samples₀ : Nat)
    (link : Option Nat) : Option Nums :=
  (prepare W first codes₀ shape₀ samples₀).bind fun P => numsAt P link

open ProofFile (Pub Ground Spot headOf)
open VerifiableInference.Desc.First.K2 (P2 At)

/-- The oracle messages beneath the roots of one sending, with their tenants: of the program's pure
layTrees. -/
def oraclesAt (grp : Nat) (codes : Codes) (sent : Array OracleNotice) : List
    VerifiableInference.Desc.Oracle :=
  match layTrees codes sent with
  | none => []
  | some lay =>
    lay.shapes.toList.zipIdx.map fun (t, i) =>
      { logLength := t.logN, words := t.mainWidth + t.maskWidth
        tenants := (List.range t.mainSymbols.size).filterMap fun j =>
          ((List.range sent.size).find? fun n =>
              lay.tree.getD n noId == i && lay.part.getD n noId == j).map fun n =>
            let x := (sent.getD n default).shape
            -- THE GROUPS ARE TOLD: every sampled message of the switch's sending (g · the kept
            -- copies · the link's own first messages) joins just the group that the switch opens
            -- (Cs.lean:543-545 · Req.lean:302-303); the fresh mask, without a sample, joins none.
            -- Kind.lean's [G35] ties grp to the run
            { main := t.mainSymbols.getD j 0, mask := t.maskSymbols.getD j 0, degree := x.mainDeg,
              sampled := x.answers != 0, groups := if x.answers != 0 then [grp] else [] } }

/-- Where a place of the kind stands. -/
def standsOf (sp : Spot) : At :=
  let h := headOf ((sp.cuts.head?.map (·.look)).getD "")
  if h == "F" then .finish else if h == "H" then .head else .link

/-- What is made once, over the harness's records: THE SIZES ARE READ off the planner's own record
of what it has made of the three public files (Z.p.chains.made.sized.proof): no search. -/
def prepOf (Z : Pub) (G : Ground) : Option Prep :=
  prepareAt Z.p.chains.made.sized.proof G.W G.first Z.s₀.st.codes Z.s₀.check.frame.shape Z.P.samples

/-- **The numbers of a place of the kind K2, out of the plan's public records**, over what was made
once. -/
def p2With (P : Prep) (Z : Pub) (sp : Spot) : Option P2 :=
  (numsAt P sp.place.link).map fun n =>
    { name := sp.name, place := sp.place, stands := standsOf sp, grp := n.grp,
      firstTree := Z.P.firstTree, samples := n.samples,
      work₁ := n.work₁, roots := n.roots, seeds := n.seeds, nonZero := n.nonZero,
      work₂ := n.work₂, answers := n.answers, positions := n.positions, logN := n.logN,
      sent := oraclesAt n.grp n.codes n.sent, read := n.read }

/-- The same at one place alone. DEAR IN A LOOP: see prepare. -/
def p2OfPlan (Z : Pub) (G : Ground) (sp : Spot) : Option P2 := (prepOf Z G).bind fun P =>
    p2With P Z sp

/-- **All places of a list that are of the kind K2, each with its numbers: the sizes made ONCE.** -/
def p2All (Z : Pub) (G : Ground) (sps : List Spot) : List (Spot × P2) :=
  match prepOf Z G with
  | none => []
  | some P => (sps.filter fun sp => sp.place.kind == .K2).filterMap fun sp =>
      (p2With P Z sp).map fun p => (sp, p)

end P1K2
