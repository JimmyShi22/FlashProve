-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Desc/First/K4/Hear.lean: the layers' own rounds, first half: what the verifier does while it
hears them.

The rounds themselves, who sends what and what is drawn, stand as a table in
OnBytes/Desc/First/K4/Rounds.lean; the numbers 1 to 7 below are that table's. No round's equation is
a test here: a masked sumcheck leaves one linear claim, and all claims are made in the second half
(OnBytes/Desc/First/K4/Claims.lean), behind the draw that batches them.

  `hearNorms`  1 to 3: the points; the norms' sums, their squares' product layer; the row products.
  `hearTerms`  4: the second sumcheck over the tokens.
  `hearStack`  4 and 5: the element that joins two claims; the batched sumcheck; its end.
  `hearGated`  6: the two product layers of the gated products.
  `hear`       all seven, with the tables of the reads and the merge of the claims on the weights.

WHAT CAN REFUSE. `covers`: the plan is one for which this text is written. `shapeFits`: what the
lookup returned has the layout's shape. Two tests read drawn values: "coin-zero": an element by
which the verifier divides was drawn as 0; and that every call's point, as the lookup returns it,
ends in the coordinates in which the lookup's own point ends. ONE TEST READS THE REQUEST: in the
first group there are T tokens, each below the vocabulary's size (inside `claimE`). All other tests
compare public numbers of the plan with each other, or unwrap a public value that may lack.
NOT HERE, AND WHO ASKS. The shape of each round (its name; how many elements are sent and drawn;
field elements alone; its rows), and that nothing is owed from the round closed in front:
K4/Steps.lean's `hearStep` and K4/Block.lean's `decide`, before `hear` runs; the shape is also asked
by Block.step's `roundsFit`.
Limits. Words below the prime, sent and drawn: asked once at the fold's front (`viewWordsBelowPrime`,
Johnson/Desc/Block.lean), not here. This text compares words as they are at two places, both on
drawn values: "coin-zero" and the test that the calls' points end alike. By reading, not by a run:
at a view whose drawn words were not so tested, an element written (p, 0, 0) would pass "coin-zero",
and its inverse is 0.
Made by program from OnBytes/Model/Layer.lean's own lines, then cut behind `covers`. No law.

-/
import OnBytes.Desc.First.K4.Engine
import OnBytes.Desc.First.K4.Rounds

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.K4
open OnBytes
open OnBytes.Model hiding layerObject stackRounds wsForkLin
open OnBytes.Model.Layer hiding shownRun hearNorms hearTerms joinStart hearStack hearGated
  claimsNorms claimRowBatch claimsTerms claimsEnds claimsGated claimsOneHot claimsPlanes
  claimEmbedding freeSlotTest

variable {m : Type → Type} [Monad m] (En : Eng m)

/-- The numbers that the lookup's run computed are the layout's. -/
def shapeFits (P : Pub) (fo : Forest.Heard) : Bool :=
  let s := fo.shape
  let y := P.y
  s.dT == y.fo.dT && s.kT == y.fo.kT && s.NT == y.fo.NT && s.rK == y.fo.rK &&
    s.first == y.fo.first && s.iota == y.fo.iota && s.callOf == y.fo.callOf

/-- The padding's places are the lookup's. After Forest.paddingLaid
(OnBytes/Model/Look.lean:447). -/
def paddingFits (g : Forest.Heard) (laid : Array Nat) : m Unit :=
  En.mustAs "internal-forest-padding-places" (laid == g.shape.pub)

/-- The points, and the messages of the norms: the convolution sums, the product layer of the
squares, the row products and their token sumcheck. fo: the lookup. -/
def hearNorms (P : Pub) (g : Nat) (fo : Forest.Heard) : m Heard := do
  let y := P.y
  let h := y.h
  let xl := h.xl
  let s := fo.shape
  let PV ← En.point .zero h.lt
  let ZE ← if g == 0 then En.point .zero (y.ls + h.lt) else pure #[]
  let tkh ← if g == 0 then En.point .zero (y.lPd - y.ls) else pure #[]
  -- The last la coordinates of every call's point are the last la of the lookup's point.
  En.mustAs "forest-depth-G" (h.la ≤ s.dT)
  let Z ← En.get (lastOf fo.zx h.la).toOption
  let ends ← En.get (fo.zk.mapM fun zk => (lastOf zk h.la).toOption)
  En.check (ofGroup g "internal-g-merged-point") (ends.all (· == Z))
  let ztF ← En.get (lastOf fo.zx h.lt).toOption
  let sW ← En.claimsIn (ledNS xl * y.NI)
  let gp ← En.batch (ledNS xl)
  let rhoI ← En.point .join P.rd.lNI
  let (C, rho) := normsStart y sW gp rhoI PV
  let wpl ← En.levelIn P.rd.muV rho C (orderDefault P.rd.muV)
  let sPv ← En.claimsIn (ledNP xl * y.NI)
  let omV ← En.batch (ledNP xl * y.NI)
  let tV ← En.tscIn PV h.lt (ledNO xl * y.NI) 2
  pure { fo, PV, ZE, tkh, ztF, sW, gp, wpl, sPv, omV, tV }

/-- The second token sumcheck. KT is its summand at its end point
(Heard.KT). The factors of KT that are not shown hold products with weights, so KT cannot be written
as a form in the reads. pscRow is therefore asked for the claim without the summand (S0 = 0, nothing
kept). It returns a form u in slots, and the sumcheck's claim reads u + eps KT = 0. So KT is set to
-u / eps and enters the start form of the batched sumcheck (joinStart), whose panels prove the
products. A drawn eps of 0 is refused at the end of the run (Blk.check); in such a run KT is 0. -/
def hearTerms (P : Pub) (H : Heard) : m Heard := do
  let tT ← En.tscIn H.ztF P.y.h.lt (nEndT P.y) 1
  En.check "coin-zero" (!isZeroE tT.p.eps)
  let (row, p) ← sumcheckClaim En tT.p zeroE
  pure { H with tT := some { tT with p := p }, KT := row.scale (negE (invE tT.p.eps)) }

/-- The start form of the batched sumcheck: the lookup's join with the inner products moved to the
sumcheck's side, less the claimed sum of the second token sumcheck, plus om[1] times what that
sumcheck leaves. Tests, as Forest.join does (OnBytes/Model/Look.lean), that there is one part
(joinPart) and one weight e for each call of the lookup; the C++ routine has no such test. Also
tests, tree by tree, that the columns which no segment lists hold as many keys as the lookup counts
as padding. That test reads the segments' lists of columns (weighedOf), not the forms. -/
def joinStart (v : Env) (H : Heard) (om : Array E) : m Aff := do
  let fo := H.fo
  let s := fo.shape
  let weighed ← En.get (v.y.calls.mapM v.weighedOf)
  let parts ← En.get ((v.y.calls.zip weighed).toList.zipIdx.mapM fun x =>
    v.joinPart fo.alpha fo.theta x.2 x.1.1 x.1.2)
  En.mustAs "internal-forest-join" (parts.length == s.calls.size && fo.e.size == s.calls.size)
  let c0 := parts.zipIdx.foldl (fun (a : Aff) x => a.addMul x.1 (fo.e.getD x.2 zeroE)) aff0
  paddingFits En fo
    (← En.get (weighed.toList.zipIdx.foldlM (fun laid x => v.laidOf x.2 x.1 laid) (Forest.noPub s)))
  let ey := eqTab fo.zy
  let pad := (List.range (2 ^ s.rK - s.NT)).foldl
    (fun a t => addE a (mulE (ey.getD (s.NT + t) zeroE) (subE fo.alpha (fo.padKey 0)))) zeroE
  let c1 := c0 + Aff.ofConst pad
  let tT ← En.get H.tT
  pure ((c1 - Aff.slot tT.sCl - fo.cEnd).addMul H.KT (om.getD 1 zeroE))

/-- The element that joins the two claims, the batched sumcheck and its end. NCLp: the number of
the panels' weight claims by the plan; lamS: the number of rounds by the plan. -/
def hearStack (P : Pub) (v : Env) (H : Heard) (lamS NCLp : Nat) : m HeardStack := do
  let y := P.y
  let om ← En.batch 2
  let tT ← En.get H.tT
  let shownT ← shownRun En tT.sEnd (nEndT y)
  let pe : PanelEnv := { v, e := H.fo.e, shownT, zt := H.ztF, stubO := stubO y }
  let TS ← En.get (callsTS P)
  let pans ← En.get (panelsT pe TS (panelsA pe {}))
  let (bl, places) := placePanels pans.bl
  En.mustAs (ofGroup v.g "internal-stack") (ceilLog2 places == lamS)
  let p ← En.pscBegin (← joinStart En v H om)
  let st ← plainRounds En { lam := lamS, p := p }
  let NVIRT := 1 + y.LamM
  En.mustAs (ofGroup v.g "internal-claim-count") (pans.nextV == NCLp)
  let (sA0, p) ← En.pscEnds st.p 2 (2 + NVIRT + NCLp)
  let sH1 := sA0 + 1
  let sB0 := sH1 + NVIRT
  let sV := sB0 + 1
  let fin ← En.get (stackEnd y bl st.rs lamS om (← shownRun En sH1 NVIRT) (← shownRun En sV NCLp)
    (← En.shown sA0) (← En.shown sB0))
  let (rowS, _) ← sumcheckClaim En p (mulE fin.As fin.Bs)
  pure { rs := st.rs, sA0, sH1, sB0, sV, fin, rowS }

/-- The product layer of the gated products, from the shown value of the never-sent vector of the
down product's panel; and the second one, of the routed experts. The routed layers' never-sent
vectors were all shown at one point of the column bits. Their values are combined under the
equality weights of a fresh point of the layer bits. -/
def hearGated (P : Pub) (H : Heard) (K : HeardStack) : m (Level × Level) := do
  let y := P.y
  let h := y.h
  let hd ← En.levelIn P.rd.muH (downFrom K.rs K.fin.wD ++ H.ztF) (Aff.slot K.sH1)
    (orderRange P.rd.muH)
  let tT ← En.get H.tT
  let rhoM ← En.point .join (h.ll - 1)
  let e := eqTab rhoM
  let C := (List.range y.LamM).foldl
    (fun (C : Aff) lm => C.addMul (Aff.slot (K.sH1 + 1 + lm)) (e.getD lm zeroE)) aff0
  let hd2 ← En.levelIn P.rd.muH2 (rhoM ++ downFrom K.rs y.lfe ++ tT.r) C (orderRange P.rd.muH2)
  pure (hd, hd2)

/-- The sub-proof's own messages: from the norms' token point, after the lookup, to the value that
the merge shows, before the root of the reads. fo: the lookup. -/
def hear (P : Pub) (hp : HPlan2) (g : Nat) (fo : Forest.Heard) : m Own := do
  En.mustAs "k4-not-covered" (covers P)
  En.mustAs (ofGroup g "internal-g-forest") (shapeFits P fo)
  let y := P.y
  let hasE := g == 0
  let iU3 ← En.get (hp.tl.ix.U.getD 2 none)
  let H ← hearTerms En P (← hearNorms En P g fo)
  -- The tables are laid out before the batched sumcheck, whose forms name their entries.
  En.must hp.tl.funOpen
  let mats := (P.tails.getD g {}).mats.map fun M => (M.m, M.k)
  let (tab, laid, nU3) ← En.get (layTables mats (tableAsks y P.rd g) 0)
  En.mustAs "internal-W-length" (nU3 == hp.nU.getD 2 0)
  let K3 := ((hp.Fp.trees[iU3]?).map (·.K)).getD 0
  let v : Env := { y, sc := P.sc, g, iU3, K3, tab, zk := fo.zk }
  let NCLp := hp.NCL - (if hasE then 1 else 0)
  let K ← hearStack En P v H hp.lamS NCLp
  let (hd, hd2) ← hearGated En P H K
  -- The merge of the weight claims. In the first group the embedding's claim comes last.
  let ce : ClaimEnv :=
    { v, wsLay := P.wsLay, rope := P.rope, rs := K.rs, rt := (H.tT.map (·.r)).getD #[] }
  let claimsP ← En.get (ce.weightClaims (← En.get (callsTS P)))
  let claimsE ← if hasE then En.get ((ce.claimE H.ZE H.tkh P.V P.tokv).map ([·])) else pure []
  let claims := (claimsP ++ claimsE).toArray
  En.mustAs (ofGroup g "internal-claim-count") (claims.size == hp.NCL)
  let sVE ← if hasE then En.claimsIn 1 else pure 0
  let sVa := (Array.range NCLp).map (K.sV + ·) ++ (if hasE then #[sVE] else #[])
  let wo ← En.wsForkEnd P.wsLay claims sVa
  -- From here on all points are known.
  let funs ← En.get (funsOf y fo (← En.get (pointsOf y H hd (some hd2))) laid)
  pure { v, H, K, hd, hd2 := some hd2, sVE, wo, funs }

end OnBytes.Desc.First.K4
