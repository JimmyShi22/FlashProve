-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/LeftAtLink.lean: THE SMALLNESS TEST: AT A PLAIN SEGMENT, BEHIND A YES OF THE
BATCHING BLOCK AT A CHALLENGE x: THREE READINGS AND SEVEN TESTS OF THE VERIFIER's TEST ON WHAT THE
ADDING HAS LEFT (OnBytes/Model/Tail.lean, "tileSelfTestF") IN ONE SENTENCE, FROM SENTENCES ON THE
DATA AND THE LEDGER IN FRONT AND ON THE SEGMENT's OTHER RUNS. NOT THE WHOLE OF THAT TEST: see the
Limits. An assembly of `five_of_walk` (Johnson/Desc/K8/Honest/TiesAtLink.lean),
`Added8.firstClause`, `Added8.tile` and the three lemmas that carry a sentence from in front
(LeftRest.lean), `wants_tile` (WantsTile.lean) and `Added8.coefOK` (SecondAtPlain.lean). None of the
library's goals.

  `AllHeld tl F`   the sentence: there are g, jo, nbW, W with: tl.heard = some g · tl.joinObj9 =
                   some jo · tl.wants = some (nbW, W) · the seven tests say yes at the ledger behind
                   the step that lays the rows' weights
  `SymbolArrays tl F`   at the ledger in front the array of each matrix's symbols is of the kind
                   "symbols", has one virtual row and the plan's numbers of rows and of columns
  `WantPlan tl w`   of one expected piece: the plan's piece under its call and index is one of the
                   calls' pieces, lies in the digits' array and has the expected virtual row, rows
                   and columns
  `AllFront tl F g nbW W`   seventeen sentences on the data and the ledger in front, as one
                   structure. A DRESS, NO PAYMENT
  **`all_of_walk`**   along the runs' own cut, at what a yes of the batching opens there: AllFront ·
                   the premise on the other runs (`RunsKeep`) ⊢ AllHeld tl' G
  **`allHeld_at_link`**   behind a yes of the batching block at a plain segment: the state behind
                   shows data tl' and a ledger G with AllHeld tl' G: one call of `filled_at_link`
                   (BitsFilled.lean) and one of the above
FALLEN AT THIS JOIN, AGAINST THE PREMISES OF THE LEMMAS THAT ARE CALLED: that the digits' array has
2 mz columns and has the ties' row (both follow from DigitsFront) · of `Added8.tile`: the two
sentences on the list of expected pieces and three of WantPub's ten fields (`wants_tile`, under 0 <
tl.tau) · Fo.CoefOK now stands at the data and the ledger in front. COME AT THIS JOIN, AGAINST THE
TEN SENTENCES ON THE FRONT THAT `fiveHeld_at_link` ASKS: Fo.CoefOK · tl.wants = some (nbW, W) · nbW
= tl.zzBlocks · 0 < tl.tau · WantPlan at every expected piece · the three tests at the data in front
· of the digits' array its name, its number of rows and its number of virtual rows.
Limits. IMPLICATIONS. NO MEMBER: THAT AllFront's SEVENTEEN CAN HOLD TOGETHER IS NOT SHOWN. PAID BY
NOBODY HERE, AND AS A WHOLE SHOWN OF NO STATE: AllFront's seventeen · RunsKeep, with two invariants
as letters · PreOk, PostOk, the list's tie · that the link's list has a member for each array. Three
of the seventeen are the verifier's own tests at the data in front (forestHeld · both callHeld ·
pointsHeld): MOVED, NOT PAID. PAYERS IN SIGHT, NOT CALLED: of every state that the chain's own
blocks reach in front of a batching, in scope, `five_at_batch`
(Johnson/P1K8R/SecondFrontAtBatch.lean) shows symbolsLaid, that every virtual row begins at column 0
(so zR and zB), and three fields of PubAt (tiesLaid · piecesLaid · apartB) · nbW = tl.zzBlocks:
`wants_blocks`
(Johnson/Desc/K8/Honest/BlocksCount.lean), `shape_wants` (BlocksPlanned.lean) · of WantPlan: the
array, the virtual row and the columns are what the public test `piecesLaid` compares
(PiecesLaid.lean), which stands in PubAt; the rows are not. At one challenge x. No prover stands in
it. OF THE VERIFIER's WHOLE TEST THESE ARE NOT IN `AllHeld`: the test on the pieces' weights
(`pieceWeightsHeld`) · the test on the ties' weights (`tieWeightsHeld`) · that the reads' row and
the ties' row of the digits' array have tau row weights each · that these row weights are the powers
of the batching element.
Nothing is claimed on completeness, soundness or hiding.

-/
import Johnson.Desc.K8.Honest.WantsTile

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open VerifiableInference.Desc VerifiableInference.Desc.First.TailClaims
open VerifiableInference.Desc.First.TailClaims.Law
open OnBytes.Tie.Pv.Tail.Port

/-- Three readings and seven tests, at data and a ledger. -/
def AllHeld (tl : HTailF2) (F : Fork) : Prop :=
  ∃ (g : Forest.Heard) (jo : Nat) (nbW : Nat) (W : List Want),
    tl.heard = some g ∧ tl.joinObj9 = some jo ∧ tl.wants = some (nbW, W) ∧
    (((coefBody tl g F).trees.getD tl.ix.ZZ {}).rows.size == 2 * nbW + 2 && tl.forestHeld g &&
      [0, 1].all (tl.callHeld g nbW)) = true ∧
    tl.piecesTile (coefBody tl g F) W = true ∧ tl.pointsHeld g = true ∧
    ((((coefBody tl g F).trees.getD tl.ix.ZZ {}).rows.getD (2 * nbW + 1) {}).L.size ==
        2 * tl.mz &&
      tl.gamX.size == tl.NM && tl.gamV.size == tl.NM &&
      (List.range tl.NM).all (tl.tieShapeHeld (coefBody tl g F)) &&
      tl.shp.foldl (fun n s => n + s.m) 0 == tl.mz &&
      tl.planesShapeHeld (coefBody tl g F) g) = true ∧
    tl.planesWeightsHeld (coefBody tl g F) g jo = true ∧
    tl.readShapeHeld
      (((coefBody tl g F).trees.getD tl.ix.ZZ {}).rows.getD (2 * nbW) {}).L = true ∧
    tl.readWeightsHeld (coefBody tl g F)
      (((coefBody tl g F).trees.getD tl.ix.ZZ {}).rows.getD (2 * nbW) {}).L = true

/-- The symbols' arrays at the ledger in front. -/
structure SymbolArrays (tl : HTailF2) (F : Fork) : Prop where
  kind : ∀ mu, mu < tl.NM → (F.trees.getD (tl.gtTree.getD mu 0) {}).kind = .symbols
  rows : ∀ mu, mu < tl.NM → (F.trees.getD (tl.gtTree.getD mu 0) {}).rows.size = 1
  R : ∀ mu, mu < tl.NM → (F.trees.getD (tl.gtTree.getD mu 0) {}).R = (tl.shp.getD mu {}).Rr
  K : ∀ mu, mu < tl.NM → (F.trees.getD (tl.gtTree.getD mu 0) {}).K = (tl.shp.getD mu {}).Kc

/-- The plan's piece under an expected piece's call and index is the expected one. -/
structure WantPlan (tl : HTailF2) (w : Want) : Prop where
  mem : (w.call, (tl.zOf w.call).pieces.getD w.i {}) ∈ joinPairs tl
  tree : ((tl.zOf w.call).pieces.getD w.i {}).tree = tl.ix.ZZ
  row : ((tl.zOf w.call).pieces.getD w.i {}).row = w.row
  r0 : ((tl.zOf w.call).pieces.getD w.i {}).r0 = w.r0
  Rp : ((tl.zOf w.call).pieces.getD w.i {}).Rp = w.Rp
  c0 : ((tl.zOf w.call).pieces.getD w.i {}).c0 = w.c0
  Cp : ((tl.zOf w.call).pieces.getD w.i {}).Cp = w.Cp

/-- What is asked of the data and the ledger in front. -/
structure AllFront (tl : HTailF2) (F : Fork) (g : Forest.Heard) (nbW : Nat) (W : List Want) :
    Prop where
  pub : PubAt tl g
  zR : ((F.trees.getD tl.ix.ZZ {}).rows.getD tl.zzRowReads {}).L0 = 0
  zB : ∀ e, e ≤ 2 → ((F.trees.getD tl.ix.BZ {}).rows.getD e {}).L0 = 0
  bits : BitsFront tl F
  bitsPub : BitsPub tl g
  digits : DigitsFront tl F
  syms : SymbolArrays tl F
  laid : symbolsLaid tl = true
  rest : TiesRest tl
  coef : Fo.CoefOK tl F
  wants : tl.wants = some (nbW, W)
  blocks : nbW = tl.zzBlocks
  tau : 0 < tl.tau
  plan : ∀ w ∈ W, WantPlan tl w
  forest : tl.forestHeld g = true
  calls : [0, 1].all (tl.callHeld g nbW) = true
  points : tl.pointsHeld g = true

/-- **ALL OF IT, ALONG THE RUNS' OWN CUT.** -/
theorem all_of_walk {L : Link S Claim} {pre post : List (Nat × String)} {t e : S}
    {cls fr k8 bk : List Claim} {e₁ e₂ : S} {F₁ F₂ Y G F : Fork} {tl tl' : HTailF2}
    {funs : Array HFun} (Wk : Walk L pre post t e cls fr k8 bk e₁ e₂ F₁ F₂ tl tl' funs)
    (A : Added8 tl tl' funs Y G F₁ F₂ fr k8 bk fr.length) (T : Tail2)
    (hYt : Y.trees = (t2FillL F T).trees) (hT : T.nt.size = F.trees.size)
    (g : Forest.Heard) (hg : tl.heard = some g) (nbW : Nat) (Wn : List Want)
    (D : AllFront tl F g nbW Wn)
    {Inv Inv₂ : S → Prop} (R : RunsKeep L pre post (FourRows tl) Inv Inv₂) (hI : Inv t) :
    AllHeld tl' G := by
  have Tf : SymbolsFront tl F := ⟨D.syms.kind, D.syms.rows, D.syms.R, D.syms.K, by
    rw [D.digits.rows]
    exact Nat.lt_succ_self _⟩
  obtain ⟨h2, h3, h4, h5, h6⟩ := five_of_walk Wk A T hYt hT g hg D.pub D.zR D.zB D.bits D.bitsPub
    D.digits.K Tf D.laid D.rest R hI
  have fG : Fo.Frame F G :=
    ((Fo.frame_fill F T).trans (Fo.frame_same hYt)).trans (Fo.frame_trees A.core.2.2.1)
  obtain ⟨wp, wa, wb⟩ := wants_tile tl nbW Wn D.wants D.tau
  have hWP : ∀ w ∈ Wn, WantPub tl w := fun w hw => by
    obtain ⟨b1, b2, b3⟩ := wb w hw
    have P := D.plan w hw
    exact ⟨P.mem, P.tree, P.row, P.r0, P.Rp, P.c0, P.Cp, b1, b2, by
      rw [← D.blocks]
      omega⟩
  rw [← D.blocks] at h3 h5 h6
  exact ⟨g, fr.length, nbW, Wn, A.heard_stays.trans hg, h2, A.wants_stays.trans D.wants,
    A.firstClause g T hYt D.digits nbW D.blocks D.forest D.calls,
    A.tile g Wn T hYt hT D.digits (A.coefOK fG D.coef) hWP wp wa,
    (A.points_stays g).trans D.points, h3, h4, h5, h6⟩

/-- **AT A PLAIN SEGMENT, BEHIND A YES OF THE BATCHING BLOCK.** -/
theorem allHeld_at_link (L : Link S Claim) (i : Nat) (pre post : List (Nat × String))
    (hord : L.order = pre ++ (i, "K8.equations") :: post) (Hpre : PreOk L pre)
    (Hpost : PostOk L post)
    (tEq : ∀ run, LinkJoin.At L (i, "K8.equations") run → LinkJoin.Under run K9L.k8Run.2)
    (p : K9.Where) (batch : S → List Fmt.RoundView → Except String S) (s t' : S) (tl : HTailF2) (F : Fork)
    (funs : Array HFun)
    (hb : ∀ rs t, batch s rs = .ok t →
      (K9.batch K9.atS p (claimsInBy L.each L.hear L.order)).decide s rs [] = .ok t)
    (ht : s.tl? = some tl) (hF : s.fork? = some F) (hf : s.funs? = some funs)
    (g : Forest.Heard) (hg : tl.heard = some g) (nbW : Nat) (Wn : List Want)
    (D : AllFront tl F g nbW Wn)
    (hT : ∀ a0, K9.atS.get? s = some a0 → a0.L.list.nt.size = F.trees.size)
    (Inv Inv₂ : S → Prop) (R : RunsKeep L pre post (FourRows tl) Inv Inv₂)
    (x : Cb.Gl.E) (hInv : ∀ t, drawnAt p s (chiAt x) = .ok t → Inv t)
    (hbt : batch s [⟨[], chiAt x⟩] = .ok t') :
    ∃ (tl' : HTailF2) (G : Fork), tlForkP.get? t' = some (tl', G) ∧ AllHeld tl' G := by
  obtain ⟨a0, t, e, e₁, e₂, cls, fr, k8, bk, tl', Y, G, F₁, F₂, ha0, hdr, Wk, hget, A, hYt⟩ :=
    filled_at_link L i pre post hord Hpre Hpost tEq p batch s t' tl F funs hb ht hF hf x hbt
  exact ⟨tl', G, hget, all_of_walk Wk A a0.L.list hYt (hT a0 ha0) g hg nbW Wn D R (hInv t hdr)⟩

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.all_of_walk
#print axioms VerifiableInference.Desc.First.K8.Honest.allHeld_at_link
