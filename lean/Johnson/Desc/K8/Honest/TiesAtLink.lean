-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/TiesAtLink.lean: THE SMALLNESS TEST: AT A PLAIN SEGMENT, BEHIND A YES OF THE
BATCHING BLOCK AT A CHALLENGE x, SIX OF THE EIGHT CONJUNCTS OF THE VERIFIER's CLAUSE ON THE TIES'
AND THE PLANES' SHAPES SAY YES (the two on the numbers of row weights of the reads' row and of the
ties' row are not among them), BESIDE THE TESTS ON THE READS' WEIGHTS, THE READS' SHAPES AND THE
PLANES' WEIGHTS: `Added8.tiesClause` (Johnson/Desc/K8/Honest/TiesClause.lean) joined to
`four_of_walk` (FourAtLink.lean). WHAT `tiesClause` ASKS AT THE LEDGER BEHIND THE RUNS IS CARRIED
FROM THE LEDGER IN FRONT by what the batching's draw fills (`full_of_fill`, `K9L.fill_looks`:
BitsFilled.lean); its premise on the number of claims is paid (`Added8.plan_bound`, TieShape.lean);
two of its public premises are drawn from the public test `symbolsLaid` (`laid_shape_apart`,
TieWhole.lean), one from `apartB`. None of the library's goals.

  `SymbolsFront tl F`   at the ledger in front: the array of each matrix's symbols is of the kind
                   "symbols", has one virtual row and the plan's numbers of rows and of columns ·
                   the digits' array has the ties' row
  `TiesRest tl`   what stays of the public premises: at each matrix K1 = k and Kc = k · the plan's
                   rows add up to mz
  `tiesAtY_of_fill`   SymbolsFront tl F · the digits' array has 2 mz columns in front · at each
                   matrix Kc = k · the list has a member for each array ⊢ TiesAtY at a ledger whose
                   arrays are F's, filled
  `tiesPub_of_laid`   symbolsLaid tl = true · TiesRest tl ⊢ TiesPub tl
  **`five_of_walk`**   `four_of_walk`'s premises, but that the digits' array has the reads' row,
                   which follows from its having the ties' row · SymbolsFront · symbolsLaid ·
                   TiesRest ⊢ its ends, with these six in the stead of the test on the planes'
                   shapes, which is one of them
  `FiveHeld tl g t'`   the state t' shows data tl', a ledger G and a number jo at which these say
                   yes
  **`fiveHeld_at_link`**   FiveHeld tl g t' behind a yes of the batching block at a plain segment:
                   one call of `filled_at_link` (BitsFilled.lean) and one of the above
Limits. IMPLICATIONS. PAID BY NOBODY HERE: all that `fourHeld_at_link` leaves · SymbolsFront ·
symbolsLaid · TiesRest. The rows are named by the plan's number of blocks (2 * tl.zzBlocks and that
number + 1), not by the number that the test computes again. PAYERS IN SIGHT, NOT CALLED: that the
four public tests `symbolsLaid`, `apartB`, `piecesLaid`, `tiesLaid` say yes, and that every virtual
row begins at column 0, are sentences on the state in front of a batching: `five_at_batch`
(Johnson/P1K8R/SecondFrontAtBatch.lean) shows them, in scope, of every state that the chain's own
blocks reach there. At one challenge x. No prover stands in it.
Nothing is claimed on completeness, soundness or hiding.

-/
import Johnson.Desc.K8.Honest.FourAtLink
import Johnson.Desc.K8.Honest.TiesClause

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open VerifiableInference.Desc VerifiableInference.Desc.First.TailClaims
open VerifiableInference.Desc.First.TailClaims.Law
open OnBytes.Tie.Pv.Tail.Port

/-- The symbols' arrays and the ties' row at the ledger in front. -/
structure SymbolsFront (tl : HTailF2) (F : Fork) : Prop where
  kind : ∀ mu, mu < tl.NM → (F.trees.getD (tl.gtTree.getD mu 0) {}).kind = .symbols
  rows : ∀ mu, mu < tl.NM → (F.trees.getD (tl.gtTree.getD mu 0) {}).rows.size = 1
  R : ∀ mu, mu < tl.NM → (F.trees.getD (tl.gtTree.getD mu 0) {}).R = (tl.shp.getD mu {}).Rr
  K : ∀ mu, mu < tl.NM → (F.trees.getD (tl.gtTree.getD mu 0) {}).K = (tl.shp.getD mu {}).Kc
  row : tl.zzRowTies < (F.trees.getD tl.ix.ZZ {}).rows.size

/-- What stays of the public premises. -/
structure TiesRest (tl : HTailF2) : Prop where
  K1 : ∀ mu, mu < tl.NM → (tl.shp.getD mu {}).K1 = (tl.shp.getD mu {}).k
  Kc : ∀ mu, mu < tl.NM → (tl.shp.getD mu {}).Kc = (tl.shp.getD mu {}).k
  sum : tl.shp.foldl (fun n s => n + s.m) 0 = tl.mz

/-- **The sizes behind the filling.** -/
theorem tiesAtY_of_fill {tl : HTailF2} {F Y : Fork} (T : Tail2) (Tf : SymbolsFront tl F)
    (hKz : (F.trees.getD tl.ix.ZZ {}).K = 2 * tl.mz)
    (hKc : ∀ mu, mu < tl.NM → (tl.shp.getD mu {}).Kc = (tl.shp.getD mu {}).k)
    (hT : T.nt.size = F.trees.size) (hY : Y.trees = (t2FillL F T).trees) : TiesAtY tl Y := by
  refine ⟨fun mu hmu => ?_, ?_⟩
  · have lk : LinkJoin.look (Y.trees.getD (tl.gtTree.getD mu 0) {}) =
        LinkJoin.look (F.trees.getD (tl.gtTree.getD mu 0) {}) := by
      rw [hY]
      exact look_at (K9L.fill_looks F T) _
    have h0 : 0 < (F.trees.getD (tl.gtTree.getD mu 0) {}).rows.size := by
      rw [Tf.rows mu hmu]
      exact Nat.one_pos
    have ht : tl.gtTree.getD mu 0 < T.nt.size := by
      rw [hT]
      exact (hasRow_of_rows rfl h0).1
    exact ⟨(congrArg (·.1) lk).trans (Tf.kind mu hmu),
      (congrArg (·.2.2.2) lk).trans (Tf.rows mu hmu), (congrArg (·.2.1) lk).trans (Tf.R mu hmu),
      (congrArg (·.2.2.1) lk).trans (Tf.K mu hmu),
      ((full_of_fill T ht h0 hY).trans (Tf.K mu hmu)).trans (hKc mu hmu)⟩
  · have ht : tl.ix.ZZ < T.nt.size := by
      rw [hT]
      exact (hasRow_of_rows rfl Tf.row).1
    exact (full_of_fill T ht Tf.row hY).trans hKz

/-- The public premises, from the public test on the symbols' arrays and what stays. -/
theorem tiesPub_of_laid {tl : HTailF2} (hS : symbolsLaid tl = true) (Tr : TiesRest tl) :
    TiesPub tl := by
  refine ⟨fun mu hmu => ⟨(laid_shape_apart tl hS mu hmu).1, Tr.K1 mu hmu, Tr.Kc mu hmu⟩,
    fun a ha b hb e => (laid_shape_apart tl hS a ha).2 a ha b hb e, Tr.sum⟩

/-- **THE CLAUSE ON THE SHAPES AND THREE TESTS, ALONG THE RUNS' OWN CUT.** -/
theorem five_of_walk {L : Link S Claim} {pre post : List (Nat × String)} {t e : S}
    {cls fr k8 bk : List Claim} {e₁ e₂ : S} {F₁ F₂ Y G F : Fork} {tl tl' : HTailF2}
    {funs : Array HFun} (W : Walk L pre post t e cls fr k8 bk e₁ e₂ F₁ F₂ tl tl' funs)
    (A : Added8 tl tl' funs Y G F₁ F₂ fr k8 bk fr.length) (T : Tail2)
    (hYt : Y.trees = (t2FillL F T).trees) (hT : T.nt.size = F.trees.size)
    (g : Forest.Heard) (hg : tl.heard = some g) (P : PubAt tl g)
    (hzR : ((F.trees.getD tl.ix.ZZ {}).rows.getD tl.zzRowReads {}).L0 = 0)
    (hzB : ∀ e, e ≤ 2 → ((F.trees.getD tl.ix.BZ {}).rows.getD e {}).L0 = 0)
    (B : BitsFront tl F) (Pb : BitsPub tl g)
    (hKz : (F.trees.getD tl.ix.ZZ {}).K = 2 * tl.mz)
    (Tf : SymbolsFront tl F) (hS : symbolsLaid tl = true) (Tr : TiesRest tl)
    {Inv Inv₂ : S → Prop} (R : RunsKeep L pre post (FourRows tl) Inv Inv₂) (hI : Inv t) :
    tl'.joinObj9 = some fr.length ∧
      ((((coefBody tl' g G).trees.getD tl'.ix.ZZ {}).rows.getD (2 * tl.zzBlocks + 1) {}).L.size ==
          2 * tl'.mz &&
        tl'.gamX.size == tl'.NM && tl'.gamV.size == tl'.NM &&
        (List.range tl'.NM).all (tl'.tieShapeHeld (coefBody tl' g G)) &&
        tl'.shp.foldl (fun n s => n + s.m) 0 == tl'.mz &&
        tl'.planesShapeHeld (coefBody tl' g G) g) = true ∧
      tl'.planesWeightsHeld (coefBody tl' g G) g fr.length = true ∧
      tl'.readShapeHeld
        (((coefBody tl' g G).trees.getD tl'.ix.ZZ {}).rows.getD (2 * tl.zzBlocks) {}).L = true ∧
      tl'.readWeightsHeld (coefBody tl' g G)
        (((coefBody tl' g G).trees.getD tl'.ix.ZZ {}).rows.getD (2 * tl.zzBlocks) {}).L = true := by
  have hRz : tl.zzRowReads < (F.trees.getD tl.ix.ZZ {}).rows.size :=
    Nat.lt_trans (Nat.lt_succ_self _) Tf.row
  obtain ⟨h2, h3, h4, -, h6⟩ := four_of_walk W A T hYt hT g hg P hzR hzB B Pb hKz hRz R hI
  have hBZ : tl.ix.BZ < T.nt.size := by
    rw [hT]
    exact (hasRow_of_rows B.rows (show 0 < 3 by omega)).1
  exact ⟨h2, A.tiesClause g tl.zzBlocks rfl (tiesAtY_of_fill T Tf hKz Tr.Kc hT hYt)
    (tiesPub_of_laid hS Tr) (A.plan_bound rfl) (bitsAt_of_fill T B hBZ hYt) Pb
    (fun mu hmu => (((apartB_iff tl).1 P.apart).2.2.2 mu hmu).1), h6, h4, h3⟩

/-- The state t' shows data, a ledger and a number at which the clause and the three tests say
yes. -/
def FiveHeld (tl : HTailF2) (g : Forest.Heard) (t' : S) : Prop :=
  ∃ (tl' : HTailF2) (G : Fork) (jo : Nat), tlForkP.get? t' = some (tl', G) ∧
    tl'.joinObj9 = some jo ∧
      ((((coefBody tl' g G).trees.getD tl'.ix.ZZ {}).rows.getD (2 * tl.zzBlocks + 1) {}).L.size ==
          2 * tl'.mz &&
        tl'.gamX.size == tl'.NM && tl'.gamV.size == tl'.NM &&
        (List.range tl'.NM).all (tl'.tieShapeHeld (coefBody tl' g G)) &&
        tl'.shp.foldl (fun n s => n + s.m) 0 == tl'.mz &&
        tl'.planesShapeHeld (coefBody tl' g G) g) = true ∧
      tl'.planesWeightsHeld (coefBody tl' g G) g jo = true ∧
      tl'.readShapeHeld
        (((coefBody tl' g G).trees.getD tl'.ix.ZZ {}).rows.getD (2 * tl.zzBlocks) {}).L = true ∧
      tl'.readWeightsHeld (coefBody tl' g G)
        (((coefBody tl' g G).trees.getD tl'.ix.ZZ {}).rows.getD (2 * tl.zzBlocks) {}).L = true

/-- **AT A PLAIN SEGMENT, BEHIND A YES OF THE BATCHING BLOCK.** -/
theorem fiveHeld_at_link (L : Link S Claim) (i : Nat) (pre post : List (Nat × String))
    (hord : L.order = pre ++ (i, "K8.equations") :: post) (Hpre : PreOk L pre)
    (Hpost : PostOk L post)
    (tEq : ∀ run, LinkJoin.At L (i, "K8.equations") run → LinkJoin.Under run K9L.k8Run.2)
    (p : K9.Where) (batch : S → List Fmt.RoundView → Except String S) (s t' : S) (tl : HTailF2) (F : Fork)
    (funs : Array HFun)
    (hb : ∀ rs t, batch s rs = .ok t →
      (K9.batch K9.atS p (claimsInBy L.each L.hear L.order)).decide s rs [] = .ok t)
    (ht : s.tl? = some tl) (hF : s.fork? = some F) (hf : s.funs? = some funs)
    (g : Forest.Heard) (hg : tl.heard = some g) (P : PubAt tl g)
    (hzR : ((F.trees.getD tl.ix.ZZ {}).rows.getD tl.zzRowReads {}).L0 = 0)
    (hzB : ∀ e, e ≤ 2 → ((F.trees.getD tl.ix.BZ {}).rows.getD e {}).L0 = 0)
    (B : BitsFront tl F) (Pb : BitsPub tl g)
    (hKz : (F.trees.getD tl.ix.ZZ {}).K = 2 * tl.mz)
    (Tf : SymbolsFront tl F) (hS : symbolsLaid tl = true) (Tr : TiesRest tl)
    (hT : ∀ a0, K9.atS.get? s = some a0 → a0.L.list.nt.size = F.trees.size)
    (Inv Inv₂ : S → Prop) (R : RunsKeep L pre post (FourRows tl) Inv Inv₂)
    (x : Cb.Gl.E) (hInv : ∀ t, drawnAt p s (chiAt x) = .ok t → Inv t)
    (hbt : batch s [⟨[], chiAt x⟩] = .ok t') : FiveHeld tl g t' := by
  obtain ⟨a0, t, e, e₁, e₂, cls, fr, k8, bk, tl', Y, G, F₁, F₂, ha0, hdr, W, hget, A, hYt⟩ :=
    filled_at_link L i pre post hord Hpre Hpost tEq p batch s t' tl F funs hb ht hF hf x hbt
  exact ⟨tl', G, fr.length, hget, five_of_walk W A a0.L.list hYt (hT a0 ha0) g hg P hzR hzB B
    Pb hKz Tf hS Tr R (hInv t hdr)⟩

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.tiesAtY_of_fill
#print axioms VerifiableInference.Desc.First.K8.Honest.tiesPub_of_laid
#print axioms VerifiableInference.Desc.First.K8.Honest.five_of_walk
#print axioms VerifiableInference.Desc.First.K8.Honest.fiveHeld_at_link
