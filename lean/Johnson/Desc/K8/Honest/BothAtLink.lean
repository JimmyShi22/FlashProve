-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/BothAtLink.lean: THE SMALLNESS TEST: AT A PLAIN SEGMENT, BEHIND A YES OF THE
BATCHING BLOCK AT A CHALLENGE x, TWO OF THE VERIFIER's TESTS ON WHAT THE ADDING OF ALL THE SEGMENT's
CLAIMS HAS LEFT SAY YES: the test on the reads' weights (`readWeightsHeld`) and, where the test on
the planes' shapes says yes, the test on the planes' weights (`planesWeightsHeld`; both
OnBytes/Model/Tail.lean). A JOIN OF SIX FILES: `open_at_link`
(Johnson/Desc/K8/Honest/OpenAtLink.lean: the walk and what a yes opens, at one cut of the list) ·
`others_of_walk` (OthersAtLink.lean: the other runs' claims) · `planeOff_of`, `plainOff_reads`
(PlanesOff.lean: the kind's own four) · `Added8.readEqs` (ReadEqs.lean) · `Added8.planeEqs`
(PlaneEqs.lean) · `eq_join_bits` (PlanesFront.lean). None of the library's goals.

  `FourRows tl cl`   the claim names no entry and no run of the reads' row of the digits' array, nor
                   of one of the three virtual rows of the bits' array
  `PubAt tl g`   eight facts on the data in front: six on public numbers, among them that the
                   arrays' numbers are apart (the test `apartB`,
                   Johnson/Desc/K8/Honest/ApartOf.lean); two on forms that the digits' lookup has
                   heard (its last claim; the start of its last sumcheck): each names no entry
  `offAt_bits`   apartB tl = true ⊢ OffAt tl tl.ix.BZ e, at every e: no tie and no read lays a
                   weight on a virtual row of the bits' array
  `rows_zero`   where two ledgers have one shape and a virtual row begins at column 0 in the one, it
                   does in the other
  `RunsKeep L pre post Q Inv Inv₂`   the three premises on the segment's other runs, as one
                   structure: each run in front of the kind's list keeps Inv and makes claims with Q
                   alone · a yes of the kind's list leads from Inv to Inv₂ · each run behind keeps
                   Inv₂ and makes claims with Q alone
  **`both_of_walk`**   the runs' own cut of the list (`Walk`) · what a yes of the batching block
                   opens at that cut (`Added8`, with the number of the claims in front) · the ledger
                   behind the runs has the shape of the ledger in front · tl.heard = some g · PubAt
                   tl g · four virtual rows begin at column 0 in front · RunsKeep at Q := FourRows
                   tl · Inv behind the draw ⊢ the three ends below, at jo := the number of the
                   claims in front
  **`both_at_link`**   the segment's order is pre ++ [(i, "K8.equations")] ++ post, with `PreOk`,
                   `PostOk` and the list's tie to its run · the state in front shows tl, F, funs ·
                   tl.heard = some g · PubAt tl g · four virtual rows begin at column 0 in F ·
                   RunsKeep at Q := FourRows tl, with Inv behind the draw · a yes of the batching
                   block at x ⊢ the state behind shows data tl' and a ledger G with: tl'.joinObj9 =
                   some jo · the test on the reads' weights says yes · planesShapeHeld → the test on
                   the planes' weights says yes at jo
Limits. AN IMPLICATION. PAID BY NOBODY HERE: `RunsKeep`, THE THREE PREMISES ON THE OTHER RUNS (which
invariants serve all runs of a segment at once is not said) · PubAt · the four rows' first columns ·
PreOk, PostOk and the tie. THE TEST ON THE PLANES' SHAPES STAYS A PREMISE OF THE SECOND END: another
clause of the same test of the verifier's. THE READS' ROW IS NAMED BY THE PLAN's NUMBER OF BLOCKS (2
* tl.zzBlocks), NOT BY THE NUMBER THAT THE TEST COMPUTES AGAIN; g is what the data IN FRONT have
heard. At one challenge x: nothing on how many challenges meet the premises. No prover stands in it.
Nothing is claimed on completeness, soundness or hiding.

-/
import Johnson.Desc.K8.Honest.OpenAtLink
import Johnson.Desc.K8.Honest.OthersAtLink
import Johnson.Desc.K8.Honest.ReadEqs
import Johnson.Desc.K8.Honest.PlaneEqs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open VerifiableInference.Desc VerifiableInference.Desc.First.TailClaims
open VerifiableInference.Desc.First.TailClaims.Law
open OnBytes.Tie.Pv.Tail.Port

/-- The claim names nothing of the reads' row, nor of one of the bits' array's three rows. -/
def FourRows (tl : HTailF2) (cl : Claim) : Prop :=
  NamesNotAt tl.ix.ZZ tl.zzRowReads cl ∧ ∀ e, e ≤ 2 → NamesNotAt tl.ix.BZ e cl

/-- The facts on the data in front. -/
structure PubAt (tl : HTailF2) (g : Forest.Heard) : Prop where
  ties : tiesLaid tl = true
  tau : tl.tau ≤ 2 ^ 64
  rows : ∀ nu, nu < tl.NM → ((tl.mats.getD nu {}).m + 2) / 3 ≤ 2 ^ 64
  cols : ColsFacts tl
  pieces : piecesLaid tl = true
  apart : apartB tl = true
  cEnd : g.cEnd.ents.isEmpty = true
  start : g.leaves.start.ents.isEmpty = true

/-- No tie and no read lays a weight on a virtual row of the bits' array, where the arrays' numbers
are apart. -/
theorem offAt_bits {tl : HTailF2} (h : apartB tl = true) (e : Nat) : OffAt tl tl.ix.BZ e := by
  obtain ⟨h1, ⟨-, h2⟩, ⟨-, h3⟩, h4⟩ := (apartB_iff tl).1 h
  exact ⟨fun c => h1 c.1, fun c => h1 c.1, fun mu hmu c => (h4 mu hmu).1 c.1, h2, h3⟩

/-- Where two ledgers have one shape and a virtual row begins at column 0 in the one, it does in
the other. -/
theorem rows_zero {A B : Array HTree} (h : shapeOf A = shapeOf B) (t r : Nat)
    (h0 : ((B.getD t {}).rows.getD r {}).L0 = 0) : ((A.getD t {}).rows.getD r {}).L0 = 0 := by
  rw [L0_of_shape, h, ← L0_of_shape]
  exact h0

/-- What is asked of the segment's other runs of claims: each run in front of the kind's list keeps
Inv and makes claims with Q alone; a yes of the kind's list leads from Inv to Inv₂; each run behind
keeps Inv₂ and makes claims with Q alone. -/
structure RunsKeep (L : Link S Claim) (pre post : List (Nat × String)) (Q : Claim → Prop)
    (Inv Inv₂ : S → Prop) : Prop where
  pre : ∀ o ∈ pre, ∀ run, LinkJoin.At L o run → ∀ (m : Nat) (u u' : S) (c : List Claim),
    Inv u → run m u = .ok (c, u') → (∀ cl ∈ c, Q cl) ∧ Inv u'
  k8 : ∀ (u : S) (tl tl' : HTailF2) (F F₂ : Fork) (funs : Array HFun) (k8 : List Claim)
    (n : Nat), Inv u → u.fork? = some F → u.tl? = some tl → u.funs? = some funs →
    equations n tl funs F = .ok (tl', F₂, k8) → Inv₂ ((u.putTl tl').putFork F₂)
  post : ∀ o ∈ post, ∀ run, LinkJoin.At L o run → ∀ (m : Nat) (u u' : S) (c : List Claim),
    Inv₂ u → run m u = .ok (c, u') → (∀ cl ∈ c, Q cl) ∧ Inv₂ u'

/-- **BOTH TESTS, ALONG THE RUNS' OWN CUT**: from the walk and what a yes of the batching block
opens at that cut. -/
theorem both_of_walk {L : Link S Claim} {pre post : List (Nat × String)} {t e : S}
    {cls fr k8 bk : List Claim} {e₁ e₂ : S} {F₁ F₂ Y G F : Fork} {tl tl' : HTailF2}
    {funs : Array HFun} (W : Walk L pre post t e cls fr k8 bk e₁ e₂ F₁ F₂ tl tl' funs)
    (A : Added8 tl tl' funs Y G F₁ F₂ fr k8 bk fr.length)
    (hsh : shapeOf Y.trees = shapeOf F.trees)
    (g : Forest.Heard) (hg : tl.heard = some g) (P : PubAt tl g)
    (hzR : ((F.trees.getD tl.ix.ZZ {}).rows.getD tl.zzRowReads {}).L0 = 0)
    (hzB : ∀ e, e ≤ 2 → ((F.trees.getD tl.ix.BZ {}).rows.getD e {}).L0 = 0)
    {Inv Inv₂ : S → Prop} (R : RunsKeep L pre post (FourRows tl) Inv Inv₂) (hI : Inv t) :
    tl'.joinObj9 = some fr.length ∧
      tl'.readWeightsHeld (coefBody tl' g G)
        (((coefBody tl' g G).trees.getD tl'.ix.ZZ {}).rows.getD (2 * tl.zzBlocks) {}).L = true ∧
      (tl'.planesShapeHeld (coefBody tl' g G) g = true →
        tl'.planesWeightsHeld (coefBody tl' g G) g fr.length = true) := by
  obtain ⟨q1, q2⟩ := others_of_walk W Inv Inv₂ (FourRows tl) R.pre R.k8 R.post hI
  have oR : ∀ c, OthersOff fr bk tl.ix.ZZ tl.zzRowReads c := fun c =>
    ⟨fun cl h => coefOn_off (q1 cl h).1 c, fun cl h => coefOn_off (q2 cl h).1 c⟩
  have oB : ∀ e, e ≤ 2 → ∀ c, OthersOff fr bk tl.ix.BZ e c := fun e he c =>
    ⟨fun cl h => coefOn_off ((q1 cl h).2 e he) c, fun cl h => coefOn_off ((q2 cl h).2 e he) c⟩
  obtain ⟨-, -, hjo, -⟩ := eq_join_bits A.eq
  have hB : tl.ix.BZ ≠ tl.ix.ZZ := fun c => ((apartB_iff tl).1 P.apart).1 c.symm
  refine ⟨hjo, ?_, fun hSh => ?_⟩
  · exact A.readEqs g tl.zzBlocks rfl P.ties P.tau P.rows P.cols (rows_zero hsh _ _ hzR)
      fun c _ => plainOff_reads A hg P.cEnd P.start P.pieces hB c (oR c)
  · exact (A.planeEqs g rfl hg hSh (fun e he => rows_zero hsh _ _ (hzB e he))
      (fun e _ => offAt_bits P.apart e)
      (fun y hy => by
        obtain ⟨z, hz, -⟩ := rowForm_ents _ _ y hy
        exact absurd hz (no_ent _ P.start z))
      fun e he c _ => planeOff_of A hg P.cEnd P.start P.pieces hB e c (oB e he c)).2

/-- **BOTH TESTS AT A PLAIN SEGMENT, BEHIND A YES OF THE BATCHING BLOCK.** -/
theorem both_at_link (L : Link S Claim) (i : Nat) (pre post : List (Nat × String))
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
    (Inv Inv₂ : S → Prop) (R : RunsKeep L pre post (FourRows tl) Inv Inv₂)
    (x : Cb.Gl.E) (hInv : ∀ t, drawnAt p s (chiAt x) = .ok t → Inv t)
    (hbt : batch s [⟨[], chiAt x⟩] = .ok t') :
    ∃ (tl' : HTailF2) (G : Fork) (jo : Nat), tlForkP.get? t' = some (tl', G) ∧
      tl'.joinObj9 = some jo ∧
      tl'.readWeightsHeld (coefBody tl' g G)
        (((coefBody tl' g G).trees.getD tl'.ix.ZZ {}).rows.getD (2 * tl.zzBlocks) {}).L = true ∧
      (tl'.planesShapeHeld (coefBody tl' g G) g = true →
        tl'.planesWeightsHeld (coefBody tl' g G) g jo = true) := by
  obtain ⟨t, e, e₁, e₂, cls, fr, k8, bk, tl', Y, G, F₁, F₂, hdr, -, W, -, hget, A, -, -, hsh⟩ :=
    open_at_link L i pre post hord Hpre Hpost tEq p batch s t' tl F funs hb ht hF hf x hbt
  exact ⟨tl', G, fr.length, hget, both_of_walk W A hsh g hg P hzR hzB R (hInv t hdr)⟩

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.offAt_bits
#print axioms VerifiableInference.Desc.First.K8.Honest.rows_zero
#print axioms VerifiableInference.Desc.First.K8.Honest.both_of_walk
#print axioms VerifiableInference.Desc.First.K8.Honest.both_at_link
