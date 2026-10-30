-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/FourAtLink.lean: THE SMALLNESS TEST: AT A PLAIN SEGMENT, BEHIND A YES OF THE
BATCHING BLOCK AT A CHALLENGE x, FOUR OF THE VERIFIER's TESTS ON WHAT THE ADDING HAS LEFT SAY YES:
on the reads' weights, the reads' shapes, the planes' shapes and the planes' weights.
`three_of_walk` (Johnson/Desc/K8/Honest/BitsFilled.lean) with the test on the reads' shapes beside
it (`Added8.readShape_run`, Johnson/Desc/K8/Honest/EqTailGuard.lean); the size of the reads' row's
weights comes, as the bits' rows' do, from what the batching's draw fills (`full_of_fill`,
BitsFilled.lean). None of the library's goals.

  **`four_of_walk`**   three_of_walk's premises · in the ledger in front the digits' array has 2 mz
                   columns and has the reads' row ⊢ tl'.joinObj9 = some ‹the number of the claims in
                   front› · readWeightsHeld · readShapeHeld · planesShapeHeld · planesWeightsHeld:
                   all four say yes
  `FourHeld tl g t'`   the state t' shows data tl', a ledger G and a number jo with: tl'.joinObj9 =
                   some jo · readWeightsHeld · readShapeHeld · planesShapeHeld · planesWeightsHeld
                   at jo
  **`fourHeld_at_link`**   FourHeld tl g t' behind a yes of the batching block at a plain segment:
                   one call of `filled_at_link` (BitsFilled.lean) and one of the above
Limits. IMPLICATIONS. PAID BY NOBODY HERE: all that `three_at_link` leaves, and the two numbers of
the digits' array in front. The reads' row is named by the plan's number of blocks (2 *
tl.zzBlocks), not by the number that the test computes again. At one challenge x. No prover stands
in it.
Nothing is claimed on completeness, soundness or hiding.

-/
import Johnson.Desc.K8.Honest.BitsFilled
import Johnson.Desc.K8.Honest.EqTailGuard

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open VerifiableInference.Desc VerifiableInference.Desc.First.TailClaims
open VerifiableInference.Desc.First.TailClaims.Law
open OnBytes.Tie.Pv.Tail.Port

/-- The state t' shows data, a ledger and a number at which the four tests say yes. -/
def FourHeld (tl : HTailF2) (g : Forest.Heard) (t' : S) : Prop :=
  ∃ (tl' : HTailF2) (G : Fork) (jo : Nat), tlForkP.get? t' = some (tl', G) ∧
    tl'.joinObj9 = some jo ∧
    tl'.readWeightsHeld (coefBody tl' g G)
      (((coefBody tl' g G).trees.getD tl'.ix.ZZ {}).rows.getD (2 * tl.zzBlocks) {}).L = true ∧
    tl'.readShapeHeld
      (((coefBody tl' g G).trees.getD tl'.ix.ZZ {}).rows.getD (2 * tl.zzBlocks) {}).L = true ∧
    tl'.planesShapeHeld (coefBody tl' g G) g = true ∧
    tl'.planesWeightsHeld (coefBody tl' g G) g jo = true

/-- **FOUR TESTS, ALONG THE RUNS' OWN CUT.** -/
theorem four_of_walk {L : Link S Claim} {pre post : List (Nat × String)} {t e : S}
    {cls fr k8 bk : List Claim} {e₁ e₂ : S} {F₁ F₂ Y G F : Fork} {tl tl' : HTailF2}
    {funs : Array HFun} (W : Walk L pre post t e cls fr k8 bk e₁ e₂ F₁ F₂ tl tl' funs)
    (A : Added8 tl tl' funs Y G F₁ F₂ fr k8 bk fr.length) (T : Tail2)
    (hYt : Y.trees = (t2FillL F T).trees) (hT : T.nt.size = F.trees.size)
    (g : Forest.Heard) (hg : tl.heard = some g) (P : PubAt tl g)
    (hzR : ((F.trees.getD tl.ix.ZZ {}).rows.getD tl.zzRowReads {}).L0 = 0)
    (hzB : ∀ e, e ≤ 2 → ((F.trees.getD tl.ix.BZ {}).rows.getD e {}).L0 = 0)
    (B : BitsFront tl F) (Pb : BitsPub tl g)
    (hKz : (F.trees.getD tl.ix.ZZ {}).K = 2 * tl.mz)
    (hRz : tl.zzRowReads < (F.trees.getD tl.ix.ZZ {}).rows.size)
    {Inv Inv₂ : S → Prop} (R : RunsKeep L pre post (FourRows tl) Inv Inv₂) (hI : Inv t) :
    tl'.joinObj9 = some fr.length ∧
      tl'.readWeightsHeld (coefBody tl' g G)
        (((coefBody tl' g G).trees.getD tl'.ix.ZZ {}).rows.getD (2 * tl.zzBlocks) {}).L = true ∧
      tl'.readShapeHeld
        (((coefBody tl' g G).trees.getD tl'.ix.ZZ {}).rows.getD (2 * tl.zzBlocks) {}).L = true ∧
      tl'.planesShapeHeld (coefBody tl' g G) g = true ∧
      tl'.planesWeightsHeld (coefBody tl' g G) g fr.length = true := by
  obtain ⟨h2, h3, h4, h5⟩ := three_of_walk W A T hYt hT g hg P hzR hzB B Pb R hI
  have hZ : tl.ix.ZZ < T.nt.size := by
    rw [hT]
    exact (hasRow_of_rows rfl hRz).1
  exact ⟨h2, h3, A.readShape_run g tl.zzBlocks rfl P.cols ((full_of_fill T hZ hRz hYt).trans hKz),
    h4, h5⟩

/-- **FOUR TESTS AT A PLAIN SEGMENT, BEHIND A YES OF THE BATCHING BLOCK.** -/
theorem fourHeld_at_link (L : Link S Claim) (i : Nat) (pre post : List (Nat × String))
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
    (hT : ∀ a0, K9.atS.get? s = some a0 → a0.L.list.nt.size = F.trees.size)
    (hKz : (F.trees.getD tl.ix.ZZ {}).K = 2 * tl.mz)
    (hRz : tl.zzRowReads < (F.trees.getD tl.ix.ZZ {}).rows.size)
    (Inv Inv₂ : S → Prop) (R : RunsKeep L pre post (FourRows tl) Inv Inv₂)
    (x : Cb.Gl.E) (hInv : ∀ t, drawnAt p s (chiAt x) = .ok t → Inv t)
    (hbt : batch s [⟨[], chiAt x⟩] = .ok t') : FourHeld tl g t' := by
  obtain ⟨a0, t, e, e₁, e₂, cls, fr, k8, bk, tl', Y, G, F₁, F₂, ha0, hdr, W, hget, A, hYt⟩ :=
    filled_at_link L i pre post hord Hpre Hpost tEq p batch s t' tl F funs hb ht hF hf x hbt
  exact ⟨tl', G, fr.length, hget, four_of_walk W A a0.L.list hYt (hT a0 ha0) g hg P hzR hzB B
    Pb hKz hRz R (hInv t hdr)⟩

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.four_of_walk
#print axioms VerifiableInference.Desc.First.K8.Honest.fourHeld_at_link
