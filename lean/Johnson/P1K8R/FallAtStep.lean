-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P1K8R/FallAtStep.lean: THE SMALLNESS TEST: THE COUNT OF Johnson/P1K8R/UnitsAtBatch.lean AT
THE SEATED BATCHING BLOCK's STEP. Lemmas; none of the library's goals. No prover stands in them;
nothing on completeness, soundness or hiding.

A chain goes on by a block's step (Johnson/Desc/Block.lean: Block.step): a test on the rounds'
shape, a test on the columns, then the block's decision at the rounds without the sealed digest and
at the columns in groups. The counts of Johnson/Desc/K8/Honest/FallCount.lean stand at the decision,
at no columns and at the round that `chiAt` gives.
  `batch_reads`    the batching block's decision reads of its one round the drawn elements alone,
      and no column
  `seated_reads`   so does a block that seats it alone
  `step_chi`       a yes of such a block's step at a round that has drawn the one element x is a yes
      of its decision at `chiAt x` and no columns, with the same return
  **`fall_at_reached_step`**   in the goals' scope, at a feed-forward segment l, at every (z, s)
      reached at 14 l + 9: at most nU[2] * d field elements x are such that the seated batching
      block's step says yes at some round that has drawn x, and `selfUnits` says no at the state
      that the step returns
One way alone (from the step to the decision): a bound from above asks no more.
WHAT IS LEFT: Johnson/P1K8R/FallAtSeat.lean's list, but for its (a) and the first half of its (c).
That a challenge of the round's shape has drawn `Slice.ofE x` for just one x is not said: the test
on the rounds' shape asks the number of drawn elements, not that their words are reduced.

-/
import Johnson.P1K8R.UnitsAtBatch
import Johnson.Desc.Sound.RunIsDecide

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K8
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open OnBytes.Model.Stages (LinkH)
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.First.K8.Honest
open OnBytes.Tie.Pv.Tail.Port (topOf)
open Johnson.Desc.First.Walk.Tied (Reach)

/-- The batching block's decision reads of its round the drawn elements alone, and no column. -/
theorem batch_reads {T : Type} (X : K9.Lens T) (p : K9.Where)
    (g : T → Except String (List Claim × T)) (t : T) (r r' : Fmt.RoundView)
    (gs gs' : List (List (Nat × List UInt64))) (h : r.drawn.elems = r'.drawn.elems) :
    (K9.batch X p g).decide t [r] gs = (K9.batch X p g).decide t [r'] gs' := by
  have hc : K9.chiOf r = K9.chiOf r' := by
    unfold K9.chiOf
    rw [h]
  simp only [K9.batch, K9.drawAlone, hc]

/-- So does a block that seats it alone. -/
theorem seated_reads {same : S → S → Bool} {b : Block S Claim} {p : K9.Where}
    {g : S → Except String (List Claim × S)} {name : String} {a : Place}
    (hb : IM.LaidAlone same b (K9.batch K9.atS p g) name a) (hk : a.kind ≠ KindName.K7) (s t : S)
    (r r' : Fmt.RoundView) (gs gs' : List (List (Nat × List UInt64)))
    (h : r.drawn.elems = r'.drawn.elems) (hy : b.decide s [r] gs = .ok t) :
    b.decide s [r'] gs' = .ok t := by
  have h1 := (IM.yes_alone hb hk s t [r] gs).1 hy
  rw [batch_reads K9.atS p g s r r' gs gs' h] at h1
  exact (IM.yes_alone hb hk s t [r'] gs').2 h1

/-- A yes of the step at a round that has drawn x is a yes of the decision at `chiAt x`. -/
theorem step_chi {same : S → S → Bool} {b : Block S Claim} {p : K9.Where}
    {g : S → Except String (List Claim × S)} {name : String} {a : Place}
    (hb : IM.LaidAlone same b (K9.batch K9.atS p g) name a) (hk : a.kind ≠ KindName.K7) (ft : Nat)
    (s t : S) (r : Fmt.RoundView) (cols : List Desc.OpenedColumn) (k : Nat) (x : Cb.Gl.E)
    (hx : r.drawn.elems = [Slice.ofE x]) (hy : b.step ft s [r] cols = .ok (t, k)) :
    b.decide s [⟨[], chiAt x⟩] [] = .ok t := by
  have h4 := ((Sound.step_ok_iff ft b s t [r] cols k).1 hy).2.2.2
  exact seated_reads hb hk s t (noDigest r) ⟨[], chiAt x⟩ _ [] hx h4

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Claim)} {c : Chain S Claim}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **The count at the step.** -/
theorem fall_at_reached_step (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : ℕ} (hl : l < 25)
    (hsub : IM.subAt l = .layers) :
    ∃ (b : Block S Claim) (p : K9.Where) (X : LinkH),
      c.blocksInOrder[14 * l + 9]? = some b ∧ IM.k9At Z l = some p ∧ Bs.G₀.built.toList[l]? = some X ∧
      ∀ (z : ProofFile.InstPub) (s : S) (d : Nat), Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * l + 9) (z, s) →
        (∀ tl F funs, s.tl? = some tl → s.fork? = some F → s.funs? = some funs →
          F.planClaimsF + topOf tl funs ≤ d + 1) →
        Prob.cnt (fun x : Cb.Gl.E => ∃ (r : Fmt.RoundView) (cols : List Desc.OpenedColumn) (t : S) (k : Nat),
          r.drawn.elems = [Slice.ofE x] ∧ b.step 0 s [r] cols = .ok (t, k) ∧
            zeroUnitAt (ProofFile.k8NU Bs.G₀ X) t = true) ≤ (ProofFile.k8NU Bs.G₀ X).getD 2 0 * d := by
  obtain ⟨Lk, p, X, e1, e2, hX, hflat, hcount⟩ := fall_at_reached hS hR O hl hsub
  obtain ⟨Lk', p', w, T, e1', e2', -, -, -, -, hb, -⟩ := (IM.k9_of hS hR O).2 l hl
  obtain rfl : Lk = Lk' := Option.some.inj (e1.symm.trans e1')
  obtain rfl : p = p' := Option.some.inj (e2.symm.trans e2')
  have k9ne : KindName.K9 ≠ KindName.K7 := by decide
  refine ⟨_, p, X, hflat, e2, hX, fun z s d hr hd => ?_⟩
  refine (Prob.cnt_mono fun x hx => ?_).trans (hcount z s d hr hd)
  obtain ⟨r, cols, t, k, hel, hst, hz⟩ := hx
  have hdec := step_chi (hb (claimsInBy Lk.each Lk.hear Lk.order)) k9ne 0 s t r cols k x hel hst
  unfold askBehind
  simp only [List.map_cons, List.map_nil]
  rw [hdec]
  exact hz

end

end P1K8

#print axioms P1K8.batch_reads
#print axioms P1K8.seated_reads
#print axioms P1K8.step_chi
#print axioms P1K8.fall_at_reached_step
