-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K8/TailValues.lean: the smallness test's named tests on values behind the batching (the run
"K8.tests", called at the member behind the batching, number 14 l + 10, or 348 at the head): where
the kind's share of these tests is silent, at a state that the wrapped blocks reach, they pass.

The seven tests of the share ask "not 0" or "all different" of weights, and they hang on the drawn
element: their silence is a fall's. The other five (the kept slots, the points, the rows' powers, the
planes' weights, the reads' weights) are shown here of every such state.

  hasRow_of_looks, hasRow_of_size, wants_first, piece_first, k8Rest_of_held
                    from what holds behind the batching to every guard beside the share (K8Rest)
  BehindHeld        what holds behind a yes of the batching block
  held_lay, held_att, held_head   that, at a segment of each sort, at a reached state
  k8_rest_behind    K8Rest at the state behind the run "K8.lsTail"
  k8_valsS_behind   the named tests accept there

Limits. The head's laws are premises in their letters: the scope, the files read, the opening, the
description's test on its plan. The silence of the share is a premise: it is a fall's.
-/
import Johnson.Desc.ProofFile.Honest.K8.AsksAtWrap
import Johnson.Desc.ProofFile.Honest.K8.AllAtSorts
import Johnson.Desc.ProofFile.Honest.K8.RestLaid
import Johnson.Desc.ProofFile.Honest.K8.ShareLaid
import Johnson.Desc.ProofFile.Honest.K8.TestsSplit
import Johnson.Desc.ProofFile.Honest.K9.AtSeatAll
import Johnson.Desc.ProofFile.Honest.K9.FromYes
import Johnson.Desc.K8.Honest.AllFrontAtAll
import Johnson.Desc.K8.Honest.Lists.ListAtBatch
import Johnson.Desc.K8.Honest.SlotAtReach
import Johnson.Desc.K8.Honest.SlotAtHeadSeg
import Johnson.Desc.K8.Honest.TieWords
import Johnson.Desc.K8.Honest.AddTheta
import Johnson.Desc.K8.Honest.RestPowers
import Johnson.Desc.First.Batch.Law.K8Tests
import Johnson.Desc.First.Link.Law.FullFour
import Johnson.Desc.First.Link.Law.FunsAtBatch
import Johnson.Desc.First.Link.Law.AttSkelAtBatch
import Johnson.Desc.First.Link.Law.HeadSkel
import Johnson.Desc.First.TailClaims.TestsCut
import Johnson.Desc.First.TailClaims.TestsChain
import Johnson.Desc.First.TailClaims.BehindSeat
import Johnson.P1K8R.StepOut
import Johnson.P1K8R.StaticAtBatch
import Johnson.P1K8R.StaticAtBuilt
import Johnson.LPFK9R.TiesWholeAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.K8.Term
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open OnBytes.Model.Stages (LinkH)
open Fo (HasRow)
open OnBytes.Tie.Pv.Tail.Port (Powered)
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.First.TailClaims
open VerifiableInference.Desc.First.TailClaims.Law (blank partOf eq_blank)
open VerifiableInference.Desc.First.TailClaims.Law.Tests
open VerifiableInference.Desc.First.K8.Honest
open VerifiableInference.Desc.K9L (coef_looks)
open ProofFile.Honest.K8 (K8Rest k8Share share_at tests_of_share size_laid allHeld_at_layers allHeld_at_att
  allHeld_at_head layAsks_at_wrap attAsks_at_wrap headWants_at_wrap)
open ProofFile.Honest.K9 (SeatedFree BatBehind free_at_seat_all behind_of_step batch_join drawnOne)
open Johnson.Desc.First.Walk.Tied (Reach reach_raw)
open _root_.P1K8

/-- A ledger whose arrays have another's looks has its virtual rows. -/
theorem hasRow_of_looks {F G : Fork} (h : G.trees.map LinkJoin.look = F.trees.map LinkJoin.look)
    {t e : Nat} (hr : HasRow F t e) : HasRow G t e := by
  obtain ⟨h1, h2⟩ := hr
  have hs : G.trees.size = F.trees.size := by simpa using congrArg Array.size h
  have ht : t < G.trees.size := hs ▸ h1
  have he : LinkJoin.look G.trees[t] = LinkJoin.look F.trees[t] := by
    have h3 := congrArg (fun A => A[t]?) h
    simpa [ht, h1] using h3
  have e1 : G.trees.getD t {} = G.trees[t] := by simp [Array.getD, ht]
  have e2 : F.trees.getD t {} = F.trees[t] := by simp [Array.getD, h1]
  refine ⟨ht, ?_⟩
  rw [e1]
  rw [e2] at h2
  have e3 : (G.trees[t]).rows.size = (F.trees[t]).rows.size := congrArg (·.2.2.2) he
  omega

/-- An array that has n + 1 virtual rows in a ledger is there, with each row up to n. -/
theorem hasRow_of_size {F : Fork} {t n e : Nat} (h : (F.trees.getD t {}).rows.size = n + 1)
    (he : e ≤ n) : HasRow F t e := by
  refine ⟨?_, by omega⟩
  by_contra hc
  have e0 : F.trees.getD t {} = {} := by simp [Array.getD, hc]
  rw [e0] at h
  exact absurd h (by simp)

/-- The second computation wants at least one block, and first a piece of call 0, number 0, at
virtual row 0. -/
theorem wants_first {tl : HTailF2} {nbW : Nat} {W : List Want} (h : tl.wants = some (nbW, W)) :
    0 < nbW ∧ ∃ w ∈ W, w.call = 0 ∧ w.i = 0 ∧ w.row = 0 := by
  unfold HTailF2.wants at h
  simp only at h
  split at h
  · cases h
  · obtain ⟨e1, e2⟩ := Prod.mk.inj (Option.some.inj h)
    subst e1 e2
    refine ⟨by split <;> omega, _, List.mem_flatMap.2 ⟨0, by simp, List.mem_cons_self⟩, rfl, rfl,
      Nat.zero_mul _⟩

/-- Where the first shapes hold and the pieces tile, a piece sits in the digits' array at virtual
row 0. -/
theorem piece_first {tl : HTailF2} {g : Forest.Heard} {G : Fork} {nbW : Nat} {W : List Want}
    (hW : tl.wants = some (nbW, W)) (hc : tl.callHeld g nbW 0 = true)
    (r5 : tl.piecesTile G W = true) :
    ∃ a ∈ Fo.allPieces tl, a.2.tree = tl.ix.ZZ ∧ a.2.row = 0 := by
  obtain ⟨hpos, w, hw, c0, i0, w0⟩ := wants_first hW
  have hsz : (tl.zOf 0).pieces.size = nbW := by
    simp only [HTailF2.callHeld, Bool.and_eq_true, beq_iff_eq] at hc
    exact hc.1.1.1.1.1.1.1.2
  have h0 : 0 < (tl.zOf 0).pieces.size := by omega
  simp only [HTailF2.piecesTile, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at r5
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := r5.2 w hw
  rw [c0, i0] at h1 h2
  rw [w0] at h2
  refine ⟨(0, (tl.zOf 0).pieces.getD 0 {}), ?_, h1, h2⟩
  unfold Fo.allPieces
  refine List.mem_append_left _ (List.mem_map.2 ⟨_, ?_, rfl⟩)
  have e0 : (tl.zOf 0).pieces.getD 0 {} = (tl.zOf 0).pieces[0] := by simp [Array.getD, h0]
  rw [e0]
  exact Array.mem_toList_iff.2 (Array.getElem_mem h0)

/-- **Every guard of the three tests beside the share**, from what holds behind the batching. -/
theorem k8Rest_of_held {nU : Array Nat} {tl : HTailF2} {F : Fork}
    (hls : tl.lsTail = F.LS.extract tl.slotA tl.slotB) (hin : tl.slotB ≤ F.LS.size)
    (hw : tl.wants.map (·.1) = some tl.zzBlocks) (hP : Powered tl F.theta) {Fs : Fork}
    (hC : Fo.CoefOK tl Fs) (r1 : (nU == tl.nUF) = true) (hV : AllHeld tl F) :
    K8Rest nU tl F := by
  obtain ⟨g, jo, nbW, W, hg, hjo, hW, r4, r5, r6, r7, r9, r10, r11⟩ := hV
  have hn : nbW = tl.zzBlocks := by
    rw [hW] at hw
    exact Option.some.inj hw
  have hz : ((coefBody tl g F).trees.getD tl.ix.ZZ {}).rows.size = (2 * nbW + 1) + 1 := by
    have h4 := r4
    simp only [Bool.and_eq_true, beq_iff_eq] at h4
    exact h4.1.1
  have hc0 : tl.callHeld g nbW 0 = true := by
    have h4 := r4
    simp only [Bool.and_eq_true, List.all_eq_true] at h4
    exact h4.2 0 (by simp)
  obtain ⟨a0, ha0, at0, ar0⟩ := piece_first hW hc0 r5
  obtain ⟨-, -, -, pB, pm⟩ := hC.piece a0 ha0
  have hB : tl.ix.BZ ≠ tl.ix.ZZ := by
    rw [← at0]
    exact pB
  have hm : ∀ mu, mu < tl.NM → tl.gtTree.getD mu 0 ≠ tl.ix.ZZ := fun mu hmu e =>
    pm mu hmu ⟨e.trans at0.symm, ar0.symm⟩
  have hl := (coef_looks tl g F).symm
  have hR : HasRow F tl.ix.ZZ tl.zzRowReads := by
    refine hasRow_of_looks hl (hasRow_of_size hz ?_)
    unfold HTailF2.zzRowReads
    omega
  have hT : HasRow F tl.ix.ZZ tl.zzRowTies := by
    refine hasRow_of_looks hl (hasRow_of_size hz ?_)
    unfold HTailF2.zzRowTies
    omega
  have s2 : (tl.lsTail.size == tl.slotB - tl.slotA) = true := by
    rw [hls]
    exact size_laid tl F hin
  have s3 : selfSlots tl F = true := by
    unfold selfSlots
    rw [hls]
    exact beq_self_eq_true _
  have s7 := rest_sizes tl g F nbW hP hR hT hB hm hn
  have s8 := rest_powers tl g F nbW hP hR hT hB hm hn
  refine ⟨r1, s2, s3, g, jo, nbW, W, hg, hjo, hW, r4, r5, r6, ?_, s8, r9, r10, r11⟩
  simp only [Bool.and_eq_true] at s7 r7 ⊢
  obtain ⟨⟨⟨⟨⟨c3, c4⟩, c5⟩, c6⟩, c7⟩, c8⟩ := r7
  exact ⟨⟨⟨⟨⟨⟨⟨s7.1, s7.2⟩, c3⟩, c4⟩, c5⟩, c6⟩, c7⟩, c8⟩

/-- What holds behind a yes of the batching block: the data tl' and the ledger G of the state t'
hold every clause of AllHeld and the powers of the batching element; tl' differs from the data tl
in front in the fourteen fields that the run "K8.equations" writes alone. -/
def BehindHeld (tl : HTailF2) (t' : S) : Prop :=
  ∃ (tl' : HTailF2) (G : Fork), tlForkP.get? t' = some (tl', G) ∧ AllHeld tl' G ∧
    Powered tl' G.theta ∧ ∀ u, blank u tl' = blank u tl

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Claim)} {c : Chain S Claim}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- From the filling behind the yes: AllHeld at the same pair gives the whole. -/
theorem behindHeld_of {L : Link S Claim} {i : Nat} {pre post : List (Nat × String)}
    (hord : L.order = pre ++ (i, "K8.equations") :: post) (Hpre : PreOk L pre)
    (Hpost : PostOk L post)
    (tEq : ∀ run, LinkJoin.At L (i, "K8.equations") run → LinkJoin.Under run K9L.k8Run.2)
    (p : K9.Where) (s t' : S) (tl : HTailF2) (F₀ : Fork) (funs : Array HFun)
    (ht : s.tl? = some tl) (hF : s.fork? = some F₀) (hf : s.funs? = some funs) (d : Fmt.Drawn)
    (hbt : (K9.batch K9.atS p (claimsInBy L.each L.hear L.order)).decide s [⟨[], d⟩] [] = .ok t')
    (hA : ∃ (tl' : HTailF2) (G : Fork), tlForkP.get? t' = some (tl', G) ∧ AllHeld tl' G) :
    BehindHeld tl t' := by
  obtain ⟨a0, t, e, e₁, e₂, cls, fr, k8, bk, tl', Y, G, F₁, F₂, -, -, -, hget, Ad, -⟩ :=
    filled_at_drawn L i pre post hord Hpre Hpost tEq p
      (fun u rs => (K9.batch K9.atS p (claimsInBy L.each L.hear L.order)).decide u rs []) s t' tl F₀
      funs (fun _ _ h => h) ht hF hf d hbt
  obtain ⟨tl'', G', hget', hH⟩ := hA
  obtain ⟨e1, e2⟩ := Prod.mk.inj (Option.some.inj (hget.symm.trans hget'))
  subst e1 e2
  refine ⟨_, _, hget, hH, ?_, fun u => eq_blank u Ad.eq⟩
  rw [addList_theta _ _ _ Ad.add]
  exact Ad.powered

end

end AtFullSide.K8.Term

#print axioms AtFullSide.K8.Term.hasRow_of_looks
#print axioms AtFullSide.K8.Term.hasRow_of_size
#print axioms AtFullSide.K8.Term.wants_first
#print axioms AtFullSide.K8.Term.piece_first
#print axioms AtFullSide.K8.Term.k8Rest_of_held
#print axioms AtFullSide.K8.Term.behindHeld_of
