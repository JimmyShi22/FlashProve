-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K8R/HeadListAtBatch.lean: the proofs of the two statements of
Johnson/P1K8R/HeadListAtBatchStatement.lean, to the letter, and four helpers. Lemmas; none of the
library's goals.

How. `head_lays`: a yes of the head's quiet step, by `head_ok` and `closed_fields`
(Johnson/Desc/K8/ReadsQuietLaws.lean): BY `head_ok`, NOT BY THE SHORTER `head_lays_tl`
(Johnson/Desc/First/K8/LawCondText.lean), SO THAT "a.x = some x" IS CARRIED. `reads_lays`: a yes of
the block of the reads' place (`IM.k1Reads`, Johnson/IMR/K1Seat.lean) at a built segment of kind 2:
`Meaning.K2.andThen_yes` (Johnson/IMR/FoldTools.lean), `quiet_arms`
(Johnson/Desc/First/K8/LawCondK1.lean), whose arms of the kinds 1 and 0 are shut by the kind.
`block_342`: number 342 of the flat list is such a block: found as `k1_head_keeps` finds it
(Johnson/K11R/LeavesAt346.lean); the kind by `IM.ground_named` (Johnson/IMR/PureJoin.lean).
`wide_back`: one step back along "reached" over an entry that leaves the reading `wide`
(Johnson/Desc/First/K8/LawWide.lean). The statement at 347: four such steps, by `P1K8S.staysAt_open`
(Johnson/P1K8R/WideAtSeat.lean) at the head's stretch (24, 5, 3); then the equation of the two
readings is taken apart.

NEAR. `reads_lays` IS THE LIBRARY's `joined_makes_head` (LawCondK1.lean) WITH `head_lays` FOR
`head_makes`. `P1K8S.wide_stays` (Johnson/P1K8R/WideToRun.lean) says of a fold over these four
entries what the four steps say along "reached".

Limits. Those of the statements. Nothing on any property.
-/
import Johnson.P1K8R.HeadListAtBatchStatement
import Johnson.P1K8R.WideAtSeat
import Johnson.K11R.LeavesAt346
import Johnson.Desc.First.K8.LawCondK1
import Johnson.Desc.K8.ReadsQuietLaws
import Johnson.IMR.PureJoin
import Johnson.IMR.FoldTools

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K8
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Chain FileDescription KindName)
open VerifiableInference.Desc.First (S kindsBeforeBatching)
open VerifiableInference.Desc.First.K8 (wide wideOf readTl keeps4_wideOf)
open VerifiableInference.Desc.First.MergeLaw (alone_decides retype_decides flat_at reach_pred)
open VerifiableInference.Desc.Keeps (Decides)
open VerifiableInference.Desc.K8 (ReadsQuiet.head ReadsQuiet.PH)
open Johnson.Desc.First.Walk.Tied (Reach stepYes_decide)

/-- A yes of the head's quiet step lays the closed list. -/
theorem head_lays (W : Verify.Public) (a : VerifiableInference.Desc.Place) {s s' : S}
    {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (h : (ReadsQuiet.head ⟨a, W.hS, W.HLy, W.H⟩).decide s rs gs = .ok s') :
    ∃ x t, HeadListLaid W s' x t := by
  obtain ⟨a₀, cov, x, t, tl', -, ho, -, hx, ht, hc, e⟩ :=
    VerifiableInference.Desc.K8.ReadsQuiet.head_ok h
  obtain ⟨c1, c2, c3, c4, -⟩ := VerifiableInference.Desc.K8.ReadsQuiet.closed_fields hc
  refine ⟨x, t, ⟨{ a₀ with t := some t, tl := tl' }, ?_, hx⟩, ⟨cov, ht⟩, tl', ?_, c1, c2, c4, c3⟩
  · rw [e]
  · rw [e]
    show (if a₀.opened then some tl' else none) = some tl'
    rw [ho]
    rfl

/-- A yes of the block of the reads' place, at a built segment of kind 2. -/
theorem reads_lays (Z : ProofFile.Pub) (G : ProofFile.Ground) (l : ℕ) (X : Stages.LinkH) (pr : ℕ)
    (reads : Option (List ℕ)) (hX : G.built[l]? = some X) (h2 : X.kind = 2) :
    Decides (fun _ s' => ∃ x t, HeadListLaid G.W s' x t) (IM.k1Reads Z G l X pr reads) := by
  intro s rs gs s' h
  obtain ⟨m, -, H⟩ := _root_.Meaning.K2.andThen_yes h
  rcases VerifiableInference.Desc.First.K8.Ready.quiet_arms G l X _ _ _ _ H with
    ⟨h1, -⟩ | ⟨-, Y, hY, hL | hH⟩
  · omega
  · obtain rfl : X = Y := Option.some.inj (hX.symm.trans hY)
    have := hL.1
    omega
  · exact head_lays G.W _ hH.2

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)} {c : Chain S ProofFile.Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- Number 342 of the flat list is such a block. -/
theorem block_342 (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) :
    ∃ b, c.blocksInOrder[342]? = some b ∧
      Decides (fun _ s' => ∃ x t, HeadListLaid Bs.G₀.W s' x t) b := by
  have hk : (kindsBeforeBatching .head (24 == 0))[4]? = some KindName.K1 := by
    unfold kindsBeforeBatching
    rfl
  obtain ⟨Lk, b, Xl, pr, pd, reads, digits, eL, e, eX, hn, harm⟩ :=
    IM.k1_later O 24 .head (IM.subs_head hS hR O.pub O.blank) 4 hk (by decide)
  obtain ⟨-, Y, eY, h2, -⟩ := IM.ground_named hS hR O.pub O.blank
  obtain rfl : Xl = Y := Option.some.inj (eX.symm.trans eY)
  have hp := IM.numbers_pieces hn
  refine ⟨b, flat_at hS hR O eL e rfl, ?_⟩
  rcases harm with ⟨-, la⟩ | ⟨h5, -⟩
  · exact alone_decides (by intro k; cases k) la
      (retype_decides (reads_lays Z Bs.G₀ 24 Xl pr reads eX h2))
  · omega

/-- One step back along "reached", over an entry that leaves the reading `wide`. -/
theorem wide_back {Q : Type} {start : Q → S} {k : ℕ} {z : Q} {s' : S}
    (h : Reach 0 c.blocksInOrder start (k + 1) (z, s'))
    (L : ∀ b, c.blocksInOrder[k]? = some b → b.Leaves wide) :
    ∃ s, Reach 0 c.blocksInOrder start k (z, s) ∧ wide s' = wide s := by
  obtain ⟨s, b, hr, hb, hy⟩ := reach_pred h k rfl
  obtain ⟨rs, gs, hd⟩ := stepYes_decide hy
  exact ⟨s, hr, L b hb s rs gs s' hd⟩

end

/-- **At 343 the closed list is laid.** -/
theorem headList_at_343 : HeadListAt343 := by
  intro P pp lay F Z Bs base c A B hS hR O Q start z s h
  obtain ⟨s₀, b, -, hb, hy⟩ := reach_pred h 342 rfl
  obtain ⟨rs, gs, hd⟩ := stepYes_decide hy
  obtain ⟨b', hb', D⟩ := block_342 hS hR O
  obtain rfl : b = b' := Option.some.inj (hb.symm.trans hb')
  exact D s₀ rs gs s hd

/-- **At 347 it is still that list.** -/
theorem headList_at_347 : HeadListAt347 := by
  intro P pp lay F Z Bs base c A B hS hR O Q start z s' h
  obtain ⟨T0, T1⟩ := P1K8S.staysAt_open hS hR O (24, 5, 3) (by decide)
  have L : ∀ j, j < 3 → ∀ b, c.blocksInOrder[344 + j]? = some b → b.Leaves wide := fun j hj b hb =>
    T1 j hj b hb _ wideOf keeps4_wideOf
  obtain ⟨s3, h3, e3⟩ := wide_back (k := 346) h (L 2 (by omega))
  obtain ⟨s2, h2, e2⟩ := wide_back (k := 345) h3 (L 1 (by omega))
  obtain ⟨s1, h1, e1⟩ := wide_back (k := 344) h2 (L 0 (by omega))
  obtain ⟨s, h0, e0⟩ := wide_back (k := 343) h1 T0
  obtain ⟨x, t, hL⟩ := headList_at_343 P pp lay F Z Bs base c A B hS hR O Q start z s h0
  obtain ⟨-, -, tl, etl, c1, c2, c3, c4⟩ := id hL
  have ew : wide s' = some (wideOf tl) := by
    rw [e3, e2, e1, e0]
    show s.tl?.map wideOf = some (wideOf tl)
    rw [etl]
    rfl
  obtain ⟨tl', etl', ee⟩ := Option.map_eq_some_iff.1 ew
  have q1 : tl'.funs = tl.funs := congrArg (fun y => y.2.2.2) ee
  have q2 : tl'.funClosed = tl.funClosed := congrArg (fun y => y.2.2.1) ee
  have q3 : tl'.mats = tl.mats := congrArg (fun y => y.1.2.2.2.2.2.2) ee
  have q4 : tl'.NM = tl.NM := congrArg (fun y => y.1.2.2.2.2.1) ee
  exact ⟨s, x, t, h0, hL, tl', etl', q2.trans c1, q1.trans c2, q3.trans c3, q4.trans c4⟩

end P1K8

-- Each line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms P1K8.head_lays
#print axioms P1K8.reads_lays
#print axioms P1K8.block_342
#print axioms P1K8.wide_back
#print axioms P1K8.headList_at_343
#print axioms P1K8.headList_at_347
