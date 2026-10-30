-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K13/PileAtFlat.lean: WHO WRITES THE ROWS ON THE TABLE ON THE FIRST
CHAIN OF THE PROOF FILE's IOP AS WRITTEN IN LEAN, IN FRONT OF K13's BATCHING: THE WALK. One
definition, and statements with their proofs. It stands on the library alone.

What it is for. Johnson/Desc/K13/Honest/PileInduction.lean shows the law on the pile's filler from
twelve premises on a chain's sub-protocols. Three of them (`quiet`, `clears`, `atEnd`) are met at
the library's own chain, at the reading rd := `S.rows` (Johnson/Desc/First/State.lean), the first
two under a premise on the plan, in ClearedBySort.lean, PileWalkAtFlat.lean and PileWalkAtDesc.lean
of this folder. Here is the one walk over the chain that they spend, and the laws on the function
"cleared".
THE LIBRARY HAS THE WALK. `IM.flat_cases` (Johnson/IMR/FlatCases.lean): each of the 358
sub-protocols has one of ten forms, by its number. Johnson/LPFK9R/PileByPlace.lean walks these forms
for a SENTENCE on one state that rides over every decision (`flat_rides`). Here the same walk is
made ONCE for a RELATION, form by form, by the same lemmas of the library: `lot_pile`,
`hear_noframe` (PileByPlace.lean), `hear_runs_stays` (LPFK9R/RoomRuns.lean), `layFront_pile`,
`openAtt_pile`, `openLay_pile`, `openLayZero_rows`, `closeOf_pile`, `batch_over`
(Johnson/Desc/First/Pile/PileSeated.lean), `link_claims_runs`, `link_behind_runs`, `IM.yes_alone`,
`IM.yes_alone_K7`, `IM.frames_arms` (Johnson/IMR/FrameSeat.lean), `clearWith_ok`, `clearWith_eq`
(Johnson/Top/H0/Walk/FrameLaw.lean). Kin: `clearWith_cases` (PileSeated.lean: the same two cases as
one "or", without what is left), `cleared_lays` (Johnson/Top/H0/Walk/FrameRow.lean: the same of the
field `out.pending`), `LPFK9.flat_rows` (PileByPlace.lean: the rows stay at the numbers 0 and 1).
Main names:
  `StaysBack s t`: the relation: the rows on the table are as they were; the state behind stands at
    the chain's end only if the state in front did: the first and the third clause of the library's
    `PileStays` (Johnson/Desc/First/Pile/PileMakers.lean). `StaysBack.of_pile`, `StaysBack.trans`.
  `flat_stays`: **In the goals' scope (`VerifierAndGoals.InScope`, `VerifierAndGoals.readFiles`), under the opening of
    the proof file's IOP (`IM.Open`: its letters Z, Bs, c are what is public, the blank ground's
    holder, the first chain): every decision of a sub-protocol of a number below 355 that is none of
    the 25 numbers 14 l + `IM.nAt` l + 7 has `StaysBack`.**
  `clearWith_rows`, `clearWith_rows_none`, `clearWith_notAtEnd`: the function "cleared": where the
    segment's public data say that it leaves a row, the verifier's own row of what the reader reads
    off the state in front (`rowBy`) is laid at the rows' end; else the rows stay; the state behind
    does not stand at the chain's end. `opened_stays`: the function "opened" has `StaysBack`.

What is not claimed. Which segments leave a row. Nothing on the numbers from 355 on. Nothing on
soundness, completeness or hiding.

-/
import Johnson.LPFK9R.RoomRuns
import Johnson.Top.H0.Walk.FrameRow

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K13

open OnBytes OnBytes.Model
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open VerifiableInference.Desc.First.Pend (pendingRowO)
open VerifiableInference.Desc.First.Close (leftHead)
open VerifiableInference.Desc.Keeps (Whole Decides Fn FnCl)
open ProofFile (Cl Lot Ground)
open Johnson.Desc.First.Walk
open Johnson.Desc.First.Walk.Law (rowBy rowBy_some)
open Johnson.Desc.First.Walk.Seat (LinkFrame framesOf frameAt zeroAt pubOf rowOf)
open Meaning.K2
open LPFK9 (lot_pile hear_noframe hear_runs_stays)

/-! ## "cleared" and "opened", on the rows on the table -/

/-- Where the segment's public data say that it leaves a row: the verifier's own row of what is left
is laid at the end of the rows on the table. -/
theorem clearWith_rows {X : LinkPub} {counts : S → Except String Unit}
    {left : S → Option WsForkOut} {lay : WsLay} {lin : Params.LinShape} {s t : S}
    (h : clearWith X counts left (fun im w n os => pendingRowO lay im w n lin os) s = .ok t)
    (hv : X.fv = true) :
    ∃ r, rowBy left lay X.NCL lin s = some r ∧ t.rows = s.rows ++ [r] := by
  obtain ⟨C, F, hC, -⟩ := Law.clearWith_ok h
  have hn := not_mem_of_link hC
  obtain ⟨w, r, os, hw, hr, ht⟩ := (Law.clearWith_eq h).2 hv
  have hn' : ∀ a, t.here ≠ .mem a := by
    rw [ht]
    exact fun _ k => nomatch k
  refine ⟨r, rowBy_some.2 ⟨w, os, hw, hr⟩, ?_⟩
  rw [rows_of_not_mem hn', rows_of_not_mem hn, ht]
  rfl

/-- Where they say that it leaves none: the rows stay. -/
theorem clearWith_rows_none {X : LinkPub} {counts : S → Except String Unit}
    {left : S → Option WsForkOut} {row : RowFn} {s t : S}
    (h : clearWith X counts left row s = .ok t) (hv : X.fv = false) : t.rows = s.rows := by
  obtain ⟨C, F, hC, -⟩ := Law.clearWith_ok h
  have hn := not_mem_of_link hC
  have e := (Law.clearWith_eq h).1 hv
  have hn' : ∀ a, t.here ≠ .mem a := by
    rw [e]
    exact fun _ k => nomatch k
  rw [rows_of_not_mem hn', rows_of_not_mem hn, e]

/-- "cleared" leaves a state that does not stand at the chain's end. -/
theorem clearWith_notAtEnd {X : LinkPub} {counts : S → Except String Unit}
    {left : S → Option WsForkOut} {row : RowFn} {s t : S}
    (h : clearWith X counts left row s = .ok t) : ∀ a, t.here ≠ .mem a := by
  obtain ⟨_, _, _, _, _, _, _, _, hbt, _⟩ := Law.clearWith_ok h
  exact not_mem_of_between hbt

/-- **The relation that is walked**: the rows on the table are as they were; and the state behind
stands at the chain's end only if the state in front did. (The first and the third clause of the
library's `PileStays`.) -/
def StaysBack (s t : S) : Prop :=
  t.rows = s.rows ∧ ((∃ a, t.here = .mem a) → ∃ a, s.here = .mem a)

theorem StaysBack.of_pile {s t : S} (q : PileStays s t) : StaysBack s t := ⟨q.1, q.2.2⟩

theorem StaysBack.trans {a b c : S} (h : StaysBack a b) (k : StaysBack b c) : StaysBack a c :=
  ⟨k.1.trans h.1, fun x => h.2 (k.2 x)⟩

/-- "opened", at the frame of every segment. -/
theorem opened_stays {built : Array Stages.LinkH} {first : Params.First} {W : Verify.Public}
    {fs : List LinkFrame} (h : framesOf built first W = .ok fs) (i : Nat) (f : LinkFrame)
    (hi : fs[i]? = some f) (s t : S) (k : f.opened s = .ok t) : StaysBack s t := by
  rcases IM.frames_arms h i f hi with ⟨X, -, -, rfl⟩ | ⟨rfl, Q, -, -, eo, -⟩ |
    ⟨Q, n, -, -, eo, -⟩ | ⟨Q, -, -, eo, -⟩
  · cases k
    exact ⟨rfl, fun x => x⟩
  · rw [eo] at k
    exact ⟨(openLayZero_rows k).1, fun ⟨a, e⟩ => absurd e ((openLayZero_rows k).2.2 a)⟩
  · rw [eo] at k
    exact .of_pile (openAtt_pile Q s t k)
  · rw [eo] at k
    exact .of_pile (openLay_pile Q s t k)

section
variable {Pp : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **THE WALK: IN FRONT OF K13's BATCHING, EVERY SUB-PROTOCOL BUT THE 25 "cleared" LEAVES THE ROWS
ON THE TABLE, AND BRINGS NO STATE TO THE CHAIN's END.** -/
theorem flat_stays (hS : VerifierAndGoals.InScope Pp = true) (hR : VerifierAndGoals.readFiles Pp = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pp.pol lay Pp.KL F Z Bs base c A B) (k : Nat) (b : Block S Cl)
    (hb : c.blocksInOrder[k]? = some b) (hk : k < 355) (hnc : ∀ l < 25, k ≠ 14 * l + IM.nAt l + 7)
    (s t : S) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (hd : b.decide s rs gs = .ok t) : StaysBack s t := by
  have h0 : Z.P.firstTree = 0 := pub_firstTree O.pub
  cases IM.flat_cases hS hR O k b hb with
  | front b hr hd' =>
    obtain rfl := (hd' s rs gs t).1 hd
    exact ⟨rfl, fun x => x⟩
  | laid l hl b hr hd' => exact .of_pile (layFront_pile l s t ((hd' s rs gs t).1 hd).1)
  | first l hl k0 b b' hk0 lot hp hj =>
    obtain ⟨Lt, hLt, hb'⟩ := lot
    obtain ⟨fs, f, m, hfs, hf, y1, -, y2, -, -⟩ := hj.yes hd
    have q : PileStays s m := (lot_pile Z h0 Bs.G₀ hLt hb' (by rw [hp]; exact (hear_noframe hk0).1)
      (by rw [hp]; exact (hear_noframe hk0).2)).1 s _ _ m y1
    exact (StaysBack.of_pile q).trans (opened_stays hfs l f hf m t y2)
  | hear l hl i hi k1 b b' name hk1 lot hp hla =>
    obtain ⟨Lt, hLt, hb'⟩ := lot
    have W := lot_pile Z h0 Bs.G₀ hLt hb' (by rw [hp]; exact (hear_noframe hk1).1)
      (by rw [hp]; exact (hear_noframe hk1).2)
    by_cases h7 : k1 = KindName.K7
    · exact .of_pile (W.1 s rs gs t ((IM.yes_alone_K7 hla h7 s t rs gs).1 hd).1)
    · exact .of_pile (W.1 s rs gs t ((IM.yes_alone hla h7 s t rs gs).1 hd).1)
  | batch l hl Lk p e1 hp hal =>
    have y := ((IM.yes_alone (hal _) (by unfold IM.a9Of; intro q; cases q) s t rs gs).1 hd).1
    exact .of_pile ((batch_over pile_trans (fun _ _ q => q) p (link_claims_runs pile_refl
      pile_trans Lk (hear_runs_stays hS hR O hl e1))).1 s rs gs t y)
  | behind l hl Lk b e1 hr hd' =>
    rw [hd'] at hd
    exact .of_pile
      (link_behind_runs pile_refl pile_trans Lk (hear_runs_stays hS hR O hl e1) s t hd)
  | close l hl p Q j k' b x hp hQ hk' ex hla =>
    have h7 : (IM.cAt l (IM.subAt l) j k').kind ≠ KindName.K7 := by
      have hm := List.mem_of_getElem? hk'
      intro q
      have q' : k' = KindName.K7 := q
      subst q'
      revert hm
      decide
    exact .of_pile ((closeOf_pile p Q x (List.mem_of_getElem? ex)).1 s rs gs t
      ((IM.yes_alone hla h7 s t rs gs).1 hd).1)
  | cleared l hl fs f b hfs hf hr hd' => exact absurd rfl (hnc l hl)
  | back j kj b b' name hkj lot hp hla =>
    obtain ⟨Lt, hLt, hb'⟩ := lot
    have hkk : kj = KindName.K2 ∨ kj = KindName.K12 := by
      rcases j with _ | _ | j
      · exact Or.inl (Option.some.inj hkj).symm
      · exact Or.inr (Option.some.inj hkj).symm
      · omega
    have hfr : kj ≠ KindName.frame := by rcases hkk with rfl | rfl <;> decide
    have h13 : kj ≠ KindName.K13 := by rcases hkk with rfl | rfl <;> decide
    have h7 : kj ≠ KindName.K7 := by rcases hkk with rfl | rfl <;> decide
    have hd2 : b.decide s rs gs = .ok t := hd
    exact .of_pile ((lot_pile Z h0 Bs.G₀ hLt hb' (by rw [hp]; exact hfr)
      (by rw [hp]; exact h13)).1 s rs gs t ((IM.yes_alone hla h7 s t rs gs).1 hd2).1)
  | last lot hla => omega

end

end ProofFile.Honest.K13

#print axioms ProofFile.Honest.K13.clearWith_rows
#print axioms ProofFile.Honest.K13.clearWith_rows_none
#print axioms ProofFile.Honest.K13.clearWith_notAtEnd
#print axioms ProofFile.Honest.K13.StaysBack.of_pile
#print axioms ProofFile.Honest.K13.StaysBack.trans
#print axioms ProofFile.Honest.K13.opened_stays
#print axioms ProofFile.Honest.K13.flat_stays
