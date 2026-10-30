-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K13/ClearedBySort.lean: ON THE FIRST CHAIN OF THE PROOF FILE's IOP AS
WRITTEN IN LEAN, IN FRONT OF K13's BATCHING: THE 25 SUB-PROTOCOLS "cleared", BY THE SEGMENT's SORT;
AND THAT NO SUB-PROTOCOL BRINGS THE STATE TO THE CHAIN's END. One definition, and statements with
their proofs. It stands on PileAtFlat.lean of this folder and the library alone.

Under: In the goals' scope (`VerifierAndGoals.InScope`, `VerifierAndGoals.readFiles`), under the opening of the proof
file's IOP (`IM.Open`: its letters Z, Bs, c are what is public, the blank ground's holder, the first
chain); for `cleared_by_sort` also hp: EVERY SUB-PROTOCOL OF THE CHAIN's LIST PASSES ITS OWN TEST ON
THE PLAN (∀ b ∈ c.blocksInOrder, b.planOk = true): public. (The library's `IM.plan_flat`,
Johnson/IMR/PlanAt.lean, has it from F.planOk = true.)
Main names:
  `cleared_by_sort`: **the 25 sub-protocols "cleared", by the segment's sort**: the head's (l = 24)
    and each layers' (l even) lay the verifier's own row of what `leftHead`, `leftLay` reads off the
    state in front (`rowBy` at that reader, the one layout, the built plan's NCL, the shape of the
    test) at the end of the rows on the table; each attention's (l odd) leaves the rows. Called:
    `IM.frame_of`, `IM.frames_arms` (Johnson/IMR/FrameSeat.lean), `P1L20.plans_hold`
    (Johnson/P1L20R/FrameSits.lean: the frame's own test on the plan holds at every segment),
    `P1L20.kind_of_sort` (P1L20R/FrameFold.lean: the sort by the number), `planLay_fv`,
    `planLayZero_fv`, `planAtt_fv` (Johnson/Top/H0/Walk/FrameProps.lean), `headFrame_fv`,
    `frameAt_att`, `frameAt_lay`, `zeroAt_some` (FrameRows.lean). NEAR KIN IN THE LIBRARY, which had
    which segments leave a row before: `P1L20.clear_with_flag` (FrameSits.lean: what a frame's
    "cleared" is, with the flag by the kind, its reader one that `leftOf` gathers),
    `P1L20.clear_by_sort` (P1L20R/RoomFold.lean: the flag by the segment's sort, from an accepting
    step), `bearing`, `isTake`, `takenAt`, `take_at` (RoomFold.lean). This one says beside: the
    reader by name; the row, on `S.rows`; at the decision.
  `NotAtEnd s`: the state does not stand at the chain's end (`here` is no `.mem`). There `S.rows` is
    the field `out.pending` (the library's `rows_of_not_mem`,
    Johnson/Desc/First/Pile/PileMakers.lean).
  `flat_notAtEnd`: **no decision of a sub-protocol of a number below 355 brings the state to the
    chain's end.** By the second clause of `flat_stays` (PileAtFlat.lean); at the 25 "cleared":
    `IM.frame_of`, `framesOf_row` (FrameRows.lean), `clearWith_notAtEnd`.
  `fold_notAtEnd`: **so at every border up to 355 the fold's state does not stand at the chain's
    end**, from a start that does not: by the library's rule `LPFK9.fold_ix`
    (Johnson/LPFK9R/PileByPlace.lean).

What is not claimed. THAT hp HOLDS AT ANY PUBLIC FILES: the library has F.planOk behind an accepting
run (`planOk_of_runEnd`, Johnson/Desc/PlanPasses.lean): that runs the wrong way for whoever wants to
show that a run accepts. That what the reader reads in front of "cleared" is what the segment's
merge left. Nothing on the numbers from 355 on. Nothing on soundness, completeness or hiding.

-/
import Johnson.Desc.ProofFile.Honest.K13.PileAtFlat
import Johnson.P1L20R.FrameFold
import Johnson.Top.H0.Walk.FrameRows

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K13

open OnBytes OnBytes.Model
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open VerifiableInference.Desc.First.Close (leftHead)
open ProofFile (Cl)
open Johnson.Desc.First.Walk
open Johnson.Desc.First.Walk.Law (rowBy)
open Johnson.Desc.First.Walk.Seat (LinkFrame framesOf frameAt zeroAt pubOf rowOf headFrame_fv
  frameAt_att frameAt_lay zeroAt_some)
open Johnson.Desc.First.Walk.Props (planAtt_fv planLay_fv planLayZero_fv)
open LPFK9 (fold_ix)

/-- The state does not stand at the chain's end. -/
def NotAtEnd (s : S) : Prop := ∀ a, s.here ≠ .mem a

section
variable {Pp : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **THE 25 "cleared", BY THE SEGMENT's SORT, WHERE EVERY SUB-PROTOCOL OF THE CHAIN PASSES ITS TEST
ON THE PLAN.** -/
theorem cleared_by_sort (hS : VerifierAndGoals.InScope Pp = true) (hR : VerifierAndGoals.readFiles Pp = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pp.pol lay Pp.KL F Z Bs base c A B)
    (hp : ∀ b ∈ c.blocksInOrder, b.planOk = true) (l : Nat) (hl : l < 25) (b : Block S Cl)
    (hb : c.blocksInOrder[14 * l + IM.nAt l + 7]? = some b) :
    ∃ Xl, Z.p.built.links[l]? = some Xl ∧
      ((l = 24 ∧ ∀ (s t : S) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))),
          b.decide s rs gs = .ok t →
          ∃ r, rowBy leftHead Z.p.X.layers.wsLay Xl.NCL Z.first.lin s = some r ∧
            t.rows = s.rows ++ [r]) ∨
        (l % 2 = 0 ∧ l ≠ 24 ∧
          ∀ (s t : S) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))),
          b.decide s rs gs = .ok t →
          ∃ r, rowBy leftLay Z.p.X.layers.wsLay Xl.NCL Z.first.lin s = some r ∧
            t.rows = s.rows ++ [r]) ∨
        (l % 2 = 1 ∧ ∀ (s t : S) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))),
          b.decide s rs gs = .ok t → t.rows = s.rows)) := by
  obtain ⟨-, fs, hfs, hall⟩ := IM.frame_of hS hR O
  obtain ⟨Lk, f, bL, bB, bC, e1, hn, hf, -, -, -, hClear, -, -, -, -, -, -, iC, -, dC⟩ := hall l hl
  have hn' : Lk.hear.length = IM.nAt l := hn
  rw [hn'] at iC
  obtain rfl : bC = b := Option.some.inj (iC.symm.trans hb)
  have hplan : f.plan = true := P1L20.plans_hold hS hR O hp hfs hl hf
  have yes : ∀ (X : LinkPub) (counts : S → Except String Unit) (left : S → Option WsForkOut),
      f.clear = clearWith X counts left (rowOf Z.p.X Z.first) → X.fv = true →
      ∀ (s t : S) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))),
        bC.decide s rs gs = .ok t →
        ∃ r, rowBy left Z.p.X.layers.wsLay X.NCL Z.first.lin s = some r ∧
          t.rows = s.rows ++ [r] := by
    intro X counts left ec hv s t rs gs hd
    rw [dC] at hd
    obtain ⟨y, -, -⟩ := (hClear s t).1 hd
    rw [ec] at y
    exact clearWith_rows y hv
  rcases IM.frames_arms hfs l f hf with ⟨Xh, h1, h2, rfl⟩ | ⟨rfl, Q, h1, hpl, -, ec⟩ |
    ⟨Q, n, h1, hpl, -, ec⟩ | ⟨Q, h1, hpl, -, ec⟩
  · have hk := P1L20.kind_of_sort hS hR O hl h1
    rw [h2] at hk
    have h24 : l = 24 := by
      by_contra hne
      unfold IM.subAt at hk
      rw [if_neg hne] at hk
      split at hk <;> cases hk
    exact ⟨Xh, h1, Or.inl ⟨h24, yes (pubOf Xh) _ leftHead rfl (headFrame_fv hplan)⟩⟩
  · obtain ⟨X, hp', hX, -, -, rfl⟩ := zeroAt_some h1
    exact ⟨X, hX, Or.inr (Or.inl ⟨rfl, by decide,
      yes (pubOf X) _ leftLay ec (planLayZero_fv (hpl ▸ hplan))⟩)⟩
  · obtain ⟨X, p, hX, -, hk1, -, rfl, -⟩ := frameAt_att h1
    have hk := P1L20.kind_of_sort hS hR O hl hX
    rw [hk1] at hk
    have hodd : l % 2 = 1 := by
      unfold IM.subAt at hk
      split at hk
      · cases hk
      · split at hk
        · cases hk
        · omega
    refine ⟨X, hX, Or.inr (Or.inr ⟨hodd, fun s t rs gs hd => ?_⟩)⟩
    rw [dC] at hd
    obtain ⟨y, -, -⟩ := (hClear s t).1 hd
    rw [ec] at y
    exact clearWith_rows_none y (planAtt_fv (hpl ▸ hplan))
  · obtain ⟨X, hp', hX, -, hk0', -, rfl⟩ := frameAt_lay h1
    have hk := P1L20.kind_of_sort hS hR O hl hX
    rw [hk0'] at hk
    have hev : l % 2 = 0 ∧ l ≠ 24 := by
      unfold IM.subAt at hk
      split at hk
      · cases hk
      · rename_i hne
        split at hk
        · rename_i he
          exact ⟨he, hne⟩
        · cases hk
    exact ⟨X, hX, Or.inr (Or.inl ⟨hev.1, hev.2,
      yes (pubOf X) _ leftLay ec (planLay_fv (hpl ▸ hplan))⟩)⟩

/-- **No sub-protocol of a number below 355 brings the state to the chain's end.** -/
theorem flat_notAtEnd (hS : VerifierAndGoals.InScope Pp = true) (hR : VerifierAndGoals.readFiles Pp = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pp.pol lay Pp.KL F Z Bs base c A B) (k : Nat) (b : Block S Cl)
    (hb : c.blocksInOrder[k]? = some b) (hk : k < 355) (s t : S) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) (hd : b.decide s rs gs = .ok t) (hs : NotAtEnd s) :
    NotAtEnd t := by
  by_cases hc : ∃ l < 25, k = 14 * l + IM.nAt l + 7
  · obtain ⟨l, hl, rfl⟩ := hc
    obtain ⟨-, fs, hfs, hall⟩ := IM.frame_of hS hR O
    obtain ⟨Lk, f, bL, bB, bC, e1, hn, hf, -, -, -, hClear, -, -, -, -, -, -, iC, -, dC⟩ :=
      hall l hl
    have hn' : Lk.hear.length = IM.nAt l := hn
    rw [hn'] at iC
    obtain rfl : bC = b := Option.some.inj (iC.symm.trans hb)
    rw [dC] at hd
    obtain ⟨y, -, -⟩ := (hClear s t).1 hd
    obtain ⟨-, X, counts, left, ec, -⟩ :=
      Johnson.Desc.First.Walk.Seat.framesOf_row hfs (List.mem_of_getElem? hf)
    rw [ec] at y
    exact clearWith_notAtEnd y
  · intro a e
    obtain ⟨a', e'⟩ :=
      (flat_stays hS hR O k b hb hk (fun l hl e => hc ⟨l, hl, e⟩) s t rs gs hd).2 ⟨a, e⟩
    exact hs a' e'

/-- **So at every border up to 355 the fold's state does not stand at the chain's end**, from a
start that does not. -/
theorem fold_notAtEnd (hS : VerifierAndGoals.InScope Pp = true) (hR : VerifierAndGoals.readFiles Pp = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pp.pol lay Pp.KL F Z Bs base c A B) (b : Nat) (hb : b ≤ 355)
    (s₀ : S) (h0 : NotAtEnd s₀) (rs : List Fmt.RoundView) (cols : List VerifiableInference.Desc.OpenedColumn)
    (r : S × List Fmt.RoundView × List VerifiableInference.Desc.OpenedColumn)
    (hf : foldBlocks 0 (c.blocksInOrder.take b) s₀ rs cols = .ok r) :
    NotAtEnd r.1 := by
  refine fold_ix (fun _ s => NotAtEnd s) 0 (c.blocksInOrder.take b) 0 ?_ s₀ rs cols r hf h0
  intro k blk hk s R gs t hd hs
  have hkb : k < b := by
    have := (List.getElem?_eq_some_iff.1 hk).1
    rw [List.length_take] at this
    omega
  rw [List.getElem?_take_of_lt hkb] at hk
  exact flat_notAtEnd hS hR O k blk hk (by omega) s t R gs hd hs

end

end ProofFile.Honest.K13

#print axioms ProofFile.Honest.K13.cleared_by_sort
#print axioms ProofFile.Honest.K13.flat_notAtEnd
#print axioms ProofFile.Honest.K13.fold_notAtEnd
