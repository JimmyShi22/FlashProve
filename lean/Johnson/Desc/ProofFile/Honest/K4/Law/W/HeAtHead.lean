-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/W/HeAtHead.lean: CONDITIONAL. UNDER THE LIBRARY's HYPOTHESIS h
: `P5J.AtMgA` (Johnson/P5J/MgAtAll.lean), AT EACH GROUP g BELOW 12: THE NUMBER `ownScalarsOf`
(`partsInFront` cF.blocksInOrder (2 * g) (`IM.k4Place` g)) IS THE LIBRARY's NUMBER `Forest.elems` AT THE
LAYOUT's SHAPE.

What is here. PUBLIC DATA ALONE: places, names of rounds, counts. A round's scalars are "own" unless
its name stands in `frameNames` (Honest/BookOf.lean). Law/W/LockAtHead.lean's statement takes a
hypothesis he : e = that number (`ownScalarsOf`, `partsInFront`: Honest/BookRowKit.lean): the own
scalars in front of the layers' own rounds (kind K4) in their segment (link) 2 g. Here it is worked
out. It is a sum with one term for each sub-protocol (Honest/Small/OwnOfRounds.lean), and it reads
of a sub-protocol its place and its declared rounds alone. In these the description's first chain
agrees, sub-protocol by sub-protocol, with the library's written description `WP` (other writers'
`planAlike_at_head`, Honest/K14/WrittenAtHead.lean; `PlanAlike`,
Johnson/AtFull/ProofPlan/PlanAlike.lean). At `WP` the sum is a closed term: an evaluation says that
it equals the term of the member number 28 g + 3. That member is there by `lookMember_head`
(Law/LookMemberHead.lean); its term is `lookRounds_own_head`'s (Law/W/LookRoundsAtHead.lean).
Definitions, statements and proofs.

  `ownOfDecls`, `frontOwn`, `front_pairs`: the number in front as a function of the list of
      pairs (place, declared rounds).
  `pairs_alike`: alike lists have one list of pairs. No kind is named.
  `wpPairs`, `frontIsThird`, `frontIsThird_all`: THE EVALUATION at the written description, for
      the twelve groups.
  `frontIsSecond_no`, `frontIsFourth_no`: two refusals: at none of the twelve is the sum the
      term of the member number 28 g + 2, nor that of the member number 28 g + 4.
  `k4_he_at_head`: **THE STATEMENT.**

Kin. Other writers' Honest/BookAlikeRows.lean has congruences at alike sub-protocols and lists,
among them `planParts_alike`, `planPartsIn_alike` and `partsWhere_alike` (the parts of those whose
place passes a test); none is on `partsInFront`, which has a `takeWhile` behind its filter: hence
`pairs_alike` and `front_pairs`. The library's `alike₂_place` and `alike₂_rounds` (PlanAlike.lean)
and other writers' `sizesIn_alike` (Honest/BookWholeAlike.lean) are similar.

Not shown here. THE THREE EVALUATIONS ARE BY LEAN's KERNEL (`decide +kernel`), REPLAYED BY NO
INDEPENDENT CHECKER; and beneath this file stand further closed facts by evaluation in Lean's
kernel, replayed by none: Honest/K14/WrittenAtHead.lean's own head names three grounds of such;
Johnson/IMR/BorderW.lean holds one. `frontIsThird` ASKS THAT TWO NUMBERS ARE EQUAL: which
sub-protocols stand in front, that the member number 28 g + 3 is one of them, and why the others add
nothing, is not said; where the list has no such member its term is read as 0. The two refusals show
that the Bool can say no, and no more. That `ownScalarsOf` of `partsInFront` is what the book's
maker counts is other writers' to show (`bookWhole_row_stretch`, Honest/BookRowStretch.lean, and
`bookWhole_row_wants`, `bookWhole_merge_stretch`, Honest/BookMergeStretch.lean, have that term in
their statements); it is not shown here. That `Forest.elems` is what the verifier's ledger moves by.
Nothing on what is sent. All that Law/W/LockAtHead.lean's head names as left, but he, stays left.
THE FULL SIZE ALONE, AND THE FORMAT's EARLIER HASH (`OnBytes.secondHashFunction`) ALONE. IT RESTS ON THREE
STATEMENTS AT LEAST OF FILES UNDER Johnson/Goal/, none called in this file: `Meaning.scope_plans`
(through Law/W/SiteShape.lean); `VerifiableInference.PlanWritten.seat_in_scope` and
`P5J.cutIs_of_laid` (through Honest/K14/WrittenAtHead.lean, whose head gives their paths). That h
can hold: the side library AtFullSide proves, with no hypothesis, that h has a member at one set of
public files (AtFullSide.Top.headMember_zFull, AtFullSide/Top/HeadMemberAtFull.lean, whose own
Limits say what it is worth). IT STANDS OVER FILES THAT ARE NO PART OF THE SEALED LIBRARY YET: of
this file's writers (Law/W/LookRoundsAtHead.lean and what its head names) and of other writers
(those that head names, and what lies beneath them; Honest/K14/WrittenAtHead.lean and what lies
beneath it). Nothing on soundness, on completeness or on any other property.
No property is claimed.
A LAW, NOT A PART: no file that defines a part of the proof file's description may import this one:
following import lines, its imports reach modules under Johnson/Goal/, under Johnson/Bridge/ and one
whose name begins Cb.Bridge.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.W.LookRoundsAtHead
import Johnson.Desc.ProofFile.Honest.K14.WrittenAtHead
import Johnson.IMR.K4Seat

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- The default instance `Inst.Model.Scl.ref` (a table of scales) is switched off in this file, so
that no statement picks a table of scales silently. -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4.W
open OnBytes
open VerifiableInference.Desc (Block Chain Place Alike₂)
open P2Law.ProofPlan (WP)

/-! ## 1 The number in front, on pairs -/

/-- The own scalars of a list of declared rounds. -/
def ownOfDecls (rs : List Fmt.DeclaredRound) : Nat :=
  rs.foldl (fun n r => if frameNames.contains r.entry.name then n else n + scalarsIn r) 0

/-- The number of own scalars in front of the place a in segment l, on a list of pairs: a place and
its declared rounds. -/
def frontOwn (ps : List (Place × List Fmt.DeclaredRound)) (l : Nat) (a : Place) : Nat :=
  (((ps.filter fun p => p.1.link == some l).takeWhile fun p => p.1 != a).map
    fun p => ownOfDecls p.2).sum

/-- That number reads of a sub-protocol its place and its declared rounds alone. -/
theorem front_pairs {σ C : Type} (bs : List (Block σ C)) (l : Nat) (a : Place) :
    ownScalarsOf (partsInFront bs l a) = frontOwn (bs.map fun b => (b.place, b.rounds)) l a := by
  rw [ownScalarsOf_partsInFront]
  unfold frontOwn
  rw [List.filter_map, List.takeWhile_map, List.map_map]
  rfl

/-- CONDITIONAL: on h. Alike lists have one list of pairs. -/
theorem pairs_alike {σ C σ' C' : Type} {l : List (Block σ C)} {l' : List (Block σ' C')}
    (h : List.Forall₂ Alike₂ l l') :
    (l.map fun b => (b.place, b.rounds)) = l'.map fun b => (b.place, b.rounds) := by
  induction h with
  | nil => rfl
  | @cons b b' l l' hb _ ih => simp only [List.map_cons, hb.1, hb.2.1, ih]

/-! ## 2 At the written description -/

/-- The written description's first chain, as pairs. -/
def wpPairs : List (Place × List Fmt.DeclaredRound) := WP.first.blocksInOrder.map fun b => (b.place, b.rounds)

/-- At group g: the number in front of K4's place equals the term of the member number 28 g + 3;
where the list has no such member, that term is read as 0. -/
def frontIsThird (g : Nat) : Bool :=
  frontOwn wpPairs (2 * g) (IM.k4Place g) == ownOfDecls ((wpPairs[28 * g + 3]?.map (·.2)).getD [])

/-- The evaluation: so at each of the twelve groups. -/
theorem frontIsThird_all : (List.range 12).all frontIsThird = true := by decide +kernel

/-- A refusal: at none of the twelve groups is it the term of the member number 28 g + 2. -/
theorem frontIsSecond_no : ((List.range 12).any fun g =>
    frontOwn wpPairs (2 * g) (IM.k4Place g) ==
      ownOfDecls ((wpPairs[28 * g + 2]?.map (·.2)).getD [])) = false := by decide +kernel

/-- A second refusal: at none of the twelve groups is it the term of the member number 28 g + 4. -/
theorem frontIsFourth_no : ((List.range 12).any fun g =>
    frontOwn wpPairs (2 * g) (IM.k4Place g) ==
      ownOfDecls ((wpPairs[28 * g + 4]?.map (·.2)).getD [])) = false := by decide +kernel

/-! ## 3 The statement -/

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place}

/-- CONDITIONAL: on h and hg. **THE NUMBER OF OWN SCALARS IN FRONT OF K4 IN ITS SEGMENT IS
`Forest.elems` AT THE LAYOUT's SHAPE.** -/
theorem k4_he_at_head (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {g : ℕ} (hg : g < 12) :
    ownScalarsOf (partsInFront cF.blocksInOrder (2 * g) (IM.k4Place g)) =
      Model.Forest.elems (P5J.At.X Zp).y.fo := by
  have hp : wpPairs = cF.blocksInOrder.map fun b => (b.place, b.rounds) :=
    pairs_alike (ProofFile.Honest.K14.planAlike_at_head h).first
  obtain ⟨blk, e1, -, -⟩ := ProofFile.Honest.K4.lookMember_head h hg
  have hk : frontOwn wpPairs (2 * g) (IM.k4Place g) =
      ownOfDecls ((wpPairs[28 * g + 3]?.map (·.2)).getD []) :=
    eq_of_beq (List.all_eq_true.1 frontIsThird_all g (List.mem_range.2 hg))
  rw [front_pairs, ← hp, hk, hp, List.getElem?_map, e1]
  exact lookRounds_own_head h hg e1

end ProofFile.Honest.K4.W

#print axioms ProofFile.Honest.K4.W.front_pairs
#print axioms ProofFile.Honest.K4.W.pairs_alike
#print axioms ProofFile.Honest.K4.W.frontIsThird_all
#print axioms ProofFile.Honest.K4.W.frontIsSecond_no
#print axioms ProofFile.Honest.K4.W.frontIsFourth_no
#print axioms ProofFile.Honest.K4.W.k4_he_at_head
