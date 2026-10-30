-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K6/Law/GoodRow.lean: CONDITIONAL. NOT `plays`, NOT `acc`, NOT at a
description of the protocol, and NO NEW EQUATION BETWEEN TWO DISTRIBUTIONS: `ExactMember`
(Honest/Small/Field.lean: the field `exact` of `Good`, Honest/Side.lean, without its hypothesis on
the opened columns; it gives that field at every `pre`), the field `fresh` of `Good` and bud's
clause AT THE ROW OF THE SUB-PROTOCOL "the output head's own rounds", under the structure
`HeadSeated` (Honest/K6/Law/Row.lean), GENERAL IN THE PLACE's PUBLIC NUMBERS p: each a JOIN, by
cases on the eight members written out, of laws at one member. THE MASKED SUMCHECK's LAW, ANOTHER
FOLDER's, STANDS HERE AS A NAMED PREMISE; Honest/K6/Law/GoodRowSum.lean pays it.

  1  `SumLawAt`   A NAMED PREMISE: the masked sumcheck's law at this row's letters and lens
  2  `head_exact_small`   `ExactMember` at the members 0, 1, 3, 4: the two laws of Honest/Small/,
     called
     `head_exact_cases`   the eight members by cases: a step
     `head_exact`   `ExactMember` at all eight: under `SumLawAt`
  3  `head_fresh`   `fresh` at all eight: under a Bool on the book: the frame's `fresh_of_nil`,
     called
  4  `headBud`, `asksFrom_zero`, `head_bud`   the row's letter bud ("every list of positions is
     empty"), a step, and its clause
  5  `head_good`, `headLettered`, `head_goodAt`   `Good` as one term, at every `pre`, at A := False
     (so `plays` and `acc` hold there for nothing); the row with its letters; THE FORM that the
     frame's rule takes (`Lettered.goodAt`), at the chain's falls, at every `earlier`

The face φ, the book, the order of places, chain and firstTree are variables; On is a variable in 2,
bud in 2 and 3, `pre` and `earlier` in 5.

What is sampled and what is fixed is, member by member, what the called laws' heads say: ONE PART AT
A TIME, ALL ELSE FIXED BEFORE THE COINS; at the members 1 and 4 nine and seven coins against nine
and seven scalars; at 0 and 3 none.

Why the premise has a name. So that this file need not import the file that states the masked
sumcheck's law on `ExactMember` (Honest/SumLaw/SumExact.lean, by other authors):
Honest/K6/Law/GoodRowSum.lean does. Other files of Honest/SumLaw/ do lie beneath this one, through
Honest/K6/Law/Row.lean.

Called. `asksFrom`: Honest/Law/Rule/Session.lean.

Limits. ALL THAT THE LIMITS OF Honest/Small/Quiet.lean AND Scalars.lean SAY HOLDS HERE: bookkeeping;
the spender's half alone.
WHAT THE ROW's VALUES READ. No move of the row reads anything of what has been seen, rounds or
opened columns: Honest/K6/Law/RowReads.lean (not in the library), a sentence that can fail. Of a
job's five functions `inY` is handed the "ends" run's own coins: the frame's letter.
WHOEVER CARRIES THE ROW's RUNS BEHIND IT. The runs are entries of the segment's mask row, and a
carried run is one oracle message's whole stretch (Honest/ForKinds.lean): whoever carries that
message behind this row holds its coins, and has to meet its own `exact` at each fixed carried run,
beside a simulator that is not handed it; and a carrier's On may tie what is carried to the front
only by an identity that holds at every value of the carried run's coins: owed by whoever writes the
carrier.
A CALL's TWO RUNS ("sum", "ends") ARE TAKEN AS UNIFORM AND INDEPENDENT by the masked sumcheck's law;
here both are stretches of one mask row: that they share no coin, AND THAT NO TWO OF THE ROW's TEN
RUNS DO, is the book's tests'. The owner's `fresh` at these spenders, the book's lending, the Bool
at the real book, On over real runs, which values are sent: not here. "Members" in this file:
`σ.members`, the frame's `Member`. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.Rule
import Johnson.Desc.ProofFile.Honest.Law.Rule.Session
import Johnson.Desc.ProofFile.Honest.K6.Law.Row
import Johnson.Desc.ProofFile.Honest.Small.Book
import Johnson.Desc.ProofFile.Honest.Small.Members
import Johnson.Desc.ProofFile.Honest.Small.Quiet
import Johnson.Desc.ProofFile.Honest.Small.Scalars

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K6
open VerifiableInference.Desc (Block Place Oracle)
open VerifiableInference.Desc.Kinds
open VerifiableInference.Desc.Part.MaskedSum (Call shapeOk)
open ProofFile.Honest.Small ProofFile.Honest.SumLaw

variable {S Cl X W₀ Rc Tr : Type}

/-! ## 1 `ExactMember` -/

/-- **THE LAW OF ANOTHER FOLDER, AS A NAMED PREMISE**: `ExactMember` at a masked sumcheck's part,
lifted as the row lifts it, beside `sumSim`, under the three premises on public data of
Honest/K6/Law/Segs.lean. A definition: a premise's form. NOTHING IS CLAIMED OF IT HERE:
Honest/K6/Law/GoodRowSum.lean pays it by `exact_sumPart_field` (Honest/SumLaw/SumExact.lean). -/
def SumLawAt (φ : Face (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) Inst)
    (σ : Side S Cl (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X Inst)
    (wit : Local W₀ Rc Inst Tr → HeadAsk) (chain firstTree : Nat)
    (On : (u : Member (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X Inst) →
      CsAll u.part.carries → Mid (Local W₀ Rc Inst Tr) X → Before → Prop)
    (bud : Nat → List Fmt.Drawn → List (List (List Nat)) → Prop) : Prop :=
  ∀ (j : Nat) (rs : List (Fmt.DeclaredRound × List Oracle)) (a' : Addr) (name endName : String)
    (J : SumJob HeadAsk Unit), shapeOk J.shape = true → StatedBy (scalarsOf J.shape) rs →
    betaMarked J.shape rs = true →
    ExactMember φ σ chain firstTree On bud
      ⟨j, rs, (sumPart name endName J : Part Unit HeadAsk Unit).lift (fun _ => ()) wit
        (fun _ => ()) fun x _ => x, sumSim a' J.shape⟩

/-- CONDITIONAL. The join: at each member either its number is one of the four small ones and
`ExactMember` holds, or it is a sum's and `ExactMember` holds under the named premise. -/
theorem head_exact_cases (φ : Face (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) Inst)
    {σ : Side S Cl (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X Inst}
    {wit : Local W₀ Rc Inst Tr → HeadAsk} {p : Head.Par} {at_ : Place}
    (h : HeadSeated σ wit p at_) (chain firstTree : Nat)
    (On : (u : Member (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X Inst) →
      CsAll u.part.carries → Mid (Local W₀ Rc Inst Tr) X → Before → Prop)
    (bud : Nat → List Fmt.Drawn → List (List (List Nat)) → Prop) :
    ∀ u ∈ σ.members, (u.number ∈ [0, 1, 3, 4] ∧ ExactMember φ σ chain firstTree On bud u) ∨
      (u.number ∈ [2, 5, 6, 7] ∧
        (SumLawAt φ σ wit chain firstTree On bud → ExactMember φ σ chain firstTree On bud u)) := by
  intro u hu
  rw [head_laid h] at hu
  simp only [headSided, headRow, headParts, headSims, headSegs, List.map_cons, List.map_nil,
    List.zip_cons_cons, List.zip_nil_right, laid, List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact .inl ⟨by simp, quietPart_exact_lift _ _ _ _ _ _ _ _ _ _ _ _ _ _ (headSeg_small p).1⟩
  · exact .inl ⟨by simp,
      scalarsPart_exact_lift _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (headSeg_small p).2.1⟩
  · exact .inr ⟨by simp, fun hS => hS _ _ _ _ _ (headSquaresJob p)
      (shapeOk_point _ _ _ (by decide)) (headSeg_sums p).1 (headSeg_beta p).1⟩
  · exact .inl ⟨by simp,
      quietPart_exact_lift _ _ _ _ _ _ _ _ _ _ _ _ _ _ (headSeg_small p).2.2.1⟩
  · exact .inl ⟨by simp,
      scalarsPart_exact_lift _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (headSeg_small p).2.2.2⟩
  · exact .inr ⟨by simp, fun hS => hS _ _ _ _ _ (headProductsJob p)
      (shapeOk_point _ _ _ (by decide)) (headSeg_sums p).2.1 (headSeg_beta p).2.1⟩
  · exact .inr ⟨by simp, fun hS => hS _ _ _ _ _ (headNormedJob p)
      (shapeOk_point _ _ _ (by decide)) (headSeg_sums p).2.2.1 (headSeg_beta p).2.2.1⟩
  · exact .inr ⟨by simp, fun hS => hS _ _ _ _ _ (headLogitsJob p)
      (shapeOk_point _ _ _ (by decide)) (headSeg_sums p).2.2.2 (headSeg_beta p).2.2.2⟩

/-- CONDITIONAL. **`ExactMember` at the four small members** (0 and 3: nothing is sent; 1 and 4:
nine and seven scalars): no premise beyond the structure. -/
theorem head_exact_small (φ : Face (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) Inst)
    {σ : Side S Cl (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X Inst}
    {wit : Local W₀ Rc Inst Tr → HeadAsk} {p : Head.Par} {at_ : Place}
    (h : HeadSeated σ wit p at_) (chain firstTree : Nat)
    (On : (u : Member (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X Inst) →
      CsAll u.part.carries → Mid (Local W₀ Rc Inst Tr) X → Before → Prop)
    (bud : Nat → List Fmt.Drawn → List (List (List Nat)) → Prop) :
    ∀ u ∈ σ.members, u.number ∈ [0, 1, 3, 4] → ExactMember φ σ chain firstTree On bud u := by
  intro u hu hn
  rcases head_exact_cases φ h chain firstTree On bud u hu with ⟨_, he⟩ | ⟨hn', _⟩
  · exact he
  · exfalso
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn hn'
    omega

/-- CONDITIONAL ON THE NAMED PREMISE `SumLawAt`. **`ExactMember` at all eight members.** It is not
the field `exact` of `Good`: it gives that field at every `pre` (`exactAt_of_exact`,
Honest/Small/Field.lean). -/
theorem head_exact (φ : Face (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) Inst)
    {σ : Side S Cl (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X Inst}
    {wit : Local W₀ Rc Inst Tr → HeadAsk} {p : Head.Par} {at_ : Place}
    (h : HeadSeated σ wit p at_) (chain firstTree : Nat)
    (On : (u : Member (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X Inst) →
      CsAll u.part.carries → Mid (Local W₀ Rc Inst Tr) X → Before → Prop)
    (bud : Nat → List Fmt.Drawn → List (List (List Nat)) → Prop)
    (hSum : SumLawAt φ σ wit chain firstTree On bud) :
    ∀ u ∈ σ.members, ExactMember φ σ chain firstTree On bud u := by
  intro u hu
  rcases head_exact_cases φ h chain firstTree On bud u hu with ⟨_, he⟩ | ⟨_, he⟩
  · exact he
  · exact he hSum

/-! ## 2 fresh -/

/-- CONDITIONAL. **The field `fresh` of `Good`, at all eight members**: under the Bool true
(`noneSpent`, Honest/Small/Field.lean, at the row's eight addresses: no entry of the book by which a
part spends names one of them as its owner), and empty there. The frame's own `fresh_of_nil`,
called. -/
theorem head_fresh (φ : Face (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) Inst)
    {σ : Side S Cl (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X Inst}
    {wit : Local W₀ Rc Inst Tr → HeadAsk} {p : Head.Par} {at_ : Place}
    (h : HeadSeated σ wit p at_) (Bk : ProverCoinCounts) (ord : List Place)
    (bud : Nat → List Fmt.Drawn → List (List (List Nat)) → Prop)
    (hB : ((List.range 8).all fun i => noneSpent Bk ⟨at_, i⟩) = true) :
    ∀ u ∈ σ.members, FreshMember φ σ Bk ord bud u := by
  intro u hu q sp ca m ds asks _ _ _
  have hb : noneSpent Bk ⟨σ.block.place, u.number⟩ = true := by
    rw [h.place]
    exact List.all_eq_true.1 hB u.number (List.mem_range.2 (head_numbers h u hu))
  exact fresh_of_nil _ (spentBy_of_noneSpent hb q) _ _

/-! ## 3 bud -/

/-- The row's letter bud: no position of a table of the row's is read: it sends none. -/
def headBud (_ : Nat) (_ : List Fmt.Drawn) (asks : List (List (List Nat))) : Prop :=
  asks.all (·.isEmpty) = true

/-- CONDITIONAL. Where no round has a root, no position is asked. -/
theorem asksFrom_zero (tree : Nat → List Nat) : ∀ (l : List Nat) (n : Nat), (∀ r ∈ l, r = 0) →
    (asksFrom tree l n).all (·.isEmpty) = true
  | [], _, _ => rfl
  | r :: l, n, h => by
    have h0 : r = 0 := h r (List.mem_cons_self ..)
    subst h0
    show (true && (asksFrom tree l (n + 0)).all (·.isEmpty)) = true
    rw [asksFrom_zero tree l (n + 0) fun x hx => h x (List.mem_cons_of_mem _ hx)]
    rfl

/-- CONDITIONAL. **bud's clause, and more than it**: at every member, every reader of trees, every
number of trees in front, every list of challenges. -/
theorem head_bud {σ : Side S Cl (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X Inst}
    {wit : Local W₀ Rc Inst Tr → HeadAsk} {p : Head.Par} {at_ : Place}
    (h : HeadSeated σ wit p at_) :
    ∀ u ∈ σ.members, ∀ (tree : Nat → List Nat) (n : Nat) (ds : List Fmt.Drawn),
      headBud u.number ds (asksFrom tree (u.rounds.map (·.2.length)) n) := by
  intro u hu tree n ds
  refine asksFrom_zero tree _ n fun x hx => ?_
  obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hx
  have hz := mem_rounds_of_member hu hr
  rw [h.rounds, h.oracles, zip_map_nil] at hz
  obtain ⟨d, _, rfl⟩ := List.mem_map.1 hz
  rfl

/-! ## 4 Good, as one term; the row with its letters -/

/-- CONDITIONAL ON THE NAMED PREMISE `SumLawAt`. **`Good` at the row's side, AS ONE TERM, at A :=
False**: `plays` and `acc` ARE MET FOR NOTHING THERE, by absurd: `fits`, `exact` and `fresh` alone
say something in this term. `pre` is a free letter: the term stands at every `pre`; its `exact` is
`head_exact` behind `exactAt_of_exact` (Honest/Small/Field.lean). The premise asks the sums'
equation at every `m.opened`, which is more than this term's `exact` needs. A and B are fields of
the frame's `Lettered` (Honest/Rule.lean), laid by whoever writes the list of rows: this file lays
no others than A := False and B := True. -/
theorem head_good {pre : List (Nat × Nat × List Fmt.DeclaredRound)}
    (φ : Face (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) Inst)
    {σ : Side S Cl (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X Inst}
    {wit : Local W₀ Rc Inst Tr → HeadAsk} {p : Head.Par} {at_ : Place}
    (h : HeadSeated σ wit p at_) (Bk : ProverCoinCounts) (ord : List Place) (chain firstTree : Nat)
    (B : Coins Bk → S → Mid (Local W₀ Rc Inst Tr) X → Env → Prop)
    (hSum : SumLawAt φ σ wit chain firstTree (fun _ _ _ _ => True) headBud)
    (hB : ((List.range 8).all fun i => noneSpent Bk ⟨at_, i⟩) = true) :
    Good pre φ σ Bk ord chain firstTree (fun _ _ _ _ => False) B (fun _ _ _ _ => True) headBud :=
  { fits := head_fits h
    plays := fun _ _ _ _ _ hA => hA.elim
    acc := fun _ _ _ _ _ hA => hA.elim
    exact := fun u hu => exactAt_of_exact pre (head_exact φ h chain firstTree _ _ hSum u hu)
    fresh := head_fresh φ h Bk ord _ hB }

/-- **The row with its letters**: A := False, B := True, On := True, bud := `headBud`. -/
def headLettered (Bk : ProverCoinCounts) (wit : Local W₀ Rc Inst Tr → HeadAsk) (p : Head.Par) (at_ : Place) :
    Lettered Bk S Cl (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X Inst :=
  { place := at_, row := headSided wit p at_, A := fun _ _ _ _ => False, B := fun _ _ _ _ => True
    On := fun _ _ _ _ => True, bud := headBud }

/-- CONDITIONAL ON THE NAMED PREMISE `SumLawAt`. **The form that the frame's rule takes**:
`Lettered.goodAt`, at the chain's list and ITS FALLS. IN FORM ALONE: the rule reads the list's own
letters A and B, which whoever writes the list lays: a list of rows that held `headLettered` as it
stands would have `plays` and `acc` for nothing. The frame's `Owed` (Honest/Owed.lean) asks `goodAt`
of the list with a condition on the opened columns laid beside A and B (`Lettered.withField`), not
of `headLettered` as it stands: that step is not taken here. AND MET FOR NOTHING WHERE NO BLOCK OF
bs STANDS AT THE PLACE, as `goodAt` itself is. `earlier` is a free letter: the form stands at every
value of it. -/
theorem head_goodAt {earlier : List (Nat × Nat × List Fmt.DeclaredRound)}
    (φ : Face (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) Inst) (Bk : ProverCoinCounts)
    (wit : Local W₀ Rc Inst Tr → HeadAsk) (p : Head.Par) (at_ : Place) (bs : List (Block S Cl))
    (ord : List Place) (chain firstTree : Nat) (fs : List (Fall S))
    (hb : ∀ b ∈ bs, b.place = at_ → b.rounds = p.rounds ∧ b.oracles = p.rounds.map fun _ => [])
    (hSum : ∀ σ : Side S Cl (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X Inst,
      SumLawAt φ σ wit chain firstTree (fun _ _ _ _ => True) headBud)
    (hB : ((List.range 8).all fun i => noneSpent Bk ⟨at_, i⟩) = true) :
    (headLettered (S := S) (Cl := Cl) (X := X) Bk wit p at_).goodAt earlier φ bs ord chain firstTree
      fs := by
  intro σ hσ
  exact head_good φ (headSeated_of_seated hσ hb) Bk ord chain firstTree _ (hSum σ) hB

end ProofFile.Honest.K6

#print axioms ProofFile.Honest.K6.head_exact_cases
#print axioms ProofFile.Honest.K6.head_exact_small
#print axioms ProofFile.Honest.K6.head_exact
#print axioms ProofFile.Honest.K6.head_fresh
#print axioms ProofFile.Honest.K6.asksFrom_zero
#print axioms ProofFile.Honest.K6.head_bud
#print axioms ProofFile.Honest.K6.head_good
#print axioms ProofFile.Honest.K6.head_goodAt
#print axioms ProofFile.Honest.K6.SumLawAt
#print axioms ProofFile.Honest.K6.headBud
#print axioms ProofFile.Honest.K6.headLettered
