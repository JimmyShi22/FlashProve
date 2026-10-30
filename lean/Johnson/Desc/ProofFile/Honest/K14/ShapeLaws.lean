-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K14/ShapeLaws.lean: THE SHARED CHAIN's SHAPE Sh2 IN THE FRAME's FORM
(Honest/Thread/ShapeMeet.lean: Shape.meet: one Bool and one update a member), and the frame's own
premises on it AT THE MEMBERS 0 TO 8 of the shared chain (Honest/Thread/Shape.lean): «Carries»,
«Returns», «Values»; the shape's own run up to the border behind the eight, in closed form; what a
thread's state is at that border; and the frame's rule applied. Statements with their proofs. A
member: a sub-protocol of the chain's list, by its number from 0; the border b stands in front of
the member b.

THE LETTERS. The type of shapes and the reader are Sh2 and sh2 (Johnson/Desc/K14/Shape/Lin.lean):
the shape of the structure ALONE: no mark stands in any statement here (Honest/K14/ShapeZ.lean lays
one beside). The test, the update and the tests on values are VARIABLES guard, upd, vals. EACH LAW
TAKES, AS PREMISES OF ITS OWN, WHAT IT SPENDS OF THEM, and nothing else: carries2, returns2 and
values2 at their own b; the run at one shape a member, the closed form. So a test that asks more
than this kind's is served by all: its surplus is owed at these nine shapes alone. The thread and
the fall are variables too.

Main names:
  valsS               the named tests on values: one: at "(rec_gamma)": no seed of the state's key
                      has the factor 0 (noZeroFactor, KeySeeds.lean)
  meet_inv, shown_like, stepShape   small ones; the first general in the state and the shape; the
                      last: behind a step of one of the members 0 to 8 the shape is the update
  carries2            **Carries bs ft (Shape.meet sh2 guard upd vals) b**, b ≤ 8, at any list that
                      begins with the front sub-protocol and the eight (FlatAt). Of the letters: upd
                      b = updS P sentU b (Johnson/Desc/K14/Shape/Run.lean). Beside: Eight P; what
                      goes out with o_u; two codes
  returns2            **Returns**, b ≤ 8. Of the letters: guard b gives factsB P b (Facts.lean);
                      vals b gives valsS b. Beside: Eight P; FlatAt; PlanFacts; the two sendings'
                      test on the plan
  values2             **Values T … fall b**, at every b and every fall. Of the letters: valsS b
                      gives vals b. Beside: Plan2; ChainAt T Q c key (AcceptedAt.lean, whose key_at3
                      is called); at b = 3: no seed of a valid input's key has the factor 0
  run2_eq, meetRun2_eq   **the shape's own run returns THE CLOSED FORM**
                      (Johnson/Desc/K14/Shape/End.lean: upTo). Of the letters, AT THE CLOSED FORM
                      ALONE, for each b below n: guard b passes there; upd b is updS Q sentU b
                      there. Nothing on the plan. By the frame's run_of_inv
                      (Honest/Thread/ShapeRun.lean). The second: the like of the frame's run with
                      code
  facts_closed        this kind's test passes at the closed form, at every border b ≤ 9, from a
                      first shape that passes factsB Q 1. Asks: Plan2. By End.lean's facts_upTo;
                      nothing is evaluated
  Z8, z8_carries, z8_run, z8_yes   a term: this kind's letters up to 8; behind them the test is
                      false. Its run from the first state's shape returns endAt; the frame's named
                      public premise up to 9
  nine_members, shape_of_thread   **AT THE THREAD's BORDER 9 THE VERIFIER's STATE HAS THE CLOSED
                      FORM's SHAPE.** Asks: Plan2; ChainAt; a valid input's key has sizes that fit.
                      By the frame's shape_at
  fits_front, accepted_to8   **the frame's rule accepted_of_shape applied at n := 9**: Accepted T
                      fall b for b ≤ 8, at every fall: so the four premises are seen to fit the rule
                      together. Asks: Plan2; ChainAt; a valid input's key has sizes that fit; at b =
                      3 no seed with the factor 0; from b = 1 on FitsAt T b. AT 1 TO 8
                      AcceptedAt.lean's accepted_at GIVES THE SAME FROM LESS; new here: b = 0

With the shape the key's sizes must fit at every member: the shape sees them, so «every first state
has one shape» (the rule's hfirst) holds only where a valid input's key fits. AcceptedAt.lean, which
reads the thread's clause on how the state was made, asks that at "(rec_gamma)" alone.

The numbers 0, 3 and 8 are held against the list of members by stepShape and returns2 under FlatAt
alone. The state of the shared chain has no mark of failure, and its members stand bare in the IOP's
list (Johnson/Desc/K14/Law/SharedFlat.lean): no test on such a mark stands in the shape.

What is not claimed. Shape.Typed: Sh2 is built of structures, not a type of the frame's Plain.
Shape.Blind. Anything at the members 9 to 11: Z8 is no shape for the chain. That every word shown is
below the prime (viewWordsBelowPrime). That the thread holds at any run. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K14.AcceptedAt
import Johnson.Desc.ProofFile.Honest.Thread.ShapeMeet
import Johnson.Desc.K14.Shape.End
import Johnson.Desc.ProofFile.Honest.K14.FitsPaid

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open OnBytes OnBytes.Params
open VerifiableInference.Desc (Block OpenedColumn step_iff)
open VerifiableInference.Desc.Own (keyFits allZero)
open VerifiableInference.Desc.K1 (planOkOwn)
open Desc.K14 (P14 St first withU frontBlock)
open Desc.K14.Honest
open Desc.K14.Shape
open Desc.K14.Law (parU parO)

/-! ## The tests on values; small ones -/

/-- **The named tests on values at the members 0 to 8**: one: at "(rec_gamma)": no seed of the
state's key has the factor 0. -/
def valsS (b : Nat) (s : St) : Bool := if b = 3 then noZeroFactor s.loc.key else true

/-- Where a shape's own step has returned, its test was passed, and it has returned the update. -/
theorem meet_inv {S Sh : Type} {sh : S → Sh} {guard : Nat → Sh → Bool} {upd : Nat → Sh → Sh}
    {vals : Nat → S → List Fmt.RoundView → List (List (Nat × List UInt64)) → Bool} {b : Nat} {a t : Sh}
    (h : (Shape.meet sh guard upd vals).g b a = .ok t) : guard b a = true ∧ t = upd b a := by
  have h' : (if guard b a then Except.ok (upd b a) else Except.error "a guard on the shape" :
    Except String Sh) = .ok t := h
  split at h'
  · exact ⟨by assumption, (Except.ok.inj h').symm⟩
  · cases h'

variable {guard : Nat → Sh2 → Bool} {upd : Nat → Sh2 → Sh2}
  {vals : Nat → St → List Fmt.RoundView → List (List (Nat × List UInt64)) → Bool} {P : P14}
  {sentU : Array OracleNotice} {layO : TreeLay} {Cl : Type}

/-- The groups of columns that a step shows its decide function hang on the declared rounds
alone. -/
theorem shown_like {x : Block St Cl} {b : Block St Unit} (h : Like x b) (ft : Nat)
    (rs : List Fmt.RoundView) (cols : List OpenedColumn) : x.shown ft rs cols = b.shown ft rs cols := by
  unfold Block.shown Block.want
  rw [h.rounds]

/-! ## The frame's three premises at a member b ≤ 8: each law with what it spends of the letters -/

/-- Behind a step of one of the members 0 to 8 the shape is the update of the shape in front. -/
theorem stepShape {bs : List (Block St Cl)} {c : Model.Verify.Chains} (B : Eight P)
    (F : FlatAt bs c B) (hU : withU P.S = some sentU) (hS : P.S.sharedSplitNeeded = true) (ft : Nat)
    (b : Nat) (hb : b ≤ 8) (blk : Block St Cl) (hblk : bs[b]? = some blk) (s s' : St)
    (rs : List Fmt.RoundView) (cols : List OpenedColumn) (n : Nat) (hs : blk.step ft s rs cols = .ok (s', n)) :
    sh2 s' = updS P sentU b (sh2 s) :=
  match b, hb, hblk with
  | 0, _, hblk => by
    have hl := F.at0 hblk
    rw [hl.step] at hs
    have hd := ((step_iff ft (frontBlock c) s s' rs cols n).1 hs).2.1
    have e : s = s' := Except.ok.inj hd
    rw [e]
    rfl
  | 1, _, hblk => by
    have hl := F.at1 hblk
    rw [hl.step] at hs
    exact (stepCarries hU hS B ft s s' rs cols n).1 hs
  | 2, _, hblk => by
    have hl := F.at2 hblk
    rw [hl.step] at hs
    exact (stepCarries hU hS B ft s s' rs cols n).2.1 hs
  | 3, _, hblk => by
    have hl := F.at3 hblk
    rw [hl.step] at hs
    exact (stepCarries hU hS B ft s s' rs cols n).2.2.1 hs
  | 4, _, hblk => by
    have hl := F.at4 hblk
    rw [hl.step] at hs
    exact (stepCarries hU hS B ft s s' rs cols n).2.2.2.1 hs
  | 5, _, hblk => by
    have hl := F.at5 hblk
    rw [hl.step] at hs
    exact (stepCarries hU hS B ft s s' rs cols n).2.2.2.2.1 hs
  | 6, _, hblk => by
    have hl := F.at6 hblk
    rw [hl.step] at hs
    exact (stepCarries hU hS B ft s s' rs cols n).2.2.2.2.2.1 hs
  | 7, _, hblk => by
    have hl := F.at7 hblk
    rw [hl.step] at hs
    exact (stepCarries hU hS B ft s s' rs cols n).2.2.2.2.2.2.1 hs
  | 8, _, hblk => by
    have hl := F.at8 hblk
    rw [hl.step] at hs
    exact (stepCarries hU hS B ft s s' rs cols n).2.2.2.2.2.2.2 hs

/-- **«Carries»** (Honest/Thread/Shape.lean) **at a member b ≤ 8**, at any list that begins with the
front sub-protocol and the eight. OF THE LETTERS IT SPENDS: the update at b is this kind's. -/
theorem carries2 {bs : List (Block St Cl)} {c : Model.Verify.Chains} (B : Eight P)
    (F : FlatAt bs c B) (hU : withU P.S = some sentU) (hS : P.S.sharedSplitNeeded = true) (ft : Nat)
    (b : Nat) (hb : b ≤ 8) (hupd : ∀ a, upd b a = updS P sentU b a) :
    Carries bs ft (Shape.meet sh2 guard upd vals) b := by
  intro blk hblk s rs cols s' n t hs hg
  obtain ⟨-, rfl⟩ := meet_inv hg
  rw [hupd]
  exact (stepShape B F hU hS ft b hb blk hblk s s' rs cols n hs).symm

/-- **«Returns» at a member b ≤ 8.** OF THE LETTERS IT SPENDS: the test at b gives this kind's test;
the tests on values at b give this kind's. A test that asks more is served. -/
theorem returns2 {bs : List (Block St Cl)} {c : Model.Verify.Chains} (B : Eight P)
    (F : FlatAt bs c B) (hP : PlanFacts P.par P.codes sentU layO)
    (hBU : planOkOwn (parU P sentU) = true) (hBO : planOkOwn (parO P) = true) (ft : Nat) (b : Nat)
    (hb : b ≤ 8) (hask : ∀ a, guard b a = true → factsB P b a = true)
    (hval : ∀ s rs gs, vals b s rs gs = true → valsS b s = true) :
    Returns bs ft (Shape.meet sh2 guard upd vals) b := by
  intro blk hblk s rs cols t hg hF hv
  obtain ⟨hgd, -⟩ := meet_inv hg
  have hf : factsB P b (sh2 s) = true := hask _ hgd
  have hvs : valsS b s = true := hval _ _ _ hv
  exact match b, hb, hblk, hf, hvs with
  | 0, _, hblk, _, _ => by
    have hl := F.at0 hblk
    exact ⟨s, by rw [hl.decide]; rfl⟩
  | 1, _, hblk, hf, _ => by
    have hl := F.at1 hblk
    have hst : stateB P 1 (sh2 s) = true := ((factsB_iff P 1 _).1 hf).1
    obtain ⟨d', hd', -⟩ := (state_next hP hBU hBO B ft s rs cols).1 hst (fits_like hl hF)
    refine ⟨d', ?_⟩
    rw [hl.decide, shown_like hl]
    exact ((step_iff ft B.b1 s d' rs cols _).1 hd').2.1
  | 2, _, hblk, hf, _ => by
    have hl := F.at2 hblk
    have hst : stateB P 2 (sh2 s) = true := ((factsB_iff P 2 _).1 hf).1
    obtain ⟨d', hd', -⟩ := (state_next hP hBU hBO B ft s rs cols).2.1 hst (fits_like hl hF)
    refine ⟨d', ?_⟩
    rw [hl.decide, shown_like hl]
    exact ((step_iff ft B.b2 s d' rs cols _).1 hd').2.1
  | 3, _, hblk, hf, hvs => by
    have hl := F.at3 hblk
    have hst : stateB P 3 (sh2 s) = true := ((factsB_iff P 3 _).1 hf).1
    have hv' : (s.loc.key.seeds.all (!allZero ·.beta)) = true := hvs
    obtain ⟨d', hd', -⟩ := (state_next hP hBU hBO B ft s rs cols).2.2.1 hst hv' (fits_like hl hF)
    refine ⟨d', ?_⟩
    rw [hl.decide, shown_like hl]
    exact ((step_iff ft B.b3 s d' rs cols _).1 hd').2.1
  | 4, _, hblk, hf, _ => by
    have hl := F.at4 hblk
    have hst : stateB P 4 (sh2 s) = true := ((factsB_iff P 4 _).1 hf).1
    obtain ⟨d', hd', -⟩ := (state_next hP hBU hBO B ft s rs cols).2.2.2.1 hst (fits_like hl hF)
    refine ⟨d', ?_⟩
    rw [hl.decide, shown_like hl]
    exact ((step_iff ft B.b4 s d' rs cols _).1 hd').2.1
  | 5, _, hblk, hf, _ => by
    have hl := F.at5 hblk
    have hst : stateB P 5 (sh2 s) = true := ((factsB_iff P 5 _).1 hf).1
    obtain ⟨d', hd', -⟩ := (state_next hP hBU hBO B ft s rs cols).2.2.2.2.1 hst (fits_like hl hF)
    refine ⟨d', ?_⟩
    rw [hl.decide, shown_like hl]
    exact ((step_iff ft B.b5 s d' rs cols _).1 hd').2.1
  | 6, _, hblk, hf, _ => by
    have hl := F.at6 hblk
    have hst : stateB P 6 (sh2 s) = true := ((factsB_iff P 6 _).1 hf).1
    obtain ⟨d', hd', -⟩ := (state_next hP hBU hBO B ft s rs cols).2.2.2.2.2.1 hst (fits_like hl hF)
    refine ⟨d', ?_⟩
    rw [hl.decide, shown_like hl]
    exact ((step_iff ft B.b6 s d' rs cols _).1 hd').2.1
  | 7, _, hblk, hf, _ => by
    have hl := F.at7 hblk
    have hst : stateB P 7 (sh2 s) = true := ((factsB_iff P 7 _).1 hf).1
    obtain ⟨d', hd', -⟩ :=
      (state_next hP hBU hBO B ft s rs cols).2.2.2.2.2.2.1 hst (fits_like hl hF)
    refine ⟨d', ?_⟩
    rw [hl.decide, shown_like hl]
    exact ((step_iff ft B.b7 s d' rs cols _).1 hd').2.1
  | 8, _, hblk, hf, _ => by
    have hl := F.at8 hblk
    have hst : stateB P 8 (sh2 s) = true := ((factsB_iff P 8 _).1 hf).1
    obtain ⟨d', hd'⟩ := (state_next hP hBU hBO B ft s rs cols).2.2.2.2.2.2.2 hst (fits_like hl hF)
    refine ⟨d', ?_⟩
    rw [hl.decide, shown_like hl]
    exact ((step_iff ft B.b8 s d' rs cols _).1 hd').2.1

variable {Bk : ProverCoinCounts} {V W X Pb : Type} {Q : P14} {T : Thread Bk St Cl V W X Pb}
  {c : Model.Verify.Chains} {key : W → TableKey}
  {fall : Nat → St → List Fmt.Drawn → Option String}

/-- **«Values» at every member b**, at every thread that begins as ChainAt says, and at every fall;
at b = 3: where no seed of a valid input's key has the factor 0. OF THE LETTERS IT SPENDS: this
kind's tests on values at b give the tests on values at b. -/
theorem values2 (hQ : Plan2 Q sentU layO) (hT : ChainAt T Q c key) (b : Nat)
    (hseeds : b = 3 → ∀ w, T.valid w → noZeroFactor (key w) = true)
    (hval : ∀ s rs gs, valsS b s = true → vals b s rs gs = true) :
    Values T (Shape.meet sh2 guard upd vals) fall b := by
  intro blk _ k s m E ds y cols hA _ _ _ _
  show vals b s _ _ = true
  refine hval _ _ _ ?_
  unfold valsS
  by_cases h3 : b = 3
  · subst h3
    rw [if_pos rfl, key_at3 hQ hT hA]
    exact hseeds rfl _ hA.2.2.2.2.2.2
  · rw [if_neg h3]

/-! ## The shape's own run up to the border behind the eight, in closed form -/

/-- **THE SHAPE's OWN RUN RETURNS THE CLOSED FORM** (Johnson/Desc/K14/Shape/End.lean: upTo). OF THE
LETTERS IT SPENDS, AT THE CLOSED FORM ALONE, one shape a member below n: the test passes there; the
update is this kind's there. Nothing on the plan. -/
theorem run2_eq (a₀ : Sh2) (n : Nat) (hpass : ∀ b, b < n → guard b (upTo Q sentU b a₀) = true)
    (hupd : ∀ b, b < n → upd b (upTo Q sentU b a₀) = updS Q sentU b (upTo Q sentU b a₀)) :
    (Shape.meet sh2 guard upd vals).run n a₀ = .ok (upTo Q sentU n a₀) := by
  obtain ⟨e, he, hi⟩ := run_of_inv (Shape.meet sh2 guard upd vals)
    (fun b (a : Sh2) => a = upTo Q sentU b a₀) n a₀ rfl (fun b hb a ha => by
      have ha' : a = upTo Q sentU b a₀ := ha
      subst ha'
      exact ⟨upd b (upTo Q sentU b a₀), meet_g_ok sh2 guard upd vals (hpass b hb), hupd b hb⟩)
  have hi' : e = upTo Q sentU n a₀ := hi
  rw [he, hi']

/-- The like of the frame's run with code (Honest/Thread/ShapeMeet.lean: meetRun). -/
theorem meetRun2_eq (a₀ : Sh2) (n : Nat) (hpass : ∀ b, b < n → guard b (upTo Q sentU b a₀) = true)
    (hupd : ∀ b, b < n → upd b (upTo Q sentU b a₀) = updS Q sentU b (upTo Q sentU b a₀)) :
    meetRun guard upd 0 n a₀ = some (upTo Q sentU n a₀) := by
  rw [← meet_runFrom sh2 guard upd (fun _ _ _ _ => true) 0 n a₀, runFrom_zero,
    run2_eq a₀ n hpass hupd]
  rfl

/-- **This kind's test passes at the closed form, at every border b ≤ 9**, from a first shape that
passes the test at the border 1. By the law on shapes; nothing is evaluated. -/
theorem facts_closed (hQ : Plan2 Q sentU layO) (a₀ : Sh2) (h : factsB Q 1 a₀ = true) (b : Nat)
    (hb : b ≤ 9) : factsB Q b (upTo Q sentU b a₀) = true := by
  obtain ⟨B⟩ := hQ.eight
  match b, hb with
  | 0, _ => rfl
  | b + 1, hb => exact facts_upTo hQ.facts hQ.planU hQ.planO B a₀ h b (by omega)

/-! ## A term, what a thread's state is at the border 9, and the frame's rule applied -/

/-- **The shape that rejects from the member 9 on**: this kind's test, update and tests on values up
to 8; behind them the test is false. It is here so that the frame's laws can be applied. -/
def Z8 (Q : P14) (sentU : Array OracleNotice) : Shape St :=
  Shape.meet sh2 (fun b a => decide (b ≤ 8) && factsB Q b a) (updS Q sentU) fun b s _ _ => valsS b s

/-- «Carries» of that term at every member: up to 8 by carries2; behind, its test is false. -/
theorem z8_carries (hQ : Plan2 Q sentU layO) (hT : ChainAt T Q c key) (j : Nat) :
    Carries T.bs T.ft (Z8 Q sentU) j := by
  obtain ⟨B⟩ := hQ.eight
  by_cases hj : j ≤ 8
  · exact carries2 B (hT.bs B) hQ.facts.goes hQ.facts.two T.ft j hj fun _ => rfl
  · intro blk _ s rs cols s' n t _ hg
    obtain ⟨hgd, -⟩ := meet_inv hg
    simp [hj] at hgd

/-- Its run from the first state's shape, at every key whose sizes fit, returns endAt. -/
theorem z8_run (hQ : Plan2 Q sentU layO) (k : TableKey)
    (hk : keyFits k Q.par.S.fold.index = true) :
    (Z8 Q sentU).run 9 (sh2 (first Q.codes k)) = .ok (endAt Q sentU k) :=
  run2_eq _ 9 (fun b hb => by
    simp [Nat.le_of_lt_succ hb, facts_closed hQ _ (facts_start Q k hk) b (Nat.le_of_lt hb)])
    fun _ _ => rfl

/-- So the frame's named public premise holds up to that border. -/
theorem z8_yes (hQ : Plan2 Q sentU layO) (k : TableKey)
    (hk : keyFits k Q.par.S.fold.index = true) :
    (Z8 Q sentU).yes (sh2 (first Q.codes k)) 9 = true := by
  unfold Shape.yes
  rw [z8_run hQ k hk]
  rfl

/-- The thread's list has the front sub-protocol and the eight. -/
theorem nine_members (hQ : Plan2 Q sentU layO) (hT : ChainAt T Q c key) : 9 ≤ T.bs.length := by
  obtain ⟨B⟩ := hQ.eight
  obtain ⟨x0, x1, x2, x3, x4, x5, x6, x7, x8, tl, e, -⟩ := hT.bs B
  rw [e]
  simp

/-- **AT THE THREAD's BORDER 9 THE VERIFIER's STATE HAS THE CLOSED FORM's SHAPE.** The closed form
is taken at the written key of the plan's sizes: it reads of a key the sizes alone. -/
theorem shape_of_thread (hQ : Plan2 Q sentU layO) (hT : ChainAt T Q c key)
    (hkey : ∀ w, T.valid w → keyFits (key w) Q.par.S.fold.index = true) {k : Coins Bk} {s : St}
    {m : Mid W X} {E : Env} (hA : Thr T 9 k s m E) :
    sh2 s = endAt Q sentU (keyW Q.par.S.fold.index) := by
  have hr := shape_at T (Z8 Q sentU) (a₀ := sh2 (firstW Q)) (n := 9) (b := 9) (nine_members hQ hT)
    (Nat.le_refl 9) (z8_yes hQ (keyW Q.par.S.fold.index) (key_fits Q.par.S.fold.index))
    (fun k w h s₀ hv hbeg => by
      rw [hT.begun _ _ _ _ hbeg]
      exact first_shape Q (key w) (hkey w hv))
    (z8_carries hQ hT) hA
  exact Except.ok.inj
    (hr.symm.trans (z8_run hQ (keyW Q.par.S.fold.index) (key_fits Q.par.S.fold.index)))

/-- The front sub-protocol declares no round: what was played passes its step's own tests. -/
theorem fits_front (hQ : Plan2 Q sentU layO) (hT : ChainAt T Q c key) : FitsAt T 0 := by
  obtain ⟨B⟩ := hQ.eight
  exact fitsAt_none fun blk hblk => by
    rw [((hT.bs B).at0 hblk).rounds]
    rfl

/-- **THE FRAME's RULE (accepted_of_shape, Honest/Thread/Shape.lean) APPLIED AT THE MEMBERS 0 TO
8**: so the four premises are seen to fit it together. -/
theorem accepted_to8 (hQ : Plan2 Q sentU layO) (hT : ChainAt T Q c key)
    (hkey : ∀ w, T.valid w → keyFits (key w) Q.par.S.fold.index = true)
    (b : Nat) (hb : b ≤ 8) (hseeds : b = 3 → ∀ w, T.valid w → noZeroFactor (key w) = true)
    (hF : 1 ≤ b → FitsAt T b) : Accepted T fall b := by
  obtain ⟨B⟩ := hQ.eight
  have hF' : FitsAt T b := by
    by_cases h0 : b = 0
    · subst h0
      exact fits_front hQ hT
    · exact hF (by omega)
  refine accepted_of_shape T (Z8 Q sentU) (a₀ := sh2 (firstW Q)) (n := 9) (nine_members hQ hT)
    (by omega) (z8_yes hQ (keyW Q.par.S.fold.index) (key_fits Q.par.S.fold.index))
    (fun k w h s₀ hv hbeg => ?_) (z8_carries hQ hT)
    (returns2 B (hT.bs B) hQ.facts hQ.planU hQ.planO T.ft b hb
      (fun a h => by simpa [hb] using h) fun _ _ _ h => h) hF'
    (values2 hQ hT b hseeds fun _ _ _ h => h)
  rw [hT.begun _ _ _ _ hbeg]
  exact first_shape Q (key w) (hkey w hv)

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.meet_inv
#print axioms ProofFile.Honest.K14.shown_like
#print axioms ProofFile.Honest.K14.stepShape
#print axioms ProofFile.Honest.K14.carries2
#print axioms ProofFile.Honest.K14.returns2
#print axioms ProofFile.Honest.K14.values2
#print axioms ProofFile.Honest.K14.run2_eq
#print axioms ProofFile.Honest.K14.meetRun2_eq
#print axioms ProofFile.Honest.K14.facts_closed
#print axioms ProofFile.Honest.K14.z8_carries
#print axioms ProofFile.Honest.K14.z8_run
#print axioms ProofFile.Honest.K14.z8_yes
#print axioms ProofFile.Honest.K14.nine_members
#print axioms ProofFile.Honest.K14.shape_of_thread
#print axioms ProofFile.Honest.K14.fits_front
#print axioms ProofFile.Honest.K14.accepted_to8
