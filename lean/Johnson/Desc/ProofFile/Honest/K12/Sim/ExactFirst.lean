-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/Sim/ExactFirst.lean: the frame's sentence `ExactMember`
(Johnson/Desc/ProofFile/Honest/Small/Field.lean: the text of the field `exact` of `Good`,
Honest/Side.lean, at one member) at the first member of a proximity test (`firstMember`,
Sim/Row.lean; its simulator's form: `firstSim`, Sim/Sims.lean), where the first fold's fresh table
has come earlier; at a state on entry that is made of the plan's public part, not shown to be the
verifier's. For every `On` and every `bud`: nothing is asked of the run. Under hypotheses on public
numbers alone.

What it says. The part takes no coin of its own; it spends a lent run of 2 k + 1 coins, the first
fold's hiding polynomial's coefficients. Played alone by the frame's own play, over these coins, at
every input, front, carried coins and challenges of the declared form, it shows "BAT" (nothing) and
2 k + 1 scalars whose law is that of what the written simulator yields: 2 k + 1 coins of its own,
laid in the rounds' order.

What it is worth: little by itself. The sentence samples the spent run afresh and looks at this
part's rounds alone. By the book these coefficients are meant to stand elsewhere in a run too:
packed into the fresh table, whose symbols stand in its sender's tree and are opened at the first
reading round's positions; and the second part carries them and folds that table's row and tail into
its new message. That these do not add up to more is the owner's sentence at the sender's member,
and clauses on the book (`OwnerDebt`, Sim/Spec.lean), which no sentence reads. The sentences at the
second member (Sim/ExactFree.lean) hold these coins fixed; nothing here joins the two.

By what. `shows_first` (Sim/ShowsFirst.lean), `fold_law` (Sim/FoldLaw.lean), and unfolding the
simulator's text.

  `getD_rep`, `depthAt_first`   no round of the first part is stated to send a tree
  `first_text`     what is shown of the term's first rounds is the first fold's 2 k + 1 values, laid
  `FirstPub`       what is asked, all of it public
  `take_laidAs`, `tells_first`   what the simulator yields
  `allSome`, `pairSome`, `tripleSome`, `map_spent`   what a part is handed afresh is not empty
                 (three local instances); how the spent run is sampled
  `exact_first`    the statement

Limits.
- It stands at a state on entry that is made of the plan's public part, not shown to be the
  verifier's: the job's state function is a letter, and what the first fold shows is computed from
  it.
- It is shown at no job that is played.
- It speaks of the parts of `proverSideOfProximityTest` (Parts.lean), not of the guarded halves (PartsByJob.lean).
- What the parts send is `testAll` (Johnson/Desc/ProofFile/Honest/K12/Test.lean), cut into parts in
  Parts.lean, over the random values of Coins.lean, both beside it. How far `testAll` is tied to the
  library's `bodyAll` is said in Test.lean's limits.
- It is the spender's half: see "What it is worth".
- Not where the fold sends its own table.
- Asked, all public: the job says that the table has come earlier; and `FirstPub`'s five: the two
  jobs stand at one place; the simulators' job says the same of the table; `formPubB` (two stages or
  more; h ≤ k at the first; the declared rounds ask the sorts that the term shows); the place has at
  least as many declared rounds as the part has moves; `tablesFitB`. Where the three on numbers are
  shown: Sim/ExactFirstKR.lean, Sim/ExactFirstAtU.lean, Sim/FirstPubAtHead.lean. "The table has come
  earlier" holds at seven of the library's nine closed places (Sim/ReachAt.lean).
- σ is a free letter, and `firstMember J Js` is the member as written out. That a seated side has
  it: `members_of_seat` (Sim/ExactSide.lean).
- It is not `Spec.exactFirst` (Sim/Spec.lean): other ties, one arm; neither gives the other.
- "Every bud" is cheap: the part sends no tree. No premise is bent here: no negative test.
- An honest verifier; fixed challenges; one part; at the level of oracle messages: no root, salt or
  hash. Nothing on completeness or on soundness.
-/
import Johnson.Desc.ProofFile.Honest.K12.Sim.ShowsFirst
import Johnson.Desc.ProofFile.Honest.K12.Sim.FoldLaw
import Johnson.Desc.ProofFile.Honest.K12.Sim.ExactPlan

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace ProofFile.Honest.K12
open OnBytes OnBytes.Params OnBytes.Slice Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.JointK
open Johnson.Prover.Link
open H2K.Pub (sgOf)
open ProofFile.Honest.Small (ExactMember)

attribute [local instance] csNonempty

/-- What a part is handed afresh is not empty. Said outright; no global instances. -/
local instance allSome (l : List (String × Due)) : Nonempty (CsAll l) := ⟨default⟩
local instance pairSome (d : Due) (l : List (String × Due)) : Nonempty (Cs d × CsAll l) :=
  ⟨(default, default)⟩
local instance tripleSome (d d' : Due) (l : List (String × Due)) :
    Nonempty (Cs d × (Cs d' × CsAll l)) := ⟨(default, default, default)⟩

variable {S Cl V W X Pb : Type}

/-! ## 1 The text -/

theorem getD_rep : ∀ (k i : ℕ) (L : List (Option ℕ)), i < k →
    (List.replicate k (none : Option ℕ) ++ L).getD i none = none
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | k + 1, 0, L, _ => by rw [List.replicate_succ, List.cons_append, List.getD_cons_zero]
  | k + 1, i + 1, L, h => by
    rw [List.replicate_succ, List.cons_append, List.getD_cons_succ]
    exact getD_rep k i L (Nat.lt_of_succ_lt_succ h)

/-- No round of the first part is stated to send a tree. -/
theorem depthAt_first (J : TestJob W X) (hfr : J.fresh.isNone = false) (s next : Fmt.M1.Stage)
    (rest : List Fmt.M1.Stage) (hst : J.p.nums.stages = s :: next :: rest) (i : ℕ)
    (hi : i < 2 + s.k) : depthAt J i = none := by
  unfold depthAt
  rw [hfr, hst]
  simp only [depths, Bool.false_eq_true, if_false, List.cons_append, List.append_assoc]
  match i, hi with
  | 0, _ => rfl
  | 1, _ => rfl
  | j + 2, hj =>
    rw [List.getD_cons_succ, List.getD_cons_succ]
    exact getD_rep s.k j _ (by omega)

/-- **What is shown of the term's first rounds.** -/
theorem first_text (J : TestJob W X) (hfr : J.fresh.isNone = false) (s next : Fmt.M1.Stage)
    (rest : List Fmt.M1.Stage) (hst : J.p.nums.stages = s :: next :: rest)
    (hk : s.k = (sgOf s).h + (sgOf s).g) (w : W) (fr : Front X) (K : TestCoins)
    (D : ℕ → Fmt.Drawn) (asks : List (List (List ℕ))) :
    shownFrom (testAll J w fr K D) (depthAt J) (firstLen J.p.nums.stages) asks =
      laidAs ((sgOf s).h + (sgOf s).g)
        (foldVals (sgOf s) (vecG (sgOf s) (rowOf (J.recB w fr (D 0))))
          (μOf (sgOf s) (J.rows₀ w fr K.mem)) (fun n => D (1 + n))
          (hideAt ((sgOf s).h + (sgOf s).g) K.hide)) := by
  have hn : firstLen J.p.nums.stages = 2 + s.k := by rw [hst]; rfl
  have hlen : ((⟨[], D 0⟩ : Fmt.RoundView) :: aFold (coinsOf (s :: next :: rest) K.hide K.rest) 0 s 1
      (J.first w fr K) (rowOf (J.recB w fr (D 0))) D).length = firstLen J.p.nums.stages := by
    rw [List.length_cons, length_aFold, hn, hk]
    omega
  rw [← hlen, shown_prefix (testAll J w fr K D) _ (restOf J w fr K D s next rest).rs
    (by rw [testAll_cut J w fr K D s next rest hst]; rfl) (depthAt J)
    (fun i hi => depthAt_first J hfr s next rest hst i (by rw [hlen, hn] at hi; exact hi)) asks]
  exact foldShown_shown (sgOf s) _ _ (fun n => D (1 + n)) _ (D 0)

/-! ## 2 What is asked; the simulator -/

/-- **What is asked, all of it public.** -/
structure FirstPub (J : TestJob W X) (Js : SimJob Pb) : Prop where
  place : Js.p = J.p
  own : Js.own = false
  form : formPubB J.p = true
  enough : firstLen J.p.nums.stages ≤ (laidOf J.p).length
  tables : tablesFitB J = true

theorem take_laidAs (k : ℕ) (x : ℕ → GE) : (laidAs k x).take (2 + k) = laidAs k x :=
  List.take_of_length_le (by simp [laidAs]; omega)

/-- **What the simulator yields.** -/
theorem tells_first (p : P12) (r₀ : Pb → Before → T12) (op : List (ℕ × ℕ × ℕ))
    (s next : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (hst : p.nums.stages = s :: next :: rest)
    (pb : Pb) (front : Before) (ds : List Fmt.Drawn) (asks : List (List (List ℕ)))
    (c : Cs (firstSim (⟨p, false, r₀, op⟩ : SimJob Pb)).takes) :
    (firstSim (⟨p, false, r₀, op⟩ : SimJob Pb)).tell pb front ds asks c =
      some (laidAs s.k (stretchOf c).e) := by
  have h0 : (⟨p, false, r₀, op⟩ : SimJob Pb).s₀ = s := by
    show p.nums.stages.headD default = s
    rw [hst]
    rfl
  have hn : firstLen (⟨p, false, r₀, op⟩ : SimJob Pb).stages = 2 + s.k := by
    show firstLen p.nums.stages = _
    rw [hst]
    rfl
  show some ((laidAs (⟨p, false, r₀, op⟩ : SimJob Pb).s₀.k (stretchOf c).e).take
    (firstLen (⟨p, false, r₀, op⟩ : SimJob Pb).stages)) = _
  rw [hn, h0, take_laidAs]

/-- The law of the spent run, out of the law of all that the part is handed afresh. -/
theorem map_spent (x : String × Due) :
    (Prob.unif (Cs ⟨0, 0⟩ × CsAll [x])).map (fun c => (c.2 : Cs x.2 × CsAll []).1) =
      Prob.unif (Cs x.2) := by
  have h1 : (Prob.unif (Cs ⟨0, 0⟩ × (Cs x.2 × CsAll []))).map Prod.snd =
      Prob.unif (Cs x.2 × CsAll []) := Prob.map_snd_unif
  have h2 : (Prob.unif (Cs x.2 × CsAll [])).map Prod.fst = Prob.unif (Cs x.2) := Prob.map_fst_unif
  exact (PMF.map_comp (Prod.snd : Cs ⟨0, 0⟩ × (Cs x.2 × CsAll []) → Cs x.2 × CsAll []) _
    Prod.fst).symm.trans ((congrArg (PMF.map Prod.fst) h1).trans h2)

/-! ## 3 The statement -/

/-- **THE FRAME's SENTENCE AT THE FIRST MEMBER, WHERE THE FRESH TABLE HAS COME EARLIER: AT EVERY On
AND bud.** -/
theorem exact_first (φ : Face V W Pb) (σ : Side S Cl V W X Pb) (J : TestJob W X) (Js : SimJob Pb)
    (chain firstTree : ℕ)
    (On : (u : Member V W X Pb) → CsAll u.part.carries → Mid W X → Before → Prop)
    (bud : ℕ → List Fmt.Drawn → List (List (List ℕ)) → Prop) (hfr : J.fresh.isNone = false)
    (T : FirstPub J Js) : ExactMember φ σ chain firstTree On bud (firstMember J Js) := by
  obtain ⟨p, ms, fresh, r0, ro, tr⟩ := J
  obtain ⟨p', own, r0', op⟩ := Js
  obtain ⟨hp, ho, hform, hen, htab⟩ := T
  simp only at hp ho hfr
  subst hp ho
  cases fresh with
  | none => simp at hfr
  | some f =>
    -- the stages
    obtain ⟨s, next, rest, hst⟩ : ∃ s next rest, p'.nums.stages = s :: next :: rest := by
      unfold formPubB at hform
      simp only at hform
      cases hs : p'.nums.stages with
      | nil => rw [hs] at hform; cases hform
      | cons a l =>
        cases l with
        | nil => rw [hs] at hform; cases hform
        | cons b r => exact ⟨a, b, r, rfl⟩
    have FP := formPub_of_B p' s next rest hst hform
    have hk : s.k = (sgOf s).h + (sgOf s).g := by
      have := FP.hk
      show s.k = s.h + (s.k - s.h)
      omega
    have h0 : (⟨p', ms, some f, r0, ro, tr⟩ : TestJob W X).s₀ = s := by
      show p'.nums.stages.headD default = s
      rw [hst]
      rfl
    intro ca m front ds asks _ _ hfit _ _ _
    have hlen : ds.length = firstLen p'.nums.stages := by
      have h := drawsFit_length _ _ hfit
      rw [h, List.length_map]
      show ((laidOf p').take _).length = _
      rw [List.length_take]
      exact Nat.min_eq_left hen
    have FT : FirstTies (⟨p', ms, some f, r0, ro, tr⟩ : TestJob W X) s next rest (byNo ds) ds :=
      ⟨hst, hen, FP.sorts, htab, hlen, fun n h => (List.getD_eq_getElem _ _ h).symm⟩
    -- the left side
    have hL : (fun c : Cs ⟨0, 0⟩ × CsAll [spentRun (⟨p', ms, some f, r0, ro, tr⟩ : TestJob W X)] =>
        σ.shows φ (firstMember (⟨p', ms, some f, r0, ro, tr⟩ : TestJob W X)
          (⟨p', false, r0', op⟩ : SimJob Pb)) (c.1, c.2, ca) m ds asks) =
        (fun x : Cs (spentRun (⟨p', ms, some f, r0, ro, tr⟩ : TestJob W X)).2 =>
          some (laidAs ((sgOf s).h + (sgOf s).g)
            (foldVals (sgOf s)
              (vecG (sgOf s) (rowOf ((⟨p', ms, some f, r0, ro, tr⟩ : TestJob W X).recB m.st.input
                (frontBy m 0) (byNo ds 0))))
              (μOf (sgOf s) (ro m.st.input (frontBy m 0) (stretches _ ca)))
              (fun n => byNo ds (1 + n)) (hideAt ((sgOf s).h + (sgOf s).g) (stretchOf x).e)))) ∘
          fun c => (c.2 : Cs (spentRun (⟨p', ms, some f, r0, ro, tr⟩ : TestJob W X)).2 ×
            CsAll []).1 := by
      funext c
      rw [shows_first φ σ _ _ s next rest m (byNo ds) ds FT (c.1, c.2, ca) asks,
        first_text _ rfl s next rest hst hk]
      rfl
    have hR : (fun c : Cs (firstSim (⟨p', false, r0', op⟩ : SimJob Pb)).takes =>
        (firstMember (⟨p', ms, some f, r0, ro, tr⟩ : TestJob W X)
          (⟨p', false, r0', op⟩ : SimJob Pb) : Member V W X Pb).tells φ c m.st.input front ds
          asks) = fun c => some (laidAs s.k (stretchOf c).e) :=
      funext fun c => tells_first p' r0' op s next rest hst _ front ds asks c
    have hd : (spentRun (⟨p', ms, some f, r0, ro, tr⟩ : TestJob W X)).2 =
        ⟨0, 2 * ((sgOf s).h + (sgOf s).g) + 1⟩ := by
      show (⟨0, 2 * (⟨p', ms, some f, r0, ro, tr⟩ : TestJob W X).s₀.k + 1⟩ : Due) = _
      rw [h0, ← hk]
    have hd' : (firstSim (⟨p', false, r0', op⟩ : SimJob Pb)).takes =
        ⟨0, 2 * ((sgOf s).h + (sgOf s).g) + 1⟩ := by
      show (⟨0, 2 * (p'.nums.stages.headD default).k + 1⟩ : Due) = _
      rw [hst, ← hk]
      rfl
    have hlaw := congrArg (PMF.map some) (fold_law (sgOf s)
      (vecG (sgOf s) (rowOf ((⟨p', ms, some f, r0, ro, tr⟩ : TestJob W X).recB m.st.input
        (frontBy m 0) (byNo ds 0))))
      (μOf (sgOf s) (ro m.st.input (frontBy m 0) (stretches _ ca))) fun n => byNo ds (1 + n))
    rw [PMF.map_comp, PMF.map_comp] at hlaw
    show PMF.map (fun c : Cs ⟨0, 0⟩ ×
        CsAll [spentRun (⟨p', ms, some f, r0, ro, tr⟩ : TestJob W X)] =>
        σ.shows φ (firstMember (⟨p', ms, some f, r0, ro, tr⟩ : TestJob W X)
          (⟨p', false, r0', op⟩ : SimJob Pb)) (c.1, c.2, ca) m ds asks)
        (Prob.unif (Cs ⟨0, 0⟩ × CsAll [spentRun (⟨p', ms, some f, r0, ro, tr⟩ : TestJob W X)])) =
      PMF.map (fun c : Cs (firstSim (⟨p', false, r0', op⟩ : SimJob Pb)).takes =>
        (firstMember (⟨p', ms, some f, r0, ro, tr⟩ : TestJob W X)
          (⟨p', false, r0', op⟩ : SimJob Pb) : Member V W X Pb).tells φ c m.st.input front ds
          asks) (Prob.unif (Cs (firstSim (⟨p', false, r0', op⟩ : SimJob Pb)).takes))
    rw [hL, hR, ← PMF.map_comp, map_spent, hk]
    exact (map_stretch hd fun x => some (laidAs ((sgOf s).h + (sgOf s).g)
        (foldVals (sgOf s)
          (vecG (sgOf s) (rowOf ((⟨p', ms, some f, r0, ro, tr⟩ : TestJob W X).recB m.st.input
            (frontBy m 0) (byNo ds 0))))
          (μOf (sgOf s) (ro m.st.input (frontBy m 0) (stretches _ ca)))
          (fun n => byNo ds (1 + n)) (hideAt ((sgOf s).h + (sgOf s).g) x)))).trans
      (hlaw.trans (map_stretch hd' fun x => some (laidAs ((sgOf s).h + (sgOf s).g) x)).symm)

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.allSome
#print axioms ProofFile.Honest.K12.pairSome
#print axioms ProofFile.Honest.K12.tripleSome
#print axioms ProofFile.Honest.K12.FirstPub
#print axioms ProofFile.Honest.K12.getD_rep
#print axioms ProofFile.Honest.K12.depthAt_first
#print axioms ProofFile.Honest.K12.first_text
#print axioms ProofFile.Honest.K12.take_laidAs
#print axioms ProofFile.Honest.K12.tells_first
#print axioms ProofFile.Honest.K12.map_spent
#print axioms ProofFile.Honest.K12.exact_first
