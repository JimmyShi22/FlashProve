-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/Sim/ExactFirstOwn.lean: the frame's sentence `ExactMember`
(Johnson/Desc/ProofFile/Honest/Small/Field.lean: the text of the field `exact` of `Good`,
Honest/Side.lean, at one member) at a proximity test's first member (`firstMember`, Sim/Row.lean),
where the first fold sends its own fresh table. For every `On`; at the bound `budBoth` on the
positions asked; under hypotheses on public numbers alone.

What it says. The part takes 2 k + 1 + 2 ^ h · r random values of its own: the coefficients of the
first fold's hiding polynomial, and a tail of r entries for each of the fresh table's 2 ^ h rows. It
spends none. Played alone by the frame's own play, over these values, at every input, front, carried
values and challenges of the declared form, it shows "BAT" (nothing), 2 k + 1 scalars, and the
table's 2 ^ h symbols at each position asked. Where the positions asked are in range and at most r
different ones, that has the distribution of what `firstSim` (Sim/Sims.lean) yields over as many
values of its own: the same text at an empty claim and at rows 0. `firstSim` reads neither the
input's public part nor the front, by its text (`fun _ _ ds asks c`, Sim/Sims.lean).

  `budBoth`      one bound for both members: at the first `budFirst` (Sim/Row.lean), where the fold
                 sends its own table; at the second `budOpened` (Sim/ExactPlan.lean)
  `FirstPubOwn`   what is asked, all of it public
  `shown_take`   what is shown of the first n rounds of two outputs is the same where their first n
                 rounds and trees are
  `own_text`     what is shown of `testAll`'s first rounds is what is shown of `ownText`
                 (Sim/ExactFirstOwnLaw.lean)
  `exact_first_job`   the statement at a `TestJob`
  `exact_first_own`   the statement at the job of a `ManyJob` (RunMany.lean)

By what. `shows_first` (Sim/ShowsFirst.lean), `testAll_rs` and `testAll_tr` (KeptLaw4.lean),
`own_law` (Sim/ExactFirstOwnLaw.lean).

Grade. Theorems: the law within the bound (`own_law`, Sim/ExactFirstOwnLaw.lean); a member of the
sentence at the full size, under the library's head, at written letters (`meets_head_O`,
Sim/MeetsOwnAtHead.lean). Said here without a theorem: at one position more than the bound allows
the distribution is another; at as many positions as the bound allows no random value is to spare;
one random value fewer will not do.

Limits.
- It stands at a state on entry that is made of the plan's public part, not shown to be the
  verifier's: the job's state function is a parameter, and what the first fold shows is computed
  from it.
- It is shown at no job that is played. σ is a variable, and `firstMember J Js` is the member as it
  is written out: that a seated side has it is `members_of_seat` (Sim/ExactSide.lean).
- It speaks of the parts of `proverSideOfProximityTest` (Parts.lean), not of the guarded halves (PartsByJob.lean).
- What the parts send is `testAll` (Johnson/Desc/ProofFile/Honest/K12/Test.lean), cut into parts in
  Parts.lean, over the random values of Coins.lean, both beside it. How far `testAll` is tied to the
  library's `bodyAll` is said in Test.lean's limits.
- The bound is a hypothesis, and the proof uses it. It counts all positions that are asked of the
  tree. It is shown at no list of positions that the frame lays: not for the test's own first
  reading round, and that no other round of the file reads that tree is shown by nobody.
- By the book these coefficients and tails are meant to be carried by the test's second part.
  Nothing here joins the two members.
- At r different positions as many values are shown as are sampled, 2 k + 1 + 2 ^ h · r. That is a
  count, no theorem that so many are needed.
- The field `rest` of what the part's moves read is the constant 0, no random value; what is shown
  of the first part's rounds does not depend on it (`own_text` holds at every value of it).
- An honest verifier; fixed challenges; one part; at the level of oracle messages: no root, salt or
  hash. No file of this folder states a security property by itself. Nothing on completeness,
  soundness or hiding.
Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.Sim.ExactFirstOwnLaw
import Johnson.Desc.ProofFile.Honest.K12.Sim.ExactFirst
import Johnson.Desc.ProofFile.Honest.K12.KeptLaw4
import Johnson.Desc.ProofFile.Honest.K12.RunMany

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace ProofFile.Honest.K12.Light
open OnBytes.Slice Cb
open VerifiableInference.Desc.K12 (P12 T12)
open H2K.JointK (laidOf)
open Johnson.Prover.Link
open H2K.Pub (sgOf)
open ProofFile.Honest.Small (ExactMember)

variable {S Cl V W X Pb : Type}

/-! ## 1 What is asked -/

/-- **One bound for both members.** -/
def budBoth (Js : SimJob Pb) (n : ℕ) (ds : List Fmt.Drawn) (asks : List (List (List ℕ))) : Prop :=
  (n = 0 → Js.own = true → budFirst Js.s₀ asks = true) ∧ budOpened Js.p.nums.stages n ds asks

/-- **What is asked, all of it public.** -/
structure FirstPubOwn (J : TestJob W X) (Js : SimJob Pb) : Prop where
  place : Js.p = J.p
  own : Js.own = true
  form : formPubB J.p = true
  enough : firstLen J.p.nums.stages ≤ (laidOf J.p).length
  tables : tablesFitB J = true
  points : J.s₀.Z.a ≤ 32

/-! ## 2 The text -/

theorem shown_take (O O' : BOut) (dep : ℕ → Option ℕ) (n : ℕ) (asks : List (List (List ℕ)))
    (hrs : O.rs.take n = O'.rs.take n) (htr : O.tr.take n = O'.tr.take n) :
    shownFrom O dep n asks = shownFrom O' dep n asks := by
  unfold shownFrom
  refine List.map_congr_left fun i hi => ?_
  have hi' : i < n := List.mem_range.1 hi
  have h1 : O.rs[i]? = O'.rs[i]? := by
    rw [← List.getElem?_take_of_lt hi', hrs, List.getElem?_take_of_lt hi']
  have h2 : O.tr[i]? = O'.tr[i]? := by
    rw [← List.getElem?_take_of_lt hi', htr, List.getElem?_take_of_lt hi']
  unfold sendingOf
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, h1, h2]

/-- **What is shown of the test's first rounds**, where the fold sends its own table. -/
theorem own_text (J : TestJob W X) (hfr : J.fresh.isNone = true) (s next : Fmt.M1.Stage)
    (rest : List Fmt.M1.Stage) (hst : J.p.nums.stages = s :: next :: rest) (hk : s.h ≤ s.k) (w : W)
    (fr : Front X) (c : ℕ → GE) (mem : ℕ → Stretch) (rs : ℕ → GE) (D : ℕ → Fmt.Drawn)
    (dep : ℕ → Option ℕ) (asks : List (List (List ℕ))) :
    shownFrom (testAll J w fr ⟨c, tailsIn s c, mem, rs⟩ D) dep (s.k + 2) asks =
      shownFrom (ownText s (vecG (sgOf s) (rowOf (J.recB w fr (D 0))))
        (μOf (sgOf s) (J.rows₀ w fr mem)) c D) dep (s.k + 2) asks := by
  have hl : (ownText s (vecG (sgOf s) (rowOf (J.recB w fr (D 0))))
      (μOf (sgOf s) (J.rows₀ w fr mem)) c D).rs.length = s.k + 2 := by
    show (firstFold (s :: next :: rest) J w fr ⟨c, tailsIn s c, mem, rs⟩ D s).length + 1 = _
    rw [firstFold_length _ J w fr _ D s hk]
  have hl' : (ownText s (vecG (sgOf s) (rowOf (J.recB w fr (D 0))))
      (μOf (sgOf s) (J.rows₀ w fr mem)) c D).tr.length = s.k + 2 := by
    show (((firstFold (s :: next :: rest) J w fr ⟨c, tailsIn s c, mem, rs⟩ D s).map
      fun (_ : Fmt.RoundView) (_ : ℕ) => ([] : List UInt64)).set 0 _).length + 1 = _
    rw [List.length_set, List.length_map, firstFold_length _ J w fr _ D s hk]
  have h0 : J.s₀ = s := by
    unfold TestJob.s₀
    rw [hst]
    rfl
  have hc : freshCol (sgOf s) (J.first w fr ⟨c, tailsIn s c, mem, rs⟩) =
      freshCol (sgOf s) { zeroPS with
        fM := packedN (sgOf s) (hideAt ((sgOf s).h + (sgOf s).g) c), fT := tailsIn s c } := by
    funext x
    show wordsOf (wr _ (freshSym _ (packedN (sgOf J.s₀) (hideAt _ c)) (tailsIn s c) x)) =
      wordsOf (wr _ (freshSym _ (packedN (sgOf s) (hideAt _ c)) (tailsIn s c) x))
    rw [h0]
  refine shown_take _ _ dep _ asks ?_ ?_
  · rw [testAll_rs J w fr _ D s next rest hst hk, List.take_of_length_le (Nat.le_of_eq hl)]
    rfl
  · rw [testAll_tr J w fr _ D s next rest hst hk, if_pos hfr, hc,
      List.take_of_length_le (Nat.le_of_eq hl')]
    rfl

/-! ## 3 The statement -/

local instance (d : Due) : Nonempty (Cs d) := ⟨default⟩
local instance (l : List (String × Due)) : Nonempty (CsAll l) := ⟨default⟩
local instance (d : Due) (l : List (String × Due)) : Nonempty (Cs d × CsAll l) :=
  ⟨(default, default)⟩

/-- **The frame's sentence at the first member, where the first fold sends its own table: for every
`On`.** -/
theorem exact_first_job (φ : Face V W Pb) (σ : Side S Cl V W X Pb) (J : TestJob W X)
    (Js : SimJob Pb) (chain firstTree : ℕ)
    (On : (u : Member V W X Pb) → CsAll u.part.carries → Mid W X → Before → Prop)
    (hfr : J.fresh.isNone = true) (T : FirstPubOwn J Js) :
    ExactMember φ σ chain firstTree On (budBoth Js) (firstMember J Js) := by
  obtain ⟨p, ms, fresh, r0, ro, tr⟩ := J
  obtain ⟨p', own, r0', op⟩ := Js
  obtain ⟨hp, ho, hform, hen, htab, hpt⟩ := T
  simp only at hp ho hfr
  subst hp ho
  cases fresh with
  | some f => simp at hfr
  | none =>
    obtain ⟨s, next, rest, hst⟩ : ∃ s next rest, p'.nums.stages = s :: next :: rest := by
      unfold formPubB at hform
      simp only at hform
      cases hs : p'.nums.stages with
      | nil => rw [hs] at hform; cases hform
      | cons a l =>
        cases l with
        | nil => rw [hs] at hform; cases hform
        | cons b r => exact ⟨a, b, r, rfl⟩
    have h0 : p'.nums.stages.headD default = s := by
      rw [hst]
      rfl
    have hn : firstLen p'.nums.stages = s.k + 2 := by
      rw [hst]
      show 2 + s.k = s.k + 2
      omega
    subst h0
    have FP := formPub_of_B p' _ next rest hst hform
    have hk : (p'.nums.stages.headD default).k = (sgOf (p'.nums.stages.headD default)).h +
        (sgOf (p'.nums.stages.headD default)).g := by
      have := FP.hk
      show (p'.nums.stages.headD default).k = (p'.nums.stages.headD default).h +
        ((p'.nums.stages.headD default).k - (p'.nums.stages.headD default).h)
      omega
    intro ca m front ds asks _ _ hfit hbud _ _
    have hlen : ds.length = firstLen p'.nums.stages := by
      have h := drawsFit_length _ _ hfit
      rw [h, List.length_map]
      show ((laidOf p').take _).length = _
      rw [List.length_take]
      exact Nat.min_eq_left hen
    have FT : FirstTies (⟨p', ms, none, r0, ro, tr⟩ : TestJob W X) _ next rest (byNo ds) ds :=
      ⟨hst, hen, FP.sorts, htab, hlen, fun n h => (List.getD_eq_getElem _ _ h).symm⟩
    have hb : budFirst (p'.nums.stages.headD default) asks = true := hbud.1 rfl rfl
    -- the left side
    have hL : (fun c : Cs ⟨0, dueFresh (p'.nums.stages.headD default)⟩ × CsAll [] =>
        σ.shows φ (firstMember (⟨p', ms, none, r0, ro, tr⟩ : TestJob W X)
          (⟨p', true, r0', op⟩ : SimJob Pb)) (c.1, c.2, ca) m ds asks) =
        (fun x : Cs ⟨0, dueFresh (p'.nums.stages.headD default)⟩ =>
          some (shownFrom (ownText (p'.nums.stages.headD default)
            (vecG _ (rowOf ((⟨p', ms, none, r0, ro, tr⟩ : TestJob W X).recB m.st.input
              (frontBy m 0) (byNo ds 0))))
            (μOf _ (ro m.st.input (frontBy m 0) (stretches _ ca))) (stretchOf x).e (byNo ds))
            (depthAt (⟨p', ms, none, r0, ro, tr⟩ : TestJob W X))
            ((p'.nums.stages.headD default).k + 2) asks)) ∘ Prod.fst := by
      funext c
      rw [shows_first φ σ _ _ _ next rest m (byNo ds) ds FT (c.1, c.2, ca) asks]
      show some (shownFrom _ _ (firstLen p'.nums.stages) asks) = _
      rw [hn]
      exact congrArg some (own_text (⟨p', ms, none, r0, ro, tr⟩ : TestJob W X) rfl _ next rest hst
        FP.hk m.st.input (frontBy m 0) (stretchOf c.1).e (stretches _ ca) (fun _ => 0) (byNo ds) _
        asks)
    -- the right side
    have hR : (fun c : Cs (firstSim (⟨p', true, r0', op⟩ : SimJob Pb)).takes =>
        (firstMember (⟨p', ms, none, r0, ro, tr⟩ : TestJob W X)
          (⟨p', true, r0', op⟩ : SimJob Pb) : Member V W X Pb).tells φ c m.st.input front ds
          asks) =
        fun x : Cs ⟨0, dueFresh (p'.nums.stages.headD default)⟩ =>
          some (shownFrom (ownText (p'.nums.stages.headD default) (vecG _ {}) (μOf _ zeroPS)
            (stretchOf x).e (byNo ds)) (depthAt (⟨p', ms, none, r0, ro, tr⟩ : TestJob W X))
            ((p'.nums.stages.headD default).k + 2) asks) := by
      funext c
      show some (shownFrom _ _ (firstLen p'.nums.stages) asks) = _
      rw [hn]
      rfl
    have hlaw := congrArg (PMF.map some) (own_law (p'.nums.stages.headD default) hk hpt
      (vecG _ (rowOf ((⟨p', ms, none, r0, ro, tr⟩ : TestJob W X).recB m.st.input (frontBy m 0)
        (byNo ds 0))))
      (μOf _ (ro m.st.input (frontBy m 0) (stretches _ ca))) (vecG _ {}) (μOf _ zeroPS) (byNo ds)
      (depthAt (⟨p', ms, none, r0, ro, tr⟩ : TestJob W X))
      ((p'.nums.stages.headD default).k + 2) asks hb)
    rw [PMF.map_comp, PMF.map_comp] at hlaw
    show PMF.map (fun c : Cs ⟨0, dueFresh (p'.nums.stages.headD default)⟩ × CsAll [] =>
        σ.shows φ (firstMember (⟨p', ms, none, r0, ro, tr⟩ : TestJob W X)
          (⟨p', true, r0', op⟩ : SimJob Pb)) (c.1, c.2, ca) m ds asks)
        (Prob.unif (Cs ⟨0, dueFresh (p'.nums.stages.headD default)⟩ × CsAll [])) =
      PMF.map (fun c : Cs (firstSim (⟨p', true, r0', op⟩ : SimJob Pb)).takes =>
        (firstMember (⟨p', ms, none, r0, ro, tr⟩ : TestJob W X)
          (⟨p', true, r0', op⟩ : SimJob Pb) : Member V W X Pb).tells φ c m.st.input front ds
          asks) (Prob.unif (Cs (firstSim (⟨p', true, r0', op⟩ : SimJob Pb)).takes))
    rw [hL, hR, ← PMF.map_comp, Prob.map_fst_unif]
    exact hlaw

/-- **The same at the job of a `ManyJob`.** -/
theorem exact_first_own (φ : Face V W Pb) (σ : Side S Cl V W X Pb) (A : ManyJob W X)
    (Js : SimJob Pb) (chain firstTree : ℕ)
    (On : (u : Member V W X Pb) → CsAll u.part.carries → Mid W X → Before → Prop)
    (hfr : A.fresh = none) (T : FirstPubOwn A.toRun.toTest Js) :
    ExactMember φ σ chain firstTree On (budBoth Js) (firstMember A.toRun.toTest Js) :=
  exact_first_job φ σ _ Js chain firstTree On
    (by show A.fresh.isNone = true; rw [hfr]; rfl) T

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.budBoth
#print axioms ProofFile.Honest.K12.Light.FirstPubOwn
#print axioms ProofFile.Honest.K12.Light.shown_take
#print axioms ProofFile.Honest.K12.Light.own_text
#print axioms ProofFile.Honest.K12.Light.exact_first_job
#print axioms ProofFile.Honest.K12.Light.exact_first_own
