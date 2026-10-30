-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/Sim/MeetsAtHead.lean: under the library's head (`P5J.AtMg`,
Johnson/P5J/AtMg.lean), at the first member of the proximity test on G_u, the six hypotheses of the
sentence `ExactMember` (Johnson/Desc/ProofFile/Honest/Small/Field.lean) hold together, in the
sentence's order, at written letters; there what the part shows is something at all random values;
and the equation in which the sentence ends holds. The job is `jobAtU` (JobShared.lean) at the proof
file's own plan and the seated place. It imports Mathlib.

The letters. On and bud: `testOn φ J Js` and `testBud Js` (Sim/Row.lean). The stand m, the carried
values ca, the positions asks, the face, the side, the chain's number and the first tree's number:
any. The front: `bareFront chain m`, the rounds that m has seen, with no column. The challenges:
`dsFull` (Sim/DrawsAtHead.lean).

  `testOn_first`, `testBud_first`   at the first member `testOn` holds at all letters; `testBud`
                 too, where the simulators' job says that the fold sends no table
  `bareFront`, `seen_bareFront`   a front made of what a stand has seen; it shows what the stand has
                 seen
  `reads_none`, `quietB`, `holds_of_quiet`   declared rounds that open nothing read nothing, so
                 every front holds all that they read
  `quiet_UFull`, `quiet_head_U`   the member's rounds open nothing: at `piUFull` by Lean's kernel;
                 at the seated place under the head
  `stop_first`   the first part has no second stop
  `k_head_U`     under the head the first stage of the seated place has k = 7
  `some_head_U`  what the part shows there is something, at all random values
  `meets_head_U`   the six, "something", and the equation

Of the six, four ask nothing at this member, at any letters: On, bud, "the front holds what is
read", and "no second stop". Two say something: the front shows what the stand has seen, which holds
here because the front is made of the stand; and the challenges have the declared form.

By what. `draws_head_U` (Sim/DrawsAtHead.lean); `firstPub_head`, `exact_first_head`, `nums_head_U`,
`thin_head_U`, `decls_thin` (Sim/FirstPubAtHead.lean); `shows_first` (Sim/ShowsFirst.lean);
`formPub_of_B` (FormPubAt.lean); `first_quiet` (HalfReturns.lean).

Limits.
- The stand is any: no stand is shown to be one that a play reaches.
- The front lists no column and no root; the challenges are written by hand: the one element
  (1, 0, 0), nine times. Neither is taken from a run. Such a front could not serve the test's second
  member, whose On asks for listed roots.
- The state on entry is any function: nothing says that it is the verifier's state.
- It is shown at no job that is played.
- It speaks of the parts of `proverSideOfProximityTest` (Parts.lean), not of halves with a guard in front.
- The parts and their random values are defined in Test.lean, Parts.lean and Coins.lean of
  Johnson/Desc/ProofFile/Honest/K12/. What the parts send is that folder's own `testAll`; how far it
  is tied to the library's `bodyAll` (Johnson/Prover/Link/BodyAll.lean) is said in the limits of
  Test.lean.
- It is the spender's half: the 2 k + 1 values that the first member spends are sampled anew in the
  equation. The same values stand in the sender's tree and in what the second part carries; nothing
  here joins these.
- The first member alone, and only where the fresh table came earlier: not at the test on G_omega.
- The full size alone. No example of the head is shown here.
Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.Sim.DrawsAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace ProofFile.Honest.K12.Light
open VerifiableInference.Desc (K1.qAt)
open VerifiableInference.Desc.K12 (T12)
open H2K.Member (piUFull)
open H2K.JointK (laidOf)
open ProofFile.Honest.K12.AtProof (fourOf)

variable {S Cl V W X Pb : Type}

/-! ## 1 The four that ask nothing -/

theorem testOn_first (φ : Face V W Pb) (J : TestJob W X) (Js : SimJob Pb)
    (ca : CsAll (firstMember (V := V) J Js).part.carries) (m : ProofFile.Honest.Mid W X)
    (front : Before) : testOn φ J Js (firstMember J Js) ca m front :=
  fun h => absurd (show (0 : ℕ) = 1 from h) Nat.zero_ne_one

theorem testBud_first (Js : SimJob Pb) (ho : Js.own = false) (ds : List Fmt.Drawn)
    (asks : List (List (List ℕ))) : testBud Js 0 ds asks :=
  ⟨fun _ h => absurd (ho.symm.trans h) Bool.false_ne_true, fun h => absurd h Nat.zero_ne_one⟩

/-- Declared rounds that open nothing read nothing. -/
theorem reads_none (chain firstTree : ℕ) (stored : ℕ → ℕ → Option (List UInt64))
    (tree : Fmt.TreeSource → Option (VerifiableInference.Desc.Place × Table)) :
    ∀ (l : List Fmt.DeclaredRound) (ds : List Fmt.Drawn),
      (∀ d ∈ l, d.stored = [] ∧ d.opens = []) → readsOf chain firstTree stored tree l ds = []
  | [], _, _ => by simp [readsOf]
  | _ :: _, [], _ => by simp [readsOf]
  | d :: l, R :: Rs, H => by
    rw [readsOf, (H d List.mem_cons_self).1, (H d List.mem_cons_self).2,
      reads_none chain firstTree stored tree l Rs fun x hx => H x (List.mem_cons_of_mem _ hx)]
    rfl

/-- No round of the list opens a stored table or a tree. -/
def quietB (l : List Fmt.DeclaredRound) : Bool := l.all fun d => d.stored.isEmpty && d.opens.isEmpty

theorem holds_of_quiet (f : Before) (chain firstTree : ℕ) (l : List Fmt.DeclaredRound)
    (ds : List Fmt.Drawn) (h : quietB l = true) : f.holds chain firstTree l ds = true := by
  unfold Before.holds
  rw [reads_none chain firstTree _ _ l ds fun d hd => by
    have := List.all_eq_true.1 h d hd
    simp only [Bool.and_eq_true, List.isEmpty_iff] at this
    exact this]
  rfl

theorem stop_first (J : TestJob W X) (Js : SimJob Pb) (v : Option V) (loc ds : List Fmt.Drawn) :
    (firstMember J Js : Member V W X Pb).part.stopAt v loc ds ≠ some .hid := by
  intro h
  unfold Part.stopAt at h
  obtain ⟨j, -, hj⟩ := List.exists_of_findSome?_eq_some h
  have hb : (firstMember J Js : Member V W X Pb).part.bad loc (ds.take j) = none :=
    (first_quiet J).1 _ _
  have hh : (v.bind fun u => (firstMember J Js : Member V W X Pb).part.hid u loc (ds.take j)) =
      none := by
    cases v with
    | none => rfl
    | some u => exact (first_quiet J).2 _ _ _
  rw [hb, hh] at hj
  simp at hj

/-! ## 2 The front -/

/-- A front made of what a stand has seen: under the chain's number ch; no column. -/
def bareFront (ch : ℕ) (m : ProofFile.Honest.Mid W X) : Before :=
  ⟨m.seen.map fun r => (ch, ⟨r.vals, []⟩, r.drawn), []⟩

theorem seen_bareFront (ch : ℕ) (m : ProofFile.Honest.Mid W X) : m.seen = (bareFront ch m).seen := by
  show m.seen = (m.seen.map fun r => ((ch, ⟨r.vals, []⟩, r.drawn) :
    ℕ × Shown × Fmt.Drawn)).map fun r => (⟨r.2.1.vals, r.2.2⟩ : Fmt.RoundView)
  rw [List.map_map]
  exact (List.map_id _).symm

/-! ## 3 At the written place, and under the head -/

theorem quiet_UFull :
    quietB (((laidOf piUFull).take (firstLen piUFull.nums.stages)).map (·.1)) = true := by
  decide +kernel

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl}

/-- Under the head the first stage of the seated place has k = 7. -/
theorem k_head_U (h : P5J.AtMg o Z D r Zp Np cF) :
    ((fourOf Np).U.nums.stages.headD default).k = 7 := by
  rw [nums_head_U h]
  rfl

section Job
variable (h : P5J.AtMg o Z D r Zp Np cF) (door : W → Front X → T12) (weights : W → Weights)
  (rand : W → TableRand) (u? : Option (W → Front X → ℕ → OnBytes.E)) (Js : SimJob Pb)
  (J : TestJob W X)
  (hjob : J = (jobAtU ⟨K1.qAt Zp Np, 0⟩ (fourOf Np).U door weights rand u?).toRun.toTest)

include h hjob in
theorem quiet_head_U : quietB ((firstMember (V := V) J Js).rounds.map (·.1)) = true := by
  subst hjob
  show quietB (((laidOf (fourOf Np).U).take (firstLen (fourOf Np).U.nums.stages)).map (·.1)) = true
  rw [List.map_take, decls_thin, thin_head_U h, ← decls_thin, ← List.map_take, nums_head_U h]
  exact quiet_UFull

include h hjob in
/-- What the part shows at the written challenges is something, at all random values. -/
theorem some_head_U (hJ : Js.p = (fourOf Np).U) (ho : Js.own = false) (φ : Face V W Pb)
    (σ : Side S Cl V W X Pb) (m : ProofFile.Honest.Mid W X) (asks : List (List (List ℕ)))
    (c : (firstMember J Js : Member V W X Pb).part.Coins) :
    (σ.shows φ (firstMember J Js) c m dsFull asks).isSome = true := by
  subst hjob
  have T := firstPub_head h door weights rand u? Js hJ ho
  have hst : (fourOf Np).U.nums.stages = piUFull.nums.stages := congrArg (·.stages) (nums_head_U h)
  obtain ⟨s, t, rest, hlit⟩ : ∃ s t rest, piUFull.nums.stages = s :: t :: rest := ⟨_, _, _, rfl⟩
  have hlen : dsFull.length = firstLen (fourOf Np).U.nums.stages := by
    rw [hst]
    rfl
  rw [shows_first φ σ _ Js s t rest m (byNo dsFull) dsFull
    ⟨hst.trans hlit, T.enough, (formPub_of_B _ s t rest (hst.trans hlit) T.form).sorts, T.tables,
      hlen, fun n hn => (List.getD_eq_getElem _ _ hn).symm⟩ c asks]
  rfl

local instance (d : Due) (l : List (String × Due)) : Nonempty (Cs d × CsAll l) :=
  ⟨(default, default)⟩

local instance (d : Due) : Nonempty (Cs d) := ⟨default⟩

include h hjob in
/-- **The six hypotheses of the sentence, in its order; "something"; the equation.** -/
theorem meets_head_U (hJ : Js.p = (fourOf Np).U) (ho : Js.own = false) (φ : Face V W Pb)
    (σ : Side S Cl V W X Pb) (chain firstTree : ℕ)
    (ca : CsAll (firstMember (V := V) J Js).part.carries) (m : ProofFile.Honest.Mid W X)
    (asks : List (List (List ℕ))) :
    testOn φ J Js (firstMember J Js) ca m (bareFront chain m) ∧
    m.seen = (bareFront chain m).seen ∧
    drawsFit ((firstMember (V := V) J Js).rounds.map (·.1)) dsFull = true ∧
    testBud Js (firstMember (V := V) J Js).number dsFull asks ∧
    (bareFront chain m).holds chain firstTree ((firstMember (V := V) J Js).rounds.map (·.1))
      dsFull = true ∧
    (firstMember J Js).part.stopAt (φ.sees m.st.input) m.loc dsFull ≠ some .hid ∧
    (∀ c, (σ.shows φ (firstMember J Js) c m dsFull asks).isSome = true) ∧
    (Prob.unif (Cs (firstMember (V := V) J Js).part.takes ×
        CsAll (firstMember (V := V) J Js).part.spends)).map
        (fun c => σ.shows φ (firstMember J Js) (c.1, c.2, ca) m dsFull asks) =
      (Prob.unif (Cs (firstMember (V := V) J Js).sim.takes)).map fun c =>
        (firstMember J Js).tells φ c m.st.input (bareFront chain m) dsFull asks := by
  have h1 := testOn_first φ J Js ca m (bareFront chain m)
  have h2 := seen_bareFront chain m
  have h3 : drawsFit ((firstMember (V := V) J Js).rounds.map (·.1)) dsFull = true := by
    subst hjob
    exact draws_head_U h door weights rand u? Js
  have h4 : testBud Js (firstMember (V := V) J Js).number dsFull asks :=
    testBud_first Js ho dsFull asks
  have h5 := holds_of_quiet (bareFront chain m) chain firstTree _ dsFull
    (quiet_head_U (V := V) h door weights rand u? Js J hjob)
  have h6 := stop_first (V := V) J Js (φ.sees m.st.input) m.loc dsFull
  refine ⟨h1, h2, h3, h4, h5, h6,
    some_head_U h door weights rand u? Js J hjob hJ ho φ σ m asks, ?_⟩
  subst hjob
  exact exact_first_head h φ σ door weights rand u? Js hJ ho chain firstTree (testOn φ _ Js)
    (testBud Js) ca m (bareFront chain m) dsFull asks h1 h2 h3 h4 h5 h6

end Job

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.testOn_first
#print axioms ProofFile.Honest.K12.Light.testBud_first
#print axioms ProofFile.Honest.K12.Light.reads_none
#print axioms ProofFile.Honest.K12.Light.quietB
#print axioms ProofFile.Honest.K12.Light.holds_of_quiet
#print axioms ProofFile.Honest.K12.Light.stop_first
#print axioms ProofFile.Honest.K12.Light.bareFront
#print axioms ProofFile.Honest.K12.Light.seen_bareFront
#print axioms ProofFile.Honest.K12.Light.quiet_UFull
#print axioms ProofFile.Honest.K12.Light.k_head_U
#print axioms ProofFile.Honest.K12.Light.quiet_head_U
#print axioms ProofFile.Honest.K12.Light.some_head_U
#print axioms ProofFile.Honest.K12.Light.meets_head_U
