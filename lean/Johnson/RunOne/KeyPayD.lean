-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/KeyPayD.lean: THEOREMS. **WHAT A «yes» OF THE KEY FILE's DESCRIPTION PAYS**: of Key.descriptionFromSource X N P (Johnson/Desc/Key/Desc.lean), of Key.descriptionFromPlan m, and on the road Key.descAt X lay cfg (Johnson/Desc/Key/Road.lean).
Over Johnson/Desc/RunLaws.lean (what a yes is made of; the tests on the plan as a structure in Prop), and Johnson/RunOne/KeyPayClauses.lean.
  fkOfMade_ok · pubsOf_ok · descAt_ok      how the description is made
  FileOkD | fileOkD_of     Key.descriptionFromSource's fileOk: Key.fileClauses, lot by lot and name by name
  Answers | Plan3          one answer to a sample in each of the three plans; the last chain's plan is just the own test's entries (out of our eight, which stand in fileOk again)
  SizedIsRead | sizedIsRead_of    the sized values ARE the values read back (the clause «cut»)
  seal_last        **the first chain's plan ends in the seal's round**: the declared rounds are some list and then ChainEnd.sealRound; so are the entries of the plan in the parameter bytes
  Paid | paid      **all of it from Key.descriptionFromSource's yes**, with «no seed's factor is 0 IN THE FIELD»
  paid_at_made     the same from a yes of the description made of a record (Key.descriptionFromPlan m)
Over the key file's texts (Johnson/Desc/Key/): fileOk has among its clauses k12.U | k12.O | k12.own; the test on the instance has two conjuncts, and the words' test is instanceOk's own keyWordsBelow (no file under Johnson/RunOne/ but KeyPayClauses.lean is imported); the seal is the chain's field «last». Nothing on soundness is claimed.

-/
import Johnson.Desc.Key.Road
import Johnson.Desc.RunLaws
import Johnson.RunOne.KeyPayClauses
import OnBytes.Slice.ProgField

set_option autoImplicit false

namespace Johnson.RunOne.KeyPay

open OnBytes OnBytes.Params VerifiableInference.Desc.Key
open Johnson.G.OfPlan (Made)
open VerifiableInference.Desc (FileDescription bind_eq_ok error_ne_ok)

/-! ## How the description is made -/

theorem fkOfMade_ok {m : Made} {F : FileDescription Xi} (h : descriptionFromPlan m = .ok F) :
    ∃ X N P, sourceOf m = .ok X ∧ rangesNumbers m = .ok N ∧ laterPlaces m = .ok P ∧ F = descriptionFromSource X N P := by
  unfold descriptionFromPlan at h
  cases h1 : sourceOf m with
  | error e => rw [h1] at h; exact (error_ne_ok h).elim
  | ok X =>
    cases h2 : rangesNumbers m with
    | error e => rw [h1, h2] at h; exact (error_ne_ok h).elim
    | ok N =>
      cases h3 : laterPlaces m with
      | error e => rw [h1, h2, h3] at h; exact (error_ne_ok h).elim
      | ok P =>
        rw [h1, h2, h3] at h
        exact ⟨X, N, P, rfl, rfl, rfl, (Except.ok.inj h).symm⟩

/-- The source's fields are m's. -/
theorem pubsOf_ok {m : Made} {X : Source} (h : sourceOf m = .ok X) :
    X.chains = m.p.chains ∧ X.set = m.p.chains.made.sized.key.set ∧ X.Y.k = m.p.chains.key ∧ X.Y.cutShape = m.p.chains.made.sized.key.once.shape ∧
      X.Y.cutCodes = (m.key.1.codes, m.key.2.1.codes, m.key.2.2.codes) ∧ X.Y.cutIdx = m.p.chains.made.sized.key.once.input ∧
      X.Y.cutRanges = m.p.chains.made.sized.key.ranges.x ∧ X.Y.cutSamples = m.p.chains.made.sized.set.samples ∧
      Johnson.G.OfPlan.declKOf m = .ok X.Y.D ∧ toldOfMade m = .ok X.Y.told := by
  unfold sourceOf at h
  obtain ⟨D, hD, h⟩ := bind_eq_ok h
  obtain ⟨t, ht, h⟩ := bind_eq_ok h
  rw [← Except.ok.inj h]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hD, ht⟩

/-- The road of record: Key.descAt is Key.madeAt, then the description of the record. -/
theorem descAt_ok {X : Model.Verify.Public} {lay cfg : ByteArray} {F : FileDescription Xi} (h : descAt X lay cfg = .ok F) :
    ∃ m, madeAt X lay cfg = .ok m ∧ descriptionFromPlan m = .ok F := by
  unfold descAt at h
  cases hm : madeAt X lay cfg with
  | error e => rw [hm] at h; exact (error_ne_ok h).elim
  | ok m => rw [hm] at h; exact ⟨m, rfl, h⟩

/-! ## Key.descriptionFromSource's fileOk -/

/-- The rounds that a chain's own blocks take. -/
def lenOf {σ : Type} (x : VerifiableInference.Desc.Chain σ Claim) : Nat := (x.blocksInOrder.flatMap (·.rounds)).length

/-- Key.descriptionFromSource's fileOk: the clauses of Key.fileClauses, lot by lot and name by name. r₁ r₂ r₃: the rounds that the description's own blocks take of the three chains. -/
structure FileOkD (X : Source) (N : H2U.PlaceNums) (P : LaterPlaces) (r₁ r₂ r₃ : Nat) : Prop where
  ok : sourceOk X.Y = true
  more : ∀ c ∈ shapeClauses X.Y.k X.chains.made.sized.key.once.shape, c.2 = true
  eight : ∀ c ∈ planClauses X.Y.k r₁ r₂ r₃, c.2 = true
  prices : VerifiableInference.Desc.keyOk X.chains.made = true
  priced : X.chains.made.key.map (·.plan.entries) = [X.Y.k.oneTime.given.plan.entries, X.Y.k.shared.given.plan.entries, X.Y.k.second.given.plan.entries]
  opened : openedAsTold X.Y = true
  entries₁ : X.Y.D.1.map (·.entry) = X.Y.k.oneTime.given.rounds
  entries₂ : X.Y.D.2.1.map (·.entry) = X.Y.k.shared.given.rounds
  entries₃ : X.Y.D.2.2.map (·.entry) = X.Y.k.second.given.rounds
  stagesRng : stagesAsSized X.Y.k.oneTime.codes X.Y.k.oneTime.ranges.stages N = true
  stagesU : stagesAsSized X.Y.k.shared.codes X.Y.k.shared.lin.testU P.U = true
  stagesO : (match P.O with | some nO => stagesAsSized X.Y.k.shared.codes X.Y.k.shared.lin.testOmega nO | none => X.Y.k.shared.lin.testOmega.isEmpty) = true
  stagesOwn : stagesAsSized X.Y.k.shared.codes X.Y.k.shared.lin.testOwn P.W = true
  /-- the digest of the public files is not 32 zero bytes: as the test's own Bool -/
  digest : (X.Y.k.oneTime.given.cfg != Fmt.zero32) = true
  /-- what the ranges' test's seat asks on the plan, at the three later tests' places -/
  k12U : asksOnPlan (H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩ P.U) = true
  k12O : (match P.O with | some nO => asksOnPlan (H2U.proximityTestParametersAt ⟨2, none, 10, .K12⟩ nO) | none => true) = true
  k12Own : asksOnPlan (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ P.W) = true

theorem fileOkD_of_clauses {X : Source} {N : H2U.PlaceNums} {P : LaterPlaces} {r₁ r₂ r₃ : Nat} (h : (fileClauses X N P r₁ r₂ r₃).all (·.2) = true) : FileOkD X N P r₁ r₂ r₃ := by
  unfold fileClauses at h
  simp only [List.all_append, Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at h4
  obtain ⟨a1, a2, a3, ⟨⟨a4, a5⟩, a6⟩, a7, a8, a9, a10, a11, a12, a13, a14⟩ := h4
  exact ⟨h1, fun c hc => (List.all_eq_true.mp h2) c hc, fun c hc => (List.all_eq_true.mp h3) c hc, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14⟩

theorem fileOkD_of {X : Source} {N : H2U.PlaceNums} {P : LaterPlaces} (h : (descriptionFromSource X N P).fileOk = true) :
    FileOkD X N P (lenOf (descriptionFromSource X N P).first) (lenOf (descriptionFromSource X N P).shared) (lenOf (descriptionFromSource X N P).second) := by
  have h' : ((fileClauses X N P (lenOf (descriptionFromSource X N P).first) (lenOf (descriptionFromSource X N P).shared) (lenOf (descriptionFromSource X N P).second)).all (·.2) && _) = true := h
  rw [Bool.and_eq_true] at h'
  exact fileOkD_of_clauses h'.1

/-- «opened.F»: Key.descriptionFromSource's fileOk's second conjunct, at the description's own roots and declared rounds: as that test's own Bool. -/
theorem openedF_of {X : Source} {N : H2U.PlaceNums} {P : LaterPlaces} (h : (descriptionFromSource X N P).fileOk = true) : openedInBlocks (descriptionFromSource X N P).roots (descriptionFromSource X N P).roundsDeclaredByBlocks = true := by
  have h' : (_ && openedInBlocks (descriptionFromSource X N P).roots (descriptionFromSource X N P).roundsDeclaredByBlocks) = true := h
  rw [Bool.and_eq_true] at h'
  exact h'.2

/-! ## Our eight on the plans' entries -/

/-- One answer to a sample, in each of the three plans. -/
structure Answers (k : KeyChains) : Prop where
  one₁ : k.oneTime.given.plan.samples = 1
  one₂ : k.shared.given.plan.samples = 1
  one₃ : k.second.given.plan.samples = 1

/-- The last chain's plan is just the own test's entries; its first stage has the own group's two codes. -/
structure Plan3 (k : KeyChains) : Prop where
  entries : Plan.okFrom (Plan.wantsThird k) k.second.given.rounds 0 = true
  noMore : k.second.given.rounds.length = (Plan.wantsThird k).length
  first : (k.shared.lin.testOwn.head?.map fun s => (s.code, s.maskCode)) = some (k.shared.lin.w.code, k.shared.lin.ownMaskCode)

theorem answers_of {Y : KeySource} {r₁ r₂ r₃ : Nat} (hok : sourceOk Y = true) (h8 : ∀ c ∈ planClauses Y.k r₁ r₂ r₃, c.2 = true) : Answers Y.k := by
  have h3 := h8 ("chain 3: public: the own test: one answer to a sample", Y.k.second.given.plan.samples == 1) (by simp [planClauses, Plan.clausesAt, Plan.stepsThird])
  simp only [beq_iff_eq] at h3
  obtain ⟨a12, a13⟩ := setting_of_ok hok
  exact ⟨a13.trans h3, a12.symm.trans (a13.trans h3), h3⟩

theorem plan3_of {k : KeyChains} {r₁ r₂ r₃ : Nat} (h8 : ∀ c ∈ planClauses k r₁ r₂ r₃, c.2 = true) : Plan3 k := by
  have h1 := h8 ("chain 3: public: the own test: chain 3's plan is just the test's entries",
    Plan.okFrom (Plan.wantsThird k) k.second.given.rounds 0 && k.second.given.rounds.length == (Plan.wantsThird k).length) (by simp [planClauses, Plan.clausesAt, Plan.stepsThird])
  have h2 := h8 ("chain 3: public: the own test: the first stage has the group's codes",
    (k.shared.lin.testOwn.head?.map fun s => (s.code, s.maskCode)) == some (k.shared.lin.w.code, k.shared.lin.ownMaskCode)) (by simp [planClauses, Plan.clausesAt, Plan.stepsThird])
  simp only [Bool.and_eq_true, beq_iff_eq] at h1 h2
  exact ⟨h1.1, h1.2, h2⟩

/-- The planner's sized values at the key are the values read back of the one-time chain's parameter bytes. -/
structure SizedIsRead (m : Made) : Prop where
  shape : m.p.chains.made.sized.key.once.shape = m.p.chains.key.oneTime.lin
  idx : m.p.chains.made.sized.key.once.input = m.p.chains.key.oneTime.indexMasks
  ranges : m.p.chains.made.sized.key.ranges.x = m.p.chains.key.oneTime.ranges
  samples : m.p.chains.made.sized.set.samples = m.p.chains.key.oneTime.given.plan.samples
  codes₁ : m.key.1.codes = m.p.chains.key.oneTime.codes
  codes₂ : m.key.2.1.codes = m.p.chains.key.oneTime.codes
  codes₃ : m.key.2.2.codes = m.p.chains.key.oneTime.codes

theorem sizedIsRead_of {m : Made} {X : Source} (h : sourceOf m = .ok X) (hok : sourceOk X.Y = true) : SizedIsRead m := by
  obtain ⟨_, _, hk, h1, h2, h3, h4, h5, _, _⟩ := pubsOf_ok h
  have c := cut_of_ok hok
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← h1, ← hk]; exact c.shape
  · rw [← h3, ← hk]; exact c.idx
  · rw [← h4, ← hk]; exact c.ranges
  · rw [← h5, ← hk]; exact c.samples
  · rw [← hk]; have := c.codes₁; rw [h2] at this; exact this
  · rw [← hk]; have := c.codes₂; rw [h2] at this; exact this
  · rw [← hk]; have := c.codes₃; rw [h2] at this; exact this

/-! ## The seal -/

/-- The first chain's blocks' rounds in a row end in the seal's round. -/
theorem chainD_rounds_last (one : OneTime) (D : List Fmt.DeclaredRound) (told : List ProofFile.Root) (set : Setting) (N : H2U.PlaceNums) :
    ∃ l, (firstChain one D told set N).blocksInOrder.flatMap (·.rounds) = l ++ [VerifiableInference.Desc.ChainEnd.sealRound] := by
  refine ⟨((firstChain one D told set N).blocksInOrder.dropLast).flatMap (·.rounds), ?_⟩
  simp only [firstChain, VerifiableInference.Desc.Chain.blocksInOrder, List.flatMap_cons, List.flatMap_append, List.flatMap_nil, List.append_nil, List.cons_append, List.dropLast_concat, ← List.cons_append]
  rfl

/-- **The first chain's plan ends in the seal's round.** -/
theorem seal_last {X : Source} {N : H2U.PlaceNums} {P : LaterPlaces} (h : (descriptionFromSource X N P).planOk = true) :
    (∃ l, X.Y.D.1 = l ++ [VerifiableInference.Desc.ChainEnd.sealRound]) ∧
      ∃ l, X.Y.k.oneTime.given.rounds = l ++ [VerifiableInference.Desc.ChainEnd.sealRound.entry] := by
  have p := ((descriptionFromSource X N P).planOk_ok).1 h
  obtain ⟨l, hl⟩ := chainD_rounds_last X.Y.k.oneTime X.Y.D.1 X.Y.told.1 X.set N
  have hd : X.Y.D.1 = l ++ [VerifiableInference.Desc.ChainEnd.sealRound] := (show (descriptionFromSource X N P).roundsDeclaredByBlocks.1 = X.Y.D.1 from p.decl₁).symm.trans hl
  refine ⟨⟨l, hd⟩, l.map (·.entry), ?_⟩
  rw [← (fileOkD_of p.fileOk).entries₁, hd]
  simp

/-! ## All of it -/

/-- **No seed's factor is 0 in the field**: its words are below the prime, and they are not all 0 (the reading readE; isZeroE_iff). -/
theorem factors_of_start {S : LinShape} {x : Xi} (st : Start S x) : ∀ z ∈ x.key.seeds, OnBytes.Slice.readE z.beta ≠ 0 := by
  intro z hz h0
  have := (OnBytes.Slice.isZeroE_iff z.beta (st.seeds z hz).1).2 h0
  rw [st.factors z hz] at this
  exact Bool.noConfusion this

/-- What a yes of Key.descriptionFromSource pays. -/
structure Paid (X : Source) (N : H2U.PlaceNums) (P : LaterPlaces) (x : Xi) : Prop where
  file : FileOkD X N P (lenOf (descriptionFromSource X N P).first) (lenOf (descriptionFromSource X N P).shared) (lenOf (descriptionFromSource X N P).second)
  openedInBlocks : openedInBlocks (descriptionFromSource X N P).roots (descriptionFromSource X N P).roundsDeclaredByBlocks = true
  read : ∃ k', KeyChains.read X.Y.k.oneTime.given.bytes X.Y.k.shared.given.bytes X.Y.k.second.given.bytes = some k' ∧ sameKeyChains k' X.Y.k = true
  made : ∃ y, madeAgain X.Y.k = .ok y ∧ y.1 = X.Y.D ∧ (y.2 == X.Y.told) = true
  answers : Answers X.Y.k
  plan3 : Plan3 X.Y.k
  tied : Tied X.Y.k
  oneLeaf : X.Y.k.oneTime.binding.logLeaves = 0
  front1 : Front1 X.Y.k.oneTime
  tests : Tests X.Y.k
  cut : Cut X.Y
  start : Start X.Y.k.shared.lin x
  sizes : Sizes x.key X.Y.k.shared.lin.fold.index
  okKey14 : _root_.Desc.K14.okKey (sharedPar X.chains []) x.key = true
  words : keyWordsBelow x.key = true
  /-- no seed's factor is 0 in the field -/
  factors : ∀ z ∈ x.key.seeds, OnBytes.Slice.readE z.beta ≠ 0
  sealD : ∃ l, X.Y.D.1 = l ++ [VerifiableInference.Desc.ChainEnd.sealRound]
  sealPlan : ∃ l, X.Y.k.oneTime.given.rounds = l ++ [VerifiableInference.Desc.ChainEnd.sealRound.entry]

/-- **What a yes of Key.descriptionFromSource pays.** -/
theorem paid {X : Source} {N : H2U.PlaceNums} {P : LaterPlaces} {x : Xi} {v₁ v₂ v₃ : Fmt.View} (hy : (descriptionFromSource X N P).run x v₁ v₂ v₃ = true) :
    (descriptionFromSource X N P).PlanOk ∧ Paid X N P x := by
  have hp := FileDescription.planOk_of_run hy
  have p := ((descriptionFromSource X N P).planOk_ok).1 hp
  have ho : (instanceOk X.Y.k.shared.lin x && _root_.Desc.K14.okKey (sharedPar X.chains []) x.key) = true := FileDescription.okStart_of_run hy
  simp only [Bool.and_eq_true] at ho
  have hw : keyWordsBelow x.key = true := by
    have hi := ho.1
    unfold instanceOk at hi
    simp only [Bool.and_eq_true] at hi
    exact hi.1.2
  have f := fileOkD_of p.fileOk
  have st := start_of_okStart ho.1
  exact ⟨p, f, openedF_of p.fileOk, read_of_ok f.ok, made_of_ok f.ok, answers_of f.ok f.eight, plan3_of f.eight, tied_of_ok f.ok, oneLeaf_of_ok f.ok, front1_of_ok f.ok, tests_of_ok f.ok, cut_of_ok f.ok, st, sizes_of_fits st.fits, ho.2, hw,
    factors_of_start st, (seal_last hp).1, (seal_last hp).2⟩

/-- **The same from a yes of the description that descriptionFromPlan makes of a record.** -/
theorem paid_at_made {m : Made} {F : FileDescription Xi} (h : descriptionFromPlan m = .ok F) {x : Xi} {v₁ v₂ v₃ : Fmt.View} (hy : F.run x v₁ v₂ v₃ = true) :
    ∃ X N P, sourceOf m = .ok X ∧ rangesNumbers m = .ok N ∧ laterPlaces m = .ok P ∧ F = descriptionFromSource X N P ∧ F.PlanOk ∧ Paid X N P x ∧ SizedIsRead m := by
  obtain ⟨X, N, P, h1, h2, h3, hF⟩ := fkOfMade_ok h
  subst hF
  obtain ⟨p, q⟩ := paid hy
  exact ⟨X, N, P, h1, h2, h3, rfl, p, q, sizedIsRead_of h1 q.file.ok⟩

end Johnson.RunOne.KeyPay

#print axioms Johnson.RunOne.KeyPay.fkOfMade_ok
#print axioms Johnson.RunOne.KeyPay.pubsOf_ok
#print axioms Johnson.RunOne.KeyPay.fileOkD_of
#print axioms Johnson.RunOne.KeyPay.answers_of
#print axioms Johnson.RunOne.KeyPay.plan3_of
#print axioms Johnson.RunOne.KeyPay.seal_last
#print axioms Johnson.RunOne.KeyPay.factors_of_start
#print axioms Johnson.RunOne.KeyPay.paid
#print axioms Johnson.RunOne.KeyPay.paid_at_made
