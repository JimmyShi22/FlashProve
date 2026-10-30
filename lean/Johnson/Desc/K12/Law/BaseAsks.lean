-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
import Johnson.Desc.K12.JoinGuarded
/-
Johnson/Desc/K12/Law/BaseAsks.lean: WHAT A YES OF THE PROXIMITY TEST's LAST PART ASKS: ten
equivalences, each between a yes of a check of Johnson/Desc/K12/JoinGuarded.lean and that check's clauses
written out; their names stand below. Statements and proofs.
NO SOUNDNESS IS CLAIMED. NOTHING ON HIDING.
WHY: in earlier mutation trials (copies of the text, each with one clause struck or turned) every
law still compiled at six places: the laws of a yes are one-way and read of baseJ5's yes the claim
and baseDecide's yes alone. An equivalence that lists EVERY test and writes the record behind out
should fail to compile when a clause of the text is struck: THAT IS TO BE TRIED, trial by trial;
until then it is expected, not shown.
  dense_eq · basePar_eq (by rfl, written out) · inRange_iff · claimAt_iff · baseJ5_planOk_iff ·
  ranged_planOk_iff · ranged_decide_iff · baseJ5_decide_iff · lastMember_iff · oneRowEach_iff ·
  lastPairOk_iff · lastTree_iff.
  spent t star a: the record behind a yes: the masking message star marked as spent, the tree a
  counted as opened once more, nothing passing, no mask waiting.
WHAT IT IS NOT: it says what the text ASKS, not what that is worth: who uses lastPairOk, lastTree's
«unopened» and the mask's spending is left to other files. STANDING HERE BY NAME, ON BOTH SIDES, so
that a change INSIDE them does not show here: (baseCase P).planOk · baseDecide · baseRounds ·
stageAt · noStored (Join.lean's) · Own.formFits · Fmt.listOf. lastTree_iff shows ten conjuncts for
the text's eleven tests: «a == b» is folded into the second. BESIDE IT, ONE-WAY: baseJ5_ok ·
ranged_ok (BaseGives.lean: the forward halves) · baseJ5_form | _keeps | _st | _bk (OutK.lean,
OutK2.lean, OutK3.lean): no equivalence on these names was found elsewhere in the library [grep].

-/
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K12
open OnBytes OnBytes.Params
open VerifiableInference.Desc.Prox (BasePar BaseClaim baseCase baseRounds baseDecide elems four)

namespace BaseAsks

theorem bind_iff {α β : Type} (x : Except String α) (f : α → Except String β) (b : β) :
    (x >>= f) = .ok b ↔ ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => exact ⟨fun h => (by cases h), fun ⟨_, h, _⟩ => (by cases h)⟩
  | ok a => exact ⟨fun h => ⟨a, rfl, h⟩, fun ⟨_, h, g⟩ => (by cases h; exact g)⟩

theorem named_iff {α : Type} (n : String) (o : Option α) (a : α) : named n o = .ok a ↔ o = some a := by
  cases o with
  | none => exact ⟨fun h => (by cases h), fun h => (by cases h)⟩
  | some x => exact ⟨fun h => (by cases h; rfl), fun h => (by cases h; rfl)⟩

theorem need_iff (n : String) (b : Bool) (u : Unit) : need n b = .ok u ↔ b = true := by
  cases b with
  | false => exact ⟨fun h => (by cases h), fun h => (by cases h)⟩
  | true => exact ⟨fun _ => rfl, fun _ => rfl⟩

end BaseAsks
open BaseAsks

/-- **What claimAt asks.** -/
theorem claimAt_iff (K : Codes) (cur : IoppStage) (row : GroupRow) (cl : BaseClaim) :
    claimAt K cur row = some cl ↔
      ∃ c, K.base[cur.code]? = some c ∧ cur.k = 0 ∧ row.kept.isEmpty = true ∧
        cl = ⟨dense (row.c.fixLow [zeroE]) (ceilLog2 c.ell), row.d.map (·.triple),
          row.target.triple⟩ := by
  cases hc : K.base[cur.code]? with
  | none => simp [claimAt, hc]
  | some c =>
    constructor
    · intro h
      unfold claimAt at h
      rw [hc] at h
      by_cases hb : (cur.k != 0 || !row.kept.isEmpty) = true
      · simp [hb] at h
      · have h2 : cur.k = 0 ∧ row.kept.isEmpty = true := by simpa using hb
        simp [hb] at h
        exact ⟨c, rfl, h2.1, h2.2, h.symm⟩
    · rintro ⟨c', h1, hk, he, rfl⟩
      cases h1
      unfold claimAt
      rw [hc]
      simp [hk, he]

/-- **The Form written out**: the text's own right side. -/
theorem dense_eq (f : Form) (vars : Nat) : dense f vars = (f.writeOut vars).map (·.triple) := rfl

/-- **The base case's numbers of the place, field by field.** -/
theorem basePar_eq (p : P12) (s : Fmt.M1.Stage) :
    basePar p s =
      { place := p.place, C := s.C, Z := s.Z, t := s.t,
        label := p.nums.firstTree + (p.nums.free + p.nums.sent.length - 1),
        own := p.nums.free + p.nums.sent.length - 1, workLam := 0, workBase := p.nums.work } := rfl

/-- **What inRange asks.** -/
theorem inRange_iff (cut : List Fmt.DeclaredRound) (rs : List Fmt.RoundView) :
    inRange cut rs = true ↔ ∀ x ∈ cut.zip rs, ∀ y ∈ x.2.drawn.poss, y < 2 ^ x.1.entry.logN := by
  simp only [inRange, List.all_eq_true, decide_eq_true_eq]

/-- **What baseJ5's test on the plan asks.** -/
theorem baseJ5_planOk_iff (p : P12) (j : Nat) (cur : Fmt.M1.Stage) (cut : List Fmt.DeclaredRound) :
    (baseJ5 p j cur cut).planOk = true ↔
      noStored cut = true ∧ 1 ≤ p.nums.sent.length ∧
        (baseCase (Cl := Unit) (basePar p cur)).planOk = true ∧ baseRounds (basePar p cur) = cut := by
  simp only [baseJ5, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, and_assoc]

/-- **What guard (z) adds on the plan.** -/
theorem ranged_planOk_iff (cut : List Fmt.DeclaredRound) (X : Part T12) :
    (ranged cut X).planOk = true ↔ X.planOk = true ∧ ∀ d ∈ cut, d.entry.logN ≤ 32 := by
  simp only [ranged, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq]

/-- **What guard (z) adds on the view.** -/
theorem ranged_decide_iff (cut : List Fmt.DeclaredRound) (X : Part T12) (t t' : T12) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) :
    (ranged cut X).decide t rs gs = .ok t' ↔ inRange cut rs = true ∧ X.decide t rs gs = .ok t' := by
  show (need _ (inRange cut rs) >>= fun _ => X.decide t rs gs) = .ok t' ↔ _
  rw [bind_iff]
  constructor
  · rintro ⟨u, h1, h2⟩
    exact ⟨(need_iff _ _ u).1 h1, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨(), (need_iff _ _ ()).2 h1, h2⟩

/-- **What lastMember asks.** -/
theorem lastMember_iff (L : GroupLayout) (m : Nat) :
    lastMember L = some m ↔
      L.k = 1 ∧ L.h = 0 ∧ L.members.size = 1 ∧ L.kept = #[false] ∧ L.mainFirst = #[some 0] ∧
        L.maskFirst = #[some 0] ∧ L.members[0]? = some m := by
  unfold lastMember
  split
  · rename_i h
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
    exact ⟨fun g => ⟨h1, h2, h3, h4, h5, h6, g⟩, fun g => g.2.2.2.2.2.2⟩
  · rename_i h
    refine ⟨fun g => (by cases g), fun g => absurd ?_ h⟩
    simp only [Bool.and_eq_true, beq_iff_eq]
    exact ⟨⟨⟨⟨⟨g.1, g.2.1⟩, g.2.2.1⟩, g.2.2.2.1⟩, g.2.2.2.2.1⟩, g.2.2.2.2.2.1⟩

/-- **What oneRowEach asks.** -/
theorem oneRowEach_iff (x : OnBytes.Oracle) (c : IoppStage) :
    oneRowEach x c = true ↔
      x.shape.mainRows = 1 ∧ x.shape.mainDeg = 3 ∧ x.shape.code = c.code ∧ x.shape.maskRows = 1 ∧
        x.shape.maskCode = c.maskCode := by
  simp only [oneRowEach, Bool.and_eq_true, beq_iff_eq, and_assoc]

/-- **What lastPairOk asks.** -/
theorem lastPairOk_iff (P : BasePar) (S : Statement) (c : IoppStage) (m star : Nat) :
    lastPairOk P S c m star = true ↔
      ∃ k z x o, S.codes.base[c.code]? = some k ∧ S.codes.mask[c.maskCode]? = some z ∧
        S.oracles[m]? = some x ∧ S.oracles[star]? = some o ∧
        (k.logN, k.ell, k.r) = (P.C.a, P.C.l, P.C.r) ∧ (z.logN, z.ell, z.r) = (P.Z.a, P.Z.l, P.Z.r) ∧
        star ≠ m ∧ oneRowEach x c = true ∧ x.groups.length ≤ 1 ∧ oneRowEach o c = true ∧
        o.sampled = false ∧ o.shape.answers = 0 ∧ o.spentAsMask = false := by
  unfold lastPairOk
  split
  · rename_i k z x o e1 e2 e3 e4
    simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, decide_eq_true_eq, Bool.not_eq_true',
      and_assoc]
    constructor
    · intro g
      exact ⟨k, z, x, o, e1, e2, e3, e4, g⟩
    · rintro ⟨k', z', x', o', f1, f2, f3, f4, g⟩
      cases e1.symm.trans f1
      cases e2.symm.trans f2
      cases e3.symm.trans f3
      cases e4.symm.trans f4
      exact g
  · rename_i hno
    refine ⟨fun g => (by cases g), ?_⟩
    rintro ⟨k, z, x, o, f1, f2, f3, f4, _⟩
    exact absurd f4 (hno k z x o f1 f2 f3)

/-- **What lastTree asks.** -/
theorem lastTree_iff (P : BasePar) (B : TreeBook) (m star a : Nat) :
    lastTree P B m star = some a ↔
      B.place[m]? = some (a, 0) ∧ B.place[star]? = some (a, 1) ∧
        ∃ T, B.trees[a]? = some T ∧ T.parts = #[m, star] ∧ T.number = P.label ∧
          T.shape.logN = P.C.a ∧ T.shape.logNzk = P.Z.a ∧ T.shape.mainSymbols = #[3, 3] ∧
          T.shape.maskSymbols = #[3, 3] ∧ T.lists = 0 := by
  unfold lastTree
  split
  · rename_i a0 b0 e1 e2
    split
    · rename_i T e3
      split
      · rename_i h
        simp only [Bool.and_eq_true, beq_iff_eq] at h
        obtain ⟨⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
        constructor
        · intro g
          cases g
          exact ⟨e1, h0 ▸ e2, T, e3, h1, h2, h3, h4, h5, h6, h7⟩
        · rintro ⟨f1, _, _⟩
          have := Option.some.inj (e1.symm.trans f1)
          exact congrArg some (congrArg Prod.fst this)
      · rename_i h
        refine ⟨fun g => (by cases g), ?_⟩
        rintro ⟨f1, f2, T', f3, g1, g2, g3, g4, g5, g6, g7⟩
        obtain rfl : a0 = a := congrArg Prod.fst (Option.some.inj (e1.symm.trans f1))
        obtain rfl : b0 = a0 := congrArg Prod.fst (Option.some.inj (e2.symm.trans f2))
        cases e3.symm.trans f3
        exact absurd (by simp only [Bool.and_eq_true, beq_iff_eq]; exact
          ⟨⟨⟨⟨⟨⟨⟨trivial, g1⟩, g2⟩, g3⟩, g4⟩, g5⟩, g6⟩, g7⟩) h
    · rename_i e3
      refine ⟨fun g => (by cases g), ?_⟩
      rintro ⟨f1, _, T', f3, _⟩
      obtain rfl : a0 = a := congrArg Prod.fst (Option.some.inj (e1.symm.trans f1))
      cases e3.symm.trans f3
  · rename_i hno
    refine ⟨fun g => (by cases g), ?_⟩
    rintro ⟨f1, f2, _⟩
    exact absurd f2 (hno a a f1)

/-- The record behind a yes of the last part. -/
def spent (t : T12) (star a : Nat) : T12 :=
  { t with
    st := { t.st with oracles := t.st.oracles.modify star fun x => { x with spentAsMask := true } }
    book := { t.book with trees := t.book.trees.modify a fun x => { x with lists := x.lists + 1 } }
    pass := .nothing, mask := none }

/-- **What a yes of the last part asks: every test of the text, in the text's order, and the record
behind written out.** -/
theorem baseJ5_decide_iff (p : P12) (j : Nat) (cur : Fmt.M1.Stage) (cut : List Fmt.DeclaredRound)
    (t t' : T12) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))) :
    (baseJ5 p j cur cut).decide t rs gs = .ok t' ↔
      ∃ (row : GroupRow) (L : GroupLayout) (c : IoppStage) (d1 d2 : Fmt.DeclaredRound) (cl u : BaseClaim)
        (m star a : Nat),
        t.pass = .claim row L ∧ stageAt p j cur = some c ∧ cut = [d1, d2] ∧
        claimAt t.st.codes c row = some cl ∧
        ((t.st.codes.base[c.code]?).any fun k =>
          Own.formFits (row.c.fixLow [zeroE]) (ceilLog2 k.ell)) = true ∧
        baseDecide (basePar p cur) cl rs gs = .ok u ∧
        (match rs, gs with
          | [_, rB], [g] => g.map (·.1) == Fmt.listOf rB.drawn.poss
          | _, _ => false) = true ∧
        lastMember L = some m ∧ t.mask = some star ∧
        lastPairOk (basePar p cur) t.st c m star = true ∧
        lastTree (basePar p cur) t.book m star = some a ∧ t' = spent t star a := by
  constructor
  · intro h
    unfold baseJ5 at h
    dsimp only at h
    split at h
    · rename_i row L c d1 d2 e1 e2
      obtain ⟨cl, h1, h⟩ := (bind_iff _ _ _).1 h
      obtain ⟨u1, h2, h⟩ := (bind_iff _ _ _).1 h
      obtain ⟨u, h3, h⟩ := (bind_iff _ _ _).1 h
      obtain ⟨u4, h4, h⟩ := (bind_iff _ _ _).1 h
      obtain ⟨m, h5, h⟩ := (bind_iff _ _ _).1 h
      obtain ⟨star, h6, h⟩ := (bind_iff _ _ _).1 h
      obtain ⟨u7, h7, h⟩ := (bind_iff _ _ _).1 h
      obtain ⟨a, h8, h⟩ := (bind_iff _ _ _).1 h
      exact ⟨row, L, c, d1, d2, cl, u, m, star, a, e1, e2, rfl, (named_iff _ _ _).1 h1,
        (need_iff _ _ _).1 h2, h3, (need_iff _ _ _).1 h4, (named_iff _ _ _).1 h5,
        (named_iff _ _ _).1 h6, (need_iff _ _ _).1 h7, (named_iff _ _ _).1 h8,
        (Except.ok.inj h).symm⟩
    · cases h
  · rintro ⟨row, L, c, d1, d2, cl, u, m, star, a, e1, e2, rfl, h1, h2, h3, h4, h5, h6, h7, h8, rfl⟩
    unfold baseJ5
    dsimp only
    rw [e1, e2]
    dsimp only
    refine (bind_iff _ _ _).2 ⟨cl, (named_iff _ _ _).2 h1, ?_⟩
    refine (bind_iff _ _ _).2 ⟨(), (need_iff _ _ _).2 h2, ?_⟩
    refine (bind_iff _ _ _).2 ⟨u, h3, ?_⟩
    refine (bind_iff _ _ _).2 ⟨(), (need_iff _ _ _).2 h4, ?_⟩
    refine (bind_iff _ _ _).2 ⟨m, (named_iff _ _ _).2 h5, ?_⟩
    refine (bind_iff _ _ _).2 ⟨star, (named_iff _ _ _).2 h6, ?_⟩
    refine (bind_iff _ _ _).2 ⟨(), (need_iff _ _ _).2 h7, ?_⟩
    refine (bind_iff _ _ _).2 ⟨a, (named_iff _ _ _).2 h8, ?_⟩
    rfl

end VerifiableInference.Desc.K12

#print axioms VerifiableInference.Desc.K12.basePar_eq
#print axioms VerifiableInference.Desc.K12.inRange_iff
#print axioms VerifiableInference.Desc.K12.claimAt_iff
#print axioms VerifiableInference.Desc.K12.baseJ5_planOk_iff
#print axioms VerifiableInference.Desc.K12.ranged_planOk_iff
#print axioms VerifiableInference.Desc.K12.ranged_decide_iff
#print axioms VerifiableInference.Desc.K12.baseJ5_decide_iff
#print axioms VerifiableInference.Desc.K12.lastMember_iff
#print axioms VerifiableInference.Desc.K12.oneRowEach_iff
#print axioms VerifiableInference.Desc.K12.lastPairOk_iff
#print axioms VerifiableInference.Desc.K12.lastTree_iff
