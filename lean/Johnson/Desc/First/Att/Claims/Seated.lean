-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/Claims/Seated.lean: kind K5: the claims' law on the seat of
Johnson/Desc/First/Att/SeatC.lean: the block's three named runs (Johnson/Desc/First/Att/RunsK.lean:
firstK, keysOfK, secondK over seatCS (parCOf A)) at the first chain's carried record, inside an
attention link (s.here = .att a).

Main names:
  `stripT`, `stripIn`: a record of tables, and of what the runs read, with its list for the
    smallness test (funs) emptied. `first_strip`, `second_strip`, `keys_strip`: the runs never read
    that list (by unfolding).
  `Four`, `Lies a f`: the four fields of the link's part of the carried record that are none until
    their steps lay them (g, planes, scores, t), and that they lie there: a.g = some f.g, and so on.
  `heardAt A a f`: the plain record of what the claims read, made of the plan's shape and number, of
    the four and of the link's part of the carried record, field by field.
  `TablesAgree A a f`: a premise, not proved here: the tables that tablesP makes anew, at the seat's
    points and the lookup's data, are, but for funs, the tables that lie in the carried record
    (f.t). A segment's tables are made by two texts. Johnson/Desc/First/Att/Claims/TablesAgree.lean
    and Johnson/Desc/First/Att/Claims/ReadsLays.lean pay it behind the step that lays them.
  `Spec.SeatedFirst`, `SeatedKeys`, `SeatedSecond`: where the seated run returns: the state is
    handed back untouched, the ledger has an array number A.iU3 with K columns, and the forms and
    key forms are the written ones at heardAt A a f and K. `Spec.SeatedWhole`: the three fill the
    middle of Fo.attT A (heardAt A a f) K. `Spec.SeatedReturn`: the seated runs return where tablesP
    returns, the ledger gives K, and the seat's record agrees in what is public with a record at
    which the three runs return.
Premises, all named in the statements: s.here = .att a; Lies a f; A.NC = A.S.calls.size; TablesAgree
A a f.
Used of OnBytes: what Johnson/Desc/First/Att/Claims/Top.lean names; the records Attention.Plan and
the fields of First.AttOwn (the four records, Tables, Forest.Heard, and the ledger's record Fork,
read for its number of columns alone, as the seat does); the seat's tools lookOf and padOf (pure
functions of the lookup: Forest.planeCols, phiB, phiP, noPub, pubRun: named by SeatC.lean, opened by
nothing here).
Not claimed: that a claim holds; TablesAgree.

Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.Claims.Returns

set_option autoImplicit false

namespace K5Law
open OnBytes OnBytes.Model OnBytes.Attention
open VerifiableInference.Desc.First
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.First.Att.P (Pts TablesP ParC geoOf ptsOfOwn parCOf seatCS lookOf padOf)
open VerifiableInference.Desc.First.Att.P.Runs (W JoinsP PadIn)

/-- A record of tables, its list for the smallness test emptied. -/
def stripT (t : TablesP) : TablesP := { t with funs := #[] }

def stripIn (i : P.Runs.In) : P.Runs.In := { i with t := stripT i.t }

/-- The runs never read the list for the smallness test. -/
theorem first_strip (i : P.Runs.In) (K : ℕ) : P.Runs.firstRun (stripIn i) K = P.Runs.firstRun i K := rfl
theorem second_strip (i : P.Runs.In) (K : ℕ) : P.Runs.secondRun (stripIn i) K = P.Runs.secondRun i K := rfl
theorem keys_strip (i : P.Runs.In) (k3 : PadIn) (j : JoinsP) :
    P.Runs.keysRun (stripIn i) k3 j = P.Runs.keysRun i k3 j := rfl

/-- The four fields of the link's part of the carried record that are none until their steps lay them. -/
structure Four where
  g : Forest.Heard
  planes : Array PlaneClaim
  scores : Array Score
  t : Tables

/-- The four lie in the carried record. -/
structure Lies (a : AttOwn) (f : Four) : Prop where
  g : a.g = some f.g
  planes : a.planes = some f.planes
  scores : a.scores = some f.scores
  t : a.t = some f.t

/-- The plain record of OnBytes/Model of what the claims read, out of the plan and the link's part of the carried record. -/
def heardAt (A : Plan) (a : AttOwn) (f : Four) : Attention.Heard :=
  { S := A.S, g := f.g, planes := f.planes, scores := f.scores, d := a.d, x := a.x, t := f.t, iU3 := A.iU3 }

/-- The tables that the kind's own text makes at the seat. -/
def seatTables (A : Plan) (a : AttOwn) (f : Four) : Option TablesP :=
  P.tablesP (parCOf A).geo (parCOf A).mats (parCOf A).nW (lookOf (parCOf A).geo.lmb f.g)
    (ptsOfOwn f.planes f.scores a.d a.x)

/-- What the seated runs read, at tables t. -/
def seatIn (A : Plan) (a : AttOwn) (f : Four) (t : TablesP) : P.Runs.In :=
  { g := (parCOf A).geo, p := ptsOfOwn f.planes f.scores a.d a.x, t := t, zk := f.g.zk, iU3 := (parCOf A).iU3 }

/-- K at the seat: the columns of the ledger's array of tables. -/
def seatK (A : Plan) (a : AttOwn) : Option ℕ := (a.F.trees[(parCOf A).iU3]?).map (·.K)

/-- **Premise (a).** The tables made anew by the kind's text are, but for funs, those in the carried record. -/
def TablesAgree (A : Plan) (a : AttOwn) (f : Four) : Prop :=
  ∀ t, seatTables A a f = some t → stripT t = tabsOld f.t

/-- Under premise (a) the seat's record, stripped, is inOld. -/
theorem seat_strip (A : Plan) (a : AttOwn) (f : Four) (t : TablesP) (h : stripT t = tabsOld f.t) :
    stripIn (seatIn A a f t) = inOld (heardAt A a f) := by
  unfold stripIn seatIn inOld heardAt
  dsimp only
  rw [h]
  rfl

/-- What the seat finds inside an attention link. -/
theorem inOf_att (A : Plan) (s : S) (a : AttOwn) (f : Four) (hs : s.here = .att a) (hf : Lies a f) :
    P.inOf (seatCS (parCOf A)) (parCOf A) s =
      (seatTables A a f).bind fun t => (seatK A a).bind fun K => some (seatIn A a f t, K) := by
  unfold P.inOf seatCS seatTables seatK seatIn
  simp only [hs, hf.g, hf.planes, hf.scores]
  rfl

/-! ### at any record that, stripped, is inOld h -/

theorem first_is_of (A : Plan) (h : Attention.Heard) (i : P.Runs.In) (e : stripIn i = inOld h)
    (hN : A.NC = h.S.calls.size) (K : ℕ) (l : List Aff) (j : JoinsP)
    (hr : P.Runs.firstRun i K = some (l, j)) :
    l = Fo.claim3T h K ++ (Fo.claim4T h K ++ Fo.claim5T h K) ∧ j = jP (Fo.attJoinsT A h) := by
  rw [← first_strip, e] at hr
  exact first_is_at A h K l j hN hr

theorem second_is_of (h : Attention.Heard) (i : P.Runs.In) (e : stripIn i = inOld h) (K : ℕ)
    (l : List Aff) (hr : P.Runs.secondRun i K = some l) :
    l = Fo.claim6T h K ++ (Fo.claim7T h K ++ Fo.claim8T h K) := by
  rw [← second_strip, e] at hr
  exact second_is h K l hr

namespace Spec

def SeatedFirst : Prop :=
  ∀ (A : Plan) (s s' : S) (a : AttOwn) (f : Four) (l : List Aff),
    s.here = .att a → Lies a f → A.NC = A.S.calls.size → TablesAgree A a f →
    P.firstK (seatCS (parCOf A)) (parCOf A) s = some (l, s') →
      s' = s ∧ ∃ K, seatK A a = some K ∧
        l = Fo.claim3T (heardAt A a f) K ++ (Fo.claim4T (heardAt A a f) K ++ Fo.claim5T (heardAt A a f) K)

def SeatedKeys : Prop :=
  ∀ (A : Plan) (s : S) (a : AttOwn) (f : Four) (kf : Array Aff),
    s.here = .att a → Lies a f → A.NC = A.S.calls.size → TablesAgree A a f →
    P.keysOfK (seatCS (parCOf A)) (parCOf A) s = some kf → kf = (Fo.attJoinsT A (heardAt A a f)).kf

def SeatedSecond : Prop :=
  ∀ (A : Plan) (s s' : S) (a : AttOwn) (f : Four) (l : List Aff),
    s.here = .att a → Lies a f → TablesAgree A a f →
    P.secondK (seatCS (parCOf A)) (parCOf A) s = some (l, s') →
      s' = s ∧ ∃ K, seatK A a = some K ∧
        l = Fo.claim6T (heardAt A a f) K ++ (Fo.claim7T (heardAt A a f) K ++ Fo.claim8T (heardAt A a f) K)

def SeatedWhole : Prop :=
  ∀ (A : Plan) (s s₁ s₂ : S) (a : AttOwn) (f : Four) (l₁ l₂ : List Aff) (kf : Array Aff),
    s.here = .att a → Lies a f → A.NC = A.S.calls.size → TablesAgree A a f →
    P.firstK (seatCS (parCOf A)) (parCOf A) s = some (l₁, s₁) →
    P.keysOfK (seatCS (parCOf A)) (parCOf A) s = some kf →
    P.secondK (seatCS (parCOf A)) (parCOf A) s = some (l₂, s₂) →
      ∃ K, seatK A a = some K ∧
        Fo.attT A (heardAt A a f) K = f.g.rows.toList ++ (l₁ ++ ([Fo.joinForm f.g kf] ++ (l₂ ++
          (Fo.planeFormsT f.g A.S.cf.lmb
            (fun e col => Fo.u3Form A.iU3 K ((if e == 0 then f.t.tBit0 else f.t.tBit1) + col))
            (fun col => Fo.u3Form A.iU3 K (f.t.tPin + col))).toList)))

def SeatedReturn : Prop :=
  ∀ (A : Plan) (s : S) (a : AttOwn) (f : Four) (t : TablesP) (K : ℕ) (i0 : P.Runs.In),
    s.here = .att a → Lies a f → seatTables A a f = some t → seatK A a = some K →
    Same (seatIn A a f t) i0 → AllReturn i0 K (padOf f.g.shape) →
      ∃ l₁ kf l₂, P.firstK (seatCS (parCOf A)) (parCOf A) s = some (l₁, s) ∧
        P.keysOfK (seatCS (parCOf A)) (parCOf A) s = some kf ∧
        P.secondK (seatCS (parCOf A)) (parCOf A) s = some (l₂, s)

end Spec

/-- The seated "first", opened. -/
theorem firstK_att (A : Plan) (s : S) (a : AttOwn) (f : Four) (hs : s.here = .att a) (hf : Lies a f) :
    P.firstK (seatCS (parCOf A)) (parCOf A) s =
      (seatTables A a f).bind fun t => (seatK A a).bind fun K =>
        (P.Runs.firstRun (seatIn A a f t) K).bind fun x => some (x.1, s) := by
  unfold P.firstK
  rw [inOf_att A s a f hs hf]
  cases seatTables A a f <;> [rfl; skip]
  cases seatK A a <;> rfl

theorem secondK_att (A : Plan) (s : S) (a : AttOwn) (f : Four) (hs : s.here = .att a) (hf : Lies a f) :
    P.secondK (seatCS (parCOf A)) (parCOf A) s =
      (seatTables A a f).bind fun t => (seatK A a).bind fun K =>
        (P.Runs.secondRun (seatIn A a f t) K).bind fun x => some (x, s) := by
  unfold P.secondK
  rw [inOf_att A s a f hs hf]
  cases seatTables A a f <;> [rfl; skip]
  cases seatK A a <;> rfl

theorem keysOfK_att (A : Plan) (s : S) (a : AttOwn) (f : Four) (hs : s.here = .att a) (hf : Lies a f) :
    P.keysOfK (seatCS (parCOf A)) (parCOf A) s =
      (seatTables A a f).bind fun t => (seatK A a).bind fun K =>
        (P.Runs.firstRun (seatIn A a f t) K).bind fun x =>
          P.Runs.keysRun (seatIn A a f t) (padOf f.g.shape) x.2 := by
  unfold P.keysOfK
  rw [inOf_att A s a f hs hf]
  have hp : (seatCS (parCOf A)).pad s = some (padOf f.g.shape) := by
    unfold seatCS
    simp only [hs, hf.g]
    rfl
  cases seatTables A a f <;> [rfl; skip]
  cases seatK A a <;> [rfl; skip]
  simp only [Option.bind_eq_bind, Option.bind_some, hp]

theorem seated_first : Spec.SeatedFirst := by
  intro A s s' a f l hs hf hN hT hr
  rw [firstK_att A s a f hs hf] at hr
  simp only [Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at hr
  obtain ⟨t, ht, K, hK, x, hx, e1, e2⟩ := hr
  refine ⟨e2.symm, K, hK, ?_⟩
  rw [← e1]
  exact (first_is_of A (heardAt A a f) _ (seat_strip A a f t (hT t ht)) hN K x.1 x.2 hx).1

theorem seated_keys : Spec.SeatedKeys := by
  intro A s a f kf hs hf hN hT hr
  rw [keysOfK_att A s a f hs hf] at hr
  simp only [Option.bind_eq_some_iff] at hr
  obtain ⟨t, ht, K, hK, x, hx, hk⟩ := hr
  rw [keys_is _ _ _ _ hk,
    (first_is_of A (heardAt A a f) _ (seat_strip A a f t (hT t ht)) hN K x.1 x.2 hx).2]
  rfl

theorem seated_second : Spec.SeatedSecond := by
  intro A s s' a f l hs hf hT hr
  rw [secondK_att A s a f hs hf] at hr
  simp only [Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at hr
  obtain ⟨t, ht, K, hK, x, hx, e1, e2⟩ := hr
  refine ⟨e2.symm, K, hK, ?_⟩
  rw [← e1]
  exact second_is_of (heardAt A a f) _ (seat_strip A a f t (hT t ht)) K x hx

theorem seated_whole : Spec.SeatedWhole := by
  intro A s s₁ s₂ a f l₁ l₂ kf hs hf hN hT h1 hk h2
  obtain ⟨_, K, hK, e1⟩ := seated_first A s s₁ a f l₁ hs hf hN hT h1
  obtain ⟨_, K', hK', e2⟩ := seated_second A s s₂ a f l₂ hs hf hT h2
  have ek := seated_keys A s a f kf hs hf hN hT hk
  have eK : K' = K := by rw [hK] at hK'; exact (Option.some.inj hK').symm
  subst eK e1 e2 ek
  refine ⟨K', hK, ?_⟩
  unfold Fo.attT
  simp only [List.append_assoc]
  rfl

theorem seated_return : Spec.SeatedReturn := by
  intro A s a f t K i0 hs hf ht hK H h0
  obtain ⟨l₁, j, kf, l₂, h1, hk, h2⟩ := returns_where _ _ K _ H h0
  refine ⟨l₁, kf, l₂, ?_, ?_, ?_⟩
  · rw [firstK_att A s a f hs hf, ht, hK]
    simp only [Option.bind_some, h1]
  · rw [keysOfK_att A s a f hs hf, ht, hK]
    simp only [Option.bind_some, h1]
    exact hk
  · rw [secondK_att A s a f hs hf, ht, hK]
    simp only [Option.bind_some, h2]

end K5Law
