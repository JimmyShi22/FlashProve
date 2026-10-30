-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
ZKCP/WithOpenings.lean: a scheme with openings in place of proofs.

To open a verifier's key of a scheme A is to name an index and a number such that A's committer, run
again at that index with its random choices read off that number (`OComp.withCoins`,
ZKCP/CoinsFirst.lean), returns that key.
`Arg.withOpenings A` is the scheme whose instances are such pairs (index, number), whose proofs are
empty, and whose verifier runs A's committer again and compares (`Arg.commitAt`). Its relation
(`openingRelation`) says "the pair names the index".
Why. Index binding of `A.withOpenings` (`HasIndexBindingWith`, ZKCP/Defs.lean) is the statement
"whoever opens a key, opens it to the index that the extractor gives from the key and its maker's
queries". So the theorems that carry index binding from one form of a scheme to another carry that
statement.
  `OpensToExtracted A Ei β`          the statement as a game of its own (`openingExp`)
  `opensToExtracted_of_binding`     it follows from index binding of `A.withOpenings`, same bound
  `OpensToExtracted.atCoins`        it is not empty: from a key that A's own committer makes at any
                                    given number, and that committer's queries, `Ei` gives the
                                    index, except with probability β tC 0 (a β of 1 or more says
                                    nothing)
The same definitions for schemes over a family of oracles: Rom/WithOpenings.lean.
This file shows of no scheme that it has the property.
-/
import ZKCP.CoinsFirst
import ZKCP.HonestKey
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

open scoped ENNReal

namespace ZKCP

variable {lam : ℕ} {I X W IVK ISK Pf : Type}

/-- The relation of openings: an instance is an index with a number, and it belongs to the index
that it names. There is no witness and there are no public parameters. -/
def openingRelation (I : Type) : IndexedRelation I (I × ℕ) Unit Unit where
  rel i x _ := x.1 = i
  pp _ := ()

/-- The verifier's key that A's committer returns at the index i, with its random choices read off
the number `coins`. Nothing is sampled. -/
def Arg.commitAt (A : Arg lam I X W IVK ISK Pf) (i : I) (coins : ℕ) : OComp lam IVK :=
  ((A.C i).withCoins coins).mapO Prod.fst

open Classical in
/-- The scheme A with openings in place of proofs. The committer is A's. An instance is an index
with a number; the proof is empty; the verifier runs A's committer at that index and number and
accepts if it returns the key. -/
def Arg.withOpenings (A : Arg lam I X W IVK ISK Pf) :
    Arg lam I (I × ℕ) Unit IVK ISK Unit where
  C := A.C
  P := fun _ _ _ => .pure ()
  V := fun key x _ => (A.commitAt x.1 x.2).mapO fun key' => decide (key' = key)

/-- The extractor for `Arg.withOpenings`: the index that E gives; there is no witness. -/
def Extractor.withOpenings (E : Extractor lam I X W IVK Pf) :
    Extractor lam I (I × ℕ) Unit IVK Unit where
  Ei := E.Ei
  Ew := fun _ _ _ _ _ => ()

/-- `commitAt` samples nothing. -/
theorem Arg.drawsNoCoin_commitAt (A : Arg lam I X W IVK ISK Pf) (i : I) (coins : ℕ) :
    (A.commitAt i coins).DrawsNoCoin := by
  unfold Arg.commitAt
  rw [← OComp.withCoins_mapO]
  exact OComp.drawsNoCoin_withCoins _ _

/-- `commitAt` makes no more queries than the committer. -/
theorem Arg.queryBound_commitAt (A : Arg lam I X W IVK ISK Pf) (i : I) (coins t : ℕ)
    (h : (A.C i).QueryBound t) : (A.commitAt i coins).QueryBound t :=
  OComp.QueryBound.mapO _ _ t (OComp.QueryBound.withCoins (A.C i) t coins h)

open Classical in
/-- Under a hash function under which A's committer returns the given key at the opening x, the
verifier of `A.withOpenings` accepts. -/
theorem Arg.run_withOpenings_V_of_eq (A : Arg lam I X W IVK ISK Pf) (f : Oracle lam) (key : IVK)
    (x : I × ℕ) (π : Unit) {k : IVK} (h : (A.commitAt x.1 x.2).run f = PMF.pure k)
    (hk : k = key) : (A.withOpenings.V key x π).run f = PMF.pure true := by
  show ((A.commitAt x.1 x.2).mapO fun key' => decide (key' = key)).run f = _
  rw [OComp.run_mapO, h, PMF.pure_map, decide_eq_true hk]

open Classical in
/-- Under a hash function under which A's committer returns another key at the opening x, the
verifier of `A.withOpenings` rejects. -/
theorem Arg.run_withOpenings_V_of_ne (A : Arg lam I X W IVK ISK Pf) (f : Oracle lam) (key : IVK)
    (x : I × ℕ) (π : Unit) {k : IVK} (h : (A.commitAt x.1 x.2).run f = PMF.pure k)
    (hk : k ≠ key) : (A.withOpenings.V key x π).run f = PMF.pure false := by
  show ((A.commitAt x.1 x.2).mapO fun key' => decide (key' = key)).run f = _
  rw [OComp.run_mapO, h, PMF.pure_map, decide_eq_false hk]

/-- The game of openings. Any committer outputs a key, and its queries are logged. Any opener, which
is given the committer's state, names an index and a number. Then A's committer runs at these. The
outcome: what `Ei` gives from the key and the log; the key; the index that was named; the key that
was computed again. -/
def openingExp (A : Arg lam I X W IVK ISK Pf) (Ei : IVK → Trace lam → Option I) {St : Type}
    (Ct : OComp lam (IVK × St)) (Ot : St → OComp lam (I × ℕ)) :
    OComp lam (Option I × IVK × I × IVK) :=
  Ct.withTrace.bind fun c => (Ot c.1.2).bind fun o => (A.commitAt o.1 o.2).bind fun key =>
    .pure (Ei c.1.1 c.2, c.1.1, o.1, key)

/-- Whoever opens a key opens it to the extracted index. For every committer with at most tC queries
and every opener with at most tO queries, the probability that the key computed again is the
committer's, while `Ei` has not given the index that the opener names, is at most β tC tO. -/
def OpensToExtracted (A : Arg lam I X W IVK ISK Pf) (Ei : IVK → Trace lam → Option I)
    (β : ℕ → ℕ → ℝ≥0∞) : Prop :=
  ∀ (tC tO : ℕ) (St : Type) (Ct : OComp lam (IVK × St)) (Ot : St → OComp lam (I × ℕ)),
    Ct.QueryBound tC → (∀ st, (Ot st).QueryBound tO) →
      Pr (openingExp A Ei Ct Ot) (fun _ => {r | r.2.2.2 = r.2.1 ∧ r.1 ≠ some r.2.2.1}) ≤ β tC tO

/-- The event of index binding at the relation of openings: the verifier accepts, and the extracted
index is not the one that the opening names. -/
theorem mem_bindingBad_opening (o : BindingOutcome I (I × ℕ) Unit) :
    o ∈ bindingBad (openingRelation I) ↔ o.accept = true ∧ o.iStar ≠ some o.x.1 := by
  obtain ⟨b, iStar, x, w⟩ := o
  cases iStar with
  | none =>
    constructor
    · rintro ⟨h, -⟩
      exact ⟨h, fun h' => Option.some_ne_none _ h'.symm⟩
    · rintro ⟨h, -⟩
      exact ⟨h, Or.inl fun h' => h'⟩
  | some i =>
    constructor
    · rintro ⟨h, h' | h'⟩
      · exact ⟨h, fun e => h' ⟨(), (Option.some.inj e).symm⟩⟩
      · exact ⟨h, fun e => h' (Option.some.inj e).symm⟩
    · rintro ⟨h, h'⟩
      exact ⟨h, Or.inr fun e => h' (congrArg some (Eq.symm e))⟩

/-- Index binding of `A.withOpenings` gives the statement on openings, with the same bound. -/
theorem opensToExtracted_of_binding {A : Arg lam I X W IVK ISK Pf}
    {E : Extractor lam I X W IVK Pf} {β : ℕ → ℕ → ℝ≥0∞}
    (h : HasIndexBindingWith (openingRelation I) A.withOpenings E.withOpenings β) :
    OpensToExtracted A E.Ei β := by
  classical
  intro tC tO St Ct Ot hC hO
  refine le_trans (MeasureTheory.lintegral_mono fun f => ?_)
    (h tC tO St Ct (fun st => (Ot st).mapO fun o => (o, ())) hC
      fun st => OComp.QueryBound.mapO _ _ tO (hO st))
  show prob ((Ct.withTrace.bind fun c => (Ot c.1.2).bind fun o =>
        (A.commitAt o.1 o.2).bind fun key =>
        (.pure (E.Ei c.1.1 c.2, c.1.1, o.1, key) : OComp lam (Option I × IVK × I × IVK))).run f)
      {r | r.2.2.2 = r.2.1 ∧ r.1 ≠ some r.2.2.1}
    ≤ prob ((Ct.withTrace.bind fun c =>
        ((Ot c.1.2).mapO fun o => (o, ())).withTrace.bind fun o' =>
        ((A.commitAt o'.1.1.1 o'.1.1.2).mapO fun key' => decide (key' = c.1.1)).bind fun b =>
        (.pure ⟨b, E.Ei c.1.1 c.2, o'.1.1, ()⟩ : OComp lam (BindingOutcome I (I × ℕ) Unit))).run f)
      (bindingBad (openingRelation I))
  rw [run_bind, run_bind, prob_bind, prob_bind]
  refine expect_mono _ fun c => ?_
  rw [OComp.withTrace_mapO, OComp.mapO_bind, run_bind, run_bind,
    ← OComp.run_withTrace_fst f (Ot c.1.2), PMF.bind_map, prob_bind, prob_bind]
  refine expect_mono _ fun o => ?_
  show prob (((A.commitAt o.1.1 o.1.2).bind fun key =>
        (.pure (E.Ei c.1.1 c.2, c.1.1, o.1.1, key) : OComp lam (Option I × IVK × I × IVK))).run f) _
    ≤ prob ((((A.commitAt o.1.1 o.1.2).mapO fun key' => decide (key' = c.1.1)).bind fun b =>
        (.pure ⟨b, E.Ei c.1.1 c.2, o.1, ()⟩ : OComp lam (BindingOutcome I (I × ℕ) Unit))).run f) _
  rw [OComp.mapO_bind, run_bind, run_bind, prob_bind, prob_bind]
  refine expect_mono _ fun key => ?_
  show prob (PMF.pure (E.Ei c.1.1 c.2, c.1.1, o.1.1, key)) _
    ≤ prob (PMF.pure (⟨decide (key = c.1.1), E.Ei c.1.1 c.2, o.1, ()⟩ :
      BindingOutcome I (I × ℕ) Unit)) _
  rw [prob_pure, prob_pure]
  split
  · rename_i hr
    obtain ⟨h1, h2⟩ := hr
    rw [if_pos ((mem_bindingBad_opening _).2 ⟨decide_eq_true h1, h2⟩)]
  · exact zero_le _

/-- The statement on openings is not empty. Let A's own committer run at an index i and at any given
number, and let the opener hand back i and that number. So, from the key and that committer's
queries, `Ei` gives i, except with probability β tC 0, where tC bounds the committer's queries. The
probability is over the hash function alone: nothing is sampled. -/
theorem OpensToExtracted.atCoins {A : Arg lam I X W IVK ISK Pf}
    {Ei : IVK → Trace lam → Option I} {β : ℕ → ℕ → ℝ≥0∞} (h : OpensToExtracted A Ei β) (i : I)
    (coins : ℕ) {tC : ℕ} (hq : (A.C i).QueryBound tC) :
    Pr (A.commitAt i coins).withTrace (fun _ => {o | Ei o.1 o.2 ≠ some i}) ≤ β tC 0 := by
  classical
  refine le_trans (MeasureTheory.lintegral_mono fun f => ?_)
    (h tC 0 Unit ((A.commitAt i coins).mapO fun key => (key, ())) (fun _ => .pure (i, coins))
      (OComp.QueryBound.mapO _ _ tC (A.queryBound_commitAt i coins tC hq)) fun _ => trivial)
  show prob ((A.commitAt i coins).withTrace.run f) {o | Ei o.1 o.2 ≠ some i}
    ≤ prob ((((A.commitAt i coins).mapO fun key => (key, ())).withTrace.bind fun c =>
        (OComp.pure (i, coins) : OComp lam (I × ℕ)).bind fun o =>
        (A.commitAt o.1 o.2).bind fun key =>
        (.pure (Ei c.1.1 c.2, c.1.1, o.1, key) : OComp lam (Option I × IVK × I × IVK))).run f)
      {r | r.2.2.2 = r.2.1 ∧ r.1 ≠ some r.2.2.1}
  rw [OComp.withTrace_mapO, OComp.mapO_bind, run_bind, prob_bind, prob_eq_expect]
  refine expect_le_on_support _ fun c hc => ?_
  obtain ⟨key, hkey⟩ := OComp.DrawsNoCoin.run f _ (A.drawsNoCoin_commitAt i coins)
  have hc1 : c.1 = key := by
    have h1 := mem_support_withTrace f _ c hc
    rw [hkey] at h1
    exact (PMF.mem_support_pure_iff _ _).1 h1
  show _ ≤ prob (((A.commitAt i coins).bind fun key =>
        (.pure (Ei c.1 c.2, c.1, i, key) : OComp lam (Option I × IVK × I × IVK))).run f) _
  rw [run_bind, hkey, PMF.pure_bind]
  show _ ≤ prob (PMF.pure (Ei c.1 c.2, c.1, i, key)) _
  rw [prob_pure]
  split
  · rename_i hbad
    rw [if_pos ⟨hc1.symm, hbad⟩]
  · exact zero_le _

end ZKCP
