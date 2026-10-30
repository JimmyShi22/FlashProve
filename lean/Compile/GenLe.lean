-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/GenLe.lean: completeness, index binding and index privacy (ZKCP/Gen.lean) transfer along a
map on verification keys and a map on proofs, if the new verifier accepts what the old one accepts
and nothing else.

Generic in the schemes. Given a scheme A = (C, P, V), maps κ on verification keys and τ on proofs,
and a verifier V' for the new keys and proofs, `mapArg A κ τ V'` is the scheme C' = C, followed by κ
on the verification key (the proving key does not change); P' = P, followed by τ on each proof; V'.
`AccLe a b`: b accepts whenever a does, in two senses at once: for every family of oracle functions
b returns true with at least the probability with which a does; and if a accepts when its queries
are answered from a trace (`RunsIn`, Compile/Spec.lean), so does b, on the same trace. (The three
properties need the first sense only; statements on accepted proof strings use the second.) Then,
with the same relation and the same bounds:

  `completeness`    if V' on (κ v, x, τ π) accepts whenever V on (v, x, π) does (`hup`)
  `binding`         if there are maps κ', σ back such that V on (κ' v', x, σ π') accepts whenever V'
                    on (v', x, π') does (`hdown`); the extractor is composed with κ' on keys and σ
                    on proofs (`pullEK`)
  `privacyWith`     always: the simulator is that of A, followed by κ on the key and by τ on each
                    proof (`pushSimK`)
  `main`            the three together
  `localTo_pullEK`  the composed extractor is `LocalTo` a query encoding m if the old one is, which
                    the step to one hash function (Rom/Family.lean) asks of an explicit extractor

Compile/GenMap.lean has the case κ = id with equalities of programs V v x π = V' v x (τ π) and τ ∘ σ
= id. Here V and V' may differ as programs (one may stop earlier and reject), κ', σ need not be
sections, and the number of V's and V''s queries does not enter: an adversarial committer or prover
against the new scheme is followed by κ' or σ, which make no query. `mapS`, `on2`, `pullV`,
`released_map` of Compile/GenMap.lean are used.

Notation: ZKCP: see `IsZKCPArg`, ZKCP/Defs.lean.

Limits: no statement on a concrete scheme. Nothing on how many queries V' makes. Refined
completeness (`HasRefinedCompletenessError`, ZKCP/Gen.lean) and the further theorems on the compiled
schemes (adaptive completeness, many proofs, extraction) are not carried over.
Terms: lean/GLOSSARY.md.
-/
import Compile.GenMap
import Compile.MerkleRom
import Rom.Family

noncomputable section

namespace Compile.GenLe
open ZKCP.Gen Rom Prob Compile.GenMap
open scoped ENNReal

variable {S : OSpec} {I X W PP IVK IVK' ISK Pf Pf' : Type}

/-- The scheme A with its verification keys and proofs mapped, and the verifier V'. -/
def mapArg (A : Arg S I X W IVK ISK Pf) (κ : IVK → IVK')
    (τ : Pf → Pf') (V' : IVK' → X → Pf' → OComp S Bool) : Arg S I X W IVK' ISK Pf' where
  C := fun i => (A.C i).bind fun o => .pure (κ o.1, o.2)
  P := fun k b => (A.P k b).bind fun l => .pure (mapS τ l)
  V := V'

/-- b accepts whenever a does: for every family of oracle functions, b returns true with at least
the probability with which a does; and if a accepts on a trace (`RunsIn`), so does b -/
def AccLe (a b : OComp S Bool) : Prop :=
  (∀ f : Fam S, PrCoins f a {true} ≤ PrCoins f b {true}) ∧
  ∀ tr : Trace S, RunsIn tr a true → RunsIn tr b true

/-! ## Lemmas for `AccLe` -/

theorem AccLe.refl (a : OComp S Bool) : AccLe a a := ⟨fun _ => le_rfl, fun _ h => h⟩

theorem AccLe.of_eq {a b : OComp S Bool} (h : a = b) : AccLe a b := h ▸ AccLe.refl a

theorem AccLe.trans {a b c : OComp S Bool} (h1 : AccLe a b) (h2 : AccLe b c) : AccLe a c :=
  ⟨fun f => le_trans (h1.1 f) (h2.1 f), fun tr h => h2.2 tr (h1.2 tr h)⟩

theorem AccLe.of_false (b : OComp S Bool) : AccLe (.pure Bool.false) b := ⟨fun f => by
  have : PrCoins f (OComp.pure Bool.false : OComp S Bool) {true} = 0 := by
    unfold PrCoins
    rw [show (OComp.pure Bool.false : OComp S Bool).runEager f = PMF.pure Bool.false from rfl,
      pr_pure]
    simp
  rw [this]
  exact zero_le _, fun _ h => absurd (runsIn_pure_iff.1 h) (by simp)⟩

theorem pr_bind_le {α β : Type} (p : PMF α) (g g' : α → PMF β)
    (E : Set β) (h : ∀ a, pr (g a) E ≤ pr (g' a) E) :
    pr (p.bind g) E ≤ pr (p.bind g') E := by
  rw [pr_bind, pr_bind]
  exact expect_mono_support p fun a _ => h a

theorem AccLe.bind {α : Type} (c : OComp S α) {g g' : α → OComp S Bool} (h : ∀ a, AccLe (g a) (g' a)) : AccLe (c.bind g) (c.bind g') := ⟨fun f => by
  unfold PrCoins
  rw [OComp.runEager_bind, OComp.runEager_bind]
  exact pr_bind_le _ _ _ _ fun a => (h a).1 f, fun tr hr => by
  obtain ⟨a, h1, h2⟩ := (runsIn_bind_iff _ _ _).1 hr
  exact (runsIn_bind_iff _ _ _).2 ⟨a, h1, (h a).2 tr h2⟩⟩

theorem prTrue_and (p q : PMF Bool) :
    pr (p.bind fun x => q.bind fun y => PMF.pure (x && y)) {true} = pr p {true} * pr q {true} := by
  have hq : ∀ x : Bool,
      pr (q.bind fun y => PMF.pure (x && y)) {true} = if x then pr q {true} else 0 := by
    intro x
    cases x with
    | true =>
      have : (q.bind fun y => PMF.pure (true && y)) = q := by simp
      rw [this]; rfl
    | false =>
      have : (q.bind fun y => PMF.pure (false && y)) = PMF.pure false := by simp
      rw [this, pr_pure]; simp
  rw [pr_bind]
  simp only [hq]
  unfold expect
  rw [tsum_fintype, Fintype.sum_bool, pr_singleton p true]
  simp

/-- the conjunction of two verdicts -/
theorem AccLe.and {a a' b b' : OComp S Bool} (h1 : AccLe a a') (h2 : AccLe b b') :
    AccLe (a.bind fun x => b.bind fun y => .pure (x && y))
      (a'.bind fun x => b'.bind fun y => .pure (x && y)) := ⟨fun f => by
  have e : ∀ u v : OComp S Bool, PrCoins f (u.bind fun x => v.bind fun y => .pure (x && y)) {true} =
      PrCoins f u {true} * PrCoins f v {true} := by
    intro u v
    unfold PrCoins
    rw [OComp.runEager_bind]
    simp only [OComp.runEager_bind]
    exact prTrue_and _ _
  rw [e, e]
  exact mul_le_mul' (h1.1 f) (h2.1 f), fun tr hr => by
  obtain ⟨x, hx, hr2⟩ := (runsIn_bind_iff _ _ _).1 hr
  obtain ⟨y, hy, hr3⟩ := (runsIn_bind_iff _ _ _).1 hr2
  obtain ⟨rfl, rfl⟩ := Bool.and_eq_true_iff.1 (runsIn_pure_iff.1 hr3)
  exact (runsIn_bind_iff _ _ _).2
    ⟨true, h1.2 tr hx, (runsIn_bind_iff _ _ _).2 ⟨true, h2.2 tr hy, RunsIn.pure _⟩⟩⟩

/-- the conjunction of three verdicts -/
theorem AccLe.and3 {a a' b b' c c' : OComp S Bool} (h1 : AccLe a a')
    (h2 : AccLe b b') (h3 : AccLe c c') :
    AccLe (a.bind fun x => b.bind fun y => c.bind fun z => .pure (x && y && z))
      (a'.bind fun x => b'.bind fun y => c'.bind fun z => .pure (x && y && z)) := by
  have e : ∀ u v w : OComp S Bool,
      (u.bind fun x => v.bind fun y => w.bind fun z => .pure (x && y && z)) =
        u.bind fun x =>
          (v.bind fun y => w.bind fun z => .pure (y && z)).bind fun t => .pure (x && t) := by
    intro u v w
    refine congrArg _ (funext fun x => ?_)
    rw [OComp.bind_assoc]
    refine congrArg _ (funext fun y => ?_)
    rw [OComp.bind_assoc]
    refine congrArg _ (funext fun z => ?_)
    show OComp.pure (x && y && z) = OComp.pure (x && (y && z))
    rw [Bool.and_assoc]
  rw [e, e]
  exact AccLe.and h1 (AccLe.and h2 h3)

/-- a check in front of both -/
theorem AccLe.guard (g : OComp S Bool) {a b : OComp S Bool} (h : AccLe a b) :
    AccLe (g.bind fun c => if c then a else .pure Bool.false)
      (g.bind fun c => if c then b else .pure Bool.false) :=
  AccLe.bind g fun c => by
    cases c
    · exact AccLe.refl _
    · exact h

theorem prFalse_eq (p : PMF Bool) : pr p {c | c = false} = 1 - pr p {true} := by
  have h1 : pr p {c | c = false} = p false := pr_singleton p false
  have h2 : p true + p false = 1 := by
    have := p.tsum_coe
    rwa [tsum_fintype, Fintype.sum_bool] at this
  rw [h1, pr_singleton, ← h2]
  exact (ENNReal.add_sub_cancel_left (PMF.apply_ne_top p true)).symm

variable {A : Arg S I X W IVK ISK Pf}
  {κ : IVK → IVK'} {τ : Pf → Pf'} {V' : IVK' → X → Pf' → OComp S Bool}

/-! ## Completeness -/

theorem verifyAll_le (hup : ∀ v x π, AccLe (A.V v x π) (V' (κ v) x (τ π))) (v : IVK) :
    ∀ l : List (X × Pf), AccLe (verifyAll A v l) (verifyAll (mapArg A κ τ V') (κ v) (l.map (on2 τ)))
  | [] => AccLe.refl _
  | (x, π) :: t => AccLe.and (hup v x π) (verifyAll_le hup v t)

theorem completenessExp_le (hup : ∀ v x π, AccLe (A.V v x π) (V' (κ v) x (τ π)))
    (i : I) (b : List (X × W)) :
    AccLe (completenessExp A i b) (completenessExp (mapArg A κ τ V') i b) := by
  have e : completenessExp (mapArg A κ τ V') i b =
      (A.C i).bind fun o =>
        (A.P o.2 b).bind fun πs =>
            verifyAll (mapArg A κ τ V') (κ o.1) (((b.map Prod.fst).zip πs.val).map (on2 τ)) := by
    show ((A.C i).bind fun o => OComp.pure (κ o.1, o.2)).bind (fun o =>
        ((A.P o.2 b).bind fun l => OComp.pure (mapS τ l)).bind fun πs =>
          verifyAll (mapArg A κ τ V') o.1 ((b.map Prod.fst).zip πs.val)) = _
    rw [OComp.bind_assoc]
    refine congrArg _ (funext fun o => ?_)
    show ((A.P o.2 b).bind fun l => OComp.pure (mapS τ l)).bind
        (fun πs => verifyAll (mapArg A κ τ V') (κ o.1) ((b.map Prod.fst).zip πs.val)) = _
    rw [OComp.bind_assoc]
    refine congrArg _ (funext fun l => ?_)
    show verifyAll (mapArg A κ τ V') (κ o.1) ((b.map Prod.fst).zip (l.val.map τ)) = _
    rw [List.zip_map_right]
  rw [e]
  exact AccLe.bind _ fun o => AccLe.bind _ fun πs => verifyAll_le hup o.1 _

/-- Completeness transfers, if V' accepts the mapped key and proof whenever V accepts. -/
theorem completeness (hup : ∀ v x π, AccLe (A.V v x π) (V' (κ v) x (τ π))) (R : RelPair I X W PP)
    {B : ℕ} {α : ℝ≥0∞} (hc : HasCompletenessError R A B α) :
    HasCompletenessError R (mapArg A κ τ V') B α := fun i b hb => by
  refine le_trans (MeasureTheory.lintegral_mono fun f => ?_) (hc i b hb)
  show PrCoins f _ {c | c = false} ≤ PrCoins f _ {c | c = false}
  unfold PrCoins
  rw [prFalse_eq, prFalse_eq]
  exact tsub_le_tsub_left ((completenessExp_le hup i b).1 f) 1

/-! ## Index binding -/

/-- the extractor, composed with κ' on keys and σ on proofs -/
def pullEK (κ' : IVK' → IVK) (σ : Pf' → Pf) (E : Extractor S I X W IVK Pf) :
    Extractor S I X W IVK' Pf' where
  Ei := fun v tr => E.Ei (κ' v) tr
  Ew := fun v tr x π tr' => E.Ew (κ' v) tr x (σ π) tr'

/-- the composed extractor is `LocalTo` m if the old one is -/
theorem localTo_pullEK {lam : ℕ} {E : Extractor S I X W IVK Pf} {m : OracleCoding S lam} (κ' : IVK' → IVK)
    (σ : Pf' → Pf) (h : LocalTo E m) : LocalTo (pullEK κ' σ E) m :=
  ⟨fun v tr => h.1 (κ' v) tr, fun v tr x π tr' => h.2 (κ' v) tr x (σ π) tr'⟩

theorem pr_outcome_le (R : RelPair I X W PP) {a b : OComp S Bool} (h : AccLe a b) (f : Fam S)
    (i : Option I) (x : X) (w : W) :
    pr ((a.bind fun c => .pure (⟨c, i, x, w⟩ : BindingOutcome I X W)).runEager f) (bindingBad R) ≤
      pr ((b.bind fun c => .pure (⟨c, i, x, w⟩ : BindingOutcome I X W)).runEager f)
        (bindingBad R) := by
  have e : ∀ u : OComp S Bool,
      pr ((u.bind fun c => .pure (⟨c, i, x, w⟩ : BindingOutcome I X W)).runEager f) (bindingBad R) =
        pr (u.runEager f) ((fun c => (⟨c, i, x, w⟩ : BindingOutcome I X W)) ⁻¹' bindingBad R) := by
    intro u
    rw [OComp.runEager_bind, ← pr_map]
    rfl
  rw [e, e]
  by_cases hb : (⟨true, i, x, w⟩ : BindingOutcome I X W) ∈ bindingBad R
  · have hs : ((fun c => (⟨c, i, x, w⟩ : BindingOutcome I X W)) ⁻¹' bindingBad R) = {true} := by
      ext c
      cases c with
      | true => simpa using hb
      | false =>
        simp only [Set.mem_preimage, Set.mem_singleton_iff, Bool.false_eq_true, iff_false]
        exact fun h => by cases h.1
    rw [hs]
    exact h.1 f
  · have hs : ((fun c => (⟨c, i, x, w⟩ : BindingOutcome I X W)) ⁻¹' bindingBad R) = ∅ := by
      ext c
      cases c with
      | true => simpa using hb
      | false =>
        simp only [Set.mem_preimage, Set.mem_empty_iff_false, iff_false]
        exact fun h => by cases h.1
    rw [hs]
    simp [pr]

/-- Index binding transfers, if V accepts the key and the proof mapped by κ' and σ whenever V'
accepts: the same bound at the same numbers of queries. -/
theorem binding {κ' : IVK' → IVK} {σ : Pf' → Pf}
    (hdown : ∀ v x π, AccLe (V' v x π) (A.V (κ' v) x (σ π))) (R : RelPair I X W PP)
    {E : Extractor S I X W IVK Pf} {ε : ℕ → ℕ → ℝ≥0∞} (hb : HasIndexBindingWith R A E ε) :
    HasIndexBindingWith R (mapArg A κ τ V') (pullEK κ' σ E) ε := fun tC tP St Ct Pt hC hP => by
  refine le_trans (MeasureTheory.lintegral_mono fun f => ?_)
    (hb tC tP St (Ct.bind fun o => .pure (κ' o.1, o.2))
      (fun st => (Pt st).bind fun o => .pure (o.1, σ o.2))
      ((hC.bind (g := fun o => OComp.pure (κ' o.1, o.2)) (t := 0) fun _ => trivial).mono
        (Nat.add_zero _).le) fun st =>
          ((hP st).bind (g := fun o => OComp.pure (o.1, σ o.2)) (t := 0) fun _ => trivial).mono
            (Nat.add_zero _).le)
  show PrCoins f _ (bindingBad R) ≤ PrCoins f _ (bindingBad R)
  have e1 : bindingExp (mapArg A κ τ V') (pullEK κ' σ E) Ct Pt = Ct.withTrace.bind fun a => (Pt a.1.2).withTrace.bind fun b =>
      (V' a.1.1 b.1.1 b.1.2).bind fun c =>
        .pure (⟨c, E.Ei (κ' a.1.1) a.2, b.1.1,
              E.Ew (κ' a.1.1) a.2 b.1.1 (σ b.1.2) b.2⟩ : BindingOutcome I X W) := rfl
  have e2 : bindingExp A E (Ct.bind fun o => .pure (κ' o.1, o.2))
      (fun st => (Pt st).bind fun o => .pure (o.1, σ o.2)) =
      Ct.withTrace.bind fun a => (Pt a.1.2).withTrace.bind fun b =>
      (A.V (κ' a.1.1) b.1.1 (σ b.1.2)).bind fun c =>
          .pure (⟨c, E.Ei (κ' a.1.1) a.2, b.1.1,
                E.Ew (κ' a.1.1) a.2 b.1.1 (σ b.1.2) b.2⟩ : BindingOutcome I X W) := by
    show ((Ct.bind fun o => OComp.pure (κ' o.1, o.2)).withTrace).bind (fun a =>
        (((Pt a.1.2).bind fun o => OComp.pure (o.1, σ o.2)).withTrace).bind fun b =>
          (A.V a.1.1 b.1.1 b.1.2).bind fun c =>
            .pure
              (⟨c, E.Ei a.1.1 a.2, b.1.1, E.Ew a.1.1 a.2 b.1.1 b.1.2 b.2⟩ : BindingOutcome I X W)) =
      _
    rw [withTrace_bind, OComp.bind_assoc]
    refine congrArg _ (funext fun a => ?_)
    show (((Pt a.1.2).bind fun o => OComp.pure (o.1, σ o.2)).withTrace).bind
        (fun b =>
          (A.V (κ' a.1.1) b.1.1 b.1.2).bind fun c =>
            .pure (⟨c, E.Ei (κ' a.1.1) (a.2 ++ []), b.1.1,
                E.Ew (κ' a.1.1) (a.2 ++ []) b.1.1 b.1.2 b.2⟩ : BindingOutcome I X W)) = _
    rw [withTrace_bind, OComp.bind_assoc, List.append_nil]
    refine congrArg _ (funext fun b => ?_)
    show (A.V (κ' a.1.1) b.1.1 (σ b.1.2)).bind (fun c =>
        .pure (⟨c, E.Ei (κ' a.1.1) a.2, b.1.1,
            E.Ew (κ' a.1.1) a.2 b.1.1 (σ b.1.2) (b.2 ++ [])⟩ : BindingOutcome I X W)) = _
    rw [List.append_nil]
  rw [e1, e2]
  unfold PrCoins
  rw [OComp.runEager_bind, OComp.runEager_bind]
  refine pr_bind_le _ _ _ _ fun a => ?_
  rw [OComp.runEager_bind, OComp.runEager_bind]
  exact pr_bind_le _ _ _ _ fun b => pr_outcome_le R (hdown _ _ _) f _ _ _

/-! ## Index privacy -/

/-- a view against A, mapped by κ and τ -/
def mapViewK (κ : IVK → IVK') (τ : Pf → Pf') (v : View S IVK X Pf) : View S IVK' X Pf' :=
  ⟨κ v.ivk, v.sessions.map (List.map (on2 τ)), v.trace, v.coins⟩

/-- the simulator of A, followed by κ on the key and by τ on each proof -/
def pushSimK (κ : IVK → IVK') (τ : Pf → Pf') (Sim : Simulator S PP IVK X Pf) :
    Simulator S PP IVK' X Pf' where
  St := Sim.St
  init := fun pp n => (Sim.init pp n).map fun o => (κ o.1, o.2)
  answer := Sim.answer
  prove := fun s xs => (Sim.prove s xs).map fun o => (mapS τ o.1, o.2)

theorem mapViewK_session (κ : IVK → IVK') (τ : Pf → Pf') (v : View S IVK X Pf) (r : List (X × Pf)) :
    mapViewK κ τ { v with sessions := v.sessions ++ [r] } =
      { mapViewK κ τ v with sessions := (mapViewK κ τ v).sessions ++ [r.map (on2 τ)] } := by
  simp only [mapViewK, List.map_append, List.map_cons, List.map_nil]

theorem realLoop_map (Z' : ViewEnv S IVK' X W Pf') (k : ISK) (V : AdvVerifier S X Pf') :
    ∀ (n : ℕ) (v : View S IVK X Pf), realLoop (mapArg A κ τ V') Z' k V n (mapViewK κ τ v) =
      (realLoop A (fun u => Z' (mapViewK κ τ u)) k (pullV τ V) n v).bind fun u =>
        .pure (mapViewK κ τ u) := by
  induction V with
  | halt => exact fun _ _ => rfl
  | query o q K ih =>
    intro n v
    simp only [realLoop, pullV, OComp.bind]
    refine congrArg _ (funext fun r => ?_)
    exact ih r n { v with trace := v.trace ++ [⟨o, q, r⟩] }
  | sample m K ih =>
    intro n v
    simp only [realLoop, pullV, OComp.bind]
    refine congrArg _ (funext fun r => ?_)
    exact ih r n { v with coins := v.coins ++ [r.val] }
  | request K ih =>
    intro n v
    cases n with
    | zero => rfl
    | succ n =>
      simp only [realLoop, pullV]
      cases hz : Z' (mapViewK κ τ v) with
      | none => rfl
      | some b =>
        simp only []
        show ((A.P k b.pairs).bind fun l => OComp.pure (mapS τ l)).bind _ = _
        rw [OComp.bind_assoc, OComp.bind_assoc]
        refine congrArg _ (funext fun l => ?_)
        show realLoop (mapArg A κ τ V') Z' k (K (b.released (l.val.map τ))) n
            { mapViewK κ τ v with
              sessions := (mapViewK κ τ v).sessions ++ [b.released (l.val.map τ)] } = _
        rw [released_map, ← mapViewK_session]
        exact ih _ n _

theorem realExp_map (Vt : IVK' → AdvVerifier S X Pf')
    (Z' : ViewEnv S IVK' X W Pf') (i : I) (N : ℕ) :
    realExp (mapArg A κ τ V') Vt Z' i N =
      (realExp A (fun v => pullV τ (Vt (κ v))) (fun u => Z' (mapViewK κ τ u)) i N).bind
        fun u => .pure (mapViewK κ τ u) := by
  show ((A.C i).bind fun o => OComp.pure (κ o.1, o.2)).bind
      (fun o => realLoop (mapArg A κ τ V') Z' o.2 (Vt o.1) N ⟨o.1, [], [], []⟩) =
    ((A.C i).bind fun o =>
        realLoop A (fun u => Z' (mapViewK κ τ u)) o.2 (pullV τ (Vt (κ o.1)))
          N ⟨o.1, [], [], []⟩).bind
      fun u => .pure (mapViewK κ τ u)
  rw [OComp.bind_assoc, OComp.bind_assoc]
  refine congrArg _ (funext fun o => ?_)
  exact realLoop_map Z' o.2 (Vt (κ o.1)) N ⟨o.1, [], [], []⟩

theorem idealLoop_map (κ : IVK → IVK') (τ : Pf → Pf') (Sim : Simulator S PP IVK X Pf)
    (Z' : ViewEnv S IVK' X W Pf') (V : AdvVerifier S X Pf') :
    ∀ (n : ℕ) (v : View S IVK X Pf) (s : Sim.St),
      idealLoop (pushSimK κ τ Sim) Z' V n (mapViewK κ τ v) s =
        (idealLoop Sim (fun u => Z' (mapViewK κ τ u)) (pullV τ V) n v s).map (mapViewK κ τ) := by
  induction V with
  | halt => exact fun _ v _ => (PMF.pure_map _ _).symm
  | query o q K ih =>
    intro n v s
    simp only [idealLoop, pullV, PMF.map_bind]
    refine congrArg _ (funext fun out => ?_)
    exact ih out.1 n { v with trace := v.trace ++ [⟨o, q, out.1⟩] } out.2
  | sample m K ih =>
    intro n v s
    simp only [idealLoop, pullV, PMF.map_bind]
    refine congrArg _ (funext fun r => ?_)
    exact ih r n { v with coins := v.coins ++ [r.val] } s
  | request K ih =>
    intro n v s
    cases n with
    | zero => exact (PMF.pure_map _ _).symm
    | succ n =>
      simp only [idealLoop, pullV]
      cases hz : Z' (mapViewK κ τ v) with
      | none => exact (PMF.pure_map _ _).symm
      | some b =>
        simp only []
        show ((Sim.prove s b.ownX).map fun o => (mapS τ o.1, o.2)).bind _ = _
        rw [PMF.bind_map, PMF.map_bind]
        refine congrArg _ (funext fun out => ?_)
        show idealLoop (pushSimK κ τ Sim) Z' (K (b.ownX.zip (out.1.val.map τ))) n
            { mapViewK κ τ v with
              sessions := (mapViewK κ τ v).sessions ++ [b.ownX.zip (out.1.val.map τ)] } out.2 = _
        rw [List.zip_map_right, ← mapViewK_session]
        exact ih _ n _ out.2

theorem idealExp_map (κ : IVK → IVK') (τ : Pf → Pf') (R : RelPair I X W PP)
    (Sim : Simulator S PP IVK X Pf) (Vt : IVK' → AdvVerifier S X Pf')
    (Z' : ViewEnv S IVK' X W Pf') (i : I) (N : ℕ) :
    idealExp R (pushSimK κ τ Sim) Vt Z' i N =
      (idealExp R Sim (fun v => pullV τ (Vt (κ v))) (fun u => Z' (mapViewK κ τ u)) i N).map
        (mapViewK κ τ) := by
  unfold idealExp
  show ((Sim.init (R.pp i) N).map fun o => (κ o.1, o.2)).bind _ = _
  rw [PMF.bind_map, PMF.map_bind]
  refine congrArg _ (funext fun out => ?_)
  exact idealLoop_map κ τ Sim Z' (Vt (κ out.1)) N ⟨out.1, [], [], []⟩ out.2

/-- Index privacy transfers, with the simulator of A followed by κ and τ. -/
theorem privacyWith (R : RelPair I X W PP) {B : ℕ} {Sim : Simulator S PP IVK X Pf}
    {ζ : ℕ → ℕ → ℝ≥0∞} (hp : HasIndexPrivacyWith R A B Sim ζ) :
    HasIndexPrivacyWith R (mapArg A κ τ V') B (pushSimK κ τ Sim) ζ := by
  intro i Z' hZ tV Vt N hV
  obtain ⟨h1, h2⟩ := hp i (fun u => Z' (mapViewK κ τ u)) (fun v b hb => hZ _ b hb) tV
    (fun v => pullV τ (Vt (κ v))) N fun v => pullV_queryBound τ _ _ (hV (κ v))
  constructor
  · refine le_trans (le_of_eq ?_) (le_trans (sd_comap_le _ _ (mapViewK κ τ)) h1)
    congr 1
    · funext T
      rw [realExp_map, Pr_bind_pure]
    · funext T
      rw [idealExp_map, pr_map]
  · rw [idealExp_map, pr_map]
    exact h2

/-! ## The three together -/

/-- Under `hup`, `hdown` the three properties transfer to the mapped scheme, with the same
bounds. -/
theorem main {κ' : IVK' → IVK} {σ : Pf' → Pf} (hup : ∀ v x π, AccLe (A.V v x π) (V' (κ v) x (τ π)))
    (hdown : ∀ v x π, AccLe (V' v x π) (A.V (κ' v) x (σ π))) {R : RelPair I X W PP} {B : ℕ}
    {E : Extractor S I X W IVK Pf} {Sim : Simulator S PP IVK X Pf} {α : ℝ≥0∞} {ε ζ : ℕ → ℕ → ℝ≥0∞}
    (h : IsZKCPArgWith R A B E Sim α ε ζ) :
    IsZKCPArgWith R (mapArg A κ τ V') B (pullEK κ' σ E) (pushSimK κ τ Sim) α ε ζ :=
  ⟨completeness hup R h.completeness, binding hdown R h.indexBinding, privacyWith R h.indexPrivacy⟩

end Compile.GenLe
