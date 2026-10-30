-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
ZKCP/GenKeyTag.lean: a tag in the verification key, which V compares with its own, for batches.

The file is in the form with batches and a family of oracles (ZKCP/Gen.lean). It is the counterpart
of ZKCP/KeyTag.lean, whose header says why and what the step does not say; all of it applies here.
Why, in short: in a family of schemes A_t nothing says that a key made under t is rejected under t';
with the tag a key names one t, and V under any other parameter rejects it (`tagKey_V_of_ne`).

  `Arg.tagKey A t`          A with the tag t before its verification key.
  `Extractor.tagKey E`      It reads the key without its tag.
  `Simulator.tagKey Sim t`  It puts t before the key that Sim makes.
  `IsZKCPArgWith.tagKey`, `IsZKCPArg.tagKey`
                            The three properties are carried over, for the same pair of relations
                            and the same bound on a batch, with the same bounds.
  `tagKey_V_of_ne`          V rejects every key that names another tag: for t' ≠ t the computation V
                            (t', ivk) x π is "false".
  `tagKey_V_self`, `QueryBound.tagKey_V`
                            On a key with its own tag V is A's V; a bound on the queries of A's V is
                            a bound for the new V.

Notation: ε, ζ : ℕ → ℕ → ℝ≥0∞, written ε tC tP, ζ tV N: the arguments bound the numbers of queries
of the adversary's committer, prover and verifier, and the number of batches (ZKCP/Gen.lean:
`HasIndexBindingWith`, `PrivacyFor`); "false": the computation `.pure false`.

Limits: those that the header of ZKCP/KeyTag.lean lists. V's own tag comes from elsewhere than the
key. The tag is a label beside ivk and is not hashed here. It is public as a constant of the scheme
and does not pass through pp(i). Nothing is said about a parameter that is chosen after queries. Of
the other properties of this library none is carried over here; that index privacy with batches in
flight follows from the form with extractor and simulator named (`IsZKCPArgWith`) is neither stated
nor proved in this library.

The file follows ZKCP/KeyTag.lean, with the experiments of ZKCP/Gen.lean in the place of those of
ZKCP/Defs.lean.
-/
import ZKCP.Gen
import Prob.Count
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

open scoped ENNReal

namespace ZKCP.Gen

open Rom (OSpec Fam)
open Prob (pr sd expect)

variable {S : OSpec} {I X W PP IVK ISK Pf T : Type}

/-! ## A function applied to the output of a computation -/

section Comp
variable {α β γ : Type}

theorem bindO_bind (c : Rom.OComp S α) (g : α → Rom.OComp S β) (h : β → Rom.OComp S γ) :
    (c.bind g).bind h = c.bind fun a => (g a).bind h := by
  induction c with
  | pure a => rfl
  | query o q k ih => simp only [Rom.OComp.bind, ih]
  | sample n k ih => simp only [Rom.OComp.bind, ih]

theorem runEager_bindO (f : Fam S) (c : Rom.OComp S α) (k : α → Rom.OComp S β) :
    (c.bind k).runEager f = (c.runEager f).bind fun a => (k a).runEager f := by
  induction c with
  | pure a => simp [Rom.OComp.bind, Rom.OComp.runEager]
  | query o q g ih => simp only [Rom.OComp.bind, Rom.OComp.runEager, ih]
  | sample n g ih => simp only [Rom.OComp.bind, Rom.OComp.runEager, ih, PMF.bind_bind]

/-- A function applied to the output of a computation. -/
def mapO (h : α → β) (c : Rom.OComp S α) : Rom.OComp S β := c.bind fun a => .pure (h a)

theorem mapO_bind (h : α → β) (c : Rom.OComp S α) (g : β → Rom.OComp S γ) :
    (mapO h c).bind g = c.bind fun a => g (h a) := bindO_bind c _ g

theorem bind_mapO (c : Rom.OComp S α) (g : α → Rom.OComp S β) (h : β → γ) :
    mapO h (c.bind g) = c.bind fun a => mapO h (g a) := bindO_bind c g _

theorem runEager_mapO (f : Fam S) (h : α → β) (c : Rom.OComp S α) :
    (mapO h c).runEager f = (c.runEager f).map h := by
  unfold mapO
  rw [runEager_bindO]
  rfl

theorem withTrace_mapO (h : α → β) (c : Rom.OComp S α) :
    (mapO h c).withTrace = mapO (fun o => (h o.1, o.2)) c.withTrace := by
  induction c with
  | pure a => rfl
  | query o q k ih =>
      show Rom.OComp.query o q
          (fun r => (mapO h (k r)).withTrace.bind fun out => .pure (out.1, ⟨o, q, r⟩ :: out.2)) =
        Rom.OComp.query o q fun r =>
          mapO (fun o => (h o.1, o.2))
            ((k r).withTrace.bind fun out => .pure (out.1, ⟨o, q, r⟩ :: out.2))
      refine congrArg _ (funext fun r => ?_)
      rw [ih r, mapO_bind, bind_mapO]
      rfl
  | sample n k ih =>
      show Rom.OComp.sample n (fun r => (mapO h (k r)).withTrace) =
        Rom.OComp.sample n fun r => mapO (fun o => (h o.1, o.2)) (k r).withTrace
      exact congrArg _ (funext ih)

theorem queryBound_mapO (h : α → β) :
    ∀ (c : Rom.OComp S α) (t : ℕ), c.QueryBound t → (mapO h c).QueryBound t
  | .pure _, _, _ => trivial
  | .query _ _ _, 0, hc => hc.elim
  | .query _ _ k, t + 1, hc => fun r => queryBound_mapO h (k r) t (hc r)
  | .sample _ k, t, hc => fun r => queryBound_mapO h (k r) t (hc r)

theorem Pr_mapO (h : α → β) (c : Rom.OComp S α) (E : Set β) :
    Rom.Pr (mapO h c) (fun _ => E) = Rom.Pr c fun _ => h ⁻¹' E := by
  unfold Rom.Pr Rom.PrCoins
  simp only [runEager_mapO, Prob.pr_map]

/-- In a computation in two steps the probability of an event is monotone in its probability in the
second step. -/
theorem pr_runEager_bind_le (f : Fam S) (c : Rom.OComp S α) {g g' : α → Rom.OComp S β} (E : Set β)
    (h : ∀ a, pr ((g a).runEager f) E ≤ pr ((g' a).runEager f) E) :
    pr ((c.bind g).runEager f) E ≤ pr ((c.bind g').runEager f) E := by
  rw [runEager_bindO, runEager_bindO, Prob.pr_bind, Prob.pr_bind]
  exact Prob.expect_mono _ h

/-- A function applied to both sides does not raise the statistical distance. -/
theorem sd_preimage_le (h : α → β) (P Q : Set α → ℝ≥0∞) :
    sd (fun E : Set β => P (h ⁻¹' E)) (fun E => Q (h ⁻¹' E)) ≤ sd P Q :=
  iSup_le fun E => le_iSup (fun E : Set α => max (P E - Q E) (Q E - P E)) (h ⁻¹' E)

end Comp

/-! ## The scheme with a tag in the key -/

/-- The extractor: it reads the key without its tag. -/
def Extractor.tagKey (E : Extractor S I X W IVK Pf) : Extractor S I X W (T × IVK) Pf :=
  ⟨fun v => E.Ei v.2, fun v => E.Ew v.2⟩

/-- The simulator: it puts the tag before the key that Sim makes. -/
def Simulator.tagKey (Sim : Simulator S PP IVK X Pf) (t : T) :
    Simulator S PP (T × IVK) X Pf where
  St := Sim.St
  init p n := (Sim.init p n).map fun o => ((t, o.1), o.2)
  answer := Sim.answer
  prove := Sim.prove

/-- The view with the tag before its key. -/
def View.tagKey (t : T) (v : View S IVK X Pf) : View S (T × IVK) X Pf :=
  ⟨(t, v.ivk), v.sessions, v.trace, v.coins⟩

theorem tagKey_idealLoop (t : T) (Sim : Simulator S PP IVK X Pf) (Z : ViewEnv S (T × IVK) X W Pf) :
    ∀ (a : AdvVerifier S X Pf) (n : ℕ) (v : View S IVK X Pf) (s : Sim.St),
      idealLoop (Sim.tagKey t) Z a n (v.tagKey t) s =
        (idealLoop Sim (fun v => Z (v.tagKey t)) a n v s).map (View.tagKey t)
  | .halt, _, _, _ => (PMF.pure_map _ _).symm
  | .query o q k, n, v, s => by
      simp only [idealLoop, PMF.map_bind]
      exact congrArg _
        (funext fun out =>
          tagKey_idealLoop t Sim Z (k out.1) n { v with trace := v.trace ++ [⟨o, q, out.1⟩] } out.2)
  | .sample m k, n, v, s => by
      simp only [idealLoop, PMF.map_bind]
      exact congrArg _
        (funext fun r => tagKey_idealLoop t Sim Z (k r) n { v with coins := v.coins ++ [r.val] } s)
  | .request _, 0, _, _ => (PMF.pure_map _ _).symm
  | .request k, n + 1, v, s => by
      simp only [idealLoop]
      cases Z (v.tagKey t) with
      | none => exact (PMF.pure_map _ _).symm
      | some b =>
          simp only [PMF.map_bind]
          exact congrArg _
            (funext fun out =>
              tagKey_idealLoop t Sim Z (k (b.ownX.zip out.1.val)) n
                { v with sessions := v.sessions ++ [b.ownX.zip out.1.val] } out.2)

theorem tagKey_idealExp (R : RelPair I X W PP) (t : T) (Sim : Simulator S PP IVK X Pf)
    (Vt : T × IVK → AdvVerifier S X Pf) (Z : ViewEnv S (T × IVK) X W Pf) (i : I) (N : ℕ) :
    idealExp R (Sim.tagKey t) Vt Z i N =
      (idealExp R Sim (fun ivk => Vt (t, ivk)) (fun v => Z (v.tagKey t)) i N).map
        (View.tagKey t) := by
  show ((Sim.init (R.pp i) N).map fun o => ((t, o.1), o.2)).bind
      (fun out => idealLoop (Sim.tagKey t) Z (Vt out.1) N ⟨out.1, [], [], []⟩ out.2) =
    ((Sim.init (R.pp i) N).bind fun out =>
        idealLoop Sim (fun v => Z (v.tagKey t)) (Vt (t, out.1)) N ⟨out.1, [], [], []⟩ out.2).map
      (View.tagKey t)
  rw [PMF.bind_map, PMF.map_bind]
  exact congrArg _
    (funext fun out => tagKey_idealLoop t Sim Z (Vt (t, out.1)) N ⟨out.1, [], [], []⟩ out.2)

variable [DecidableEq T]

/-- The scheme: C outputs ((t, ivk), isk); P is A's; V, given (t', ivk), runs A's V on ivk if t' = t
and rejects otherwise, without a query. -/
def Arg.tagKey (A : Arg S I X W IVK ISK Pf) (t : T) : Arg S I X W (T × IVK) ISK Pf where
  C i := mapO (fun k => ((t, k.1), k.2)) (A.C i)
  P := A.P
  V v x π := if v.1 = t then A.V v.2 x π else .pure false

variable (R : RelPair I X W PP) (A : Arg S I X W IVK ISK Pf) (t : T)

/-- V rejects every key that names another tag: the computation is "false". -/
theorem tagKey_V_of_ne {t' : T} (h : t' ≠ t) (ivk : IVK) (x : X) (π : Pf) :
    (A.tagKey t).V (t', ivk) x π = .pure false := if_neg h

theorem tagKey_V_self (ivk : IVK) (x : X) (π : Pf) : (A.tagKey t).V (t, ivk) x π = A.V ivk x π :=
  if_pos rfl

theorem QueryBound.tagKey_V {N : ℕ} (h : ∀ ivk x π, (A.V ivk x π).QueryBound N)
    (v : T × IVK) (x : X) (π : Pf) :
    ((A.tagKey t).V v x π).QueryBound N := by
  show (if v.1 = t then A.V v.2 x π else .pure false : Rom.OComp S Bool).QueryBound N
  split
  · exact h _ _ _
  · trivial

/-! ## Completeness -/

theorem tagKey_verifyAll (ivk : IVK) :
    ∀ l : List (X × Pf), verifyAll (A.tagKey t) (t, ivk) l = verifyAll A ivk l
  | [] => rfl
  | (x, π) :: rest => by
      show ((A.tagKey t).V (t, ivk) x π).bind
          (fun c => (verifyAll (A.tagKey t) (t, ivk) rest).bind fun cs => .pure (c && cs)) =
        (A.V ivk x π).bind fun c => (verifyAll A ivk rest).bind fun cs => .pure (c && cs)
      rw [tagKey_V_self, tagKey_verifyAll ivk rest]

theorem tagKey_sessionExp (ivk : IVK) (isk : ISK) (b : List (X × W)) :
    sessionExp (A.tagKey t) (t, ivk) isk b = sessionExp A ivk isk b := by
  show (A.P isk b).bind (fun πs => verifyAll (A.tagKey t) (t, ivk) ((b.map Prod.fst).zip πs.val)) =
    (A.P isk b).bind fun πs => verifyAll A ivk ((b.map Prod.fst).zip πs.val)
  simp only [tagKey_verifyAll]

theorem tagKey_completenessExp (i : I) (b : List (X × W)) :
    completenessExp (A.tagKey t) i b = completenessExp A i b := by
  show (mapO (fun k => ((t, k.1), k.2)) (A.C i)).bind
      (fun key => sessionExp (A.tagKey t) key.1 key.2 b) =
    (A.C i).bind fun key => sessionExp A key.1 key.2 b
  rw [mapO_bind]
  simp only [tagKey_sessionExp]

variable {R A}

theorem HasCompletenessError.tagKey {B : ℕ} {α : ℝ≥0∞} (h : HasCompletenessError R A B α) :
    HasCompletenessError R (A.tagKey t) B α := fun i b hb => by
  rw [tagKey_completenessExp]
  exact h i b hb

/-! ## Index binding -/

theorem HasIndexBindingWith.tagKey
    {E : Extractor S I X W IVK Pf} {ε : ℕ → ℕ → ℝ≥0∞} (h : HasIndexBindingWith R A E ε) :
    HasIndexBindingWith R (A.tagKey t) (E.tagKey (T := T)) ε := by
  intro tC tP St Ct Pt hC hP
  refine le_trans ?_
    (h tC tP (T × St) (mapO (fun o => (o.1.2, (o.1.1, o.2))) Ct) (fun s => Pt s.2)
      (queryBound_mapO _ Ct tC hC) fun s => hP s.2)
  refine MeasureTheory.lintegral_mono fun f => ?_
  show pr ((Ct.withTrace.bind fun o =>
        (Pt o.1.2).withTrace.bind fun o' =>
          ((A.tagKey t).V o.1.1 o'.1.1 o'.1.2).bind fun b =>
            .pure (⟨b, E.Ei o.1.1.2 o.2, o'.1.1,
                E.Ew o.1.1.2 o.2 o'.1.1 o'.1.2 o'.2⟩ : BindingOutcome I X W)).runEager f)
      (bindingBad R) ≤
    pr (((mapO (fun o => (o.1.2, (o.1.1, o.2))) Ct).withTrace.bind fun o =>
        (Pt o.1.2.2).withTrace.bind fun o' =>
          (A.V o.1.1 o'.1.1 o'.1.2).bind fun b =>
            .pure (⟨b, E.Ei o.1.1 o.2, o'.1.1,
                E.Ew o.1.1 o.2 o'.1.1 o'.1.2 o'.2⟩ : BindingOutcome I X W)).runEager f)
      (bindingBad R)
  rw [withTrace_mapO, mapO_bind]
  refine pr_runEager_bind_le f _ _ fun o => pr_runEager_bind_le f _ _ fun o' => ?_
  by_cases e : o.1.1.1 = t
  · have e2 : (A.tagKey t).V o.1.1 o'.1.1 o'.1.2 = A.V o.1.1.2 o'.1.1 o'.1.2 := if_pos e
    rw [e2]
  · have e2 : (A.tagKey t).V o.1.1 o'.1.1 o'.1.2 = .pure false := if_neg e
    rw [e2]
    refine le_trans (le_of_eq ?_) (zero_le _)
    show pr (PMF.pure _) (bindingBad R) = 0
    rw [Prob.pr_pure, if_neg]
    exact fun hb => Bool.noConfusion hb.1

theorem HasIndexBinding.tagKey {ε : ℕ → ℕ → ℝ≥0∞} (h : HasIndexBinding R A ε) :
    HasIndexBinding R (A.tagKey t) ε :=
  h.elim fun E hE => ⟨E.tagKey, hE.tagKey t⟩

/-! ## Index privacy -/

theorem tagKey_realLoop (Z : ViewEnv S (T × IVK) X W Pf) (isk : ISK) :
    ∀ (a : AdvVerifier S X Pf) (n : ℕ) (v : View S IVK X Pf),
      realLoop (A.tagKey t) Z isk a n (v.tagKey t) =
        mapO (View.tagKey t) (realLoop A (fun v => Z (v.tagKey t)) isk a n v)
  | .halt, _, _ => rfl
  | .query o q k, n, v => by
      show Rom.OComp.query o q (fun r =>
          realLoop (A.tagKey t) Z isk (k r) n
            (View.tagKey t { v with trace := v.trace ++ [⟨o, q, r⟩] })) =
        Rom.OComp.query o q fun r =>
          mapO (View.tagKey t)
            (realLoop A (fun v => Z (v.tagKey t)) isk (k r) n
              { v with trace := v.trace ++ [⟨o, q, r⟩] })
      exact congrArg _ (funext fun r => tagKey_realLoop Z isk (k r) n _)
  | .sample m k, n, v => by
      show Rom.OComp.sample m (fun r =>
          realLoop (A.tagKey t) Z isk (k r) n
            (View.tagKey t { v with coins := v.coins ++ [r.val] })) =
        Rom.OComp.sample m fun r =>
          mapO (View.tagKey t)
            (realLoop A (fun v => Z (v.tagKey t)) isk (k r)
              n { v with coins := v.coins ++ [r.val] })
      exact congrArg _ (funext fun r => tagKey_realLoop Z isk (k r) n _)
  | .request _, 0, _ => rfl
  | .request k, n + 1, v => by
      simp only [realLoop]
      cases Z (v.tagKey t) with
      | none => rfl
      | some b =>
          show (A.P isk b.pairs).bind (fun πs =>
              realLoop (A.tagKey t) Z isk (k (b.released πs.val)) n
                (View.tagKey t { v with sessions := v.sessions ++ [b.released πs.val] })) =
            mapO (View.tagKey t)
              ((A.P isk b.pairs).bind fun πs =>
                realLoop A (fun v => Z (v.tagKey t)) isk (k (b.released πs.val)) n
                  { v with sessions := v.sessions ++ [b.released πs.val] })
          rw [bind_mapO]
          exact congrArg _ (funext fun πs => tagKey_realLoop Z isk (k (b.released πs.val)) n _)

theorem tagKey_realExp (Vt : T × IVK → AdvVerifier S X Pf)
    (Z : ViewEnv S (T × IVK) X W Pf) (i : I) (N : ℕ) :
    realExp (A.tagKey t) Vt Z i N =
      mapO (View.tagKey t) (realExp A (fun ivk => Vt (t, ivk)) (fun v => Z (v.tagKey t)) i N) := by
  show (mapO (fun k => ((t, k.1), k.2)) (A.C i)).bind
      (fun key => realLoop (A.tagKey t) Z key.2 (Vt key.1) N ⟨key.1, [], [], []⟩) =
    mapO (View.tagKey t)
      ((A.C i).bind fun key =>
        realLoop A (fun v => Z (v.tagKey t)) key.2 (Vt (t, key.1)) N ⟨key.1, [], [], []⟩)
  rw [mapO_bind, bind_mapO]
  exact congrArg _
    (funext fun key => tagKey_realLoop t Z key.2 (Vt (t, key.1)) N ⟨key.1, [], [], []⟩)

theorem PrivacyFor.tagKey {Sim : Simulator S PP IVK X Pf} {ζ : ℕ → ℕ → ℝ≥0∞} {i : I}
    {Z : ViewEnv S (T × IVK) X W Pf} (h : PrivacyFor R A Sim ζ i fun v => Z (v.tagKey t)) :
    PrivacyFor R (A.tagKey t) (Sim.tagKey t) ζ i Z := by
  intro tV Vt N hV
  have b := h tV (fun ivk => Vt (t, ivk)) N fun ivk => hV (t, ivk)
  simp only [tagKey_realExp, tagKey_idealExp, Pr_mapO, Prob.pr_map]
  exact ⟨le_trans (sd_preimage_le (View.tagKey t) _ _) b.1, b.2⟩

theorem HasIndexPrivacyWith.tagKey {B : ℕ} {Sim : Simulator S PP IVK X Pf}
    {ζ : ℕ → ℕ → ℝ≥0∞} (h : HasIndexPrivacyWith R A B Sim ζ) :
    HasIndexPrivacyWith R (A.tagKey t) B (Sim.tagKey t) ζ :=
  fun i Z hZ => (h i (fun v => Z (v.tagKey t)) fun _ b e => hZ _ b e).tagKey t

theorem HasIndexPrivacy.tagKey {B : ℕ} {ζ : ℕ → ℕ → ℝ≥0∞} (h : HasIndexPrivacy R A B ζ) :
    HasIndexPrivacy R (A.tagKey t) B ζ :=
  h.elim fun Sim hS => ⟨Sim.tagKey t, hS.tagKey t⟩

/-! ## The primitive -/

/-- The form with extractor and simulator named is carried over from A to `A.tagKey t`, with the
same bounds, `E.tagKey` and `Sim.tagKey t`. -/
theorem IsZKCPArgWith.tagKey {B : ℕ} {E : Extractor S I X W IVK Pf} {Sim : Simulator S PP IVK X Pf}
    {α : ℝ≥0∞} {ε ζ : ℕ → ℕ → ℝ≥0∞} (h : IsZKCPArgWith R A B E Sim α ε ζ) :
    IsZKCPArgWith R (A.tagKey t) B (E.tagKey (T := T)) (Sim.tagKey t) α ε ζ :=
  ⟨h.completeness.tagKey t, h.indexBinding.tagKey t, h.indexPrivacy.tagKey t⟩

/-- The form `IsZKCPArg`, which says of extractor and simulator only that they exist, is carried
over from A to `A.tagKey t`, with the same bounds. -/
theorem IsZKCPArg.tagKey {B : ℕ} {α : ℝ≥0∞} {ε ζ : ℕ → ℕ → ℝ≥0∞} (h : IsZKCPArg R A B α ε ζ) :
    IsZKCPArg R (A.tagKey t) B α ε ζ :=
  ⟨h.completeness.tagKey t, h.indexBinding.tagKey t, h.indexPrivacy.tagKey t⟩

end ZKCP.Gen
