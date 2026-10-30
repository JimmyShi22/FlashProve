-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Hiop/Seeded/WholeProof.lean: proofs of the statements of Hiop/Seeded/Whole.lean.

The work is done in Hiop/Seeded/FormProof.lean, for an experiment in which nothing is left of the
three protocols but how a simulated run reads the encoded indices (`Spec.form_laws`,
Hiop/Seeded/Form.lean). Here the experiment of Hiop/Seeded/Whole.lean is shown to be a case of it.
 Part 1: the simulator of the theorem is the host of a family of laws (`simLawsS`); what one step of
   an environment does with such a host;
 Part 2: the form of the runs (`batchForm`); environments, laws and simulated runs in that form
   (`toF`, `lawsF`, `simsF`); a simulated run in that form has the law of the simulated session;
 Part 3: the two experiments have the same law (`run_toF`, `view_toF`); bounds and premises carry
   over;
 Part 4: the real side with given provers is near good simulators (`near_realS`);
 Part 5: the theorems.

Limits: see the head of Hiop/Seeded/Whole.lean.
Terms: lean/GLOSSARY.md.

-/
import Hiop.Seeded.Whole
import Hiop.Seeded.FormProof

set_option autoImplicit false

noncomputable section

namespace Hiop.Seeded
open Prob Iop Compile.Lifetime Compile.BatchLife
open scoped ENNReal

variable {I X : Type} {L : HolographicProtocol I X} {α : Type}

/-! ## Part 1. The simulator's host is the host of a family of laws -/

def simLawsS (L : HolographicProtocol I X) (Sm : SimsS L) (i₀ : I) : LawsS L where
  rc := fun u => L.recOf i₀ u.1 u.2
  T := fun e u => simSess L.offline (Sm.T e) (L.recOf i₀ u.1 u.2) (L.encodeIndex i₀ u.1)
  Lk := fun e u u' =>
    simSess L.link (Sm.Lk e) (L.recOf i₀ u.1 u.2, L.recOf i₀ u'.1 u'.2)
      (L.encodeIndex i₀ u.1, L.encodeIndex i₀ u'.1)
  B := fun e u J xs _ =>
    simBsess L.onlineBatch (Sm.B e) J (fun j => (xs j, L.recOf i₀ u.1 u.2)) (L.encodeIndex i₀ u.1)
  y := fun u p => L.encodeIndex i₀ u.1 p

theorem simHostS_eq (Sm : SimsS L) (i₀ : I) :
    (simWholeS L Sm i₀).host = (simLawsS L Sm i₀).host := rfl

section HostEqs
variable (W : LawsS L)

theorem viewS_host (s₀ : L.OutOfDomainSeed) (E : L.Rec → EnvS L α) :
    W.host.view s₀ E =
      (unif L.EncodingRandomness).bind fun r => (E (W.rc (r, s₀))).run W.host (0, fun _ => (r, s₀)) := by
  show ((unif L.EncodingRandomness).map fun r => (W.rc (r, s₀), ((0, fun _ => (r, s₀)) : StS L))).bind
      (fun p => (E p.1).run W.host p.2) = _
  simp only [PMF.bind_map, Function.comp_def]
theorem runS_stop (a : α) (st : StS L) : (EnvS.stop a : EnvS L α).run W.host st = PMF.pure a := rfl
theorem runS_draw (β : Type) (d : PMF β) (k : β → EnvS L α) (st : StS L) :
    (EnvS.draw β d k).run W.host st = d.bind fun y => (k y).run W.host st := rfl
theorem runS_fresh (s : L.OutOfDomainSeed) (k : L.Rec → EnvS L α) (c : ℕ) (f : ℕ → L.EncodingRandomness × L.OutOfDomainSeed) :
    (EnvS.fresh s k).run W.host (c, f) =
      (unif L.EncodingRandomness).bind fun r =>
        (k (W.rc (r, s))).run W.host (c + 1, Function.update f (c + 1) (r, s)) := by
  show ((unif L.EncodingRandomness).map fun r =>
        (W.rc (r, s), ((c + 1, Function.update f (c + 1) (r, s)) : StS L))).bind
      (fun p => (k p.1).run W.host p.2) = _
  simp only [PMF.bind_map, Function.comp_def]
theorem runS_test (e : ℕ) (k : Sess L.offline → EnvS L α) (st : StS L) :
    (EnvS.test e k).run W.host st = (W.T e (st.2 e)).bind fun a => (k a).run W.host st := by
  show ((W.T e (st.2 e)).map fun a => (a, st)).bind (fun p => (k p.1).run W.host p.2) = _
  simp only [PMF.bind_map, Function.comp_def]
theorem runS_link (e : ℕ) (k : Sess L.link → EnvS L α) (st : StS L) :
    (EnvS.link e k).run W.host st =
      (W.Lk e (st.2 0) (st.2 e)).bind fun a => (k a).run W.host st := by
  show ((W.Lk e (st.2 0) (st.2 e)).map fun a => (a, st)).bind
      (fun p => (k p.1).run W.host p.2) = _
  simp only [PMF.bind_map, Function.comp_def]
theorem runS_session (e : ℕ) (J : Finset (Fin L.maxBatchSize)) (xs : J → X)
    (rest : {j : Fin L.maxBatchSize // j ∉ J} → Option X) (k : BSess L.onlineBatch J → EnvS L α) (st : StS L) :
    (EnvS.session e J xs rest k).run W.host st =
      (W.B e (st.2 e) J xs rest).bind fun a => (k a).run W.host st := by
  show ((W.B e (st.2 e) J xs rest).map fun a => (a, st)).bind
      (fun p => (k p.1).run W.host p.2) = _
  simp only [PMF.bind_map, Function.comp_def]
theorem runS_read (e : ℕ) (p : Fin L.wordLength) (k : L.Symbol → EnvS L α) (st : StS L) :
    (EnvS.read e p k).run W.host st = (k (W.y (st.2 e) p)).run W.host st := by
  show (PMF.pure (W.y (st.2 e) p, st)).bind (fun q => (k q.1).run W.host q.2) = _
  rw [PMF.pure_bind]
end HostEqs

/-! ## Part 2. The form of the runs -/

/-- What the runs of Hiop/Seeded/Whole.lean are asked with and what they show. A session is asked
with the set J of slots that are shown and their instances; what the other slots hold is the part
that the simulator is not told. -/
abbrev batchForm (L : HolographicProtocol I X) : Form X where
  RT := Sess L.offline
  RL := Sess L.link
  QB := Σ J : Finset (Fin L.maxBatchSize), (J → X)
  HB := fun q => {j : Fin L.maxBatchSize // j ∉ q.1} → Option X
  RB := fun q => BSess L.onlineBatch q.1
  wt := fun q => q.1.card
  okB := fun ok q rest => (∀ j, ok (q.2 j)) ∧ ∀ j x, rest j = some x → ok x

def toF : EnvS L α → EnvF L (batchForm L) α
  | .stop a => .stop a
  | .fresh s k => .fresh s fun a => toF (k a)
  | .test e k => .test e fun a => toF (k a)
  | .link e k => .link e fun a => toF (k a)
  | .session e J xs rest k => .session e ⟨J, xs⟩ rest fun a => toF (k a)
  | .read e p k => .read e p fun y => toF (k y)
  | .draw β d k => .draw β d fun y => toF (k y)

def lawsF (W : LawsS L) : LawsF L (batchForm L) :=
  ⟨W.rc, W.T, W.Lk, fun e u q rest => W.B e u q.1 q.2 rest, W.y⟩

/-- The simulated sessions as simulated runs: the auxiliary value is the verifier's randomness,
uniform; the positions are the verifier's. -/
def simsF (Sm : SimsS L) : SimsF L (batchForm L) where
  T := fun e x =>
    ⟨Rho L.offline.shape, unif _, fun ρ => L.offline.extReads x ρ,
      fun ρ ans => (Sm.T e x ρ ans).map fun o => (ρ, o)⟩
  Lk := fun e x =>
    ⟨Rho L.link.shape, unif _, fun ρ => L.link.extReads x ρ,
      fun ρ ans => (Sm.Lk e x ρ ans).map fun o => (ρ, o)⟩
  B := fun e q x =>
    ⟨BRho L.maxBatchSize L.onlineBatch.loc.shape L.onlineBatch.ann, unif _,
      fun ρ => readsJ L.onlineBatch q.1 (fun j => (q.2 j, x)) fun j => ρ.slot j.1,
      fun ρ ans =>
        (Sm.B e q.1 (fun j => (q.2 j, x)) (fun j => ρ.slot j.1) ans).map
          fun o => (fun j => ρ.slot j.1, o)⟩

theorem law_simsF_T (Sm : SimsS L) (e : ℕ) (x : L.Rec) (y : Fin L.wordLength → L.Symbol) :
    ((simsF Sm).T e x).law y = simSess L.offline (Sm.T e) x y := rfl

theorem law_simsF_Lk (Sm : SimsS L) (e : ℕ) (x : L.Rec × L.Rec) (y y' : Fin L.wordLength → L.Symbol) :
    ((simsF Sm).Lk e x).law (Sum.elim y y') = simSess L.link (Sm.Lk e) x (y, y') := rfl

open Classical in
/-- The law of a simulated run, with the symbols read written in another way. -/
theorem RunSim.law_congr {Pos Sym Out : Type} (R : RunSim Pos Sym Out) (str : Pos → Sym)
    (g : R.Aux → Pos → Option Sym)
    (hg : ∀ a p, (p ∈ R.reads a → g a p = some (str p)) ∧ (p ∉ R.reads a → g a p = none)) :
    R.law str = R.μ.bind fun a => R.out a (g a) := by
  unfold RunSim.law
  refine congrArg _ (funext fun a => congrArg _ (funext fun p => ?_))
  by_cases h : p ∈ R.reads a
  · rw [if_pos h, (hg a p).1 h]
  · rw [if_neg h, (hg a p).2 h]

theorem law_simsF_B (Sm : SimsS L) (e : ℕ) (J : Finset (Fin L.maxBatchSize)) (xs : J → X) (x : L.Rec)
    (y : Fin L.wordLength → L.Symbol) :
    ((simsF Sm).B e ⟨J, xs⟩ x).law y = simBsess L.onlineBatch (Sm.B e) J (fun j => (xs j, x)) y := by
  rw [RunSim.law_congr _ _
    (fun ρ => L.onlineBatch.extAnsJ J (fun j => (xs j, x)) (fun j => BRho.slot j.1 ρ) y) fun ρ p => ?_]
  · rfl
  · unfold BatchInteractiveOracleProof.extAnsJ
    exact ⟨fun h => if_pos (mem_readsJ.1 h), fun h => if_neg fun hh => h (mem_readsJ.2 hh)⟩

/-- The simulator's laws, in that form. -/
theorem lawsF_sim (Sm : SimsS L) (j : I) :
    lawsF (simLawsS L Sm j) = simLawsF L (batchForm L) (simsF Sm) j := by
  show (⟨_, _, _, _, _⟩ : LawsF L (batchForm L)) = ⟨_, _, _, _, _⟩
  congr 1
  funext e u q rest
  obtain ⟨J, xs⟩ := q
  exact (law_simsF_B Sm e J xs _ _).symm

/-! ## Part 3. The two experiments have the same law -/

theorem run_toF (W : LawsS L) (t : EnvS L α) :
    ∀ st : StS L, (toF t).run (lawsF W).host st = t.run W.host st := by
  induction t with
  | stop a => intro st; rfl
  | draw β d k ih =>
    intro st
    show (d.bind fun y => (toF (k y)).run (lawsF W).host st) = d.bind fun y => (k y).run W.host st
    exact congrArg _ (funext fun y => ih y st)
  | fresh s k ih =>
    intro st
    obtain ⟨c, f⟩ := st
    rw [runS_fresh]
    show (EnvF.fresh s fun a => toF (k a)).run (lawsF W).host (c, f) = _
    rw [runF_fresh]
    exact congrArg _ (funext fun r => ih _ _)
  | test e k ih =>
    intro st
    rw [runS_test]
    show (EnvF.test e fun a => toF (k a)).run (lawsF W).host st = _
    rw [runF_test]
    exact congrArg _ (funext fun a => ih a st)
  | link e k ih =>
    intro st
    rw [runS_link]
    show (EnvF.link e fun a => toF (k a)).run (lawsF W).host st = _
    rw [runF_link]
    exact congrArg _ (funext fun a => ih a st)
  | session e J xs rest k ih =>
    intro st
    rw [runS_session]
    show (EnvF.session (F := batchForm L) e ⟨J, xs⟩ rest fun a => toF (k a)).run
      (lawsF W).host st = _
    rw [runF_session]
    exact congrArg _ (funext fun a => ih a st)
  | read e p k ih =>
    intro st
    rw [runS_read]
    show (EnvF.read e p fun y => toF (k y)).run (lawsF W).host st = _
    rw [runF_read]
    exact ih _ st

theorem view_toF (W : LawsS L) (s₀ : L.OutOfDomainSeed) (E : L.Rec → EnvS L α) :
    (lawsF W).host.view s₀ (fun a => toF (E a)) = W.host.view s₀ E := by
  rw [viewS_host, viewF_host]
  exact congrArg _ (funext fun r => run_toF W _ _)

theorem adm_toF {B : BoundsR} {Gs : L.OutOfDomainSeed → Prop} {ok : X → Prop} (t : EnvS L α) :
    ∀ (c : ℕ) (u : UsedR), t.Adm B Gs ok c u → (toF t).Adm B Gs ok c u := by
  induction t with
  | stop a => intro _ _ _; exact trivial
  | draw β d k ih => intro c u h y; exact ih y c u (h y)
  | fresh s k ih => intro c u h; exact ⟨h.1, h.2.1, fun a => ih a (c + 1) u (h.2.2 a)⟩
  | test e k ih => intro c u h; exact ⟨h.1, h.2.1, fun a => ih a c _ (h.2.2 a)⟩
  | link e k ih => intro c u h; exact ⟨h.1, h.2.1, h.2.2.1, fun a => ih a c _ (h.2.2.2 a)⟩
  | session e J xs rest k ih =>
    intro c u h
    exact ⟨h.1, h.2.1, h.2.2.1, ⟨h.2.2.2.1, h.2.2.2.2.1⟩, fun a => ih a c _ (h.2.2.2.2.2 a)⟩
  | read e p k ih => intro c u h; exact ⟨h.1, h.2.1, fun y => ih y c _ (h.2.2 y)⟩

theorem counts_simsF {Gs : L.OutOfDomainSeed → Prop} {b qT qpar qch qon : ℕ}
    (hR : ReadsS L Gs b qT qpar qch qon) (Sm : SimsS L) :
    (simsF Sm).Counts qT qpar qch qon where
  cntT := fun _ x ρ => hR.cntT x ρ
  cntLp := fun _ x ρ => hR.cntLp x ρ
  cntLc := fun _ x ρ => hR.cntLc x ρ
  cntB := fun _ q _ ρ => card_readsJ_le hR.cntB q.1 _ ρ

theorem near_lawsF {W : LawsS L} {Sm : SimsS L} {Gs : L.OutOfDomainSeed → Prop} {i : I} {ok : X → Prop}
    {zT zL zO : ℝ≥0∞} (hN : W.Near Sm Gs i ok zT zL zO) :
    (lawsF W).Near (simsF Sm) Gs i ok zT zL zO where
  rc := hN.rc
  y := hN.y
  T := hN.T
  Lk := hN.Lk
  B := fun e u q rest hu hq => by
    obtain ⟨J, xs⟩ := q
    show tv (W.B e u J xs rest) (((simsF Sm).B e ⟨J, xs⟩ (L.recOf i u.1 u.2)).law (L.encodeIndex i u.1)) ≤ _
    rw [law_simsF_B]
    exact hN.B e u J xs rest hu hq.1 hq.2

/-! ## Part 4. The real side with given provers -/

/-- The real side with the provers P is near simulators that are good for P. -/
theorem near_realS {Gs : L.OutOfDomainSeed → Prop} {Ryes : I → X → Prop} {zT zL zO : ℝ≥0∞} {P : ProversS L}
    (hX : P.Ext) {Sm : SimsS L} (hS : Sm.Good P Gs Ryes zT zL zO) (i : I) :
    (realLawsS L P i).Near Sm Gs i (Ryes i) zT zL zO where
  rc := fun _ => rfl
  y := fun _ _ => rfl
  T := fun e u hu => by
    have h1 := tv_sess_le (P.T e) (Sm.T e) (i, u.1, u.2) (L.recOf i u.1 u.2)
      (hS.goodT e (i, u.1, u.2) _ rfl hu)
    rw [hX.extT] at h1
    exact h1
  Lk := fun e u u' hu hu' => by
    obtain ⟨r, s⟩ := u
    obtain ⟨r', s'⟩ := u'
    have h1 := tv_sess_le (P.Lk e) (Sm.Lk e) (i, (r, s), (r', s'))
      (L.recOf i r s, L.recOf i r' s') (hS.goodL e (i, (r, s), (r', s')) _ rfl hu hu')
    rw [hX.extL] at h1
    exact h1
  B := fun e u J xs rest hu h1 h2 => by
    have hv : ∀ j xj,
        vec J (fun j => (xs j, L.recOf i u.1 u.2))
            (fun j => (rest j).map fun x => (x, L.recOf i u.1 u.2)) j = some xj →
        L.validB Ryes (i, u.1, u.2) xj :=
      valid_vec J _ _ (fun j => ⟨rfl, h1 j⟩) fun j x hx => by
        cases hr : rest j with
        | none => rw [hr] at hx; cases hx
        | some x' =>
          rw [hr] at hx
          cases hx
          exact ⟨rfl, h2 j x' hr⟩
    have h3 := tv_bsess_le (P.B e) (Sm.B e) (i, u.1, u.2) _ J
      (fun j => (xs j, L.recOf i u.1 u.2))
      (hS.goodB e (i, u.1, u.2) _ hu hv J _ (vec_of_mem J _ _))
    rw [hX.extB] at h3
    exact h3

/-! ## Part 5. The theorems -/

section Nice
variable {B : BoundsR} {Gs : L.OutOfDomainSeed → Prop} {ok : X → Prop}

/-- Further encoded indices at the seeds of a list keep the bounds if there is room for them, the
seeds are in Gs, and what follows keeps the bounds. -/
theorem adm_freshAll (ss : List L.OutOfDomainSeed) :
    ∀ (K : List L.Rec → EnvS L α) (c : ℕ) (u : UsedR), (∀ s ∈ ss, Gs s) →
      c + ss.length ≤ B.nenc → (∀ as, (K as).Adm B Gs ok (c + ss.length) u) →
        (freshAll ss K).Adm B Gs ok c u := by
  induction ss with
  | nil => intro K c u _ _ h; exact h []
  | cons s ss ih =>
    intro K c u hG hc h
    have hl : c + (s :: ss).length = c + 1 + ss.length := by
      rw [List.length_cons]
      omega
    rw [hl] at hc
    show Gs s ∧ c < B.nenc ∧ ∀ a, (freshAll ss fun as => K (a :: as)).Adm B Gs ok (c + 1) u
    refine ⟨hG s (List.mem_cons.2 (Or.inl rfl)), by omega, fun a =>
      ih _ (c + 1) u (fun t ht => hG t (List.mem_cons.2 (Or.inr ht))) hc fun as => ?_⟩
    have h0 := h (a :: as)
    rw [hl] at h0
    exact h0

end Nice

/-- For given laws of runs. (not all hypotheses are named here: see `Spec.whole_laws`) -/
theorem whole_laws : Spec.whole_laws := by
  intro I X L Gs ok b qT qpar qch qon zT zL zO hR Sm W i hN B hB i₀ α s₀ E h0 hE
  have h := form_laws I X L (batchForm L) Gs ok b qT qpar qch qon zT zL zO hR.hidE (simsF Sm)
    (counts_simsF hR Sm) (lawsF W) i (near_lawsF hN) B hB i₀ α s₀ (fun a => toF (E a)) h0
    fun a => adm_toF (E a) 0 _ (hE a)
  rw [simHostF_eq, ← lawsF_sim, view_toF, view_toF] at h
  rw [simHostS_eq]
  exact h

/-- For given provers. (not all hypotheses are named here: see `Spec.whole_provers`) -/
theorem whole_provers : Spec.whole_provers :=
  fun I X L Gs Ryes b qT qpar qch qon zT zL zO hR _ hX Sm hS B hB i₀ i =>
    whole_laws I X L Gs (Ryes i) b qT qpar qch qon zT zL zO hR Sm _ i (near_realS hX hS i) B hB i₀

/-- From honest-verifier zero knowledge of each honest side. (not all hypotheses are named here: see
`Spec.whole_hiding`) -/
theorem whole_hiding : Spec.whole_hiding := by
  intro I X L Gs Ryes b qT qpar qch qon zT zL zO hR P hX hH
  refine ⟨⟨fun e => Classical.choose (hH.hidT e), fun e => Classical.choose (hH.hidL e),
    fun e => Classical.choose (hH.hidB e)⟩, fun B hB i₀ =>
      whole_provers I X L Gs Ryes b qT qpar qch qon zT zL zO hR P hX _ ⟨?_, ?_, ?_⟩ B hB i₀⟩
  · exact fun e w x hv hg => Classical.choose_spec (hH.hidT e) w x ⟨hv, hg⟩
  · exact fun e w x hv hg hg' => Classical.choose_spec (hH.hidL e) w x ⟨hv, hg, hg'⟩
  · exact fun e w x hg hv J xs hx =>
      Classical.choose_spec (hH.hidB e) w x (fun j xj h => ⟨hv j xj h, hg⟩) J xs hx

/-- The form to quote: for given provers, at all seeds. (not all hypotheses are named here: see
`Spec.whole_all_seeds`) -/
theorem whole_all_seeds : Spec.whole_all_seeds :=
  fun I X L Ryes b qT qpar qch qon zT zL zO hR =>
    whole_provers I X L (fun _ => True) Ryes b qT qpar qch qon zT zL zO (readsS_iff.2 hR)

/-- All encoded indices made at the start, at a given list of seeds. -/
theorem whole_vector : Spec.whole_vector :=
  fun _ _ _ _ _ _ _ _ _ hV α s₀ ss K h0 hs hl hK =>
    hV α s₀ (fun a => freshAll ss (K a)) h0 fun a =>
      adm_freshAll ss (K a) 0 UsedR.zero hs (by rw [Nat.zero_add]; exact hl) fun as => by
        rw [Nat.zero_add]
        exact hK a as

/-- An environment that draws coins before it names the first seed: the same bound. -/
theorem ViewNear.pre {H : HostS L} {Gs : L.OutOfDomainSeed → Prop} {ok : X → Prop} {B : BoundsR}
    {S : SimulatorS L} {z : ℝ≥0∞} (h : ViewNear H Gs ok B S z) {β : Type} (d : PMF β)
    (s₀ : β → L.OutOfDomainSeed) (E : β → L.Rec → EnvS L α) (h0 : ∀ y, Gs (s₀ y))
    (hE : ∀ y a, (E y a).Adm B Gs ok 0 UsedR.zero) :
    tv (d.bind fun y => H.view (s₀ y) (E y)) (d.bind fun y => S.host.view (s₀ y) (E y)) ≤ z :=
  tv_bind_right_le_of_forall d _ _ fun y _ => h α (s₀ y) (E y) (h0 y) (hE y)

end Hiop.Seeded

#print axioms Hiop.Seeded.whole_laws
#print axioms Hiop.Seeded.whole_provers
#print axioms Hiop.Seeded.whole_all_seeds
#print axioms Hiop.Seeded.whole_hiding
#print axioms Hiop.Seeded.whole_vector
#print axioms Hiop.Seeded.ViewNear.pre
