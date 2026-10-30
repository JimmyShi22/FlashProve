-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/TransportProofs.lean: the proofs of the statements of Run/Transport.lean.

What the statements say, how the proofs go and what is not said: Run/Transport.lean, the head. The
proofs follow the pattern of ZKCP/KeyTag.lean (a tag in the key) and use its tools on "a function
applied to the output of a computation" as they stand.

Main names:
  `c.adv a`, `c.view v`: the adversarial verifier that is handed typed proofs and reads them
    printed; a view with its proofs printed.
-/
import Run.Transport

set_option autoImplicit false

open scoped ENNReal

namespace Run
open ZKCP

namespace Wr
variable {lam : ℕ} {I X W PP IVK ISK Pf B : Type} (c : Wr Pf B)

theorem V_print (A : Arg lam I X W IVK ISK Pf) (ivk : IVK) (x : X) (π : Pf) :
    (c.arg A).V ivk x (c.print π) = A.V ivk x π := by
  show (match c.parse (c.print π) with | none => OComp.pure false | some π => A.V ivk x π) = _
  rw [c.back]

theorem V_none (A : Arg lam I X W IVK ISK Pf) (ivk : IVK) (x : X) (b : B) (h : c.parse b = none) :
    (c.arg A).V ivk x b = .pure false := by
  show (match c.parse b with | none => OComp.pure false | some π => A.V ivk x π) = _
  rw [h]

theorem V_some (A : Arg lam I X W IVK ISK Pf) (ivk : IVK) (x : X) (b : B)
    (π : Pf) (h : c.parse b = some π) :
    (c.arg A).V ivk x b = A.V ivk x π := by
  show (match c.parse b with | none => OComp.pure false | some π => A.V ivk x π) = _
  rw [h]

/-! ### Completeness -/

theorem sessionExp_eq (A : Arg lam I X W IVK ISK Pf) (ivk : IVK) (isk : ISK) (x : X) (w : W) :
    sessionExp (c.arg A) ivk isk x w = sessionExp A ivk isk x w := by
  show ((A.P isk x w).mapO c.print).bind (fun b => (c.arg A).V ivk x b) =
    (A.P isk x w).bind fun π => A.V ivk x π
  rw [OComp.mapO_bind]
  simp only [V_print]

theorem completenessExp_eq (A : Arg lam I X W IVK ISK Pf) (i : I) (x : X) (w : W) :
    completenessExp (c.arg A) i x w = completenessExp A i x w := by
  show (A.C i).bind (fun key => sessionExp (c.arg A) key.1 key.2 x w) =
    (A.C i).bind fun key => sessionExp A key.1 key.2 x w
  simp only [sessionExp_eq]

/-! ### Privacy: the adversary and the view -/

/-- The adversarial verifier that is handed typed proofs and reads them printed. -/
def adv : AdvVerifier lam X B → AdvVerifier lam X Pf
  | .halt => .halt
  | .query q k => .query q fun r => adv (k r)
  | .sample n k => .sample n fun r => adv (k r)
  | .request k => .request fun x π => adv (k x (c.print π))

theorem adv_bound : ∀ (a : AdvVerifier lam X B) (t : ℕ), a.QueryBound t → (c.adv a).QueryBound t
  | .halt, _, _ => trivial
  | .query _ _, 0, h => h.elim
  | .query _ k, t + 1, h => fun r => adv_bound (k r) t (h r)
  | .sample _ k, t, h => fun r => adv_bound (k r) t (h r)
  | .request k, t, h => fun x π => adv_bound (k x (c.print π)) t (h x (c.print π))

/-- A view with its proofs printed. -/
def view (v : View lam IVK X Pf) : View lam IVK X B :=
  ⟨v.ivk, v.sessions.map fun s => (s.1, c.print s.2), v.trace, v.coins⟩

theorem view_snoc (v : View lam IVK X Pf) (x : X) (π : Pf) :
    ({ c.view v with sessions := (c.view v).sessions ++ [(x, c.print π)] } : View lam IVK X B) =
      c.view { v with sessions := v.sessions ++ [(x, π)] } := by
  simp [view]

theorem realLoop_eq (A : Arg lam I X W IVK ISK Pf) (Z : ViewEnv lam IVK X W B) (isk : ISK) :
    ∀ (a : AdvVerifier lam X B) (n : ℕ) (v : View lam IVK X Pf),
      realLoop (c.arg A) Z isk a n (c.view v) =
        (realLoop A (fun v => Z (c.view v)) isk (c.adv a) n v).mapO c.view
  | .halt, _, _ => rfl
  | .query q k, n, v => by
      show OComp.query q (fun r =>
          realLoop (c.arg A) Z isk (k r) n (c.view { v with trace := v.trace ++ [(q, r)] })) =
        OComp.query q fun r =>
          (realLoop A (fun v => Z (c.view v)) isk (c.adv (k r)) n
            { v with trace := v.trace ++ [(q, r)] }).mapO c.view
      exact congrArg _ (funext fun r => realLoop_eq A Z isk (k r) n _)
  | .sample m k, n, v => by
      show OComp.sample m (fun r =>
          realLoop (c.arg A) Z isk (k r) n (c.view { v with coins := v.coins ++ [r.val] })) =
        OComp.sample m fun r =>
          (realLoop A (fun v => Z (c.view v)) isk (c.adv (k r)) n
            { v with coins := v.coins ++ [r.val] }).mapO c.view
      exact congrArg _ (funext fun r => realLoop_eq A Z isk (k r) n _)
  | .request _, 0, _ => rfl
  | .request k, n + 1, v => by
      simp only [realLoop, adv]
      cases Z (c.view v) with
      | none => rfl
      | some xw =>
          show ((A.P isk xw.1 xw.2).mapO c.print).bind (fun b =>
              realLoop (c.arg A) Z isk (k xw.1 b) n
                { c.view v with sessions := (c.view v).sessions ++ [(xw.1, b)] }) =
            ((A.P isk xw.1 xw.2).bind fun π =>
              realLoop A (fun v => Z (c.view v)) isk (c.adv (k xw.1 (c.print π))) n
                { v with sessions := v.sessions ++ [(xw.1, π)] }).mapO c.view
          rw [OComp.mapO_bind, OComp.bind_mapO]
          refine congrArg _ (funext fun π => ?_)
          rw [view_snoc]
          exact realLoop_eq A Z isk (k xw.1 (c.print π)) n _

theorem realExp_eq (A : Arg lam I X W IVK ISK Pf) (Vt : IVK → AdvVerifier lam X B)
    (Z : ViewEnv lam IVK X W B) (i : I) (N : ℕ) :
    realExp (c.arg A) Vt Z i N =
      (realExp A (fun ivk => c.adv (Vt ivk)) (fun v => Z (c.view v)) i N).mapO c.view := by
  show (A.C i).bind (fun key => realLoop (c.arg A) Z key.2 (Vt key.1) N ⟨key.1, [], [], []⟩) =
    ((A.C i).bind fun key =>
      realLoop A (fun v => Z (c.view v)) key.2 (c.adv (Vt key.1)) N ⟨key.1, [], [], []⟩).mapO c.view
  rw [OComp.bind_mapO]
  exact congrArg _ (funext fun key => realLoop_eq c A Z key.2 (Vt key.1) N ⟨key.1, [], [], []⟩)

theorem idealLoop_eq (S : Simulator lam PP IVK X Pf) (Z : ViewEnv lam IVK X W B) :
    ∀ (a : AdvVerifier lam X B) (n : ℕ) (v : View lam IVK X Pf) (s : S.St),
      idealLoop (c.sim S) Z a n (c.view v) s =
        (idealLoop S (fun v => Z (c.view v)) (c.adv a) n v s).map c.view
  | .halt, _, _, _ => (PMF.pure_map _ _).symm
  | .query q k, n, v, s => by
      simp only [idealLoop, adv, PMF.map_bind]
      exact congrArg _
        (funext fun out =>
          idealLoop_eq S Z (k out.1) n { v with trace := v.trace ++ [(q, out.1)] } out.2)
  | .sample m k, n, v, s => by
      simp only [idealLoop, adv, PMF.map_bind]
      exact congrArg _
        (funext fun r => idealLoop_eq S Z (k r) n { v with coins := v.coins ++ [r.val] } s)
  | .request _, 0, _, _ => (PMF.pure_map _ _).symm
  | .request k, n + 1, v, s => by
      simp only [idealLoop, adv]
      cases Z (c.view v) with
      | none => exact (PMF.pure_map _ _).symm
      | some xw =>
          show ((S.prove s xw.1).map fun o => (c.print o.1, o.2)).bind (fun out =>
              idealLoop (c.sim S) Z (k xw.1 out.1) n
                { c.view v with sessions := (c.view v).sessions ++ [(xw.1, out.1)] } out.2) =
            ((S.prove s xw.1).bind fun out =>
              idealLoop S (fun v => Z (c.view v)) (c.adv (k xw.1 (c.print out.1))) n
                { v with sessions := v.sessions ++ [(xw.1, out.1)] } out.2).map c.view
          rw [PMF.bind_map, PMF.map_bind]
          refine congrArg _ (funext fun out => ?_)
          show idealLoop (c.sim S) Z (k xw.1 (c.print out.1)) n
              { c.view v with sessions := (c.view v).sessions ++ [(xw.1, c.print out.1)] } out.2 = _
          rw [view_snoc]
          exact idealLoop_eq S Z (k xw.1 (c.print out.1)) n _ out.2

theorem idealExp_eq (R : IndexedRelation I X W PP) (S : Simulator lam PP IVK X Pf)
    (Vt : IVK → AdvVerifier lam X B) (Z : ViewEnv lam IVK X W B) (i : I) (N : ℕ) :
    idealExp R (c.sim S) Vt Z i N =
      (idealExp R S (fun ivk => c.adv (Vt ivk)) (fun v => Z (c.view v)) i N).map c.view := by
  show (S.init (R.pp i) N).bind
      (fun out => idealLoop (c.sim S) Z (Vt out.1) N ⟨out.1, [], [], []⟩ out.2) =
    ((S.init (R.pp i) N).bind fun out =>
      idealLoop S (fun v => Z (c.view v)) (c.adv (Vt out.1)) N ⟨out.1, [], [], []⟩ out.2).map c.view
  rw [PMF.map_bind]
  exact congrArg _ (funext fun out => idealLoop_eq c S Z (Vt out.1) N ⟨out.1, [], [], []⟩ out.2)

end Wr

theorem wr_V : Spec.wr_V := fun _ _ _ _ _ _ _ _ c A =>
  ⟨c.V_print A, c.V_none A, c.V_some A, fun N h ivk x b => by
    cases e : c.parse b with
    | none => rw [c.V_none A ivk x b e]; trivial
    | some π => rw [c.V_some A ivk x b π e]; exact h ivk x π⟩

theorem wr_complete : Spec.wr_complete := fun _ _ _ _ _ _ _ _ _ c R A α h i x w hr => by
  rw [c.completenessExp_eq]
  exact h i x w hr

theorem wr_binding : Spec.wr_binding := by
  intro lam I X W PP IVK ISK Pf B c d R A E ε h tC tP St Ct Pt hC hP
  refine le_trans ?_
    (h tC tP St Ct (fun s => (Pt s).mapO fun o => (o.1, (c.parse o.2).getD d)) hC
      fun s => OComp.QueryBound.mapO _ (Pt s) tP (hP s))
  refine MeasureTheory.lintegral_mono fun f => ?_
  show prob ((Ct.withTrace.bind fun o =>
        (Pt o.1.2).withTrace.bind fun o' =>
          ((c.arg A).V o.1.1 o'.1.1 o'.1.2).bind fun b =>
            .pure (⟨b, E.Ei o.1.1 o.2, o'.1.1,
                E.Ew o.1.1 o.2 o'.1.1 ((c.parse o'.1.2).getD d)
                  o'.2⟩ : BindingOutcome I X W)).run f) (bindingBad R) ≤
    prob ((Ct.withTrace.bind fun o =>
        ((Pt o.1.2).mapO fun o => (o.1, (c.parse o.2).getD d)).withTrace.bind fun o' =>
          (A.V o.1.1 o'.1.1 o'.1.2).bind fun b =>
            .pure (⟨b, E.Ei o.1.1 o.2, o'.1.1,
                E.Ew o.1.1 o.2 o'.1.1 o'.1.2 o'.2⟩ : BindingOutcome I X W)).run f) (bindingBad R)
  simp only [OComp.withTrace_mapO, OComp.mapO_bind]
  refine prob_run_bind_le f _ _ fun o => prob_run_bind_le f _ _ fun o' => ?_
  cases e : c.parse o'.1.2 with
  | some π =>
    rw [c.V_some A _ _ _ π e]
    exact le_rfl
  | none =>
    rw [c.V_none A _ _ _ e]
    refine le_trans (le_of_eq ?_) (zero_le _)
    show prob (PMF.pure _) (bindingBad R) = 0
    rw [prob_pure, if_neg]
    exact fun hb => Bool.noConfusion hb.1

theorem wr_privacy : Spec.wr_privacy := by
  intro lam I X W PP IVK ISK Pf B c R A S ζ h i Z hZ tV Vt N hV
  have b := h i (fun v => Z (c.view v)) (fun _ x w e => hZ _ x w e) tV (fun ivk => c.adv (Vt ivk)) N
    fun ivk => c.adv_bound (Vt ivk) tV (hV ivk)
  simp only [Wr.realExp_eq, Wr.idealExp_eq, Pr_mapO, prob_map]
  exact ⟨le_trans (SD_preimage_le c.view _ _) b.1, b.2⟩

theorem wr_arg : Spec.wr_arg := fun lam I X W PP IVK ISK Pf B c d R A E S α ε ζ h =>
  ⟨wr_complete lam I X W PP IVK ISK Pf B c R A α h.completeness,
    wr_binding lam I X W PP IVK ISK Pf B c d R A E ε h.indexBinding,
    wr_privacy lam I X W PP IVK ISK Pf B c R A S ζ h.indexPrivacy⟩

end Run
