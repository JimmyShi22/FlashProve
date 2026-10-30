-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/TransportPrintProofs.lean: the proofs of the statements of Run/TransportPrint.lean.

What the statements say and do not say: Run/TransportPrint.lean, the head. The steps are those of
the privacy part of Run/TransportProofs.lean, with any function pr in the place of the printer and
any verifier V'.

Main names:
  `prAdv pr a`, `prView pr v`: the adversarial verifier that is handed typed proofs and reads them
    through pr; a view with its proofs put through pr.
-/
import Run.TransportPrint

set_option autoImplicit false

open scoped ENNReal

namespace Run
open ZKCP

section
variable {lam : ℕ} {I X W PP IVK ISK Pf B : Type} (pr : Pf → B) (V' : IVK → X → B → OComp lam Bool)

/-! ### Privacy: the adversary and the view -/

/-- The adversarial verifier that is handed typed proofs and reads them through pr. -/
def prAdv : AdvVerifier lam X B → AdvVerifier lam X Pf
  | .halt => .halt
  | .query q k => .query q fun r => prAdv (k r)
  | .sample n k => .sample n fun r => prAdv (k r)
  | .request k => .request fun x π => prAdv (k x (pr π))

theorem prAdv_bound :
    ∀ (a : AdvVerifier lam X B) (t : ℕ), a.QueryBound t → (prAdv pr a).QueryBound t
  | .halt, _, _ => trivial
  | .query _ _, 0, h => h.elim
  | .query _ k, t + 1, h => fun r => prAdv_bound (k r) t (h r)
  | .sample _ k, t, h => fun r => prAdv_bound (k r) t (h r)
  | .request k, t, h => fun x π => prAdv_bound (k x (pr π)) t (h x (pr π))

/-- A view with its proofs put through pr. -/
def prView (v : View lam IVK X Pf) : View lam IVK X B :=
  ⟨v.ivk, v.sessions.map fun s => (s.1, pr s.2), v.trace, v.coins⟩

theorem prView_snoc (v : View lam IVK X Pf) (x : X) (π : Pf) :
    ({ prView pr v with sessions := (prView pr v).sessions ++ [(x, pr π)] } : View lam IVK X B) =
      prView pr { v with sessions := v.sessions ++ [(x, π)] } := by
  simp [prView]

theorem prRealLoop (A : Arg lam I X W IVK ISK Pf) (Z : ViewEnv lam IVK X W B) (isk : ISK) :
    ∀ (a : AdvVerifier lam X B) (n : ℕ) (v : View lam IVK X Pf),
      realLoop (prArg pr V' A) Z isk a n (prView pr v) =
        (realLoop A (fun v => Z (prView pr v)) isk (prAdv pr a) n v).mapO (prView pr)
  | .halt, _, _ => rfl
  | .query q k, n, v => by
      show OComp.query q (fun r =>
          realLoop (prArg pr V' A) Z isk (k r) n
            (prView pr { v with trace := v.trace ++ [(q, r)] })) =
        OComp.query q fun r =>
          (realLoop A (fun v => Z (prView pr v)) isk (prAdv pr (k r)) n
              { v with trace := v.trace ++ [(q, r)] }).mapO (prView pr)
      exact congrArg _ (funext fun r => prRealLoop A Z isk (k r) n _)
  | .sample m k, n, v => by
      show OComp.sample m (fun r =>
          realLoop (prArg pr V' A) Z isk (k r) n
            (prView pr { v with coins := v.coins ++ [r.val] })) =
        OComp.sample m fun r =>
          (realLoop A (fun v => Z (prView pr v)) isk (prAdv pr (k r)) n
              { v with coins := v.coins ++ [r.val] }).mapO (prView pr)
      exact congrArg _ (funext fun r => prRealLoop A Z isk (k r) n _)
  | .request _, 0, _ => rfl
  | .request k, n + 1, v => by
      simp only [realLoop, prAdv]
      cases Z (prView pr v) with
      | none => rfl
      | some xw =>
          show ((A.P isk xw.1 xw.2).mapO pr).bind (fun b =>
              realLoop (prArg pr V' A) Z isk (k xw.1 b) n
                { prView pr v with sessions := (prView pr v).sessions ++ [(xw.1, b)] }) =
            ((A.P isk xw.1 xw.2).bind fun π =>
                realLoop A (fun v => Z (prView pr v)) isk (prAdv pr (k xw.1 (pr π))) n
                  { v with sessions := v.sessions ++ [(xw.1, π)] }).mapO (prView pr)
          rw [OComp.mapO_bind, OComp.bind_mapO]
          refine congrArg _ (funext fun π => ?_)
          rw [prView_snoc]
          exact prRealLoop A Z isk (k xw.1 (pr π)) n _

theorem prRealExp (A : Arg lam I X W IVK ISK Pf) (Vt : IVK → AdvVerifier lam X B)
    (Z : ViewEnv lam IVK X W B) (i : I) (N : ℕ) :
    realExp (prArg pr V' A) Vt Z i N =
      (realExp A (fun ivk => prAdv pr (Vt ivk)) (fun v => Z (prView pr v)) i N).mapO
        (prView pr) := by
  show (A.C i).bind (fun key => realLoop (prArg pr V' A) Z key.2 (Vt key.1) N ⟨key.1, [], [], []⟩) =
    ((A.C i).bind fun key =>
        realLoop A (fun v => Z (prView pr v)) key.2 (prAdv pr (Vt key.1))
          N ⟨key.1, [], [], []⟩).mapO (prView pr)
  rw [OComp.bind_mapO]
  exact congrArg _ (funext fun key => prRealLoop pr V' A Z key.2 (Vt key.1) N ⟨key.1, [], [], []⟩)

theorem prIdealLoop (S : Simulator lam PP IVK X Pf) (Z : ViewEnv lam IVK X W B) :
    ∀ (a : AdvVerifier lam X B) (n : ℕ) (v : View lam IVK X Pf) (s : S.St),
      idealLoop (prSim pr S) Z a n (prView pr v) s =
        (idealLoop S (fun v => Z (prView pr v)) (prAdv pr a) n v s).map (prView pr)
  | .halt, _, _, _ => (PMF.pure_map _ _).symm
  | .query q k, n, v, s => by
      simp only [idealLoop, prAdv, PMF.map_bind]
      exact congrArg _
        (funext fun out =>
          prIdealLoop S Z (k out.1) n { v with trace := v.trace ++ [(q, out.1)] } out.2)
  | .sample m k, n, v, s => by
      simp only [idealLoop, prAdv, PMF.map_bind]
      exact congrArg _
        (funext fun r => prIdealLoop S Z (k r) n { v with coins := v.coins ++ [r.val] } s)
  | .request _, 0, _, _ => (PMF.pure_map _ _).symm
  | .request k, n + 1, v, s => by
      simp only [idealLoop, prAdv]
      cases Z (prView pr v) with
      | none => exact (PMF.pure_map _ _).symm
      | some xw =>
          show ((S.prove s xw.1).map fun o => (pr o.1, o.2)).bind (fun out =>
              idealLoop (prSim pr S) Z (k xw.1 out.1) n
                { prView pr v with sessions := (prView pr v).sessions ++ [(xw.1, out.1)] } out.2) =
            ((S.prove s xw.1).bind fun out =>
                idealLoop S (fun v => Z (prView pr v)) (prAdv pr (k xw.1 (pr out.1))) n
                  { v with sessions := v.sessions ++ [(xw.1, out.1)] } out.2).map (prView pr)
          rw [PMF.bind_map, PMF.map_bind]
          refine congrArg _ (funext fun out => ?_)
          show idealLoop (prSim pr S) Z (k xw.1 (pr out.1)) n
              { prView pr v with sessions := (prView pr v).sessions ++ [(xw.1, pr out.1)] } out.2 =
            _
          rw [prView_snoc]
          exact prIdealLoop S Z (k xw.1 (pr out.1)) n _ out.2

theorem prIdealExp (R : IndexedRelation I X W PP) (S : Simulator lam PP IVK X Pf)
    (Vt : IVK → AdvVerifier lam X B) (Z : ViewEnv lam IVK X W B) (i : I) (N : ℕ) :
    idealExp R (prSim pr S) Vt Z i N =
      (idealExp R S (fun ivk => prAdv pr (Vt ivk)) (fun v => Z (prView pr v)) i N).map
        (prView pr) := by
  show (S.init (R.pp i) N).bind
      (fun out => idealLoop (prSim pr S) Z (Vt out.1) N ⟨out.1, [], [], []⟩ out.2) =
    ((S.init (R.pp i) N).bind fun out =>
        idealLoop S (fun v => Z (prView pr v)) (prAdv pr (Vt out.1)) N
          ⟨out.1, [], [], []⟩ out.2).map (prView pr)
  rw [PMF.map_bind]
  exact congrArg _ (funext fun out => prIdealLoop pr S Z (Vt out.1) N ⟨out.1, [], [], []⟩ out.2)

end

theorem pr_privacy : Spec.pr_privacy := by
  intro lam I X W PP IVK ISK Pf B pr V' R A S ζ h i Z hZ tV Vt N hV
  have b := h i (fun v => Z (prView pr v)) (fun _ x w e => hZ _ x w e) tV
    (fun ivk => prAdv pr (Vt ivk)) N fun ivk => prAdv_bound pr (Vt ivk) tV (hV ivk)
  simp only [prRealExp, prIdealExp, Pr_mapO, prob_map]
  exact ⟨le_trans (SD_preimage_le (prView pr) _ _) b.1, b.2⟩

theorem pr_wr : Spec.pr_wr := fun _ _ _ _ _ _ _ _ _ _ _ _ => ⟨rfl, rfl⟩

end Run
