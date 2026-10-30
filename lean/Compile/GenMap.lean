-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/GenMap.lean: completeness, index binding and index privacy (ZKCP/Gen.lean) transfer along a
map on proofs (index binding: if the map has a section). Generic in the schemes.

Two schemes A = (C, P, V) and A' = (C', P', V') over the same family of oracles, with the same
indices, instances, witnesses and verification keys, but with other types of proving keys and of
proofs, are in the relation `Via A A' φ τ` if C is C' followed by the map φ on the proving key; P'
is P on the key φ k, followed by the map τ on each proof; V on a proof π is V' on τ π. These are
equalities of programs. Then, with the same relation and the same bounds:

  `completeness`   Completeness transfers from A to A' (and back: the two experiments are one
                   program, `completenessExp_via`).
  `binding`        Index binding transfers from A to A', if τ has a section σ; the extractor is
                   `pullE σ E`.
  `privacyWith`, `privacy`
                   Index privacy transfers from A to A': the simulator of A' is that of A followed
                   by τ on each proof (`pushSim`).

`mapSlots_via`: for schemes that prove a batch request by request (`Compile.mapSlots`) the clause on
P follows from the same for one request.

Limits: no statement on a concrete scheme. This file has no counterpart. The plan follows
ZKCP/SameRun.lean, which compares schemes with the same types through their output distributions.
-/
import Compile.Spec
import Rom.OverOneN
import Rom.Prefix

noncomputable section

namespace Compile.GenMap
open ZKCP.Gen Rom Prob
open scoped ENNReal

variable {S : OSpec} {I X W PP IVK ISK ISK' Pf Pf' : Type}

/-- the map on each proof of a batch -/
def mapS (τ : Pf → Pf') {β : Type} {b : List β} (l : Slots Pf b) : Slots Pf' b :=
  ⟨l.val.map τ, (List.length_map τ).trans l.property⟩

/-- the map on the proof of a pair (instance, proof) -/
abbrev on2 (τ : Pf → Pf') : X × Pf → X × Pf' := Prod.map id τ

/-- A is A' up to a map on proving keys and a map on proofs: equalities of programs. -/
structure Via (A : Arg S I X W IVK ISK Pf) (A' : Arg S I X W IVK ISK' Pf')
    (φ : ISK' → ISK) (τ : Pf → Pf') : Prop where
  C : ∀ i, A.C i = (A'.C i).bind fun o => .pure (o.1, φ o.2)
  P : ∀ k b, A'.P k b = (A.P (φ k) b).bind fun l => .pure (mapS τ l)
  V : ∀ v x π, A.V v x π = A'.V v x (τ π)

/-- a batch that is proved request by request -/
theorem mapSlots_via {β : Type} {g : β → OComp S Pf} {g' : β → OComp S Pf'} {τ : Pf → Pf'}
    (h : ∀ a, g' a = (g a).bind fun π => .pure (τ π)) :
    ∀ b : List β, mapSlots g' b = (mapSlots g b).bind fun l => .pure (mapS τ l)
  | [] => rfl
  | a :: t => by
      simp only [mapSlots, h a, mapSlots_via h t, OComp.bind_assoc]
      rfl

variable {A : Arg S I X W IVK ISK Pf}
  {A' : Arg S I X W IVK ISK' Pf'} {φ : ISK' → ISK} {τ : Pf → Pf'}

/-! ## Completeness -/

theorem verifyAll_via (h : Via A A' φ τ) (v : IVK) :
    ∀ l : List (X × Pf), verifyAll A v l = verifyAll A' v (l.map (on2 τ))
  | [] => rfl
  | (x, π) :: t => by
      show (A.V v x π).bind (fun c => (verifyAll A v t).bind fun cs => .pure (c && cs)) =
        (A'.V v x (τ π)).bind fun c =>
          (verifyAll A' v (t.map (on2 τ))).bind fun cs => .pure (c && cs)
      rw [h.V, verifyAll_via h v t]

theorem sessionExp_via (h : Via A A' φ τ) (v : IVK) (k : ISK') (b : List (X × W)) :
    sessionExp A' v k b = sessionExp A v (φ k) b := by
  show (A'.P k b).bind (fun πs => verifyAll A' v ((b.map Prod.fst).zip πs.val)) =
    (A.P (φ k) b).bind fun πs => verifyAll A v ((b.map Prod.fst).zip πs.val)
  rw [h.P, OComp.bind_assoc]
  refine congrArg _ (funext fun l => ?_)
  show verifyAll A' v ((b.map Prod.fst).zip (l.val.map τ)) = _
  rw [verifyAll_via h, List.zip_map_right]

/-- Under `Via`, the two experiments of completeness are one program. -/
theorem completenessExp_via (h : Via A A' φ τ) (i : I) (b : List (X × W)) :
    completenessExp A i b = completenessExp A' i b := by
  show (A.C i).bind (fun o => sessionExp A o.1 o.2 b) =
    (A'.C i).bind fun o => sessionExp A' o.1 o.2 b
  rw [h.C, OComp.bind_assoc]
  refine congrArg _ (funext fun o => ?_)
  exact (sessionExp_via h o.1 o.2 b).symm

theorem completeness (h : Via A A' φ τ) (R : RelPair I X W PP) {B : ℕ}
    {α : ℝ≥0∞} (hc : HasCompletenessError R A B α) : HasCompletenessError R A' B α :=
  fun i b hb => by
    rw [← completenessExp_via h]
    exact hc i b hb

/-! ## Index binding -/

/-- the extractor of A' applies the section to a proof; E_i is the same function -/
def pullE (σ : Pf' → Pf) (E : Extractor S I X W IVK Pf) : Extractor S I X W IVK Pf' where
  Ei := E.Ei
  Ew := fun v tr x π tr' => E.Ew v tr x (σ π) tr'

/-- Under `Via`, for a section σ of τ: the experiment of index binding against A' is the experiment
against A, the adversarial prover followed by the section. -/
theorem bindingExp_via (h : Via A A' φ τ) {σ : Pf' → Pf}
    (hσ : ∀ π, τ (σ π) = π) (E : Extractor S I X W IVK Pf) {St : Type}
    (Ct : OComp S (IVK × St)) (Pt : St → OComp S (X × Pf')) :
    bindingExp A E Ct (fun st => (Pt st).bind fun o => .pure (o.1, σ o.2)) =
      bindingExp A' (pullE σ E) Ct Pt := by
  show Ct.withTrace.bind (fun a => (((Pt a.1.2).bind fun o => OComp.pure (o.1, σ o.2)).withTrace).bind fun b =>
      (A.V a.1.1 b.1.1 b.1.2).bind fun c =>
        .pure (⟨c, E.Ei a.1.1 a.2, b.1.1, E.Ew a.1.1 a.2 b.1.1 b.1.2 b.2⟩ : BindingOutcome I X W)) =
    Ct.withTrace.bind fun a => (Pt a.1.2).withTrace.bind fun b =>
      (A'.V a.1.1 b.1.1 b.1.2).bind fun c =>
        .pure
          (⟨c, E.Ei a.1.1 a.2, b.1.1, E.Ew a.1.1 a.2 b.1.1 (σ b.1.2) b.2⟩ : BindingOutcome I X W)
  refine congrArg _ (funext fun a => ?_)
  rw [withTrace_bind, OComp.bind_assoc]
  refine congrArg _ (funext fun b => ?_)
  show (A.V a.1.1 b.1.1 (σ b.1.2)).bind (fun c =>
      .pure (⟨c, E.Ei a.1.1 a.2, b.1.1,
          E.Ew a.1.1 a.2 b.1.1 (σ b.1.2) (b.2 ++ [])⟩ : BindingOutcome I X W)) = _
  rw [h.V, hσ, List.append_nil]

theorem binding (h : Via A A' φ τ) {σ : Pf' → Pf} (hσ : ∀ π, τ (σ π) = π) (R : RelPair I X W PP)
    {E : Extractor S I X W IVK Pf} {ε : ℕ → ℕ → ℝ≥0∞} (hb : HasIndexBindingWith R A E ε) :
    HasIndexBindingWith R A' (pullE σ E) ε :=
  fun tC tP St Ct Pt hC hP => by
    rw [← bindingExp_via h hσ]
    exact hb tC tP St Ct _ hC fun st =>
      ((hP st).bind (g := fun o => OComp.pure (o.1, σ o.2)) (t := 0) fun _ => trivial).mono
        (Nat.add_zero _).le

/-! ## Index privacy -/

/-- an adversarial verifier against A', as one against A: it applies τ to its proofs -/
def pullV (τ : Pf → Pf') : AdvVerifier S X Pf' → AdvVerifier S X Pf
  | .halt => .halt
  | .query o q k => .query o q fun r => pullV τ (k r)
  | .sample n k => .sample n fun r => pullV τ (k r)
  | .request k => .request fun l => pullV τ (k (l.map (on2 τ)))

theorem pullV_queryBound (τ : Pf → Pf') (V : AdvVerifier S X Pf') :
    ∀ t, V.QueryBound t → (pullV τ V).QueryBound t := by
  induction V with
  | halt => exact fun _ _ => trivial
  | query o q k ih =>
    intro t h
    cases t with
    | zero => exact h
    | succ t => exact fun r => ih r t (h r)
  | sample n k ih => exact fun t h r => ih r t (h r)
  | request k ih => exact fun t h l => ih _ t (h _)

/-- a view against A, mapped by τ -/
def mapView (τ : Pf → Pf') (v : View S IVK X Pf) : View S IVK X Pf' :=
  ⟨v.ivk, v.sessions.map (List.map (on2 τ)), v.trace, v.coins⟩

/-- the simulator of A, followed by τ on each proof -/
def pushSim (τ : Pf → Pf') (Sim : Simulator S PP IVK X Pf) : Simulator S PP IVK X Pf' where
  St := Sim.St
  init := Sim.init
  answer := Sim.answer
  prove := fun s xs => (Sim.prove s xs).map fun o => (mapS τ o.1, o.2)

theorem released_map (τ : Pf → Pf') (b : Batch X W) (πs : List Pf) :
    b.released (πs.map τ) = (b.released πs).map (on2 τ) := by
  unfold Batch.released
  rw [List.zip_map_right, List.filter_map, List.map_map, List.map_map]
  rfl

theorem mapView_session (τ : Pf → Pf') (v : View S IVK X Pf) (r : List (X × Pf)) :
    mapView τ { v with sessions := v.sessions ++ [r] } =
      { mapView τ v with sessions := (mapView τ v).sessions ++ [r.map (on2 τ)] } := by
  simp only [mapView, List.map_append, List.map_cons, List.map_nil]

theorem realLoop_via (h : Via A A' φ τ) (Z' : ViewEnv S IVK X W Pf')
    (k : ISK') (V : AdvVerifier S X Pf') :
    ∀ (n : ℕ) (v : View S IVK X Pf), realLoop A' Z' k V n (mapView τ v) =
      (realLoop A (fun u => Z' (mapView τ u)) (φ k) (pullV τ V) n v).bind fun u =>
        .pure (mapView τ u) := by
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
      cases hz : Z' (mapView τ v) with
      | none => rfl
      | some b =>
        simp only []
        rw [h.P, OComp.bind_assoc, OComp.bind_assoc]
        refine congrArg _ (funext fun l => ?_)
        show realLoop A' Z' k (K (b.released (l.val.map τ))) n
            { mapView τ v with sessions := (mapView τ v).sessions ++ [b.released (l.val.map τ)] } =
          _
        rw [released_map, ← mapView_session]
        exact ih _ n _

theorem realExp_via (h : Via A A' φ τ) (Vt : IVK → AdvVerifier S X Pf')
    (Z' : ViewEnv S IVK X W Pf') (i : I) (N : ℕ) :
    realExp A' Vt Z' i N =
      (realExp A (fun v => pullV τ (Vt v)) (fun u => Z' (mapView τ u)) i N).bind
        fun u => .pure (mapView τ u) := by
  show (A'.C i).bind (fun o => realLoop A' Z' o.2 (Vt o.1) N ⟨o.1, [], [], []⟩) =
    ((A.C i).bind fun o =>
        realLoop A (fun u => Z' (mapView τ u)) o.2 (pullV τ (Vt o.1)) N ⟨o.1, [], [], []⟩).bind
      fun u => .pure (mapView τ u)
  rw [h.C, OComp.bind_assoc, OComp.bind_assoc]
  refine congrArg _ (funext fun o => ?_)
  exact realLoop_via h Z' o.2 (Vt o.1) N ⟨o.1, [], [], []⟩

theorem idealLoop_via (τ : Pf → Pf') (Sim : Simulator S PP IVK X Pf)
    (Z' : ViewEnv S IVK X W Pf') (V : AdvVerifier S X Pf') :
    ∀ (n : ℕ) (v : View S IVK X Pf) (s : Sim.St), idealLoop (pushSim τ Sim) Z' V n (mapView τ v) s =
      (idealLoop Sim (fun u => Z' (mapView τ u)) (pullV τ V) n v s).map (mapView τ) := by
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
      cases hz : Z' (mapView τ v) with
      | none => exact (PMF.pure_map _ _).symm
      | some b =>
        simp only []
        show ((Sim.prove s b.ownX).map fun o => (mapS τ o.1, o.2)).bind _ = _
        rw [PMF.bind_map, PMF.map_bind]
        refine congrArg _ (funext fun out => ?_)
        show idealLoop (pushSim τ Sim) Z' (K (b.ownX.zip (out.1.val.map τ))) n
            { mapView τ v with
              sessions := (mapView τ v).sessions ++ [b.ownX.zip (out.1.val.map τ)] } out.2 = _
        rw [List.zip_map_right, ← mapView_session]
        exact ih _ n _ out.2

theorem idealExp_via (τ : Pf → Pf') (R : RelPair I X W PP) (Sim : Simulator S PP IVK X Pf)
    (Vt : IVK → AdvVerifier S X Pf') (Z' : ViewEnv S IVK X W Pf') (i : I) (N : ℕ) :
    idealExp R (pushSim τ Sim) Vt Z' i N =
      (idealExp R Sim (fun v => pullV τ (Vt v)) (fun u => Z' (mapView τ u)) i N).map
        (mapView τ) := by
  unfold idealExp
  rw [PMF.map_bind]
  refine congrArg _ (funext fun out => ?_)
  exact idealLoop_via τ Sim Z' (Vt out.1) N ⟨out.1, [], [], []⟩ out.2

/-- Under `Via`, index privacy transfers from A to A', with the simulator of A followed
by τ. -/
theorem privacyWith (h : Via A A' φ τ) (R : RelPair I X W PP) {B : ℕ}
    {Sim : Simulator S PP IVK X Pf} {ζ : ℕ → ℕ → ℝ≥0∞} (hp : HasIndexPrivacyWith R A B Sim ζ) :
    HasIndexPrivacyWith R A' B (pushSim τ Sim) ζ := by
  intro i Z' hZ tV Vt N hV
  obtain ⟨h1, h2⟩ := hp i (fun u => Z' (mapView τ u)) (fun v b hb => hZ _ b hb) tV
    (fun v => pullV τ (Vt v)) N fun v => pullV_queryBound τ _ _ (hV v)
  constructor
  · refine le_trans (le_of_eq ?_) (le_trans (sd_comap_le _ _ (mapView τ)) h1)
    congr 1
    · funext T
      rw [realExp_via h, Pr_bind_pure]
    · funext T
      rw [idealExp_via, pr_map]
  · rw [idealExp_via, pr_map]
    exact h2

theorem privacy (h : Via A A' φ τ) (R : RelPair I X W PP) {B : ℕ}
    {ζ : ℕ → ℕ → ℝ≥0∞} (hp : HasIndexPrivacy R A B ζ) : HasIndexPrivacy R A' B ζ :=
  let ⟨Sim, hs⟩ := hp
  ⟨pushSim τ Sim, privacyWith h R hs⟩

end Compile.GenMap
