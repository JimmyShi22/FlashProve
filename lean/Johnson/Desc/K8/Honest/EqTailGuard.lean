-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/EqTailGuard.lean: THE SMALLNESS TEST: WHAT A YES OF THE RUN "K8.equations"
HAS TESTED OF EACH TABLE THAT IT READS: THE WHOLE OF ITS GUARD "shape-functional": the table's
length is not 0, divides its matrix's number of rows, and the table has a weight a place. The
library's law on the run's tail (`eqTail_total`, Johnson/Desc/First/TailClaims/EquationsTotal.lean)
hands on the last third alone, and at the tables that have a segment. SO `ReadsPub`
(Johnson/Desc/K8/Honest/ReadShape.lean) IS NO PREMISE OF ITS OWN BEHIND A YES OF THE RUN. None of
the library's goals.

  `TabGuard tl Fn`   the guard's three clauses at the table Fn
  `runFoldE_mem`   each member of a walked list has had its step. The library's `runFoldE_all`
                   (Johnson/Desc/First/TailClaims/EquationsRuns.lean) is the like for a step of the
                   form "P a ∧ …" with P free of the states
  **`eqTail_guard`**   a yes of the run's tail ⊢ TabGuard at each table on a matrix of the list in
                   the first or the third vector, at the data behind the run's weights
  **`eq_guard`**   the same from a yes of the whole run, at the data in front
  `Added8.readsPub`   Added8 ⊢ ReadsPub tl
  **`Added8.readShape_run`**   `Added8.readShape` without that premise
THE PROOF OF `eqTail_guard` WALKS THE RUN's TEXT AS THE PROOF OF `eqTail_total` DOES, line for line
in its first half and in the tables' loop, with another sentence at each table; the tools are the
library's (`forInE_inv`, `forInE_inv_array`, `RunFoldE`,
Johnson/Desc/First/TailClaims/EquationsRuns.lean).
Limits. From a yes alone: nothing says that the run says yes. `Added8.readShape_run` keeps the four
other premises of `Added8.readShape`, paid by nobody here.
Nothing is claimed on completeness, soundness or hiding.

-/
import Johnson.Desc.K8.Honest.ReadShape

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open VerifiableInference.Desc VerifiableInference.Desc.First.TailClaims
open VerifiableInference.Desc.First.TailClaims.Law
open OnBytes.Tie.Pv.Tail.Port

/-- The guard's three clauses at a table. -/
def TabGuard (tl : HTailF2) (Fn : HFun) : Prop :=
  Fn.len ≠ 0 ∧ (tl.mats.getD Fn.mat {}).m % Fn.len = 0 ∧ Fn.phi.size = Fn.len

/-- Each member of a walked list has had its step. -/
theorem runFoldE_mem {α β : Type} (step : α → β → St → β → St → Prop) :
    ∀ (l : List α) (b : β) (s : St) (b' : β) (s' : St), RunFoldE step l b s b' s' →
      ∀ a ∈ l, ∃ b0 s0 b1 s1, step a b0 s0 b1 s1
  | [], _, _, _, _, _ => fun _ ha => absurd ha List.not_mem_nil
  | x :: l, b, s, _, _, h => by
    obtain ⟨b1, s1, hs, hr⟩ := h
    intro a ha
    rcases List.mem_cons.1 ha with rfl | ha
    · exact ⟨b, s, b1, s1, hs⟩
    · exact runFoldE_mem step l _ _ _ _ hr a ha

/-- **A YES OF THE RUN's TAIL HAS TESTED THE WHOLE GUARD AT EACH TABLE THAT IT READS.** -/
theorem eqTail_guard (before : Nat) (tlb tl' : HTailF2) (funs : Array HFun)
    (front : Nat) (s s' : St) (h : eqTail before tlb funs front s = .ok (tl', s')) :
    ∃ tl1, eqWeights tlb front s = .ok (tl1, s) ∧
      ∀ Fn ∈ funs.toList, Fn.mat < tl1.NM → (Fn.tree = 0 ∨ Fn.tree = 2) → TabGuard tl1 Fn := by
  unfold eqTail at h
  obtain ⟨n0, t0, h0, k0⟩ := (eq_bind_ok _ _ _ _ _).1 h
  obtain ⟨en0, et0⟩ := eq_claims_ok h0
  rw [en0, et0] at k0
  obtain ⟨u1, t1, h1, k1⟩ := (eq_bind_ok _ _ _ _ _).1 k0
  obtain ⟨-, et1⟩ := eq_must_ok h1
  rw [et1] at k1
  obtain ⟨tl1, t2, hW, k2⟩ := (eq_bind_ok _ _ _ _ _).1 k1
  have eW : t2 = s := by
    unfold eqWeights at hW
    obtain ⟨x3, t3, g1, g2⟩ := (eq_bind_ok _ _ _ _ _).1 hW
    rw [(eq_ask_ok g1).2] at g2
    exact (eq_get_ok g2).2
  rw [eW] at hW k2
  obtain ⟨sz, t3, h3, k3⟩ := (eq_bind_ok _ _ _ _ _).1 k2
  rw [(eq_ask_ok h3).2] at k3
  obtain ⟨bT, sT, -, k4⟩ := (eq_bind_ok _ _ _ _ _).1 k3
  obtain ⟨bR, sR, hR, -⟩ := (eq_bind_ok _ _ _ _ _).1 k4
  have rR := forInE_inv front _
    (fun mu => RunFoldE (fun un => RunFoldE (fun (Fn : HFun)
      (_ : MProd Nat (Array (Array Bool))) (_ : St) (_ : MProd Nat (Array (Array Bool)))
      (_ : St) => (Fn.mat == mu && Fn.tree == un) = true →
        Fn.len ≠ 0 ∧ (tl1.mats.getD mu {}).m % Fn.len = 0 ∧ Fn.phi.size = Fn.len)
      funs.toList) [0, 2])
    (by
      intro mu b s r s1 hb
      obtain ⟨b2, x1, c1, d1⟩ := (eq_bind_ok _ _ _ _ _).1 hb
      obtain ⟨u', x2, c2, d2⟩ := (eq_bind_ok _ _ _ _ _).1 d1
      rw [((eq_pure_ok _ _ _ _ _).1 c2).2] at d2
      obtain ⟨er, ex⟩ := (eq_pure_ok _ _ _ _ _).1 d2
      rw [ex]
      refine ⟨_, er, ?_⟩
      refine forInE_inv front _ _ ?_ _ _ _ _ _ c1
      intro un b s r s1 hb
      obtain ⟨b3, y1, c3, d3⟩ := (eq_bind_ok _ _ _ _ _).1 hb
      obtain ⟨u'', y2, c4, d4⟩ := (eq_bind_ok _ _ _ _ _).1 d3
      rw [((eq_pure_ok _ _ _ _ _).1 c4).2] at d4
      obtain ⟨er', ex'⟩ := (eq_pure_ok _ _ _ _ _).1 d4
      rw [ex']
      refine ⟨_, er', ?_⟩
      refine forInE_inv_array front _ _ ?_ _ _ _ _ _ c3
      intro Fn b s r s1 hb
      by_cases hc : (Fn.mat == mu && Fn.tree == un) = true
      · rw [if_pos hc] at hb
        obtain ⟨v1, z1, e1, f1⟩ := (eq_bind_ok _ _ _ _ _).1 hb
        rw [(eq_must_ok e1).2] at f1
        obtain ⟨v2, z2, e2, f2⟩ := (eq_bind_ok _ _ _ _ _).1 f1
        obtain ⟨hsf, ez2⟩ := eq_must_ok e2
        rw [ez2] at f2
        obtain ⟨b4', z3, e3, f3⟩ := (eq_bind_ok _ _ _ _ _).1 f2
        obtain ⟨v4, z4, e4, f4⟩ := (eq_bind_ok _ _ _ _ _).1 f3
        rw [((eq_pure_ok _ _ _ _ _).1 e4).2] at f4
        obtain ⟨er2, -⟩ := (eq_pure_ok _ _ _ _ _).1 f4
        simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne] at hsf
        exact ⟨_, er2, fun _ => ⟨hsf.1.1, hsf.1.2, hsf.2⟩⟩
      · rw [if_neg hc] at hb
        obtain ⟨v1, z1, e1, f1⟩ := (eq_bind_ok _ _ _ _ _).1 hb
        rw [((eq_pure_ok _ _ _ _ _).1 e1).2] at f1
        obtain ⟨er2, -⟩ := (eq_pure_ok _ _ _ _ _).1 f1
        exact ⟨_, er2, fun hh => absurd hh hc⟩) _ _ _ _ _ hR
  refine ⟨tl1, hW, fun Fn hFn hm ht => ?_⟩
  obtain ⟨_, _, _, _, r1⟩ := runFoldE_mem _ _ _ _ _ _ rR Fn.mat (List.mem_range.2 hm)
  obtain ⟨_, _, _, _, r2⟩ := runFoldE_mem _ _ _ _ _ _ r1 Fn.tree (by
    rcases ht with e | e <;> simp [e])
  obtain ⟨_, _, _, _, r3⟩ := runFoldE_mem _ _ _ _ _ _ r2 Fn hFn
  exact r3 (by simp)

/-- **The same from a yes of the whole run, at the data in front.** -/
theorem eq_guard {front : Nat} {tl tl' : HTailF2} {funs : Array HFun} {F F1 : Fork}
    {cls : List Claim} (h : equations front tl funs F = .ok (tl', F1, cls)) :
    ∀ Fn ∈ funs.toList, Fn.mat < tl.NM → (Fn.tree = 0 ∨ Fn.tree = 2) → TabGuard tl Fn := by
  obtain ⟨before, tla, tlb, s1, s2, arr, -, -, k9, -⟩ := eq_parts h
  obtain ⟨tl1, hW, hG⟩ := eqTail_guard before tlb tl' funs _ s2 _ k9
  obtain ⟨tl2, hW2, -, -, etl, -, -⟩ :=
    eqTail_total Reading.gl allZero F before tlb tl' funs _ s2 _ k9
  obtain rfl : tl1 = tl2 := congrArg Prod.fst (Except.ok.inj (hW.symm.trans hW2))
  have eN : tl1.NM = tl.NM :=
    (congrArg (·.NM) etl).symm.trans (eq_same (·.NM) h (fun _ _ => rfl) (fun _ _ => rfl)
      (fun _ _ => rfl) (fun _ _ _ _ => rfl))
  have eM : tl1.mats = tl.mats :=
    (congrArg (·.mats) etl).symm.trans (eq_same (·.mats) h (fun _ _ => rfl) (fun _ _ => rfl)
      (fun _ _ => rfl) (fun _ _ _ _ => rfl))
  intro Fn hFn hm ht
  have g := hG Fn hFn (by rw [eN]; exact hm) ht
  unfold TabGuard at g ⊢
  rw [eM] at g
  exact g

section
variable {tl tl' : HTailF2} {funs : Array HFun} {Y G F₁ F₂ : Fork} {fr k8 bk : List Claim}
  {n₀ : Nat}

/-- Behind a yes of the run the premise on the tables is no premise of its own. -/
theorem Added8.readsPub (A : Added8 tl tl' funs Y G F₁ F₂ fr k8 bk n₀) : ReadsPub tl := by
  intro Fn hFn hm ht
  have g := eq_guard A.eq Fn (by rw [eq_funs A.eq]; exact hFn) hm ht
  exact ⟨g.1, g.2.1⟩

/-- **THE TEST ON THE READS' SHAPES SAYS YES BEHIND THE ADDING, WITHOUT THE PREMISE ON THE
TABLES.** -/
theorem Added8.readShape_run (A : Added8 tl tl' funs Y G F₁ F₂ fr k8 bk n₀) (g : Forest.Heard)
    (nbW : Nat) (hn : nbW = tl.zzBlocks) (C : ColsFacts tl)
    (hsz : ((Y.trees.getD tl.ix.ZZ {}).rows.getD tl.zzRowReads {}).L.size = 2 * tl.mz) :
    tl'.readShapeHeld
      (((coefBody tl' g G).trees.getD tl'.ix.ZZ {}).rows.getD (2 * nbW) {}).L = true :=
  A.readShape g nbW hn C A.readsPub hsz

end

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.runFoldE_mem
#print axioms VerifiableInference.Desc.First.K8.Honest.eqTail_guard
#print axioms VerifiableInference.Desc.First.K8.Honest.eq_guard
#print axioms VerifiableInference.Desc.First.K8.Honest.Added8.readsPub
#print axioms VerifiableInference.Desc.First.K8.Honest.Added8.readShape_run
