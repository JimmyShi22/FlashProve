-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/KeyLookup/PartsRows.lean: what the joint after k steps of the parts' chain says, written out
as rows with public targets and as one masked claim on each part's root.

Definitions, statements and proofs, on the chain of Cb/Pv/KeyLookup/Parts.lean. After the pattern of
Cb/Ld/LdLkpTieRows.lean. Only files of Cb/ and that file are imported.

Main names:
  D.be l o: the challenge β of the further variable of step l.
  D.rowsAt l s  the rows on the hiding coefficients of the steps below l (the latest first); l of
    them (rowsAt_length).
  D.bR l s j: (β, the value sent) of the masked claim on the root j, for j < l.
  D.Done l s m: the rows hold, and for j < l: root j + m (cAt j false) · β_j = the value sent.
  D.formAt k x i, D.tgtAt k x i: form and target of the claim on part i after k steps. For i < k:
    β_i
    at the place cAt i false, 0 elsewhere; the value sent. For i ≥ k: the form and the target of the
    joint's own open claim.
  D.Claims x m: at k = n, for every part i ≤ n: root i + (formAt n x i on m) = tgtAt n x i.
  partsR_ride: D.ride, field by field: A0 at the first state, and D.Done.
  partsR_cj: entered beside a joint of the form cj (Cb/Ld/LdLkpKit.lean), the joint before step l is
    of that form.
  formAt_zero, formAt_open: the open claim's form written out: before any step the form that came
    in; after k + 1 steps β of step k at the place cAt k true, 0 elsewhere.
  partsR_out: Done n and claim n hold if and only if the rows hold and Claims holds.
  partsR_end: the joint after the n steps, in the form cj: what rode along, the rows, one claim a
    part.
  rootP, rootP_inc, rootP_holds: form and target of the claim on part i have the types that RootP
    (Cb/Ld/LdLkpRoot.lean) takes, for a forest of one tree over the state after the steps: R.IncOK
    holds, and R.Holds is the claim if level 0 of the letter U is the root i (the premise hU).

Limits: no premise but hU in rootP_holds, which is discharged at no U here; nothing calls rootP. It
shows that the types fit and no more: the block of RootP costs a round with one value, which the
lookup with parts does not have. Nothing on soundness is proved in this file.

-/
import Cb.Pv.KeyLookup.Parts
import Cb.Ld.LdLkpRoot

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lk6
open Iop IOR Hiop Prob Cb Cb.LdLkp

noncomputable section
variable {E : Type} [Field E] [Fintype E]

namespace PartsP
variable (D : PartsP E)

theorem emB (l : ℕ) : IsEmpty (D.lv l).T.par.B := by
  cases l with
  | zero => exact inferInstanceAs (IsEmpty Empty)
  | succ l => exact inferInstanceAs (IsEmpty Empty)

/-- The challenge β of the dummy variable of step l. -/
def be (l : ℕ) (o : (D.lv l).T.par.Out) : E := (D.lv l).T.lst o.st ((D.lv l).T.par.hp o.st o.pt)

/-- The rows of the steps below l, the latest first. -/
def rowsAt : (l : ℕ) → (D.lv l).T.St → List (Row E D.J)
  | 0, _ => []
  | l + 1, o => rowUof (D.lv l).T (D.emB l) (D.lv l).toJ o :: rowsAt l o.st

/-- (β, target) of the masked claim on the root j. -/
def bR : (l : ℕ) → (D.lv l).T.St → ℕ → E × E
  | 0, _, _ => (0, 0)
  | l + 1, o, j => if j = l then (D.be l o, o.vals (D.lv l).pt) else bR l o.st j

/-- All that is done before step l. -/
def Done (l : ℕ) (s : (D.lv l).T.St) (m : D.J → E) : Prop :=
  RowsHold (D.rowsAt l s) m ∧
  ∀ j < l, D.root ((D.lv l).base s) m j + m (D.cAt j false) * (D.bR l s j).1 = (D.bR l s j).2

open Classical in
/-- The form of the claim on part i after k steps. -/
def formAt (k : ℕ) (x : E × (D.lv k).T.St) (i : ℕ) : D.J → E :=
  if i < k then fun j => if j = D.cAt i false then (D.bR k x.2 i).1 else 0
  else pushJ (D.lv k).toJ ((D.lv k).T.slS x.2)

/-- Its target. -/
def tgtAt (k : ℕ) (x : E × (D.lv k).T.St) (i : ℕ) : E := if i < k then (D.bR k x.2 i).2 else x.1

/-- After the n steps: one masked claim on each part's root. -/
def Claims (x : E × (D.lv D.n).T.St) (m : D.J → E) : Prop :=
  ∀ i ≤ D.n, D.root ((D.lv D.n).base x.2) m i + ∑ j, D.formAt D.n x i j * m j = D.tgtAt D.n x i

/-- The claim on part i as a value of the library's RootP: a forest of one tree over the state after
the steps. -/
def rootP (i : ℕ)
    (U : E × (D.lv D.n).T.St → (D.J → E) → (l : ℕ) → (Fin (0 + l) → Bool) → E)
    (wK : (l : ℕ) → PIdx (List.replicate (0 + l) (pfCube E 2) ++ [pDummy E 2]) → D.J)
    (cK : ℕ → Bool → D.J) : RootP E :=
  ⟨{ St0 := E × (D.lv D.n).T.St, J := D.J, g := 0, U := U, inc0 := fun x _ => D.formAt D.n x i,
     wAt := wK, cAt := cK },
    fun x _ => D.formAt D.n x i, fun x _ => D.tgtAt D.n x i⟩

end PartsP
end

section
variable {E : Type} [Field E] [Fintype E] (D : PartsP E)

theorem PartsP.rowsAt_length : ∀ (l : ℕ) (s : (D.lv l).T.St), (D.rowsAt l s).length = l
  | 0, _ => rfl
  | l + 1, o => congrArg Nat.succ (PartsP.rowsAt_length l o.st)

/-- Glue: the masked claim that rides along, written out. -/
theorem PartsP.eR : ∀ (l : ℕ) (o : (D.lv l).T.par.Out) (m : D.J → E),
    (D.lv l).T.par.EHolds o (fun i => m ((D.lv l).toJ i)) (D.lv l).pt ↔
    D.root ((D.lv l).base o.st) m l + m (D.cAt l false) * D.be l o = o.vals (D.lv l).pt
  | 0, _, _ => Iff.rfl
  | _ + 1, _, _ => Iff.rfl

/-- Glue: one more step done. -/
theorem PartsP.done_succ (l : ℕ) (o : (D.lv l).T.par.Out) (m : D.J → E) :
    D.Done (l + 1) o m ↔
    D.Done l o.st m ∧
    (D.lv l).T.par.UHolds o (fun j => m ((D.lv l).toJ j)) ∧
    (D.lv l).T.par.EHolds o (fun j => m ((D.lv l).toJ j)) (D.lv l).pt := by
  rw [D.eR l o m, ← ldLkpTieR_rowU E (D.lv l).T (D.emB l) D.J (D.lv l).toJ o m]
  constructor
  · rintro ⟨hr, ht⟩
    refine ⟨⟨fun r h => hr r (List.mem_cons_of_mem _ h), fun j hj => ?_⟩,
      hr _ List.mem_cons_self, ?_⟩
    · have := ht j (Nat.lt_succ_of_lt hj)
      have e : D.bR (l + 1) o j = D.bR l o.st j := if_neg (Nat.ne_of_lt hj)
      rw [e] at this
      exact this
    · have := ht l (Nat.lt_succ_self l)
      have e : D.bR (l + 1) o l = (D.be l o, o.vals (D.lv l).pt) := if_pos rfl
      rw [e] at this
      exact this
  · rintro ⟨⟨hr, ht⟩, hu, he⟩
    refine ⟨fun r h => ?_, fun j hj => ?_⟩
    · rcases List.mem_cons.mp h with rfl | h
      · exact hu
      · exact hr r h
    · by_cases hjl : j = l
      · subst hjl
        have e : D.bR (j + 1) o j = (D.be j o, o.vals (D.lv j).pt) := if_pos rfl
        rw [e]
        exact he
      · have e : D.bR (l + 1) o j = D.bR l o.st j := if_neg hjl
        rw [e]
        exact ht j (by omega)

theorem PartsP.done_zero (s : (D.lv 0).T.St) (m : D.J → E) : D.Done 0 s m :=
  ⟨fun _ h => absurd h List.not_mem_nil, fun j hj => absurd hj (Nat.not_lt_zero j)⟩

/-- What rides along, field by field. -/
theorem partsR_ride (Ex : ExtSpec) (M Wp Kc : Type) (msg : M → D.J → E)
    (A0 : Rels Kc D.St0 Ex (M × Wp)) (l : ℕ) :
    (∀ s y w, (D.ride msg A0 l).rel s y w ↔ A0.rel ((D.lv l).base s) y w ∧ D.Done l s (msg w.1)) ∧
    (∀ s y w,
      (D.ride msg A0 l).relR (s, y) w ↔ A0.relR ((D.lv l).base s, y) w ∧ D.Done l s (msg w.1)) ∧
    (∀ s y, (D.ride msg A0 l).on (s, y) ↔ A0.on ((D.lv l).base s, y)) ∧
    (D.ride msg A0 l).core = A0.core := by
  induction l with
  | zero =>
    exact ⟨fun s y w => ⟨fun h => ⟨h, D.done_zero s _⟩, fun h => h.1⟩,
      fun s y w => ⟨fun h => ⟨h, D.done_zero s _⟩, fun h => h.1⟩, fun _ _ => Iff.rfl, rfl⟩
  | succ l ih =>
    obtain ⟨h1, h2, h3, h4⟩ := ih
    refine ⟨fun s y w => ?_, fun s y w => ?_, fun s y => h3 s.st y, h4⟩
    · rw [D.done_succ l s (msg w.1), ← and_assoc]
      exact and_congr (h1 s.st y w) Iff.rfl
    · rw [D.done_succ l s (msg w.1), ← and_assoc]
      exact and_congr (h2 s.st y w) Iff.rfl

/-- Entered beside a joint of the form cj, the joint before step l is of that form. -/
theorem partsR_cj (Ex : ExtSpec) (Kc St M Wp : Type) (R0 : Rels Kc St Ex (M × Wp))
    (msg : M → D.J → E) (pr : D.St0 → St) (Φ ΦR : D.St0 → (D.J → E) → Prop) (l : ℕ) :
    D.jtAt msg (cj R0 msg pr Φ ΦR) l =
      cj R0 msg (fun x => pr ((D.lv l).base x.2))
        (fun x m => (Φ ((D.lv l).base x.2) m ∧ D.Done l x.2 m) ∧ D.claim l x m)
        (fun x m => (ΦR ((D.lv l).base x.2) m ∧ D.Done l x.2 m) ∧ D.claim l x m) := by
  obtain ⟨h1, h2, h3, h4⟩ := partsR_ride D Ex M Wp Kc msg (cj R0 msg pr Φ ΦR) l
  refine rels_ext (funext fun x => funext fun y => funext fun w => propext ?_)
    (funext fun a => funext fun w => propext ?_) (funext fun a => propext (h3 a.1.2 a.2)) h4
  · show (D.ride msg (cj R0 msg pr Φ ΦR) l).rel x.2 y w ∧ _ ↔ _
    rw [h1]
    exact ⟨fun h => ⟨h.1.1.1, ⟨h.1.1.2, h.1.2⟩, h.2⟩, fun h => ⟨⟨⟨h.1, h.2.1.1⟩, h.2.1.2⟩, h.2.2⟩⟩
  · show (D.ride msg (cj R0 msg pr Φ ΦR) l).relR (a.1.2, a.2) w ∧ _ ↔ _
    rw [h2]
    exact ⟨fun h => ⟨h.1.1.1, ⟨h.1.1.2, h.1.2⟩, h.2⟩, fun h => ⟨⟨⟨h.1, h.2.1.1⟩, h.2.1.2⟩, h.2.2⟩⟩

/-- The value of the form of a part that is split off. -/
theorem PartsP.form_lt (k : ℕ) (x : E × (D.lv k).T.St) (i : ℕ) (h : i < k) (m : D.J → E) :
    ∑ j, D.formAt k x i j * m j = m (D.cAt i false) * (D.bR k x.2 i).1 := by
  classical
  unfold PartsP.formAt
  rw [if_pos h]
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  exact mul_comm _ _

/-- The value of the form of the open claim. -/
theorem PartsP.form_ge (k : ℕ) (x : E × (D.lv k).T.St) (i : ℕ) (h : ¬ i < k) (m : D.J → E) :
    ∑ j, D.formAt k x i j * m j = ∑ j, (D.lv k).T.slS x.2 j * m ((D.lv k).toJ j) := by
  unfold PartsP.formAt
  rw [if_neg h]
  exact ldLkpP_push E _ _ _ _ _

/-- The place of the mask entry on the value that the next step takes up. -/
theorem PartsP.cAt_nx : ∀ l, (D.lv l).toJ ((D.lv l).T.cAt (D.lv l).nx) = D.cAt l true
  | 0 => rfl
  | _ + 1 => rfl

/-- The open claim's form, written out. Before any step: the form that came in. -/
theorem PartsP.formAt_zero (x : E × (D.lv 0).T.St) (i : ℕ) (j : D.J) :
    D.formAt 0 x i j = D.inc x.2 j := by
  classical
  unfold PartsP.formAt
  rw [if_neg (Nat.not_lt_zero i)]
  show (∑ j' : D.J, if j' = j then D.inc x.2 j' else 0) = D.inc x.2 j
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]

open Classical in
/-- After k + 1 steps: β of step k at the place cAt k true, 0 elsewhere. -/
theorem PartsP.formAt_open (k : ℕ) (x : E × (D.lv (k + 1)).T.St) (i : ℕ) (h : ¬ i < k + 1)
    (j : D.J) :
    D.formAt (k + 1) x i j = if j = D.cAt k true then D.be k x.2 else 0 := by
  unfold PartsP.formAt
  rw [if_neg h]
  show (∑ j' : D.J, if j' = j then
      (if j' = (D.lv k).toJ ((D.lv k).T.cAt (D.lv k).nx) then D.be k x.2 else 0) else 0) = _
  rw [D.cAt_nx k]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- After the n steps: the rows, and one claim a part. -/
theorem partsR_out (x : E × (D.lv D.n).T.St) (m : D.J → E) :
    D.Done D.n x.2 m ∧ D.claim D.n x m ↔ RowsHold (D.rowsAt D.n x.2) m ∧ D.Claims x m := by
  have hlast : D.claim D.n x m ↔
      D.root ((D.lv D.n).base x.2) m D.n + ∑ j, D.formAt D.n x D.n j * m j = D.tgtAt D.n x D.n := by
    unfold PartsP.claim PartsP.tgtAt
    rw [D.form_ge D.n x D.n (Nat.lt_irrefl _) m, D.rest_last, if_neg (Nat.lt_irrefl _)]
  have hlt : ∀ i, i < D.n →
      (D.root ((D.lv D.n).base x.2) m i + m (D.cAt i false) * (D.bR D.n x.2 i).1 =
          (D.bR D.n x.2 i).2 ↔
        D.root ((D.lv D.n).base x.2) m i + ∑ j, D.formAt D.n x i j * m j = D.tgtAt D.n x i) := by
    intro i hi
    unfold PartsP.tgtAt
    rw [D.form_lt D.n x i hi m, if_pos hi]
  constructor
  · rintro ⟨⟨hr, ht⟩, hc⟩
    refine ⟨hr, fun i hi => ?_⟩
    rcases Nat.lt_or_eq_of_le hi with h | rfl
    · exact (hlt i h).1 (ht i h)
    · exact hlast.1 hc
  · rintro ⟨hr, hc⟩
    exact ⟨⟨hr, fun i hi => (hlt i hi).2 (hc i (Nat.le_of_lt hi))⟩,
      hlast.2 (hc D.n (Nat.le_refl _))⟩

/-- The joint after the n steps: what rode, the rows, one claim a part. -/
theorem partsR_end (Ex : ExtSpec) (Kc St M Wp : Type) (R0 : Rels Kc St Ex (M × Wp))
    (msg : M → D.J → E) (pr : D.St0 → St) (Φ ΦR : D.St0 → (D.J → E) → Prop) :
    D.jtAt msg (cj R0 msg pr Φ ΦR) D.n =
      cj R0 msg (fun x => pr ((D.lv D.n).base x.2))
        (fun x m => Φ ((D.lv D.n).base x.2) m ∧ RowsHold (D.rowsAt D.n x.2) m ∧ D.Claims x m)
        (fun x m => ΦR ((D.lv D.n).base x.2) m ∧ RowsHold (D.rowsAt D.n x.2) m ∧ D.Claims x m) := by
  rw [partsR_cj]
  exact ldLkpK_congr E Kc St M Wp D.J _ Ex R0 msg _ _ _ _ _
    (fun x m => by rw [and_assoc, partsR_out]) (fun x m => by rw [and_assoc, partsR_out])

section
variable (i : ℕ) (U : E × (D.lv D.n).T.St → (D.J → E) → (l : ℕ) → (Fin (0 + l) → Bool) → E)
  (wK : (l : ℕ) → PIdx (List.replicate (0 + l) (pfCube E 2) ++ [pDummy E 2]) → D.J)
  (cK : ℕ → Bool → D.J)

theorem rootP_inc : (D.rootP i U wK cK).IncOK := by
  intro st (ϱ : Fin (0 + 0) → E) j
  show D.formAt D.n st i j = ∑ θ : Fin (0 + 0) → Bool, Alg.eqk ϱ θ * D.formAt D.n st i j
  rw [← Finset.sum_mul]
  exact ((congrArg (· * D.formAt D.n st i j) (Alg.sum_eqk ϱ)).trans (one_mul _)).symm

theorem rootP_holds (hU : ∀ x m θ, U x m 0 θ = D.root ((D.lv D.n).base x.2) m i)
    (x : E × (D.lv D.n).T.St) (m : D.J → E) :
    (D.rootP i U wK cK).Holds x m ↔
      D.root ((D.lv D.n).base x.2) m i + ∑ j, D.formAt D.n x i j * m j = D.tgtAt D.n x i := by
  constructor
  · intro h
    have := h (fun _ => false)
    rw [← hU x m fun _ => false]
    exact this
  · intro h θ
    show U x m 0 θ + ∑ j, D.formAt D.n x i j * m j = D.tgtAt D.n x i
    rw [hU x m θ]
    exact h

end
end
end Lk6
