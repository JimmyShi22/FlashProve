-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Lookup/Blocks/TieFRows.lean: the tie of a lookup (Cb/Pv/Lookup/Blocks/TieF.lean): what its
steps leave, read off the nested state.

Definitions, statements (in `Cb.Spec`) and proofs. As Cb/Ld/LdLkpTieRows.lean, for `TieF`.
Each step of the tie leaves one linear row on the entries (`rowUof`, Cb/Ld/LdLkpTieRows.lean) and,
for each value that the next step does not take up, a claim value + (an entry) · β = (scalar sent).
This file collects them and restates the tie's joints in the form in which the lookup's assembly
uses them.

Main names:
  `D.rowsAt l`: the rows of the steps below l.
  `D.bK l`, `D.bT l`: (β, target) of the claim on PK; on PT_j, j ≤ l.
  `D.Done l s m`: the rows of the steps 0, .., l hold, and the claims on PK and on PT_0, .., PT_l.
  `Spec.tieFR_ride`: what rides along before step l + 1 is the joint with which the tie was entered
    and `D.Done l`.
  `Spec.tieFR_cj`: entered beside a joint of the form `cj` (Cb/Ld/LdLkpKit.lean), the tie's joint
    before step l + 1 is of that form.
  `Spec.tieFR_open`: the open claim before step l + 1 says Q_(l+1) + (an entry) · β = target.
Limits: book-keeping: equivalences and equations, without a premise; no property of a protocol is
stated here. That PK, PT_j are the products of a lookup is the caller's matter.

-/
import Cb.Pv.Lookup.Blocks.TieF
import Cb.Ld.LdLkpTieRows

set_option autoImplicit false

namespace Cb.LdLkp
open Iop IOR Hiop Prob

noncomputable section
variable {E : Type} [Field E] [Fintype E]

namespace TieF
variable (D : TieF E)

theorem emB (l : ℕ) : IsEmpty (D.lv l).T.par.B := by
  cases l with
  | zero => exact inferInstanceAs (IsEmpty Empty)
  | succ l => exact inferInstanceAs (IsEmpty Empty)

/-- The challenge β of the dummy variable of step l. -/
def be (l : ℕ) (o : (D.lv l).T.par.Out) : E := (D.lv l).T.lst o.st ((D.lv l).T.par.hp o.st o.pt)

/-- The rows of the steps below l, the newest first (as in Cb/Ld/LdLkpTieRows.lean). -/
def rowsAt : (l : ℕ) → (D.lv l).T.St → List (Row E D.J)
  | 0, _ => []
  | l + 1, o => rowUof (D.lv l).T (D.emB l) (D.lv l).toJ o :: rowsAt l o.st

/-- (β, target) of the masked claim on PK. -/
def bK : (l : ℕ) → (D.lv (l + 1)).T.St → E × E
  | 0, o => (D.be 0 o, o.vals (none : Option Bool))
  | l + 1, o => bK l o.st

/-- (β, target) of the masked claim on PT_j, j ≤ l. -/
def bT : (l : ℕ) → (D.lv (l + 1)).T.St → ℕ → E × E
  | 0, o, _ => (D.be 0 o, o.vals (some true : Option Bool))
  | l + 1, o, j => if j = l + 1 then (D.be (l + 1) o, o.vals true) else bT l o.st j

/-- All that is done before step l + 1. -/
def Done (l : ℕ) (s : (D.lv (l + 1)).T.St) (m : D.J → E) : Prop :=
  RowsHold (D.rowsAt (l + 1) s) m ∧
  D.PK ((D.lv (l + 1)).base s) m + m D.cZ * (D.bK l s).1 = (D.bK l s).2 ∧
  ∀ j < l + 1, D.PT ((D.lv (l + 1)).base s) m j + m (D.cAt j true) * (D.bT l s j).1 = (D.bT l s j).2

end TieF
end
end Cb.LdLkp

namespace Cb.Spec
open Iop IOR Hiop Prob Cb.LdLkp

section
variable (E : Type) [Field E] [Fintype E]

/-- What rides along before step l + 1: the joint with which the tie was entered, and `D.Done l`. -/
def tieFR_ride : Prop :=
  ∀ (D : TieF E) (Ex : ExtSpec) (M Wp Kc : Type) (msg : M → D.J → E)
      (A0 : Rels Kc D.St0 Ex (M × Wp)) (l : ℕ),
    (∀ s y w,
      (D.ride msg A0 (l + 1)).rel s y w ↔
      A0.rel ((D.lv (l + 1)).base s) y w ∧ D.Done l s (msg w.1)) ∧
    (∀ s y w,
      (D.ride msg A0 (l + 1)).relR (s, y) w ↔
      A0.relR ((D.lv (l + 1)).base s, y) w ∧ D.Done l s (msg w.1)) ∧
    (∀ s y, (D.ride msg A0 (l + 1)).on (s, y) ↔ A0.on ((D.lv (l + 1)).base s, y)) ∧
    (D.ride msg A0 (l + 1)).core = A0.core

/-- Entered beside a joint of the form `cj`, the tie's joint before step l + 1 is of that form. -/
def tieFR_cj : Prop :=
  ∀ (D : TieF E) (Ex : ExtSpec) (Kc St M Wp : Type) (R0 : Rels Kc St Ex (M × Wp))
      (msg : M → D.J → E) (pr : D.St0 → St) (Φ ΦR : D.St0 → (D.J → E) → Prop) (l : ℕ),
    D.jtAt msg (cj R0 msg pr Φ ΦR) (l + 1) =
      cj R0 msg (fun x => pr ((D.lv (l + 1)).base x.2))
        (fun x m => (Φ ((D.lv (l + 1)).base x.2) m ∧ D.Done l x.2 m) ∧ D.claim (l + 1) x m)
        (fun x m => (ΦR ((D.lv (l + 1)).base x.2) m ∧ D.Done l x.2 m) ∧ D.claim (l + 1) x m)

/-- The open claim, in closed form. -/
def tieFR_open : Prop :=
  ∀ (D : TieF E) (l : ℕ) (x : E × (D.lv (l + 1)).T.St) (m : D.J → E),
    D.claim (l + 1) x m ↔
    D.Q ((D.lv (l + 1)).base x.2) m (l + 1) + m (D.cAt l false) * D.be l x.2 = x.1

end
end Cb.Spec

namespace Cb
open Iop IOR Hiop Prob Cb.LdLkp

section
variable (E : Type) [Field E] [Fintype E]

/-- Glue: what "for all values that ride along" says at step 0, and at a later step. -/
theorem LdLkp.TieF.pts0 (D : TieF E) (P : (D.lv 0).T.A → Prop) :
    (∀ a ∈ (D.lv 0).pts, P a) ↔ P (none : Option Bool) ∧ P (some true : Option Bool) := by
  constructor
  · intro h
    exact ⟨h _ (show (none : Option Bool) ∈ [none, some true] from List.mem_cons_self),
      h _ (show (some true : Option Bool) ∈ [none, some true] from
        List.mem_cons_of_mem _ List.mem_cons_self)⟩
  · intro h a ha
    have ha' : a ∈ [(none : Option Bool), some true] := ha
    rcases List.mem_cons.mp ha' with rfl | ha'
    · exact h.1
    · rcases List.mem_cons.mp ha' with rfl | ha'
      · exact h.2
      · exact absurd ha' List.not_mem_nil

theorem LdLkp.TieF.ptsS (D : TieF E) (l : ℕ) (P : (D.lv (l + 1)).T.A → Prop) :
    (∀ a ∈ (D.lv (l + 1)).pts, P a) ↔ P true := by
  constructor
  · intro h
    exact h _ (show true ∈ [true] from List.mem_cons_self)
  · intro h a ha
    have ha' : a ∈ [true] := ha
    rcases List.mem_cons.mp ha' with rfl | ha'
    · exact h
    · exact absurd ha' List.not_mem_nil

/-- Glue: the masked claims that ride along, written out. -/
theorem LdLkp.TieF.eK (D : TieF E) (o : (D.lv 0).T.par.Out) (m : D.J → E) :
    (D.lv 0).T.par.EHolds o (fun j => m ((D.lv 0).toJ j)) (none : Option Bool) ↔
    D.PK o.st m + m D.cZ * D.be 0 o = o.vals (none : Option Bool) := Iff.rfl

theorem LdLkp.TieF.eT0 (D : TieF E) (o : (D.lv 0).T.par.Out) (m : D.J → E) :
    (D.lv 0).T.par.EHolds o (fun j => m ((D.lv 0).toJ j)) (some true : Option Bool) ↔
    D.PT o.st m 0 + m (D.cAt 0 true) * D.be 0 o = o.vals (some true : Option Bool) := Iff.rfl

theorem LdLkp.TieF.eT (D : TieF E) (j : ℕ) (o : (D.lv (j + 1)).T.par.Out) (m : D.J → E) :
    (D.lv (j + 1)).T.par.EHolds o (fun i => m ((D.lv (j + 1)).toJ i)) true ↔
    D.PT ((D.lv (j + 1)).base o.st) m (j + 1) + m (D.cAt (j + 1) true) * D.be (j + 1) o =
      o.vals true := Iff.rfl

/-- Glue: one more step done. -/
theorem LdLkp.TieF.done_succ (D : TieF E) (l : ℕ) (o : (D.lv (l + 1)).T.par.Out) (m : D.J → E) :
    D.Done (l + 1) o m ↔
    D.Done l o.st m ∧
    (D.lv (l + 1)).T.par.UHolds o (fun j => m ((D.lv (l + 1)).toJ j)) ∧
    ∀ a ∈ (D.lv (l + 1)).pts,
      (D.lv (l + 1)).T.par.EHolds o (fun j => m ((D.lv (l + 1)).toJ j)) a := by
  rw [D.ptsS E l, D.eT E l o m,
    ← ldLkpTieR_rowU E (D.lv (l + 1)).T (D.emB (l + 1)) D.J (D.lv (l + 1)).toJ o m]
  constructor
  · rintro ⟨hr, hk, ht⟩
    refine ⟨⟨fun r h => hr r (List.mem_cons_of_mem _ h), hk, fun j hj => ?_⟩,
      hr _ List.mem_cons_self,
      ?_⟩
    · have := ht j (Nat.lt_succ_of_lt hj)
      have e : D.bT (l + 1) o j = D.bT l o.st j := if_neg (Nat.ne_of_lt hj)
      rw [e] at this
      exact this
    · have := ht (l + 1) (Nat.lt_succ_self (l + 1))
      have e : D.bT (l + 1) o (l + 1) = (D.be (l + 1) o, o.vals true) := if_pos rfl
      rw [e] at this
      exact this
  · rintro ⟨⟨hr, hk, ht⟩, hu, he⟩
    refine ⟨fun r h => ?_, hk, fun j hj => ?_⟩
    · rcases List.mem_cons.mp h with rfl | h
      · exact hu
      · exact hr r h
    · by_cases hjl : j = l + 1
      · subst hjl
        have e : D.bT (l + 1) o (l + 1) = (D.be (l + 1) o, o.vals true) := if_pos rfl
        rw [e]
        exact he
      · have e : D.bT (l + 1) o j = D.bT l o.st j := if_neg hjl
        rw [e]
        exact ht j (by omega)

theorem LdLkp.TieF.done_zero (D : TieF E) (o : (D.lv 0).T.par.Out) (m : D.J → E) :
    D.Done 0 o m ↔
    (D.lv 0).T.par.UHolds o (fun j => m ((D.lv 0).toJ j)) ∧
    ∀ a ∈ (D.lv 0).pts, (D.lv 0).T.par.EHolds o (fun j => m ((D.lv 0).toJ j)) a := by
  rw [D.pts0 E, D.eK E o m, D.eT0 E o m,
    ← ldLkpTieR_rowU E (D.lv 0).T (D.emB 0) D.J (D.lv 0).toJ o m]
  constructor
  · rintro ⟨hr, hk, ht⟩
    exact ⟨hr _ List.mem_cons_self, hk, ht 0 Nat.one_pos⟩
  · rintro ⟨hu, hk, ht⟩
    refine ⟨fun r h => ?_, hk, fun j hj => ?_⟩
    · rcases List.mem_cons.mp h with rfl | h
      · exact hu
      · exact absurd h List.not_mem_nil
    · have hj0 : j = 0 := by omega
      subst hj0
      exact ht

theorem tieFR_ride : Spec.tieFR_ride E := by
  intro D Ex M Wp Kc msg A0 l
  induction l with
  | zero =>
    exact ⟨fun s y w => and_congr_right fun _ => (D.done_zero E s (msg w.1)).symm,
      fun s y w => and_congr_right fun _ => (D.done_zero E s (msg w.1)).symm,
      fun _ _ => Iff.rfl, rfl⟩
  | succ l ih =>
    obtain ⟨h1, h2, h3, h4⟩ := ih
    refine ⟨fun s y w => ?_, fun s y w => ?_, fun s y => h3 s.st y, h4⟩
    · rw [D.done_succ E l s (msg w.1), ← and_assoc]
      exact and_congr (h1 s.st y w) Iff.rfl
    · rw [D.done_succ E l s (msg w.1), ← and_assoc]
      exact and_congr (h2 s.st y w) Iff.rfl

theorem tieFR_cj : Spec.tieFR_cj E := by
  intro D Ex Kc St M Wp R0 msg pr Φ ΦR l
  obtain ⟨h1, h2, h3, h4⟩ := tieFR_ride E D Ex M Wp Kc msg (cj R0 msg pr Φ ΦR) l
  refine rels_ext (funext fun x => funext fun y => funext fun w => propext ?_)
    (funext fun a => funext fun w => propext ?_) (funext fun a => propext (h3 a.1.2 a.2)) h4
  · show (D.ride msg (cj R0 msg pr Φ ΦR) (l + 1)).rel x.2 y w ∧ _ ↔ _
    rw [h1]
    exact ⟨fun h => ⟨h.1.1.1, ⟨h.1.1.2, h.1.2⟩, h.2⟩, fun h => ⟨⟨⟨h.1, h.2.1.1⟩, h.2.1.2⟩, h.2.2⟩⟩
  · show (D.ride msg (cj R0 msg pr Φ ΦR) (l + 1)).relR (a.1.2, a.2) w ∧ _ ↔ _
    rw [h2]
    exact ⟨fun h => ⟨h.1.1.1, ⟨h.1.1.2, h.1.2⟩, h.2⟩, fun h => ⟨⟨⟨h.1, h.2.1.1⟩, h.2.1.2⟩, h.2.2⟩⟩

theorem tieFR_open : Spec.tieFR_open E := by
  intro D l x m
  have h := tieF_form E D l x.2 m
  rw [D.c_nx l] at h
  show D.Q ((D.lv (l + 1)).base x.2) m (l + 1) +
      ∑ j, (D.lv (l + 1)).T.slS x.2 j * m ((D.lv (l + 1)).toJ j) = x.1 ↔ _
  rw [h, mul_comm]
  exact Iff.rfl

end
end Cb
