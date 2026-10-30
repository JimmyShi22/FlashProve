-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLkpTieRows.lean: what rides along through the tie of a lookup, read off the nested state.
This file is book-keeping on the statements between the steps of a chain of reductions: the claims
that earlier steps have left are written out as claims on the entries.

Definitions, statements (in `Cb.Spec`) and proofs. Glue for the assembly; no new protocol.
The tie (`TieP.tieA`, Cb/Ld/LdLkpTie.lean) is the chain of sumchecks of that file. The states of its
steps are nested: the state of step l + 1 is the output of step l, which contains the state of step
l. What rides along before step l + 1 (`TieP.ride`) contains, beside the joint with which the tie
was entered:
  the rows on the hiding coefficients of the steps 0, .., l;
  the masked claim on PK (made by step 0);
  the masked claims on PT_j, j < l (made by step j + 1).
Here they are read off the state. PK and PT_j are functions of state and entries (fields of `TieP`);
that they are the products of a lookup, and `D.StepTo` for them, is the caller's matter
(Cb/Ld/LdLkpTie.lean, Limits).

Main names:
  `rowUof`: for any sumcheck none of whose maps stays unrevealed: its row on the hiding coefficients
    as a row in the sense of Cb/Ld/LdLkpTree.lean, in another naming of the entries.
  `D.bK l`, `D.bT l`: (β, public target) of the masked claim on PK; on PT_j.
  `D.Done l s m`: all that is done before step l + 1.
  `Spec.ldLkpTieR_rowU`: the row holds if and only if the sumcheck's own claim on its hiding
    coefficients holds.
  `Spec.ldLkpTieR_ride`: what rides along before step l + 1 is: the joint with which the tie was
    entered, at the state with which it was entered, and `D.Done l` (in `rel` and `relR`; `on` and
    `core` are that joint's).
  `Spec.ldLkpTieR_cj`: entered beside a joint of the form "a riding joint, and claims on the
    entries" (`cj`, Cb/Ld/LdLkpKit.lean), the tie's joint before step l + 1 is of that form.

Limits: this file says nothing on soundness or zero knowledge.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdLkpTie
import Cb.Ld.LdLkpKit

set_option autoImplicit false

namespace Cb.LdLkp
open Iop IOR Hiop Prob

noncomputable section
variable {E : Type} [Field E] [Fintype E]

/-- The row on the hiding coefficients of a sumcheck none of whose maps stays unrevealed. -/
def rowUof (T : PscOur E) (h : IsEmpty T.par.B) {J : Type} (toJ : T.J → J) (o : T.par.Out) :
    Row E J :=
  ⟨pushJ toJ (T.par.slU (fun _ b _ _ => (h.false b).elim) o), T.par.tU o⟩

namespace TieP
variable (D : TieP E)

theorem emB (l : ℕ) : IsEmpty (D.lv l).T.par.B := by
  cases l with
  | zero => exact inferInstanceAs (IsEmpty Empty)
  | succ l => exact inferInstanceAs (IsEmpty Empty)

/-- The challenge β of the dummy variable of step l. -/
def be (l : ℕ) (o : (D.lv l).T.par.Out) : E := (D.lv l).T.lst o.st ((D.lv l).T.par.hp o.st o.pt)

/-- The rows of the steps below l. -/
def rowsAt : (l : ℕ) → (D.lv l).T.St → List (Row E D.J)
  | 0, _ => []
  | l + 1, o => rowUof (D.lv l).T (D.emB l) (D.lv l).toJ o :: rowsAt l o.st

/-- (β, target) of the masked claim on PK. -/
def bK : (l : ℕ) → (D.lv (l + 1)).T.St → E × E
  | 0, o => (D.be 0 o, o.vals (D.lv 0).pt)
  | l + 1, o => bK l o.st

/-- (β, target) of the masked claim on PT_j. -/
def bT : (l : ℕ) → (D.lv (l + 1)).T.St → ℕ → E × E
  | 0, _, _ => (0, 0)
  | l + 1, o, j => if j = l then (D.be (l + 1) o, o.vals (D.lv (l + 1)).pt) else bT l o.st j

/-- All that is done before step l + 1. -/
def Done (l : ℕ) (s : (D.lv (l + 1)).T.St) (m : D.J → E) : Prop :=
  RowsHold (D.rowsAt (l + 1) s) m ∧
  D.PK ((D.lv (l + 1)).base s) m + m (D.cS false) * (D.bK l s).1 = (D.bK l s).2 ∧
  ∀ j < l, D.PT ((D.lv (l + 1)).base s) m j + m (D.cAt j true) * (D.bT l s j).1 = (D.bT l s j).2

end TieP
end
end Cb.LdLkp

namespace Cb.Spec
open Iop IOR Hiop Prob Cb.LdLkp

section
variable (E : Type) [Field E] [Fintype E]

def ldLkpTieR_rowU : Prop :=
  ∀ (T : PscOur E) (h : IsEmpty T.par.B) (J : Type) [Fintype J] (toJ : T.J → J)
      (o : T.par.Out) (m : J → E),
    (rowUof T h toJ o).Holds m ↔ T.par.UHolds o fun j => m (toJ j)

def ldLkpTieR_ride : Prop :=
  ∀ (D : TieP E) (Ex : ExtSpec) (M Wp Kc : Type) (msg : M → D.J → E)
      (A0 : Rels Kc D.St0 Ex (M × Wp)) (l : ℕ),
    (∀ s y w,
      (D.ride msg A0 (l + 1)).rel s y w ↔
      A0.rel ((D.lv (l + 1)).base s) y w ∧ D.Done l s (msg w.1)) ∧
    (∀ s y w,
      (D.ride msg A0 (l + 1)).relR (s, y) w ↔
      A0.relR ((D.lv (l + 1)).base s, y) w ∧ D.Done l s (msg w.1)) ∧
    (∀ s y, (D.ride msg A0 (l + 1)).on (s, y) ↔ A0.on ((D.lv (l + 1)).base s, y)) ∧
    (D.ride msg A0 (l + 1)).core = A0.core

def ldLkpTieR_cj : Prop :=
  ∀ (D : TieP E) (Ex : ExtSpec) (Kc St M Wp : Type) (R0 : Rels Kc St Ex (M × Wp))
      (msg : M → D.J → E) (pr : D.St0 → St) (Φ ΦR : D.St0 → (D.J → E) → Prop) (l : ℕ),
    D.jtAt msg (cj R0 msg pr Φ ΦR) (l + 1) =
      cj R0 msg (fun x => pr ((D.lv (l + 1)).base x.2))
        (fun x m => (Φ ((D.lv (l + 1)).base x.2) m ∧ D.Done l x.2 m) ∧ D.claim (l + 1) x m)
        (fun x m => (ΦR ((D.lv (l + 1)).base x.2) m ∧ D.Done l x.2 m) ∧ D.claim (l + 1) x m)

end
end Cb.Spec

namespace Cb
open Iop IOR Hiop Prob Cb.LdLkp

section
variable (E : Type) [Field E] [Fintype E]

theorem ldLkpTieR_rowU : Spec.ldLkpTieR_rowU E := by
  intro T h J _ toJ o m
  rw [psc_row_U E T.par (fun _ b _ _ => (h.false b).elim) (fun _ _ b _ => (h.false b).elim) o]
  unfold Row.Holds Slf.Holds rowUof
  rw [ldLkpP_push]
  exact Iff.rfl

/-- Glue: the masked claims that ride along, written out. -/
theorem LdLkp.TieP.eK (D : TieP E) (o : (D.lv 0).T.par.Out) (m : D.J → E) :
    (D.lv 0).T.par.EHolds o (fun j => m ((D.lv 0).toJ j)) (D.lv 0).pt ↔
    D.PK o.st m + m (D.cS false) * D.be 0 o = o.vals (D.lv 0).pt := Iff.rfl

theorem LdLkp.TieP.eT (D : TieP E) (j : ℕ) (o : (D.lv (j + 1)).T.par.Out) (m : D.J → E) :
    (D.lv (j + 1)).T.par.EHolds o (fun i => m ((D.lv (j + 1)).toJ i)) (D.lv (j + 1)).pt ↔
    D.PT ((D.lv (j + 1)).base o.st) m j + m (D.cAt j true) * D.be (j + 1) o =
      o.vals (D.lv (j + 1)).pt := Iff.rfl

/-- Glue: one more step done. -/
theorem LdLkp.TieP.done_succ (D : TieP E) (l : ℕ) (o : (D.lv (l + 1)).T.par.Out) (m : D.J → E) :
    D.Done (l + 1) o m ↔
    D.Done l o.st m ∧
    (D.lv (l + 1)).T.par.UHolds o (fun j => m ((D.lv (l + 1)).toJ j)) ∧
    (D.lv (l + 1)).T.par.EHolds o (fun j => m ((D.lv (l + 1)).toJ j)) (D.lv (l + 1)).pt := by
  rw [D.eT E l o m, ← ldLkpTieR_rowU E (D.lv (l + 1)).T (D.emB (l + 1)) D.J (D.lv (l + 1)).toJ o m]
  constructor
  · rintro ⟨hr, hk, ht⟩
    refine ⟨⟨fun r h => hr r (List.mem_cons_of_mem _ h), hk, fun j hj => ?_⟩,
      hr _ List.mem_cons_self,
      ?_⟩
    · have := ht j (Nat.lt_succ_of_lt hj)
      have e : D.bT (l + 1) o j = D.bT l o.st j := if_neg (Nat.ne_of_lt hj)
      rw [e] at this
      exact this
    · have := ht l (Nat.lt_succ_self l)
      have e : D.bT (l + 1) o l = (D.be (l + 1) o, o.vals (D.lv (l + 1)).pt) := if_pos rfl
      rw [e] at this
      exact this
  · rintro ⟨⟨hr, hk, ht⟩, hu, he⟩
    refine ⟨fun r h => ?_, hk, fun j hj => ?_⟩
    · rcases List.mem_cons.mp h with rfl | h
      · exact hu
      · exact hr r h
    · by_cases hjl : j = l
      · subst hjl
        have e : D.bT (j + 1) o j = (D.be (j + 1) o, o.vals (D.lv (j + 1)).pt) := if_pos rfl
        rw [e]
        exact he
      · have e : D.bT (l + 1) o j = D.bT l o.st j := if_neg hjl
        rw [e]
        exact ht j (by omega)

theorem LdLkp.TieP.done_zero (D : TieP E) (o : (D.lv 0).T.par.Out) (m : D.J → E) :
    D.Done 0 o m ↔
    (D.lv 0).T.par.UHolds o (fun j => m ((D.lv 0).toJ j)) ∧
    (D.lv 0).T.par.EHolds o (fun j => m ((D.lv 0).toJ j)) (D.lv 0).pt := by
  rw [D.eK E o m, ← ldLkpTieR_rowU E (D.lv 0).T (D.emB 0) D.J (D.lv 0).toJ o m]
  constructor
  · rintro ⟨hr, hk, _⟩
    exact ⟨hr _ List.mem_cons_self, hk⟩
  · rintro ⟨hu, hk⟩
    refine ⟨fun r h => ?_, hk, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
    rcases List.mem_cons.mp h with rfl | h
    · exact hu
    · exact absurd h List.not_mem_nil

theorem ldLkpTieR_ride : Spec.ldLkpTieR_ride E := by
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

theorem ldLkpTieR_cj : Spec.ldLkpTieR_cj E := by
  intro D Ex Kc St M Wp R0 msg pr Φ ΦR l
  obtain ⟨h1, h2, h3, h4⟩ := ldLkpTieR_ride E D Ex M Wp Kc msg (cj R0 msg pr Φ ΦR) l
  refine rels_ext (funext fun x => funext fun y => funext fun w => propext ?_)
    (funext fun a => funext fun w => propext ?_) (funext fun a => propext (h3 a.1.2 a.2)) h4
  · show (D.ride msg (cj R0 msg pr Φ ΦR) (l + 1)).rel x.2 y w ∧ _ ↔ _
    rw [h1]
    exact ⟨fun h => ⟨h.1.1.1, ⟨h.1.1.2, h.1.2⟩, h.2⟩, fun h => ⟨⟨⟨h.1, h.2.1.1⟩, h.2.1.2⟩, h.2.2⟩⟩
  · show (D.ride msg (cj R0 msg pr Φ ΦR) (l + 1)).relR (a.1.2, a.2) w ∧ _ ↔ _
    rw [h2]
    exact ⟨fun h => ⟨h.1.1.1, ⟨h.1.1.2, h.1.2⟩, h.2⟩, fun h => ⟨⟨⟨h.1, h.2.1.1⟩, h.2.1.2⟩, h.2.2⟩⟩

end
end Cb
