-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLkpAsmProofs.lean: the proofs of the statements of Cb/Ld/LdLkpAsm.lean (the lookup,
assembled: `LkAsm`). Before them lemmas and definitions that no statement reads: lists of rows; a
form with one entry; the row on the number of keys; the claims that wait after the head
(`LkHead.headA`), by name; the two junctions (head to keys' side (`segK`), keys' side to table's
side (`SegTab.segT`)) and the read-out as equivalences of claims.

Main names (statements and hypotheses: Cb/Ld/LdLkpAsm.lean):
  `ldLkpAsm_base`: the assembled lookup, at the base.
  `ldLkpAsm_ok`: the assembled lookup over a signature.
  `ldLkpAsm_rounds`: the number of rounds.

Limits: what the head of Cb/Ld/LdLkpAsm.lean lists as not said is not said here either.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdLkpAsm
import Cb.Ld.LdLkpSegTProofs

set_option autoImplicit false

namespace Cb
open Iop IOR Hiop Prob Cb.LdLkp Cb.Lkp Finset

section
variable {E : Type} [Field E] [Fintype E]

namespace LdLkp

omit [Fintype E] in
theorem rowsHold_cons {N : Type} [Fintype N] (r : Row E N) (l : List (Row E N)) (μ : N → E) :
    RowsHold (r :: l) μ ↔ r.Holds μ ∧ RowsHold l μ :=
  ⟨fun h => ⟨h r List.mem_cons_self, fun s hs => h s (List.mem_cons_of_mem _ hs)⟩, fun h s hs => by
    rcases List.mem_cons.mp hs with rfl | hs
    · exact h.1
    · exact h.2 s hs⟩

omit [Fintype E] in
theorem rowsHold_append {N : Type} [Fintype N] (a b : List (Row E N)) (μ : N → E) :
    RowsHold (a ++ b) μ ↔ RowsHold a μ ∧ RowsHold b μ :=
  ⟨fun h => ⟨fun s hs => h s (List.mem_append_left _ hs), fun s hs => h s (List.mem_append_right _ hs)⟩, fun h s hs => by
    rcases List.mem_append.mp hs with hs | hs
    · exact h.1 s hs
    · exact h.2 s hs⟩

omit [Fintype E] in
open Classical in
theorem sum_one {N : Type} [Fintype N] (c : N) (β : E) (μ : N → E) :
    ∑ j, (if j = c then β else 0) * μ j = μ c * β := by
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  exact mul_comm _ _

namespace LkAsm
variable (A : LkAsm E)

/-- the claims that wait after the head, by name -/
def PKc (x : A.X2) (m : A.J → E) : Prop :=
  keyProd (A.v' + 1) (A.key (A.b2 x).1 m) (A.b2 x).2 + m (A.cS false) * (A.H.tie.bK A.n x.2).1 =
    (A.H.tie.bK A.n x.2).2
def PTc (x : A.X2) (m : A.J → E) : Prop :=
  ∀ j < A.n,
    A.H.PT (A.b2 x) m j + m (A.cAt j true) * (A.H.tie.bT A.n x.2 j).1 = (A.H.tie.bT A.n x.2 j).2
def Opn (x : A.X2) (m : A.J → E) : Prop := A.H.tie.claim (A.n + 1) x m
def Num (m : A.J → E) : Prop := NumKeys (A.v' + 1) A.d (A.n + 1) (A.H.bit m)
def Bt (m : A.J → E) : Prop := Bits A.d A.w (A.H.bit m)

/-- what rides past the keys' side; past the table's side.  P: what the honest side knows more -/
def ΨK (P : A.St → (A.J → E) → Prop) (x : A.X2) (m : A.J → E) : Prop :=
  (A.H.Rest (A.b2 x) m ∧ P (A.b2 x).1 m) ∧ RowsHold (A.rows2 x) m ∧ A.PTc x m ∧ A.Opn x m
def ΨT (P : A.St → (A.J → E) → Prop) (x : A.X4) (m : A.J → E) : Prop :=
  ((A.Num m ∧ P (A.b2 (A.o4 x)).1 m) ∧ RowsHold (A.rows2 (A.o4 x)) m) ∧
  RowsHold (A.rows4 x) m ∧
  (A.clK x).Holds (A.v' + 1) (A.key (A.b2 (A.o4 x)).1 m) m

theorem num_iff (m : A.J → E) : A.numRow.Holds m ↔ A.Num m := by
  classical
  have e : ∑ i, A.numRow.cf i * m i =
      ∑ u ∈ range (2 ^ A.d), ∑ j ∈ range (A.n + 1), (2 : E) ^ j * A.H.bit m u j := by
    unfold numRow
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rfl
  unfold Row.Holds Num NumKeys
  rw [e]
  exact Iff.rfl

/-- junction 1: what the head leaves is what the keys' side takes -/
theorem junction1 (P : A.St → (A.J → E) → Prop) (x : A.X2) (m : A.J → E) :
    (((A.H.Rest (A.b2 x) m ∧ P (A.b2 x).1 m) ∧ A.H.tie.Done A.n x.2 m) ∧
      A.H.tie.claim (A.n + 1) x m) ↔
    (A.ΨK P x m ∧
      keyProd (A.v' + 1) (A.IK.key (A.IK.st x) m) (A.IK.lam x) + ∑ j, A.fK x j * m j = A.tK x) := by
  have hs : ∑ j, A.fK x j * m j = m (A.cS false) * (A.H.tie.bK A.n x.2).1 := sum_one _ _ _
  rw [hs]
  constructor
  · rintro ⟨⟨hRP, hr, hk, ht⟩, ho⟩
    exact ⟨⟨hRP, hr, ht, ho⟩, hk⟩
  · rintro ⟨⟨hRP, hr, ht, ho⟩, hk⟩
    exact ⟨⟨hRP, hr, hk, ht⟩, ho⟩

open Classical in
/-- under `hW`: the claims on the products of the table are the roots' claims -/
theorem roots_iff (hW : A.n + 1 ≤ 2 ^ A.w) (x : A.X4) (m : A.J → E) :
    (A.H.Idle (A.b2 (A.o4 x)) m ∧ A.PTc (A.o4 x) m ∧ A.Opn (A.o4 x) m) ↔ A.Q.R.Holds x m := by
  have hU : ∀ θ : Fin (A.w + 0) → Bool, A.Q.R.D.U x m 0 θ = A.H.PT (A.b2 (A.o4 x)) m (numLE θ) :=
    fun θ => ldLkpInst_rootT E A.IT x m θ
  have hO : A.Opn (A.o4 x) m ↔
      A.H.PT (A.b2 (A.o4 x)) m A.n +
          ∑ j, pushJ (A.H.tie.lv (A.n + 1)).toJ ((A.H.tie.lv (A.n + 1)).T.slS (A.o4 x).2) j * m j =
        (A.o4 x).1 := by
    have hq : A.H.tie.Q (A.b2 (A.o4 x)) m A.n = A.H.PT (A.b2 (A.o4 x)) m A.n :=
      ldLkpHead_open E A.H (A.b2 (A.o4 x)) m
    rw [ldLkpP_push, ← hq]
    exact Iff.rfl
  have hlt : ∀ θ : Fin (A.w + 0) → Bool, numLE θ < 2 ^ A.w := fun θ => ldLkpNum_lt (A.w + 0) θ
  constructor
  · rintro ⟨hI, hT, hOp⟩ (θ : Fin (A.w + 0) → Bool)
    show A.Q.R.D.U x m 0 θ + ∑ j, A.formT x θ j * m j = A.tgtT x θ
    rw [hU θ]
    by_cases h1 : numLE θ < A.n
    · have ef : A.formT x θ =
        fun j =>
          if j = A.cAt (numLE θ) true then (A.H.tie.bT A.n (A.o4 x).2 (numLE θ)).1
          else 0 := if_pos h1
      have et : A.tgtT x θ = (A.H.tie.bT A.n (A.o4 x).2 (numLE θ)).2 := if_pos h1
      rw [ef, et, sum_one]
      exact hT _ h1
    · by_cases h2 : numLE θ = A.n
      · have ef : A.formT x θ =
            pushJ (A.H.tie.lv (A.n + 1)).toJ ((A.H.tie.lv (A.n + 1)).T.slS (A.o4 x).2) :=
          (if_neg h1).trans (if_pos h2)
        have et : A.tgtT x θ = (A.o4 x).1 := (if_neg h1).trans (if_pos h2)
        rw [ef, et, h2]
        exact hO.mp hOp
      · have ef : A.formT x θ = 0 := (if_neg h1).trans (if_neg h2)
        have et : A.tgtT x θ = 1 := (if_neg h1).trans (if_neg h2)
        rw [ef, et]
        simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero, add_zero]
        exact hI _ (show A.n + 1 ≤ numLE θ by omega) (hlt θ)
  · intro h
    have h' : ∀ θ : Fin (A.w + 0) → Bool,
        A.H.PT (A.b2 (A.o4 x)) m (numLE θ) + ∑ j, A.formT x θ j * m j = A.tgtT x θ := fun θ => by
      rw [← hU θ]
      exact h θ
    refine ⟨fun j hj hjw => ?_, fun j hj => ?_, hO.mpr ?_⟩
    · have hj' : A.n + 1 ≤ j := hj
      obtain ⟨θ, rfl⟩ := numLE_surj (k := A.w + 0) (c := j) hjw
      have h1 : ¬ numLE θ < A.n := by omega
      have h2 : ¬ numLE θ = A.n := by omega
      have ef : A.formT x θ = 0 := (if_neg h1).trans (if_neg h2)
      have et : A.tgtT x θ = 1 := (if_neg h1).trans (if_neg h2)
      have := h' θ
      rw [ef, et] at this
      simpa only [Pi.zero_apply, zero_mul, Finset.sum_const_zero, add_zero] using this
    · obtain ⟨θ, rfl⟩ := numLE_surj (k := A.w + 0) (c := j) (by show j < 2 ^ A.w; omega)
      have ef : A.formT x θ =
        fun j =>
          if j = A.cAt (numLE θ) true then (A.H.tie.bT A.n (A.o4 x).2 (numLE θ)).1
          else 0 := if_pos hj
      have et : A.tgtT x θ = (A.H.tie.bT A.n (A.o4 x).2 (numLE θ)).2 := if_pos hj
      have := h' θ
      rw [ef, et, sum_one] at this
      exact this
    · obtain ⟨θ, hθ⟩ := numLE_surj (k := A.w + 0) (c := A.n) (by show A.n < 2 ^ A.w; omega)
      have h1 : ¬ numLE θ < A.n := by omega
      have ef : A.formT x θ =
          pushJ (A.H.tie.lv (A.n + 1)).toJ ((A.H.tie.lv (A.n + 1)).T.slS (A.o4 x).2) :=
        (if_neg h1).trans (if_pos hθ)
      have et : A.tgtT x θ = (A.o4 x).1 := (if_neg h1).trans (if_pos hθ)
      have := h' θ
      rw [ef, et, hθ] at this
      exact this

/-- junction 2, under `hW`: what the keys' side leaves is what the table's side takes -/
theorem junction2 (hW : A.n + 1 ≤ 2 ^ A.w) (P : A.St → (A.J → E) → Prop) (x : A.X4) (m : A.J → E) :
    ((A.ΨK P (oldK A.IK A.v' x) m ∧ RowsHold (rowsK A.IK A.v' x) m) ∧
      ((A.IK.setV (A.v' + 1)).topCl x).Holds
        (A.v' + 1) (A.IK.key (A.IK.st (oldK A.IK A.v' x)) m) m) ↔
    (A.ΨT P x m ∧ Bits A.Q.I.d A.Q.I.w (A.Q.I.bit m) ∧ A.Q.R.Holds x m) := by
  rw [← A.roots_iff hW x m]
  constructor
  · rintro ⟨⟨⟨⟨⟨hb, hn, hi⟩, hP⟩, hr2, hT, hO⟩, hr4⟩, hc⟩
    exact ⟨⟨⟨⟨hn, hP⟩, hr2⟩, hr4, hc⟩, hb, hi, hT, hO⟩
  · rintro ⟨⟨⟨⟨hn, hP⟩, hr2⟩, hr4, hc⟩, hb, hi, hT, hO⟩
    exact ⟨⟨⟨⟨⟨hb, hn, hi⟩, hP⟩, hr2, hT, hO⟩, hr4⟩, hc⟩

/-- the read-out -/
theorem out_iff (o : A.Q.XB) (m : A.J → E) :
    A.lk.out id id (A.rd o) m ↔
    (A.ΨT (fun _ _ => True) (A.Q.oldT o) m ∧ RowsHold (A.Q.rowsT o) m) := by
  have e : RowsHold (A.rd o).2.2 m ↔
      A.Num m ∧
      RowsHold (A.rows2 (A.o4 (A.Q.oldT o))) m ∧
      RowsHold (A.rows4 (A.Q.oldT o)) m ∧
      RowsHold (A.rowsB o) m := by
    show RowsHold
        (A.numRow :: (A.rows2 (A.o4 (A.Q.oldT o)) ++ (A.rows4 (A.Q.oldT o) ++ A.rowsB o))) m ↔
      _
    rw [rowsHold_cons, rowsHold_append, rowsHold_append, A.num_iff]
  constructor
  · rintro ⟨hc, hr, _⟩
    obtain ⟨hn, h2, h4, hB⟩ := e.mp hr
    exact ⟨⟨⟨⟨hn, trivial⟩, h2⟩, h4, hc⟩, hB⟩
  · rintro ⟨⟨⟨⟨hn, _⟩, h2⟩, h4, hc⟩, hB⟩
    exact ⟨hc, e.mpr ⟨hn, h2, h4, hB⟩, trivial⟩

end LkAsm
end LdLkp
end

section
variable (E : Type) [Field E] [Fintype E]

/-- an auxiliary lemma, under `hA`, `hMu` and for E of characteristic p: the chain before the
read-out is `Good` from the lookup claim to the joint written out below -/
theorem LdLkp.LkAsm.chain_good (p : ℕ) [CharP E p] (A : LkAsm E) (Mu : A.St → (A.J → E) → Prop)
    (Ex : ExtSpec) (Kc M Wp : Type) (R0 : Rels Kc A.St Ex (M × Wp)) (msg : M → A.J → E)
    (hA : A.H.lkb.Adm p) (hMu : A.H.MuOK Mu) :
    (A.chainA Ex M Wp Kc msg).Good (cj R0 msg id (A.lk.inP Mu) A.lk.inR)
      (cj R0 msg (fun o => (A.b2 (A.o4 (A.Q.oldT o))).1)
        (fun o m => A.ΨT Mu (A.Q.oldT o) m ∧ RowsHold (A.Q.rowsT o) m)
        fun o m => A.ΨT (fun _ _ => True) (A.Q.oldT o) m ∧ RowsHold (A.Q.rowsT o) m) := by
  have g1 := ldLkpHead_good E p A.H Mu Ex Kc M Wp R0 msg hA hMu
  have g2 := ldLkpSegK_good E A.IK A.v' A.tK Ex Kc A.St M Wp R0 msg (fun x => (A.b2 x).1)
    (A.ΨK Mu) (A.ΨK fun _ _ => True)
  have g3 := ldLkpSegT_good E A.Q Ex M Wp Kc A.St R0 msg (fun x => (A.b2 (A.o4 x)).1)
    (A.ΨT Mu) (A.ΨT fun _ _ => True)
  have e1 := ldLkpK_congr E Kc A.St M Wp A.J A.X2 Ex R0 msg (fun x => (A.b2 x).1)
    (fun x m =>
      ((A.H.Rest (A.b2 x) m ∧ Mu (A.b2 x).1 m) ∧ A.H.tie.Done A.n x.2 m) ∧
      A.H.tie.claim (A.n + 1) x m)
    (fun x m => (A.H.Rest (A.b2 x) m ∧ A.H.tie.Done A.n x.2 m) ∧ A.H.tie.claim (A.n + 1) x m)
    (fun x m =>
      A.ΨK Mu x m ∧
      keyProd (A.v' + 1) (A.IK.key (A.IK.st x) m) (A.IK.lam x) + ∑ j, A.fK x j * m j = A.tK x)
    (fun x m =>
      A.ΨK (fun _ _ => True) x m ∧
      keyProd (A.v' + 1) (A.IK.key (A.IK.st x) m) (A.IK.lam x) + ∑ j, A.fK x j * m j = A.tK x)
    (fun x m => A.junction1 Mu x m)
    (fun x m => Iff.trans (by simp only [and_true]) (A.junction1 (fun _ _ => True) x m))
  have e2 := ldLkpK_congr E Kc A.St M Wp A.J A.X4 Ex R0 msg (fun x => (A.b2 (A.o4 x)).1) _ _ _ _
    (fun x m => A.junction2 hA.1 Mu x m) (fun x m => A.junction2 hA.1 (fun _ _ => True) x m)
  have g12 : ((A.H.headA Ex M Wp Kc msg).seq (segK A.IK A.v' A.tK Ex M Wp Kc msg)).Good
      (cj R0 msg id (A.lk.inP Mu) A.lk.inR) _ :=
    segT_seq (e1 ▸ g1) g2
  exact segT_seq (e2 ▸ g12) g3

theorem ldLkpAsm_base : Spec.ldLkpAsm_base E := by
  intro p _ A Mu Ex Kc M Wp R0 msg hA hMu
  have g123 := A.chain_good E p Mu Ex Kc M Wp R0 msg hA hMu
  unfold BkA.Good at g123 ⊢
  refine goodAt_postMap Kc M _ _ _ Ex Ex Wp Wp _ _ _ _ _ _ _ A.rd g123 ?_ ?_ ?_ ?_
  · intro o y w h
    exact ⟨h.1, (A.out_iff o _).mpr ⟨⟨⟨⟨h.2.1.1.1.1, trivial⟩, h.2.1.1.2⟩, h.2.1.2⟩, h.2.2⟩⟩
  · exact fun _ _ h => h
  · exact fun _ => rfl
  · intro o y w _ h
    exact ⟨h.1, (A.out_iff o _).mp h.2⟩

theorem ldLkpAsm_ok : Spec.ldLkpAsm_ok E := by
  intro p _ A Mu S E₀ Kc Wp R0 msg hA hMu
  exact sigLift_goodB E S Kc _ _ Wp Wp E₀ E₀ _ _ _ _ _ _
    (ldLkpAsm_base E p A Mu E₀ Kc S.Msg Wp R0 msg hA hMu)

theorem ldLkpAsm_rounds : Spec.ldLkpAsm_rounds E := by
  intro A Ex M Wp Kc msg
  have e : (A.baseA Ex M Wp Kc msg).R.shape =
      ((A.H.headA Ex M Wp Kc msg).R.shape ++ (segK A.IK A.v' A.tK Ex M Wp Kc msg).R.shape) ++
        (A.Q.segT Ex Wp Kc msg).R.shape := rfl
  rw [e, List.length_append, List.length_append, ldLkpHead_rounds E A.H Ex M Wp Kc msg,
    ldLkpSegK_rounds E A.IK A.v' A.tK Ex M Wp Kc msg, ldLkpSegT_len E A.Q Ex M Wp Kc msg]
  rfl

end
end Cb
