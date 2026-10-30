-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Att/End/Seam.lean: what the chain of an attention sub-proof's own rounds claims at its start
gives the identities that the own rounds are there to prove, the join at the rule values, and the
test of the denominators at the lookup's point.

Statements and proofs. The chain is that of Cb/Pv/Att/OwnAt.lean. Its claim at its start (Ch.Todo)
says that there are further scalars of the first three sumchecks of which the three linear claims
hold, whose start values are the three sums, and so on (ownAt_todo). With the linear claims at their
meant value (Cb/Pv/Att/End/Hid.lean) every named scalar that the key forms read then has its rule
value as its hidden value.

Main names:
  OwnM P m: the identities at1 and at2 of the relation of the segment (idnVal in
    Inst/Model/Att/Trace.lean) are 0 at every valid index, on the cells of m.
  att_todo: the chain's claim at its start gives OwnM.
  ReadK D k: the named scalars that the key forms read.
  KF_congr: the key forms read no other.
  hid_rule: under the chain's claim at its start, with its further scalars, the hidden value of each
    such scalar is its rule value.
  att_seam: the chain's claim at its start gives OwnM, the join with the key forms at the rule
    values, and that the test of the denominators has the value 0 (denOut in
    Cb/Pv/Att/Mean/DenStep.lean).

Limits: that the key forms at the rule values are the extensions of the vectors of looked-up values
is not shown here. The places of the scalars are those for two plane messages: att_seam asks npl =
2. Nothing on an honest prover or on hiding.


-/
import Cb.Pv.Att.End.Hid
import Cb.Pv.Att.OwnAt
import Cb.Pv.Att.Mean.DenStep

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Att.End
open TWhole Cb Cb.Sub Finset Blocks
open Inst.Model Inst.Model.AttSeg

/-- The named scalars that the key forms read. -/
def ReadK (D : Dim) : KSc → Prop
  | .cell .m1 jj => jj < 3
  | .cell .d1 jj => jj < 3
  | .cell .m2 jj => jj < 5
  | .cell .d2 jj => jj < 5
  | .cell _ _ => False
  | .ib k => k < D.lT
  | _ => True

section Congr
variable {E : Type} [Field E] [scl : Scl] (D : Dim) (C : Calls) (p : Pub E) {v v' : KSc → E}
  (h : ∀ k, ReadK D k → v k = v' k)
include h

theorem DP_congr (r : Reg) : DP D C p v r = DP D C p v' r := by
  cases r with
  | M => simp only [DP, h (.ms .M) trivial, h (.ss .M) trivial]
  | D => simp only [DP, h (.ms .D) trivial, h (.ss .D) trivial]

omit scl in
theorem REM_congr : REM v = REM v' := by
  simp only [REM, h .acc trivial, h .zc trivial, h .zo trivial]

/-- The key forms read the scalars of ReadK alone. -/
theorem KF_congr (c : Fin 4) : KF D C p v c = KF D C p v' c := by
  match c with
  | 0 =>
    simp only [KF]
    refine sum_congr rfl fun u hu => ?_
    have hu' : u = .m1 ∨ u = .d1 := by simpa using hu
    rcases hu' with rfl | rfl
    · rw [h (.cell .m1 0) (show (0 : ℕ) < 3 by norm_num),
        h (.cell .m1 1) (show (1 : ℕ) < 3 by norm_num),
        h (.cell .m1 2) (show (2 : ℕ) < 3 by norm_num)]
    · rw [h (.cell .d1 0) (show (0 : ℕ) < 3 by norm_num),
        h (.cell .d1 1) (show (1 : ℕ) < 3 by norm_num),
        h (.cell .d1 2) (show (2 : ℕ) < 3 by norm_num)]
  | 1 =>
    simp only [KF]
    congr 1
    refine sum_congr rfl fun u hu => ?_
    have hu' : u = .m2 ∨ u = .d2 := by simpa using hu
    rcases hu' with rfl | rfl
    · rw [DP_congr D C p h, h (.cell .m2 0) (show (0 : ℕ) < 5 by norm_num),
        h (.cell .m2 1) (show (1 : ℕ) < 5 by norm_num),
        h (.cell .m2 2) (show (2 : ℕ) < 5 by norm_num),
        h (.cell .m2 3) (show (3 : ℕ) < 5 by norm_num),
        h (.cell .m2 4) (show (4 : ℕ) < 5 by norm_num)]
    · rw [DP_congr D C p h, h (.cell .d2 0) (show (0 : ℕ) < 5 by norm_num),
        h (.cell .d2 1) (show (1 : ℕ) < 5 by norm_num),
        h (.cell .d2 2) (show (2 : ℕ) < 5 by norm_num),
        h (.cell .d2 3) (show (3 : ℕ) < 5 by norm_num),
        h (.cell .d2 4) (show (4 : ℕ) < 5 by norm_num)]
  | 2 =>
    have es : ∑ k ∈ range D.lT, (2 : E) ^ k * v (.ib k) = ∑ k ∈ range D.lT, 2 ^ k * v' (.ib k) :=
      sum_congr rfl fun k hk => by rw [h (.ib k) (show k < D.lT from mem_range.mp hk)]
    simp only [KF]
    rw [REM_congr D h, h .rh trivial, h .rh' trivial, h .zc trivial, es]
  | 3 =>
    simp only [KF]
    rw [h .rg trivial, h .rg' trivial]

end Congr

section Own
variable {E M X : Type} [Field E] [Fintype E] (P : OwnPar E M X)

/-- The identities that the own rounds are there to prove. -/
def OwnM (m : M) : Prop :=
  (∀ k b g i, (Idn.at1 k b g i).Valid P.D → idnVal P.D (P.tOf m) (.at1 k b g i) = 0) ∧
    ∀ b g i, (Idn.at2 b g i).Valid P.D → idnVal P.D (P.tOf m) (.at2 b g i) = 0

/-- The chain's claim at its start gives these identities. -/
theorem att_todo (hK : P.D.lT ≤ 2 ^ P.kap) (x : X) (m : M)
    (h : (P.own (theMeans E P.D P.C P.kap)).ch.Todo x m) : OwnM P m := by
  obtain ⟨rM, -, -, -, rD, -, -, -, rE, -, -, -, -, h1, h2⟩ := (ownAt_todo P x m).mp h
  exact ⟨at1_of_cubeT P.D (P.tOf m) P.kap hK fun b hb X hX => h2 ⟨b, hb⟩ X hX,
    at2_of_cubeG P.D (P.tOf m) fun b hb Y hY => h1 ⟨b, hb⟩ Y hY⟩

variable {P}

/-- The hidden value of each named scalar that the key forms read is its rule value, if the linear
claims hold, the three sums are the hidden start values, and the rule value of ACC is the hidden
ACC. -/
theorem hid_rule (hn : P.npl = 2) (x : X) (m : M) (rM : Fin (3 * P.npl + 7) → E) (rD : Fin 7 → E)
    (rE : Fin (5 + P.D.lT + 2) → E) (hM : LMat P (x, []) rM m)
    (hD : LDat P (x, [List.ofFn rM]) rD m)
    (hE : RuleAt P.D P.C (nameE P.D) rE P.kE (P.pub0 (x, [List.ofFn rM, List.ofFn rD])) (P.tOf m)
      (P.msg m))
    (sM : sumPhi P.D P.C (P.pub0 (x, [])) (P.tOf m) .s6b =
      rM (Fin.last _) - P.msg m (P.kM (Fin.last _)))
    (sD : sumPhi P.D P.C (P.pub0 (x, [List.ofFn rM])) (P.tOf m) .s6d =
      rD (Fin.last _) - P.msg m (P.kD (Fin.last _)))
    (sE : sumPhi P.D P.C (P.pub0 (x, [List.ofFn rM, List.ofFn rD])) (P.tOf m) .s8 =
      rE P.iZO - P.msg m (P.kE P.iZO))
    (sA : rv P.D P.C (pubOfZ E (P.zOf x)) (P.tOf m) .acc = rE P.iACC - P.msg m (P.kE P.iACC))
    (k : KSc) (hk : ReadK P.D k) :
    hidV P (x, [List.ofFn rM, List.ofFn rD]) rE m k =
      rv P.D P.C (pubOfZ E (P.zOf x)) (P.tOf m) k := by
  have aM : ∀ (j : ℕ) (hj : j < 3 * P.npl + 7) (k' : KSc), nameM j = some k' →
      hv (List.ofFn rM) P.kM (P.msg m) j = rv P.D P.C (pubOfZ E (P.zOf x)) (P.tOf m) k' :=
    fun j hj k' hn' => (hv_ofFn rM P.kM (P.msg m) ⟨j, hj⟩).trans (hM ⟨j, hj⟩ k' hn')
  have aD : ∀ (j : ℕ) (hj : j < 7) (k' : KSc), nameD j = some k' →
      hv (List.ofFn rD) P.kD (P.msg m) j = rv P.D P.C (pubOfZ E (P.zOf x)) (P.tOf m) k' :=
    fun j hj k' hn' => (hv_ofFn rD P.kD (P.msg m) ⟨j, hj⟩).trans (hD ⟨j, hj⟩ k' hn')
  have aE : ∀ (j : ℕ) (hj : j < 5 + P.D.lT + 2) (k' : KSc), nameE P.D j = some k' →
      hv (List.ofFn rE) P.kE (P.msg m) j = rv P.D P.C (pubOfZ E (P.zOf x)) (P.tOf m) k' :=
    fun j hj k' hn' => (hv_ofFn rE P.kE (P.msg m) ⟨j, hj⟩).trans (hE ⟨j, hj⟩ k' hn')
  cases k with
  | cell u jj =>
    cases u with
    | m1 =>
      have hjj : jj < 3 := hk
      exact aM jj (by omega) _ (by unfold nameM; rw [if_pos hjj])
    | d1 =>
      have hjj : jj < 3 := hk
      exact aM (3 + jj) (by omega) _ (by
        unfold nameM
        rw [if_neg (by omega), if_pos (by omega), Nat.add_sub_cancel_left])
    | m2 =>
      have hjj : jj < 5 := hk
      exact aM (6 + jj) (by omega) _ (by
        unfold nameM
        rw [if_neg (by omega), if_neg (by omega), Nat.add_sub_cancel_left]
        interval_cases jj <;> rfl)
    | d2 =>
      have hjj : jj < 5 := hk
      exact aD jj (by omega) _ (by
        unfold nameD
        interval_cases jj <;> rfl)
    | w3 => exact hk.elim
    | x3 => exact hk.elim
    | f4 => exact hk.elim
  | ms r =>
    cases r with
    | M => exact aM 11 (by omega) _ rfl
    | D => exact aD 5 (by omega) _ rfl
  | ss r =>
    cases r with
    | M =>
      have e : (⟨12, by omega⟩ : Fin (3 * P.npl + 7)) = Fin.last _ := Fin.ext (by
        show 12 = 3 * P.npl + 6
        omega)
      refine (hv_ofFn rM P.kM (P.msg m) ⟨12, by omega⟩).trans ?_
      rw [e]
      exact sM.symm
    | D => exact (hv_ofFn rD P.kD (P.msg m) ⟨6, by omega⟩).trans sD.symm
  | acc => exact (hv_ofFn rE P.kE (P.msg m) ⟨0, by omega⟩).trans sA.symm
  | zo => exact (hv_ofFn rE P.kE (P.msg m) ⟨1, by omega⟩).trans sE.symm
  | zc => exact aE 2 (by omega) _ (by simp [nameE])
  | rh => exact aE 3 (by omega) _ (by simp [nameE])
  | rh' => exact aE 4 (by omega) _ (by simp [nameE])
  | ib j =>
    have hj : j < P.D.lT := hk
    exact aE (5 + j) (by omega) _ (by
      unfold nameE
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
        if_pos (by omega), Nat.add_sub_cancel_left])
  | rg =>
    exact aE (5 + P.D.lT) (by omega) _ (by
      unfold nameE
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
        if_neg (by omega), if_pos rfl])
  | rg' =>
    exact aE (5 + P.D.lT + 1) (by omega) _ (by
      unfold nameE
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
        if_neg (by omega), if_neg (by omega), if_pos rfl])

/-- What the chain's claim at its start gives the lookup's side. hLM, hLD, hLE: the three free
linear claims of P are those of Cb/Pv/Att/End/Hid.lean. -/
theorem att_seam (Q : JoinLay P) (hn : P.npl = 2) (hK : P.D.lT ≤ 2 ^ P.kap)
    (hLM : ∀ x r m, P.LM x r m ↔ LMat P x r m) (hLD : ∀ x r m, P.LD x r m ↔ LDat P x r m)
    (hLE : ∀ x r m, P.LE x r m ↔ LEat P Q x r m) (x : X) (m : M)
    (h : (P.own (theMeans E P.D P.C P.kap)).ch.Todo x m) :
    OwnM P m ∧
      joinVal (Q.q x) (KF (scl := Q.scl) P.D P.C (pubOfZ E (P.zOf x))
        (rv P.D P.C (pubOfZ E (P.zOf x)) (P.tOf m))) ((Q.ce x).val (P.msg m)) = 0 ∧
      denOut P.D P.C (P.zOf x) (P.tOf m) = 0 := by
  refine ⟨att_todo P hK x m h, ?_⟩
  obtain ⟨rM, lM, sM, -, rD, lD, sD, -, rE, lE, sE, -, ⟨sA, sC⟩, -, -⟩ := (ownAt_todo P x m).mp h
  obtain ⟨lE1, lE2⟩ := (hLE _ _ _).mp lE
  have hr := hid_rule hn x m rM rD rE ((hLM _ _ _).mp lM) ((hLD _ _ _).mp lD) lE1 sM sD sE sA
  constructor
  · have e : KF (scl := Q.scl) P.D P.C (pubOfZ E (P.zOf x))
        (rv P.D P.C (pubOfZ E (P.zOf x)) (P.tOf m)) =
        KF (scl := Q.scl) P.D P.C (P.pub0 (x, [List.ofFn rM, List.ofFn rD]))
          (hidV P (x, [List.ofFn rM, List.ofFn rD]) rE m) :=
      funext fun c => (KF_congr (scl := Q.scl) P.D P.C _ hr c).symm
    rw [e]
    exact lE2
  · rw [denOut_split, sub_eq_zero]
    have z2 := lE1 P.iZC .zc (by simp [nameE, OwnPar.iZC])
    exact z2.symm.trans sC.symm

end Own

end Cb.Pv.Att.End

#print axioms Cb.Pv.Att.End.KF_congr
#print axioms Cb.Pv.Att.End.att_todo
#print axioms Cb.Pv.Att.End.att_seam
