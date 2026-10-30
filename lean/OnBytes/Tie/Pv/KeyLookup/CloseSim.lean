-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Tie/Pv/KeyLookup/CloseSim.lean: under equality weights with a degree for each variable, what
the sumcheck over the field computes is what the plain functions of CloseRun.lean compute.

The sumcheck over the field (`PscF`, OnBytes/Slice/KeyPscRun.lean) is a text of the program's
sumcheck, over the field. That the program's run, read in the field, is what it computes is shown in
files that are not in this library yet.

It imports OnBytes/Tie/Pv/KeyLookup/PortSim.lean (`rdMF`: a mask form as a function on the entries;
the rules for `PscF.hidingWalk` and `PscF.Weight.complete` under equality weights), CloseRun.lean
(`Clo.hidM`, `Clo.finM`) and PscIdx.lean (`Cf.portIdx`).
Main names:
  `claim_finM`    the running claim over the field behind k rounds (`PscF.claimAfter`) is `Clo.finM`
                  of the flat rounds, if there are k rounds and round i sends as many scalars as its
                  variable's degree.
  `walk_hidM`     for k + 1 variables: the fresh mask entries with the weights of
                  `PscF.hidingWalk`, read by `rdMF`, are `Clo.hidM`, under three conditions: there
                  are k + 1 challenges; there are at least 1 + Σ (degrees) fresh entries; the place
                  of the name i is the fresh entry number `Cf.portIdx i`.
Limits: statements on lists over the field. Nothing on the program's blocks on machine words.

-/
import OnBytes.Tie.Pv.KeyLookup.PortSim
import Cb.Pv.KeyLookup.CloseRun
import Cb.Pv.KeyLookup.PscIdx

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lk6.Clo

open OnBytes OnBytes.Slice Flat Cb Cb.LdLkp Finset Lk6.PortSim

/-! ### sums over the members of a list -/

theorem sum_getD (q : List GE) : ∑ t : Fin q.length, q.getD t.val 0 = q.sum := by
  induction q with
  | nil => rfl
  | cons a q ih =>
    show ∑ t : Fin (q.length + 1), (a :: q).getD t.val 0 = _
    rw [Fin.sum_univ_succ, List.sum_cons, ← ih]
    rfl

theorem sum_getD' (q : List GE) (n : ℕ) (h : q.length = n) :
    ∑ t : Fin n, q.getD t.val 0 = q.sum := by
  subst h
  exact sum_getD q

theorem poly_getD (g : GE) (q : List GE) :
    ∑ t : Fin q.length, q.getD t.val 0 * g ^ (t.val + 1) = PscF.polyAt q g * g := by
  induction q with
  | nil =>
    show (0 : GE) = 0 * g
    rw [zero_mul]
  | cons a q ih =>
    show ∑ t : Fin (q.length + 1), (a :: q).getD t.val 0 * g ^ (t.val + 1) = _
    rw [Fin.sum_univ_succ, PscF.polyAt_cons]
    have e : ∑ t : Fin q.length, (a :: q).getD t.succ.val 0 * g ^ (t.succ.val + 1) =
        (∑ t : Fin q.length, q.getD t.val 0 * g ^ (t.val + 1)) * g := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun t _ => ?_
      show q.getD t.val 0 * g ^ (t.val + 1 + 1) = _
      ring
    rw [e, ih]
    show a * g ^ (0 + 1) + _ = _
    ring

theorem poly_getD' (g : GE) (q : List GE) (n : ℕ) (h : q.length = n) :
    ∑ t : Fin n, q.getD t.val 0 * g ^ (t.val + 1) = PscF.polyAt q g * g := by
  subst h
  exact poly_getD g q

/-! ### the running claim -/

theorem claim_finM : ∀ (k : ℕ) (dg : Fin k → ℕ) (z : Fin k → GE) (σ : GE)
    (rs : List (List GE × GE)), rs.length = k →
    (∀ i : Fin k, (rs.getD i.val ([], 0)).1.length = dg i) →
    PscF.claimAfter (List.ofFn fun i => PscF.Weight.equality (z i) (dg i + 1)) rs σ =
      Clo.finM k dg z σ (rs.map fun r => (r.1, [r.2]))
  | 0, _, _, _, [], _, _ => by
    rw [List.ofFn_zero]
    rfl
  | 0, _, _, _, _ :: _, h, _ => absurd h (by simp)
  | _ + 1, _, _, _, [], h, _ => absurd h (by simp)
  | k + 1, dg, z, σ, (q, g) :: rs, hl, hq => by
    have h0 : q.length = dg 0 := hq 0
    rw [List.ofFn_succ]
    show PscF.claimAfter
      (List.ofFn fun i : Fin k => PscF.Weight.equality (z i.succ) (dg i.succ + 1))
      rs (PscF.polyAt ((PscF.Weight.equality (z 0) (dg 0 + 1)).complete q σ) g) = _
    rw [complete_eq (z 0) (dg 0 + 1) q σ (by omega), PscF.polyAt_cons,
      claim_finM k (fun i => dg i.succ) (fun i => z i.succ) _ rs (by simpa using hl)
        fun i => hq i.succ]
    show _ = Clo.finM k (fun i => dg i.succ) (fun i => z i.succ)
      (σ - z 0 * (∑ t : Fin (dg 0), q.getD t.val 0) +
        ∑ t : Fin (dg 0), q.getD t.val 0 * g ^ (t.val + 1)) (rs.map fun r => (r.1, [r.2]))
    rw [sum_getD' q _ h0, poly_getD' g q _ h0]
    exact congrArg (fun s => Clo.finM k (fun i => dg i.succ) (fun i => z i.succ) s
      (rs.map fun r => (r.1, [r.2])))
      (show PscF.polyAt q g * g + (σ - z 0 * q.sum) = σ - z 0 * q.sum + PscF.polyAt q g * g by ring)

/-! ### the form on the coefficients of the hiding polynomial -/

variable {J : Type} [DecidableEq J] (sl : Slot → J)

theorem zip_append_right {α β : Type} : ∀ (a b : List β) (fr : List α), a.length ≤ fr.length →
    fr.zip (a ++ b) = fr.zip a ++ (fr.drop a.length).zip b
  | [], _, _, _ => by simp
  | _ :: _, _, [], h => absurd h (by simp)
  | x :: a, b, s :: fr, h =>
    congrArg (List.cons (s, x)) (zip_append_right a b fr (by simpa using h))

theorem getD_drop {α : Type} (l : List α) (n i : ℕ) (d : α) :
    (l.drop n).getD i d = l.getD (n + i) d := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_drop]

theorem rdMF_pows (j : J) : ∀ (n : ℕ) (fr : List Slot) (c g : GE), n ≤ fr.length →
    rdMF sl (fr.zip (PscF.powers c g n)) j =
      ∑ t : Fin n, Parts.one (sl (fr.getD t.val default)) (c * g ^ t.val) j
  | 0, fr, c, g, _ => by
    rw [PscF.powers_zero, List.zip_nil_right]
    rfl
  | _ + 1, [], _, _, h => absurd h (by simp)
  | n + 1, s :: fr, c, g, h => by
    rw [PscF.powers_succ, List.zip_cons_cons, rdMF_cons,
      rdMF_pows j n fr (c * g) g (by simpa using h), Fin.sum_univ_succ]
    show Parts.one (sl s) c j + _ = Parts.one (sl s) (c * g ^ 0) j +
      ∑ t : Fin n, Parts.one (sl (fr.getD t.val default)) (c * g ^ (t.val + 1)) j
    rw [pow_zero, mul_one]
    refine congrArg _ (Finset.sum_congr rfl fun t _ => ?_)
    rw [show c * g * g ^ t.val = c * g ^ (t.val + 1) by ring]

theorem allEq_zip {k : ℕ} (z : Fin k → GE) (d : Fin k → ℕ) (cs : List GE) :
    AllEq ((List.ofFn fun i => PscF.Weight.equality (z i) (d i)).zip cs) := fun p hp => by
  have h1 := (List.of_mem_zip hp).1
  obtain ⟨i, hi⟩ := (List.mem_ofFn' _ _).1 h1
  rw [← hi]
  rfl

theorem walk_hidM (j : J) : ∀ (k : ℕ) (dg : Fin (k + 1) → ℕ) (z : Fin (k + 1) → GE) (cs : List GE)
    (fr : List Slot) (w : PIdx (pfMix GE (k + 1) dg) → J), cs.length = k + 1 →
    1 + ∑ i, dg i ≤ fr.length →
    (∀ i, w i = sl (fr.getD (Cf.portIdx (pfMix GE (k + 1) dg) i) default)) →
    rdMF sl (fr.zip (PscF.hidingWalk
      ((List.ofFn fun i => PscF.Weight.equality (z i) (dg i + 1)).zip cs)).1) j =
      Clo.hidM (k + 1) dg w (fun i => cs.getD i 0) j
  | 0, dg, z, [g], s :: fr, w, _, hf, hw => by
    have hn : dg 0 ≤ fr.length := by
      have : 1 + dg 0 ≤ fr.length + 1 := by simpa using hf
      omega
    have e : (List.ofFn fun i : Fin 1 => PscF.Weight.equality (z i) (dg i + 1)).zip [g] =
        [(PscF.Weight.equality (z 0) (dg 0 + 1), g)] := by
      rw [List.ofFn_succ, List.ofFn_zero]
      rfl
    rw [e, walk_one]
    show rdMF sl ((s :: fr).zip (PscF.powers 1 g (dg 0 + 1))) j = _
    rw [PscF.powers_succ, List.zip_cons_cons, rdMF_cons, rdMF_pows sl j (dg 0) fr (1 * g) g hn]
    show _ = (∑ t : Fin (dg 0), Lev.one (w (.inl t)) (g ^ (t.val + 1)) j) +
      Lev.one (w (.inr ())) 1 j
    rw [hw (.inr ()), add_comm]
    refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun t _ => ?_) rfl
    rw [hw (.inl t)]
    show Parts.one (sl (fr.getD t.val default)) (1 * g * g ^ t.val) j =
      Parts.one (sl ((s :: fr).getD (1 + t.val) default)) (g ^ (t.val + 1)) j
    rw [Nat.add_comm 1 t.val, show (1 : GE) * g * g ^ t.val = g ^ (t.val + 1) by ring]
    rfl
  | 0, _, _, [], _, _, h, _, _ => absurd h (by simp)
  | 0, _, _, _ :: _ :: _, _, _, h, _, _ => absurd h (by simp)
  | 0, _, _, [_], [], _, _, h, _ => absurd h (by simp)
  | _ + 1, _, _, [], _, _, h, _, _ => absurd h (by simp)
  | k + 1, dg, z, g :: cs, fr, w, hl, hf, hw => by
    have hs : ∑ i, dg i = dg 0 + ∑ i : Fin (k + 1), dg i.succ := Fin.sum_univ_succ dg
    have hn : dg 0 ≤ fr.length := by omega
    have hl' : cs.length = k + 1 := by simpa using hl
    obtain ⟨p, l, hpl⟩ : ∃ p l, (List.ofFn fun i : Fin (k + 1) =>
        PscF.Weight.equality (z i.succ) (dg i.succ + 1)).zip cs = p :: l := by
      obtain ⟨g', cs', rfl⟩ : ∃ g' cs', cs = g' :: cs' := by
        cases cs with
        | nil => exact absurd hl' (by simp)
        | cons a b => exact ⟨a, b, rfl⟩
      rw [List.ofFn_succ]
      exact ⟨_, _, rfl⟩
    have hlen : 1 + ∑ i : Fin (k + 1), (fun i : Fin (k + 1) => dg i.succ) i ≤
        (fr.drop (dg 0)).length := by
      rw [List.length_drop]
      show 1 + ∑ i : Fin (k + 1), dg i.succ ≤ _
      omega
    have hA : AllEq (p :: l) := hpl ▸ allEq_zip (fun i => z i.succ) (fun i => dg i.succ + 1) cs
    rw [List.ofFn_succ, List.zip_cons_cons, hpl, walk_cons _ g p l hA, ← hpl]
    show rdMF sl (fr.zip (PscF.powers g g (dg 0) ++ _)) j = _
    rw [zip_append_right _ _ fr (by rw [PscF.powers_length]; exact hn), rdMF_append,
      PscF.powers_length, rdMF_pows sl j (dg 0) fr g g hn,
      walk_hidM j k (fun i => dg i.succ) (fun i => z i.succ) cs (fr.drop (dg 0))
        (fun i => w (.inr i)) hl' hlen fun i => by
          show w (.inr i) = _
          rw [hw (.inr i), getD_drop]
          rfl]
    show _ = (∑ t : Fin (dg 0), Lev.one (w (.inl t)) (g ^ (t.val + 1)) j) +
      Clo.hidM (k + 1) (fun i => dg i.succ) (fun i => w (.inr i)) (fun i => cs.getD i 0) j
    refine congrArg (· + _) (Finset.sum_congr rfl fun t _ => ?_)
    rw [hw (.inl t), show g * g ^ t.val = g ^ (t.val + 1) by ring]
    rfl

end Lk6.Clo

#print axioms Lk6.Clo.claim_finM
#print axioms Lk6.Clo.walk_hidM
