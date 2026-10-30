-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLkpAsm2ErrProofs.lean: the proofs of the statements of Cb/Ld/LdLkpAsm2Err.lean (the
assembled lookup, `LkAsm2` (Cb/Ld/LdLkpAsm2.lean): errors, numbers of values, the number of rounds
in closed form).

The theorems are "ldLkpAsm2E_* : Cb.Spec.ldLkpAsm2E_*"; the general auxiliary definitions and lemmas
are those of Cb/Ld/LdLkpAsmErrProofs.lean (`LL`, ll_*, f2_*), with one more block: a sumcheck where
no map is revealed (`ll_core`; `PscPar.core`, Cb/Ld/LdPsc.lean), and three lemmas on sums and counts
(`sum_add_choose`, `flat_count`, `pscVals_one`). `LL b es vs`: the block b has the errors es and the
numbers of values vs.

Main names (statements and hypotheses: Cb/Ld/LdLkpAsm2Err.lean):
  `ldLkpAsm2E_errs`, `ldLkpAsm2E_vals`, `ldLkpAsm2E_sub`: the two lists, at the base and over a
    signature.
  `ldLkpAsm2E_len`, `ldLkpAsm2E_closed`: the number of rounds.
  `ldLkpAsm2E_last`: the rounds in which the verifier sends nothing.
  `ldLkpAsm2E_small`: every error against its number of values.
-/
import Cb.Ld.LdLkpAsm2Err
import Cb.Ld.LdLkpAsm2PullProofs
import Cb.Ld.LdLkpAsmErrProofs

set_option autoImplicit false

namespace Cb
open Iop IOR Hiop Prob Cb.LdLkp

namespace LdLkp
variable {E : Type} [Field E] [Fintype E]

/-- One sumcheck, where no map is revealed (`PscPar.core`, Cb/Ld/LdPsc.lean). -/
theorem ll_core (Y : PscPar E) (k n : ℕ) (hf : Y.fmt = List.replicate k (pfCube E n))
    (Ex : ExtSpec) (Kc : Type) :
    (Y.numsC Ex Kc).err.toList = coreErrs k n ∧
    (Y.core Ex).shape.chalList = coreVals (Fintype.card E) k := by
  constructor
  · show 1 :: (pErr Y.fmt).toList = _
    rw [pErr_list, hf]
    simp [coreErrs]
  · show Fintype.card E :: (pRounds Y.fmt).chalList = _
    rw [pRounds_list, hf]
    simp [coreVals]

namespace LkAsm2
variable (A : LkAsm2 E) (Ex : ExtSpec) (M Wp Kc : Type) (msg : M → A.J → E)

theorem ll_root :
    LL (A.R.rootA Ex M Wp Kc) [A.w * Fintype.card E ^ (A.w - 1)] [Fintype.card E ^ A.w] := by
  refine ⟨?_, ?_⟩
  · show [A.R.toIn.ev.err] = _
    rw [ldLkpRoot_err E A.R]
    rfl
  · show [Fintype.card (Fin (A.w + 0) → E)] = _
    simp

theorem ll_forest :
    ∀ l, LL (A.forest Ex M Wp Kc msg l)
      (((List.range (A.v' + 1)).flatMap fun l => pscErrs (0 + l) 2 2 ++ [1]) ++
        (List.range l).flatMap fun l => pscErrs (A.w + l) 2 2 ++ [1])
      (((List.range (A.v' + 1)).flatMap fun l =>
          pscVals (Fintype.card E) (0 + l) ++ [Fintype.card E]) ++
        (List.range l).flatMap fun l => pscVals (Fintype.card E) (A.w + l) ++ [Fintype.card E])
  | 0 => by
    have h := ll_postM (ll_segK A.IK A.v' (fun x => A.tK (A.oR x)) Ex M Wp Kc msg) A.enterT
    simpa using h
  | l + 1 => by
    have hl : LL (A.D.levA Ex Wp Kc msg l) (pscErrs (A.w + l) 2 2 ++ [1])
        (pscVals (Fintype.card E) (A.w + l) ++ [Fintype.card E]) :=
      ll_lev A.D Ex M Wp Kc msg l
    have h := ll_seq (ll_forest l) hl
    rw [List.range_succ (n := l), List.flatMap_append, List.flatMap_append]
    simpa [List.append_assoc] using h

theorem ll_end :
    LL (A.endA Ex M Wp Kc msg) (coreErrs (A.w + A.d) 2) (coreVals (Fintype.card E) (A.w + A.d)) :=
  ll_core A.En.par (A.w + A.d) 2 rfl Ex Kc

theorem ll_bit :
    LL (A.bitA Ex M Wp Kc msg)
      ([(A.w + A.d) * Fintype.card E ^ (A.w + A.d - 1)] ++ pscErrs (A.w + A.d) 2 2)
      ([Fintype.card E ^ (A.w + A.d)] ++ pscVals (Fintype.card E) (A.w + A.d)) := by
  have h1 : LL
      (⟨IOR.draw A.Bt.zc.toIn.ev.D A.Bt.zc.toIn.nxX Ex,
        Honest.draw A.Bt.zc.toIn.ev.D A.Bt.zc.toIn.nxX Ex (M × Wp),
        Nums.draw Kc A.Bt.zc.toIn.ev.D A.Bt.zc.toIn.nxX Ex A.Bt.zc.toIn.ev.err⟩ :
        BkA Kc M A.XE (E × A.Bt.zc.next.St) Ex Wp)
      [(A.w + A.d) * Fintype.card E ^ (A.w + A.d - 1)] [Fintype.card E ^ (A.w + A.d)] := by
    refine ⟨?_, ?_⟩
    · show [A.Bt.zc.toIn.ev.err] = _
      rw [ldLkpBit_err E A.Bt]
      rfl
    · show [Fintype.card (Unit × (Fin (A.w + A.d) → E))] = _
      simp
  have h2 : LL
      (⟨A.Bt.zc.next.par.psc Ex,
        A.Bt.zc.next.par.hon Ex fun w : M × Wp => msg w.1,
        A.Bt.zc.next.par.nums Ex Kc⟩ : BkA Kc M (E × A.Bt.zc.next.St) A.XB Ex Wp)
      (pscErrs (A.w + A.d) 2 2) (pscVals (Fintype.card E) (A.w + A.d)) :=
    ll_psc A.Bt.zc.next (A.w + A.d) 2 rfl Ex Kc
  exact ll_seq h1 h2

theorem ll_baseN (N : Type) (ι : N → A.J) :
    LL (A.baseN ι Ex M Wp Kc msg) (A.errs (Fintype.card E)) (A.vals (Fintype.card E)) :=
  ll_postM (ll_seq
    (ll_seq (ll_seq (ll_seq (ll_head A.H Ex M Wp Kc msg) (A.ll_root Ex M Wp Kc))
        (A.ll_forest Ex M Wp Kc msg A.d))
      (A.ll_end Ex M Wp Kc msg))
    (A.ll_bit Ex M Wp Kc msg)) (A.rdN ι)

end LkAsm2

theorem coreErrs_len (k n : ℕ) : (coreErrs k n).length = k + 1 := by simp [coreErrs]
theorem coreVals_len (q k : ℕ) : (coreVals q k).length = k + 1 := by simp [coreVals]

theorem f2_core (k n q : ℕ) (h1 : 1 < q) (hn : n < q) :
    List.Forall₂ (· < ·) (coreErrs k n) (coreVals q k) :=
  List.Forall₂.cons h1 (f2_rep n q hn k)

/-- the sum of l + c over l < n -/
theorem sum_add_choose (c : ℕ) : ∀ n, ∑ l ∈ Finset.range n, (l + c) = n.choose 2 + c * n
  | 0 => by simp
  | n + 1 => by
    rw [Finset.sum_range_succ, sum_add_choose c n, Nat.choose_succ_succ' n 1, Nat.choose_one_right]
    ring

theorem flat_count (f : ℕ → List ℕ) (a : ℕ) :
    ∀ n, ((List.range n).flatMap f).count a = ∑ l ∈ Finset.range n, (f l).count a
  | 0 => rfl
  | n + 1 => by rw [List.range_succ, List.flatMap_append, List.count_append, flat_count f a n, Finset.sum_range_succ]; simp

theorem pscVals_one (q k : ℕ) (hq : 2 < q) : (pscVals q k).count 1 = 1 := by
  have h1 : q ≠ 1 := by omega
  have h2 : q - 1 ≠ 1 := by omega
  simp [pscVals, List.count_append, List.count_replicate, h1, h2]

theorem coreVals_one (q k : ℕ) (hq : 2 < q) : (coreVals q k).count 1 = 0 := by
  have h1 : q ≠ 1 := by omega
  simp [coreVals, List.count_replicate, h1]

end LdLkp

section
variable (E : Type) [Field E] [Fintype E]

theorem ldLkpAsm2E_errs : Spec.ldLkpAsm2E_errs E := fun A N ι Ex M Wp Kc msg =>
  (A.ll_baseN Ex M Wp Kc msg N ι).1
theorem ldLkpAsm2E_vals : Spec.ldLkpAsm2E_vals E := fun A N ι Ex M Wp Kc msg =>
  (A.ll_baseN Ex M Wp Kc msg N ι).2

theorem ldLkpAsm2E_sub : Spec.ldLkpAsm2E_sub E :=
  ⟨fun A N ι S E₀ Kc Wp msg => A.ll_baseN E₀ S.Msg Wp Kc msg N ι,
    fun A N ι C S msg => A.ll_baseN C.E0 (C.Msg × S.Msg) Unit Unit msg N ι⟩

theorem ldLkpAsm2E_len : Spec.ldLkpAsm2E_len E := by
  intro A q
  have hE : (A.errs q).length =
      (1 + 3 * (A.n + 1)) + 1 +
        ((∑ l ∈ Finset.range (A.v' + 1), (0 + l + 3 + 1)) +
          ∑ l ∈ Finset.range A.d, (A.w + l + 3 + 1)) +
        (A.w + A.d + 1) + (1 + (A.w + A.d + 3)) := by
    unfold LkAsm2.errs
    simp only [List.length_append, flat_len, pscErrs_len, coreErrs_len, List.length_cons,
      List.length_nil, Finset.sum_const, Finset.card_range, smul_eq_mul, Nat.zero_add]
    omega
  have hV : (A.vals q).length =
      (1 + 3 * (A.n + 1)) + 1 +
        ((∑ l ∈ Finset.range (A.v' + 1), (0 + l + 3 + 1)) +
          ∑ l ∈ Finset.range A.d, (A.w + l + 3 + 1)) +
        (A.w + A.d + 1) + (1 + (A.w + A.d + 3)) := by
    unfold LkAsm2.vals
    simp only [List.length_append, flat_len, pscVals_len, coreVals_len, List.length_cons,
      List.length_nil, Finset.sum_const, Finset.card_range, smul_eq_mul, Nat.zero_add]
    omega
  exact ⟨hE.trans hV.symm, hE⟩

theorem ldLkpAsm2E_closed : Spec.ldLkpAsm2E_closed E := by
  intro A q
  rw [(ldLkpAsm2E_len E A q).2]
  have h1 : ∑ l ∈ Finset.range (A.v' + 1), (0 + l + 3 + 1) = (A.v' + 1).choose 2 + 4 * (A.v' + 1) :=
    (Finset.sum_congr rfl fun l _ => by omega).trans (sum_add_choose 4 (A.v' + 1))
  have h2 : ∑ l ∈ Finset.range A.d, (A.w + l + 3 + 1) = A.d.choose 2 + (A.w + 4) * A.d :=
    (Finset.sum_congr rfl fun l _ => by omega).trans (sum_add_choose (A.w + 4) A.d)
  rw [h1, h2]
  ring

theorem ldLkpAsm2E_last : Spec.ldLkpAsm2E_last E := by
  intro A q hq hw
  have h1 : q ≠ 1 := by omega
  have hw' : A.w ≠ 0 := Nat.pos_iff_ne_zero.1 hw
  unfold LkAsm2.vals
  simp only [List.count_append, flat_count, pscVals_one q _ hq, coreVals_one q _ hq,
    List.count_cons, List.count_nil, Finset.sum_const, Finset.card_range, smul_eq_mul]
  simp [h1, hw']
  omega

theorem ldLkpAsm2E_small : Spec.ldLkpAsm2E_small E := by
  intro A N ι Ex M Wp Kc msg hv hq hw
  rw [chainErr_small, (A.ll_baseN Ex M Wp Kc msg N ι).1, (A.ll_baseN Ex M Wp Kc msg N ι).2]
  have h1 : 1 < Fintype.card E := by omega
  have h2 : 2 < Fintype.card E := by omega
  have p1 : ∀ k, List.Forall₂ (· < ·) (pscErrs k 2 1) (pscVals (Fintype.card E) k) := fun k =>
    f2_psc k 2 1 _ h1 h2 (by omega)
  have p2 : ∀ k, List.Forall₂ (· < ·) (pscErrs k 2 2) (pscVals (Fintype.card E) k) := fun k =>
    f2_psc k 2 2 _ h1 h2 (by omega)
  have p3 : ∀ k, List.Forall₂ (· < ·) (pscErrs k 2 3) (pscVals (Fintype.card E) k) := fun k =>
    f2_psc k 2 3 _ h1 h2 (by omega)
  have hl : 2 ^ (A.v' + 1) - 1 < Fintype.card E := by
    have : 0 < 2 ^ (A.v' + 1) := Nat.two_pow_pos _
    omega
  exact f2_app
    (f2_app (f2_app
        (f2_app (f2_app (f2_one hl) (f2_app (p1 0) (f2_flat _ _ (fun _ => p3 0) A.n)))
          (f2_one (pt_lt A.w _ (by omega))))
        (f2_app (f2_flat _ _ (fun l => f2_app (p2 (0 + l)) (f2_one h1)) (A.v' + 1))
          (f2_flat _ _ (fun l => f2_app (p2 (A.w + l)) (f2_one h1)) A.d)))
      (f2_core (A.w + A.d) 2 _ h1 h2))
    (f2_app (f2_one (pt_lt (A.w + A.d) _ hw)) (p2 (A.w + A.d)))

end
end Cb
