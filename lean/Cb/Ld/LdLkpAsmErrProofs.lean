-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLkpAsmErrProofs.lean: the proofs of the statements of Cb/Ld/LdLkpAsmErr.lean (the errors of
the assembled lookup `LkAsm` (Cb/Ld/LdLkpAsm.lean) as one list). Before them auxiliary lemmas: the
two lists of two blocks in a row, of a chain, of a sumcheck, of the parts. `LL b es vs`: the block b
has the errors es and the numbers of values vs.
Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdLkpAsmErr
import Cb.Ld.LdLkpAsmPullProofs

set_option autoImplicit false

namespace Cb
open Iop IOR Hiop Prob Cb.LdLkp

namespace LdLkp

/-- the block has these errors and these numbers of values -/
def LL {K M X₁ X₂ : Type} {Ex : ExtSpec} {Wp : Type} (b : BkA K M X₁ X₂ Ex Wp) (es vs : List ℕ) :
    Prop :=
  b.P.err.toList = es ∧ b.R.shape.chalList = vs

section Gen
variable {K M X₁ X₂ X₃ : Type} {Ex : ExtSpec} {Wp : Type}

theorem ll_seq {a : BkA K M X₁ X₂ Ex Wp} {b : BkA K M X₂ X₃ Ex Wp} {e₁ v₁ e₂ v₂ : List ℕ}
    (h₁ : LL a e₁ v₁) (h₂ : LL b e₂ v₂) :
    LL (a.seq b) (e₁ ++ e₂) (v₁ ++ v₂) :=
  ⟨(Err.toList_app a.P.err b.P.err).trans (by rw [h₁.1, h₂.1]),
    (Shape.chalList_append a.R.shape b.R.shape).trans (by rw [h₁.2, h₂.2])⟩

theorem ll_chain (X : ℕ → Type) (b : ∀ l, BkA K M (X l) (X (l + 1)) Ex Wp)
    (e v : ℕ → List ℕ) (h : ∀ l, LL (b l) (e l) (v l)) :
    ∀ n, LL (BkA.chain X b n) ((List.range (n + 1)).flatMap e) ((List.range (n + 1)).flatMap v)
  | 0 => by
    have h0 := h 0
    simpa [LL, BkA.chain, List.range_succ] using h0
  | n + 1 => by
    have h1 := ll_seq (ll_chain X b e v h n) (h (n + 1))
    rw [List.range_succ (n := n + 1), List.flatMap_append, List.flatMap_append]
    simpa using h1

theorem ll_preM {b : BkA K M X₂ X₃ Ex Wp} {e v : List ℕ} (h : LL b e v) (φ : X₁ → X₂) :
    LL (b.preM φ) e v := h
theorem ll_postM {b : BkA K M X₁ X₂ Ex Wp} {e v : List ℕ} (h : LL b e v) (φ : X₂ → X₃) :
    LL (b.postM φ) e v := h

end Gen

theorem cardOf_any {α : Type} (i j : Fintype α) : @Fintype.card α i = @Fintype.card α j := by
  congr
  exact Subsingleton.elim _ _

section Psc
variable {E : Type} [Field E] [Fintype E]

omit [Fintype E] in
theorem pErr_list : ∀ l : List (PFmt E), (pErr l).toList = l.map fun f => f.n
  | [] => rfl
  | f :: l => congrArg (List.cons f.n) (pErr_list l)

omit [Fintype E] in
theorem pRounds_list : ∀ l : List (PFmt E), (pRounds l).chalList = l.map fun f => Fintype.card f.Ch
  | [] => rfl
  | f :: l => congrArg (List.cons (Fintype.card f.Ch)) (pRounds_list l)

theorem card_dummy (D : ℕ) : Fintype.card (pDummy E D).Ch = Fintype.card E - 1 := by
  classical
  show @Fintype.card {x : E // x ≠ 0} _ = _
  rw [cardOf_any _ inferInstance, Fintype.card_subtype_compl, Fintype.card_subtype_eq]

/-- One sumcheck. -/
theorem ll_psc (T : PscOur E) (k n : ℕ) (hf : T.fmt = List.replicate k (pfCube E n))
    (Ex : ExtSpec) (Kc : Type) :
    (T.par.nums Ex Kc).err.toList = pscErrs k n T.DY ∧
    (T.par.psc Ex).shape.chalList = pscVals (Fintype.card E) k := by
  have hfm : T.par.fmt = List.replicate k (pfCube E n) ++ [pDummy E T.DY] := by
    show T.fmt ++ [pDummy E T.DY] = _
    rw [hf]
  constructor
  · show (T.par.err Ex).toList = _
    refine (Err.toList_app (s := (T.par.core Ex).shape) (t := (T.par.ends Ex).shape)
      (T.par.errC Ex) (0, ())).trans ?_
    show (1 :: (pErr T.par.fmt).toList) ++ [0] = _
    rw [pErr_list, hfm]
    simp [pscErrs, pDummy]
  · show ((T.par.core Ex).shape ++ (T.par.ends Ex).shape).chalList = _
    refine (Shape.chalList_append (T.par.core Ex).shape (T.par.ends Ex).shape).trans ?_
    show (Fintype.card E :: (pRounds T.par.fmt).chalList) ++ [Fintype.card Unit] = _
    rw [pRounds_list, hfm]
    simp [pscVals, card_dummy]

end Psc
end LdLkp

section
variable (E : Type) [Field E] [Fintype E]

namespace LdLkp
variable {E}

theorem ll_draw {K M X X' : Type} (Ex : ExtSpec) (Wp : Type) (D : Type) [Fintype D] [Nonempty D]
    (nx : X → D → X') (e : ℕ) :
    LL (⟨IOR.draw D nx Ex,
        Honest.draw D nx Ex (M × Wp),
        Nums.draw K D nx Ex e⟩ : BkA K M X X' Ex Wp)
      [e] [Fintype.card D] := ⟨rfl, rfl⟩

theorem tree_fmt (D : TreeP E) (l : ℕ) :
    (D.lv l).T.fmt = List.replicate (D.g + l) (pfCube E 2) ∧ (D.lv l).T.DY = 2 := by
  cases l <;> exact ⟨rfl, rfl⟩

theorem ll_lev (D : TreeP E) (Ex : ExtSpec) (M Wp Kc : Type) (msg : M → D.J → E) (l : ℕ) :
    LL (D.levA Ex Wp Kc msg l) (pscErrs (D.g + l) 2 2 ++ [1])
      (pscVals (Fintype.card E) (D.g + l) ++ [Fintype.card E]) := by
  have h := ll_psc (D.lv l).T (D.g + l) 2 (tree_fmt D l).1 Ex Kc
  rw [(tree_fmt D l).2] at h
  exact ll_seq (a := D.pscA Ex Wp Kc msg l) (b := D.lineA Ex M Wp Kc l) h ⟨rfl, rfl⟩

theorem ll_tree (D : TreeP E) (Ex : ExtSpec) (M Wp Kc : Type) (msg : M → D.J → E) (n : ℕ) :
    LL (D.treeA Ex Wp Kc msg n) ((List.range (n + 1)).flatMap fun l => pscErrs (D.g + l) 2 2 ++ [1])
      ((List.range (n + 1)).flatMap fun l =>
        pscVals (Fintype.card E) (D.g + l) ++ [Fintype.card E]) :=
  ll_chain _ _ _ _ (ll_lev D Ex M Wp Kc msg) n

theorem ll_tieStep (D : TieP E) (Ex : ExtSpec) (M Wp Kc : Type) (msg : M → D.J → E) (l : ℕ) :
    LL (D.stepA Ex Wp Kc msg l) (pscErrs 0 2 (if l = 0 then 1 else 3))
      (pscVals (Fintype.card E) 0) := by
  cases l with
  | zero => exact ll_psc (D.lv 0).T 0 2 rfl Ex Kc
  | succ l => exact ll_psc (D.lv (l + 1)).T 0 2 rfl Ex Kc

theorem ll_tie (D : TieP E) (Ex : ExtSpec) (M Wp Kc : Type) (msg : M → D.J → E) (n : ℕ) :
    LL (D.tieA Ex Wp Kc msg n) (pscErrs 0 2 1 ++ (List.range n).flatMap fun _ => pscErrs 0 2 3)
      (pscVals (Fintype.card E) 0 ++
        (List.range n).flatMap fun _ => pscVals (Fintype.card E) 0) := by
  have h := ll_chain _ _ _ _ (ll_tieStep D Ex M Wp Kc msg) n
  rw [List.range_succ_eq_map, List.flatMap_cons, List.flatMap_cons,
    List.flatMap_map, List.flatMap_map] at h
  exact h

theorem ll_forest (Q : SegTab E) (Ex : ExtSpec) (M Wp Kc : Type) (msg : M → Q.I.J → E) :
    ∀ l, LL (Q.forest Ex Wp Kc msg l)
      ([Q.I.w * Fintype.card E ^ (Q.I.w - 1)] ++
        (List.range l).flatMap fun l => pscErrs (Q.I.w + l) 2 2 ++ [1])
      ([Fintype.card E ^ Q.I.w] ++
        (List.range l).flatMap fun l => pscVals (Fintype.card E) (Q.I.w + l) ++ [Fintype.card E])
  | 0 => by
    refine ⟨?_, ?_⟩
    · show [Q.R.toIn.ev.err] = _
      rw [ldLkpRoot_err E Q.R]
      rfl
    · show [Fintype.card (Fin (Q.I.w + 0) → E)] = _
      simp
  | l + 1 => by
    have h := ll_seq (ll_forest Q Ex M Wp Kc msg l) (ll_lev Q.D Ex M Wp Kc msg l)
    rw [List.range_succ, List.flatMap_append, List.flatMap_append]
    simpa [List.append_assoc] using h

theorem ll_head (H : LkHead E) (Ex : ExtSpec) (M Wp Kc : Type) (msg : M → H.J → E) :
    LL (H.headA Ex M Wp Kc msg)
      ([2 ^ H.v - 1] ++ (pscErrs 0 2 1 ++ (List.range H.n).flatMap fun _ => pscErrs 0 2 3))
      ([Fintype.card E] ++
        (pscVals (Fintype.card E) 0 ++
          (List.range H.n).flatMap fun _ => pscVals (Fintype.card E) 0)) :=
  ll_seq (ll_draw Ex Wp E Prod.mk (2 ^ H.v - 1))
    (ll_preM (ll_tie H.tie Ex M Wp Kc msg H.n) fun x => ((0 : E), x))

theorem ll_segK (I : LkInst E) (v' : ℕ) (tK : I.X → E) (Ex : ExtSpec)
    (M Wp Kc : Type) (msg : M → I.J → E) :
    LL (segK I v' tK Ex M Wp Kc msg)
      ((List.range (v' + 1)).flatMap fun l => pscErrs (0 + l) 2 2 ++ [1])
      ((List.range (v' + 1)).flatMap fun l =>
        pscVals (Fintype.card E) (0 + l) ++ [Fintype.card E]) :=
  ll_tree (I.setV (v' + 1)).DK Ex M Wp Kc msg v'

theorem ll_end (Q : SegTab E) (Ex : ExtSpec) (M Wp Kc : Type) (msg : M → Q.I.J → E) :
    LL (Q.endA Ex Wp Kc msg) (pscErrs (Q.I.w + Q.I.d) 2 1)
      (pscVals (Fintype.card E) (Q.I.w + Q.I.d)) :=
  ll_psc Q.En.psc (Q.I.w + Q.I.d) 2 rfl Ex Kc

theorem ll_bit (Q : SegTab E) (Ex : ExtSpec) (M Wp Kc : Type) (msg : M → Q.I.J → E) :
    LL (Q.bitA Ex Wp Kc msg)
      ([(Q.I.w + Q.I.d) * Fintype.card E ^ (Q.I.w + Q.I.d - 1)] ++ pscErrs (Q.I.w + Q.I.d) 2 2)
      ([Fintype.card E ^ (Q.I.w + Q.I.d)] ++ pscVals (Fintype.card E) (Q.I.w + Q.I.d)) := by
  have h1 : LL
      (⟨IOR.draw Q.Bt.zc.toIn.ev.D Q.Bt.zc.toIn.nxX Ex,
        Honest.draw Q.Bt.zc.toIn.ev.D Q.Bt.zc.toIn.nxX Ex (M × Wp),
        Nums.draw Kc Q.Bt.zc.toIn.ev.D Q.Bt.zc.toIn.nxX Ex Q.Bt.zc.toIn.ev.err⟩ :
        BkA Kc M Q.XE (E × Q.Bt.zc.next.St) Ex Wp)
      [(Q.I.w + Q.I.d) * Fintype.card E ^ (Q.I.w + Q.I.d - 1)]
      [Fintype.card E ^ (Q.I.w + Q.I.d)] := by
    refine ⟨?_, ?_⟩
    · show [Q.Bt.zc.toIn.ev.err] = _
      rw [ldLkpBit_err E Q.Bt]
      rfl
    · show [Fintype.card (Unit × (Fin (Q.I.w + Q.I.d) → E))] = _
      simp
  have h2 : LL
      (⟨Q.Bt.zc.next.par.psc Ex,
        Q.Bt.zc.next.par.hon Ex fun w : M × Wp => msg w.1,
        Q.Bt.zc.next.par.nums Ex Kc⟩ : BkA Kc M (E × Q.Bt.zc.next.St) Q.XB Ex Wp)
      (pscErrs (Q.I.w + Q.I.d) 2 2) (pscVals (Fintype.card E) (Q.I.w + Q.I.d)) :=
    ll_psc Q.Bt.zc.next (Q.I.w + Q.I.d) 2 rfl Ex Kc
  exact ll_seq h1 h2

theorem ll_segT (Q : SegTab E) (Ex : ExtSpec) (M Wp Kc : Type) (msg : M → Q.I.J → E) :
    LL (Q.segT Ex Wp Kc msg)
      ((([Q.I.w * Fintype.card E ^ (Q.I.w - 1)] ++
            (List.range Q.I.d).flatMap fun l => pscErrs (Q.I.w + l) 2 2 ++ [1]) ++
          pscErrs (Q.I.w + Q.I.d) 2 1) ++
        ([(Q.I.w + Q.I.d) * Fintype.card E ^ (Q.I.w + Q.I.d - 1)] ++ pscErrs (Q.I.w + Q.I.d) 2 2))
      ((([Fintype.card E ^ Q.I.w] ++
            (List.range Q.I.d).flatMap fun l =>
              pscVals (Fintype.card E) (Q.I.w + l) ++ [Fintype.card E]) ++
          pscVals (Fintype.card E) (Q.I.w + Q.I.d)) ++
        ([Fintype.card E ^ (Q.I.w + Q.I.d)] ++ pscVals (Fintype.card E) (Q.I.w + Q.I.d))) :=
  ll_seq (ll_seq (ll_forest Q Ex M Wp Kc msg Q.I.d) (ll_end Q Ex M Wp Kc msg))
    (ll_bit Q Ex M Wp Kc msg)

theorem ll_baseN (A : LkAsm E) (N : Type) (ι : N → A.J) (Ex : ExtSpec)
    (M Wp Kc : Type) (msg : M → A.J → E) :
    LL (A.baseN ι Ex M Wp Kc msg) (A.errs (Fintype.card E)) (A.vals (Fintype.card E)) :=
  ll_postM (ll_seq (ll_seq (ll_head A.H Ex M Wp Kc msg) (ll_segK A.IK A.v' A.tK Ex M Wp Kc msg))
    (ll_segT A.Q Ex M Wp Kc msg)) (A.rdN ι)

/-! ### Lengths; when every error is below its number of values -/

theorem flat_len (f : ℕ → List ℕ) :
    ∀ n, ((List.range n).flatMap f).length = ∑ l ∈ Finset.range n, (f l).length
  | 0 => rfl
  | n + 1 => by rw [List.range_succ, List.flatMap_append, List.length_append, flat_len f n, Finset.sum_range_succ]; simp

theorem pscErrs_len (k n D : ℕ) : (pscErrs k n D).length = k + 3 := by simp [pscErrs]
theorem pscVals_len (q k : ℕ) : (pscVals q k).length = k + 3 := by simp [pscVals]

theorem f2_app {a b c d : List ℕ} (h₁ : List.Forall₂ (· < ·) a b) (h₂ : List.Forall₂ (· < ·) c d) :
    List.Forall₂ (· < ·) (a ++ c) (b ++ d) :=
  List.rel_append h₁ h₂

theorem f2_flat (f g : ℕ → List ℕ) (h : ∀ l, List.Forall₂ (· < ·) (f l) (g l)) :
    ∀ n, List.Forall₂ (· < ·) ((List.range n).flatMap f) ((List.range n).flatMap g)
  | 0 => List.Forall₂.nil
  | n + 1 => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_append]
    refine f2_app (f2_flat f g h n) ?_
    simpa using h n

theorem f2_rep (n q : ℕ) (h : n < q) :
    ∀ k, List.Forall₂ (· < ·) (List.replicate k n) (List.replicate k q)
  | 0 => List.Forall₂.nil
  | k + 1 => List.Forall₂.cons h (f2_rep n q h k)

theorem f2_psc (k n D q : ℕ) (h1 : 1 < q) (hn : n < q) (hD : D < q - 1) :
    List.Forall₂ (· < ·) (pscErrs k n D) (pscVals q k) :=
  List.Forall₂.cons h1
    (f2_app (f2_rep n q hn k)
      (List.Forall₂.cons hD (List.Forall₂.cons Nat.one_pos List.Forall₂.nil)))

theorem f2_one {a b : ℕ} (h : a < b) : List.Forall₂ (· < ·) [a] [b] :=
  List.Forall₂.cons h List.Forall₂.nil

theorem pt_lt (w q : ℕ) (h : w < q) : w * q ^ (w - 1) < q ^ w := by
  cases w with
  | zero => simp
  | succ w =>
    have hq : 0 < q ^ w := Nat.pow_pos (Nat.lt_of_le_of_lt (Nat.zero_le _) h)
    show (w + 1) * q ^ w < q ^ (w + 1)
    rw [pow_succ, Nat.mul_comm (q ^ w) q]
    exact Nat.mul_lt_mul_of_pos_right h hq

end LdLkp

theorem ldLkpAsmE_errs : Spec.ldLkpAsmE_errs E := fun A N ι Ex M Wp Kc msg =>
  (ll_baseN A N ι Ex M Wp Kc msg).1
theorem ldLkpAsmE_vals : Spec.ldLkpAsmE_vals E := fun A N ι Ex M Wp Kc msg =>
  (ll_baseN A N ι Ex M Wp Kc msg).2

theorem ldLkpAsmE_sub : Spec.ldLkpAsmE_sub E :=
  ⟨fun A N ι S E₀ Kc Wp msg => ll_baseN A N ι E₀ S.Msg Wp Kc msg,
    fun A N ι C S msg => ll_baseN A N ι C.E0 (C.Msg × S.Msg) Unit Unit msg⟩

theorem ldLkpAsmE_len : Spec.ldLkpAsmE_len E := by
  intro A q
  have hE : (A.errs q).length =
      (1 + 3 * (A.n + 1)) + (∑ l ∈ Finset.range (A.v' + 1), (0 + l + 3 + 1)) +
        ((1 + ∑ l ∈ Finset.range A.d, (A.w + l + 3 + 1)) +
          (A.w + A.d + 3) + (1 + (A.w + A.d + 3))) := by
    unfold LkAsm.errs
    simp only [List.length_append, flat_len, pscErrs_len, List.length_cons, List.length_nil,
      Finset.sum_const, Finset.card_range, smul_eq_mul, Nat.zero_add]
    omega
  have hV : (A.vals q).length =
      (1 + 3 * (A.n + 1)) + (∑ l ∈ Finset.range (A.v' + 1), (0 + l + 3 + 1)) +
        ((1 + ∑ l ∈ Finset.range A.d, (A.w + l + 3 + 1)) +
          (A.w + A.d + 3) + (1 + (A.w + A.d + 3))) := by
    unfold LkAsm.vals
    simp only [List.length_append, flat_len, pscVals_len, List.length_cons, List.length_nil,
      Finset.sum_const, Finset.card_range, smul_eq_mul, Nat.zero_add]
    omega
  exact ⟨hE.trans hV.symm, hE⟩

theorem ldLkpAsmE_small : Spec.ldLkpAsmE_small E := by
  intro A N ι Ex M Wp Kc msg hv hq hw
  rw [chainErr_small, (ll_baseN A N ι Ex M Wp Kc msg).1, (ll_baseN A N ι Ex M Wp Kc msg).2]
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
    (f2_app (f2_app (f2_one hl) (f2_app (p1 0) (f2_flat _ _ (fun _ => p3 0) A.n)))
      (f2_flat _ _ (fun l => f2_app (p2 (0 + l)) (f2_one h1)) (A.v' + 1)))
    (f2_app (f2_app
        (f2_app (f2_one (pt_lt A.w _ (by omega)))
          (f2_flat _ _ (fun l => f2_app (p2 (A.w + l)) (f2_one h1)) A.d))
        (p1 (A.w + A.d)))
      (f2_app (f2_one (pt_lt (A.w + A.d) _ hw)) (p2 (A.w + A.d))))

end
end Cb
