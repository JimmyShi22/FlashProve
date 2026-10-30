-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdBldWfSuppProofs.lean: the proofs of Cb/Ld/LdBldWfSupp.lean's three statements. They have two
parts. First come Cb/Ld/LdLkpSuppProofs.lean's rules on the rows of a product tree, here with the
hypothesis on the inner masks (`G (D.cAt l' b)`) asked of the levels l' below a given level only.
Then comes Cb/Ld/LdLkpAsm2PullProofs.lean's proof of the coarse statement, part by part: only the
keys' tree reads the inner masks cK. What is said and what is not: the head of
Cb/Ld/LdBldWfSupp.lean.

Main names (statements and hypotheses: Cb/Ld/LdBldWfSupp.lean):
  `ldBldWf_placesR`: `A.PlacesInR G` from `A.PlacesIn G`.
  `ldBldWf_suppRows`, under `A.PlacesInR G`: the rows of the read-out, 0 outside G.
  `ldBldWf_suppPull`, under `A.PlacesInR G`: the same in the form of the rows' half of the
    preamble's clause `lkpS` (Cb/Ld/LdWf.lean).
-/
import Cb.Ld.LdBldWfSupp
import Cb.Ld.LdLkpAsm2PullProofs
import Cb.Ld.LdLkpSuppFine

set_option autoImplicit false

namespace Cb
open Iop IOR Hiop Prob Cb.LdLkp Cb.Lkp

section
variable {E : Type} [Field E] [Fintype E] (D : TreeP E) (G : D.J → Prop)

/-- In the form "0 outside G", under `h0` and the hypothesis below on all levels below l: the
incoming form of level l reads the entry form (l = 0) or the two inner masks of level l - 1. -/
theorem tree_slSF (h0 : ∀ st ϱ, SuppIn G (D.inc0 st ϱ)) :
    ∀ l, (∀ l', l' < l → ∀ b, G (D.cAt l' b)) →
      ∀ s, SuppIn (fun j => G ((D.lv l).toJ j)) ((D.lv l).T.slS s)
  | 0, _, s => h0 s.1 s.2
  | l + 1, hc, s => tree_slS_succ D G l (hc l (Nat.lt_succ_self l)) s

theorem tree_rowUF (hw : ∀ l i, G (D.wAt l i)) (h0 : ∀ st ϱ, SuppIn G (D.inc0 st ϱ)) (l : ℕ)
    (hc : ∀ l', l' < l → ∀ b, G (D.cAt l' b)) (o : (D.lv l).T.par.Out) : SuppIn G (D.rowU l o).cf :=
  supp_pushJ _ _ G
    (supp_slU (D.lv l).T.par (D.emB l) _ o _ (tree_wAt D G hw l) (tree_slSF D G h0 l hc o.st))

/-- Under `hw`, `h0`: the rows of the levels below l read the inner masks of the levels below l - 1
only. -/
theorem tree_rowsAtF (hw : ∀ l i, G (D.wAt l i)) (h0 : ∀ st ϱ, SuppIn G (D.inc0 st ϱ)) :
    ∀ l, (∀ l', l' + 1 < l → ∀ b, G (D.cAt l' b)) → ∀ s, RowsSupp G (D.rowsAt l s)
  | 0, _, _ => fun _ hr => absurd hr List.not_mem_nil
  | l + 1, hc, s => fun r hr => by
      rcases List.mem_cons.1 hr with e | h
      · rw [e]; exact tree_rowUF D G hw h0 l (fun l' hl' => hc l' (Nat.succ_lt_succ hl')) s.1
      · exact tree_rowsAtF hw h0 l (fun l' hl' => hc l' (Nat.lt_succ_of_lt hl')) s.1.st r h

end

section
variable (E : Type) [Field E] [Fintype E]

theorem ldBldWf_placesR : Spec.ldBldWf_placesR E := fun _ _ h => h.toR

/-! ### The parts that do not read the keys' tree's inner masks: the proofs of `supp2_fK` to
`supp2_rowsB` (Cb/Ld/LdLkpAsm2PullProofs.lean) under `A.PlacesInR G` -/

theorem suppR_fK (A : LkAsm2 E) (G : A.J → Prop) (h : A.PlacesInR G) (x : A.X2) :
    SuppIn G (A.fK x) :=
  fun j hj => if_neg fun e : j = A.cS false => hj (e ▸ h.cS false)

theorem suppR_formT (A : LkAsm2 E) (G : A.J → Prop) (h : A.PlacesInR G)
    (x : A.X2) (θ : Fin (A.w + 0) → Bool) : SuppIn G (A.formT x θ) := by
  intro j hj
  unfold LkAsm2.formT
  split_ifs with h1 h2
  · exact if_neg fun e : j = A.cAt (numLE θ) true => hj (e ▸ h.cAt _ true)
  · exact supp_pushJ _ _ G (tie_slS A.H.tie G h.cS h.cAt (A.n + 1) x.2) j hj
  · rfl

theorem suppR_numRow (A : LkAsm2 E) (G : A.J → Prop) (h : A.PlacesInR G) :
    SuppIn G A.numRow.cf := by
  classical
  intro i hi
  have hne : ∀ u j, A.bAt u j ≠ i := fun u j e => hi (e ▸ h.bAt u j)
  show (∑ u ∈ Finset.range (2 ^ A.d), ∑ j ∈ Finset.range (A.n + 1), if A.bAt u j = i then
        (2 : E) ^ j
      else 0) = 0
  simp [hne]

theorem suppR_inc0 (A : LkAsm2 E) (G : A.J → Prop) (h : A.PlacesInR G) :
    ∀ st ϱ, SuppIn G (A.D.inc0 st ϱ) := fun st ϱ j hj =>
  Finset.sum_eq_zero fun θ _ => by
    show Alg.eqk ϱ θ * A.formT (A.oR (A.o4 st)) θ j = 0
    rw [suppR_formT E A G h (A.oR (A.o4 st)) θ j hj, mul_zero]

theorem suppR_rowsB (A : LkAsm2 E) (G : A.J → Prop) (h : A.PlacesInR G) (o : A.XB) :
    RowsSupp G (A.rowsB o) := by
  classical
  intro r hr
  rcases List.mem_append.1 hr with hf | hr'
  · exact tree_rowsAt A.D G h.wT h.cT (suppR_inc0 E A G h) A.d (A.outE o).st r hf
  rcases List.mem_cons.1 hr' with e | hr'
  · rw [e]
    refine supp_slUB A.En.par A.En.rowB (A.En.outOf (A.outE o)) G h.wE
      (supp_pushJ _ _ G (tree_slS A.D G h.cT (suppR_inc0 E A G h) A.d (A.outE o).st))
      fun _ X j hj => ?_
    have h1 : ∀ b, A.En.tAt b ≠ j := fun b e => hj (e ▸ h.bAt _ _)
    show (∑ b, if A.En.tAt b = j then _ else 0) = (0 : E)
    simp [h1]
  rcases List.mem_cons.1 hr' with e | hr'
  · rw [e]; exact supp_slU A.Bt.zc.next.par (inferInstanceAs (IsEmpty Empty)) (fun _ b => b.elim) o G h.wB fun _ _ => rfl
  rcases List.mem_cons.1 hr' with e | hr'
  · rw [e]; exact supp_bitRow A.Bt G (fun b => h.bAt _ _) h.cB o
  · exact absurd hr' List.not_mem_nil

/-- Under `A.PlacesInR G` all rows of the read-out are 0 outside G: in this form, no row reads the
inner masks of the keys' tree's last level. -/
theorem ldBldWf_suppRows : Spec.ldBldWf_suppRows E := by
  intro A G h o r hr
  have hr' : r ∈ A.rows2 (A.oR (A.o4 (A.oldT o))) ∨ r ∈ A.rows4 (A.oldT o) ∨
      r ∈ A.rowsB o ∨ r = A.numRow := by
    have : r ∈
        A.rows2 (A.oR (A.o4 (A.oldT o))) ++ (A.rows4 (A.oldT o) ++ (A.rowsB o ++ [A.numRow])) := hr
    simpa only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] using this
  rcases hr' with h2 | h4 | hB | e
  · exact tie_rowsAt A.H.tie G h.wS h.cS h.wAt h.cAt (A.n + 1) _ r h2
  · exact tree_rowsAtF (A.IK.setV (A.v' + 1)).DK G h.wK (fun st _ => suppR_fK E A G h (A.oR st))
      (A.v' + 1) (fun l' hl' b => h.cK l' (Nat.lt_of_succ_lt_succ hl') b) _ r h4
  · exact suppR_rowsB E A G h o r hB
  · rw [e]; exact suppR_numRow E A G h

omit [Fintype E] in
/-- An auxiliary lemma: an entry of a list of pulled-back rows. It repeats `LdLkp.getD_pull` of
Cb/Ld/LdWfBlocksProofs.lean, because that file imports this one. -/
theorem getD_pullR {J N : Type} (ι : N → J) (G : J → Prop) (n : N) (hn : ¬ G (ι n)) :
    ∀ (l : List (Row E J)) (i : ℕ),
      RowsSupp G l → ((l.map (Row.pull ι)).getD i ⟨fun _ => 0, 0⟩).cf n = 0
  | [], _, _ => rfl
  | r :: _, 0, h => h r List.mem_cons_self (ι n) hn
  | _ :: l, i + 1, h => getD_pullR ι G n hn l i fun r hr => h r (List.mem_cons_of_mem _ hr)

theorem ldBldWf_suppPull : Spec.ldBldWf_suppPull E := fun A _ ι G h o i n hn =>
  getD_pullR E ι G n hn _ i (ldBldWf_suppRows E A G h o)

end
end Cb
