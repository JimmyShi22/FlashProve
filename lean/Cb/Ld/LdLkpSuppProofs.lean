-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLkpSuppProofs.lean: proofs for Cb/Ld/LdLkpSupp.lean (at which entries the coefficients of
the assembled lookup's (`LkAsm`, Cb/Ld/LdLkpAsm.lean) output claims can differ from 0), part by
part: the row on the hiding polynomial's coefficients of a sumcheck none of whose maps stays
unrevealed (its own places, and the support of its incoming form); a form pushed along a map of
names; the levels of a tree; the steps of the tie; the closing's and the bit test's rows on the bits
(`LkEnd`, `LkBit`); the table's side; the pull-back; the read-out.
Many statements of this library are written twice: a definition in the namespace `Spec` states a
proposition, and a theorem of the same name outside that namespace proves it (lean/GLOSSARY.md).

Defined in Cb/Ld/LdLkpSupp.lean: `SuppIn G c`: the coefficients are 0 outside G; `A.PlacesIn G`: G
holds of all places that the data name.

Main names (statements and hypotheses: Cb/Ld/LdLkpSupp.lean):
  `ldLkpSupp_sum`: a form that is 0 outside the range of an injective naming ι, and its pull-back:
    the same value.
  `ldLkpSupp_row_pull`, `ldLkpSupp_rows_pull`: a row, a list of rows, whose coefficients are 0
    outside the range of the injective ι, pulled back along ι, against the originals.
  `ldLkpSupp_cl_pull`: see its statement in Cb/Ld/LdLkpSupp.lean.
  `ldLkpSupp_rows`: under `A.PlacesIn G`: all rows that the read-out (`A.rd`) lists: 0 outside G.
  `ldLkpSupp_form`: see its statement in Cb/Ld/LdLkpSupp.lean.
  `ldLkpSupp_out`: the corollary for callers: ι injective, with all named places in the range of ι:
    what the read-out states on J, and what its pull-back states on N.

Limits: what the head of Cb/Ld/LdLkpSupp.lean lists as not said is not said here either.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdLkpSupp
import Cb.Ld.LdLkpAsmProofs

set_option autoImplicit false

namespace Cb
open Iop IOR Hiop Prob Cb.LdLkp

section Links
variable {E : Type} [Field E]

theorem supp_pushJ {J' J : Type} [Fintype J'] (f : J' → J) (c : J' → E)
    (G : J → Prop) (h : SuppIn (fun j' => G (f j')) c) : SuppIn G (pushJ f c) := by
  classical
  intro j hj
  unfold pushJ
  refine Finset.sum_eq_zero fun j' _ => ?_
  split_ifs with e
  · exact h j' fun hg => hj (e ▸ hg)
  · rfl

/-- the row on the hiding polynomial's coefficients -/
theorem supp_slU (Y : PscPar E) (hB : IsEmpty Y.B)
    (rowB : (st : Y.St) → Y.B → HPt (Y.vars st) → Y.J → E) (o : Y.Out) (G : Y.J → Prop)
    (hw : ∀ i, G (Y.wAt i)) (hs : SuppIn G (Y.slS o.st)) : SuppIn G (Y.slU rowB o) := by
  intro j hj
  unfold PscPar.slU
  have h1 : ∀ i, Y.wAt (pIx Y.fmt (Y.dat o.st) i) ≠ j := fun i e => hj (e ▸ hw _)
  haveI := hB
  rw [hs j hj]
  simp [h1]

variable [Fintype E]

theorem supp_rowUof (T : PscOur E) (h : IsEmpty T.par.B) {J : Type} (toJ : T.J → J) (o : T.par.Out)
    (G : J → Prop) (hw : ∀ i, G (toJ (T.wAt i))) (hs : SuppIn (fun j => G (toJ j)) (T.slS o.st)) :
    SuppIn G (rowUof T h toJ o).cf :=
  supp_pushJ toJ _ G (supp_slU T.par h _ o _ hw hs)

/-! ### The tree -/

section Tree
variable (D : TreeP E) (G : D.J → Prop)

theorem tree_wAt (hw : ∀ l i, G (D.wAt l i)) : ∀ l i, G ((D.lv l).toJ ((D.lv l).T.wAt i))
  | 0, i => hw 0 i
  | l + 1, i => hw (l + 1) i

theorem tree_cAt (hc : ∀ l b, G (D.cAt l b)) :
    ∀ l b, G ((D.lv l).toJ ((D.lv l).T.cAt ((D.lv l).two b)))
  | 0, b => hc 0 b
  | l + 1, b => hc (l + 1) b

theorem tree_slS (hc : ∀ l b, G (D.cAt l b)) (h0 : ∀ st ϱ, SuppIn G (D.inc0 st ϱ)) :
    ∀ l s, SuppIn (fun j => G ((D.lv l).toJ j)) ((D.lv l).T.slS s)
  | 0, s => h0 s.1 s.2
  | l + 1, s => fun j hj => by
      classical
      show (D.lv l).T.lst s.1.st ((D.lv l).T.par.hp s.1.st s.1.pt) *
          ((if j = (D.lv l).toJ ((D.lv l).T.cAt ((D.lv l).two false)) then 1 - s.2 else 0) +
            if j = (D.lv l).toJ ((D.lv l).T.cAt ((D.lv l).two true)) then s.2 else 0) = 0
      have h1 : j ≠ (D.lv l).toJ ((D.lv l).T.cAt ((D.lv l).two false)) := fun e =>
        hj (e ▸ tree_cAt D G hc l false)
      have h2 : j ≠ (D.lv l).toJ ((D.lv l).T.cAt ((D.lv l).two true)) := fun e =>
        hj (e ▸ tree_cAt D G hc l true)
      rw [if_neg h1, if_neg h2]
      simp

theorem tree_rowU (hw : ∀ l i, G (D.wAt l i)) (hc : ∀ l b, G (D.cAt l b))
    (h0 : ∀ st ϱ, SuppIn G (D.inc0 st ϱ)) (l : ℕ) (o : (D.lv l).T.par.Out) :
    SuppIn G (D.rowU l o).cf :=
  supp_pushJ _ _ G
    (supp_slU (D.lv l).T.par (D.emB l) _ o _ (tree_wAt D G hw l) (tree_slS D G hc h0 l o.st))

theorem tree_rowsAt (hw : ∀ l i, G (D.wAt l i))
    (hc : ∀ l b, G (D.cAt l b)) (h0 : ∀ st ϱ, SuppIn G (D.inc0 st ϱ)) :
    ∀ l s, RowsSupp G (D.rowsAt l s)
  | 0, _ => fun _ hr => absurd hr List.not_mem_nil
  | l + 1, s => fun r hr => by
      rcases List.mem_cons.1 hr with e | h
      · rw [e]; exact tree_rowU D G hw hc h0 l s.1
      · exact tree_rowsAt hw hc h0 l s.1.st r h

end Tree

/-! ### The tie -/

section Tie
variable (D : TieP E) (G : D.J → Prop)

theorem tie_wAt (hS : ∀ i, G (D.wS i)) (hw : ∀ l i, G (D.wAt l i)) :
    ∀ l i, G ((D.lv l).toJ ((D.lv l).T.wAt i))
  | 0, i => hS i
  | l + 1, i => hw l i

theorem tie_cAt (hS : ∀ b, G (D.cS b)) (hc : ∀ l b, G (D.cAt l b)) :
    ∀ l a, G ((D.lv l).toJ ((D.lv l).T.cAt a))
  | 0, a => hS a
  | l + 1, a => hc l a

theorem tie_slS (hS : ∀ b, G (D.cS b)) (hc : ∀ l b, G (D.cAt l b)) :
    ∀ l s, SuppIn (fun j => G ((D.lv l).toJ j)) ((D.lv l).T.slS s)
  | 0, _ => fun _ _ => rfl
  | l + 1, s => fun j hj => by
      classical
      show (if j = (D.lv l).toJ ((D.lv l).T.cAt (D.lv l).nx) then
            (D.lv l).T.lst s.st ((D.lv l).T.par.hp s.st s.pt)
          else 0) = 0
      exact if_neg fun e : j = (D.lv l).toJ ((D.lv l).T.cAt (D.lv l).nx) =>
        hj (e ▸ tie_cAt D G hS hc l _)

theorem tie_rowsAt (hwS : ∀ i, G (D.wS i)) (hcS : ∀ b, G (D.cS b))
    (hw : ∀ l i, G (D.wAt l i)) (hc : ∀ l b, G (D.cAt l b)) : ∀ l s, RowsSupp G (D.rowsAt l s)
  | 0, _ => fun _ hr => absurd hr List.not_mem_nil
  | l + 1, s => fun r hr => by
      rcases List.mem_cons.1 hr with e | h
      · rw [e]; exact supp_rowUof (D.lv l).T (D.emB l) (D.lv l).toJ s G (tie_wAt D G hwS hw l) (tie_slS D G hcS hc l s.st)
      · exact tie_rowsAt hwS hcS hw hc l s.st r h

end Tie

/-! ### The table's side -/

theorem supp_endRow (B : LkEnd E) (G : B.J → Prop) (ht : ∀ b, G (B.tAt b))
    (hc : G B.cAt) (o : B.psc.par.Out) :
    SuppIn G (B.psc.par.slE B.rowA () o) := by
  classical
  intro j hj
  have h1 : ∀ b, B.tAt b ≠ j := fun b e => hj (e ▸ ht b)
  have h2 : j ≠ B.cAt := fun e => hj (e ▸ hc)
  show (∑ b, if B.tAt b = j then _ else 0) + (if j = B.cAt then _ else 0) = (0 : E)
  simp [h1, h2]

theorem supp_bitRow (B : LkBit E) (G : B.J → Prop) (ht : ∀ b, G (B.tAt b))
    (hc : G B.cAt) (o : B.zc.next.par.Out) :
    SuppIn G (B.zc.next.par.slE B.rowA () o) := by
  classical
  intro j hj
  have h1 : ∀ b, B.tAt b ≠ j := fun b e => hj (e ▸ ht b)
  have h2 : j ≠ B.cAt := fun e => hj (e ▸ hc)
  show (∑ b, if B.tAt b = j then _ else 0) + (if j = B.cAt then _ else 0) = (0 : E)
  simp [h1, h2]

theorem supp_rowsT (Q : SegTab E) (G : Q.I.J → Prop) (hb : ∀ u j, G (Q.I.bAt u j))
    (hw : ∀ l i, G (Q.I.wT l i)) (hc : ∀ l b, G (Q.I.cT l b)) (hf : ∀ x θ, SuppIn G (Q.I.formT x θ))
    (hwE : ∀ i, G (Q.wE i)) (hcE : G Q.cE) (hwB : ∀ i, G (Q.wB i)) (hcB : G Q.cB) (o : Q.XB) :
    RowsSupp G (Q.rowsT o) := by
  have h0 : ∀ st ϱ, SuppIn G (Q.D.inc0 st ϱ) := fun st ϱ j hj =>
    Finset.sum_eq_zero fun θ _ => by rw [hf st θ j hj, mul_zero]
  intro r hr
  unfold SegTab.rowsT at hr
  simp only [List.mem_cons] at hr
  rcases hr with e | e | e | e | h
  · rw [e]; exact supp_slU Q.Bt.zc.next.par (inferInstanceAs (IsEmpty Empty)) (fun _ b => b.elim) o G hwB fun _ _ => rfl
  · rw [e]; exact supp_bitRow Q.Bt G (fun b => hb _ _) hcB o
  · rw [e]; exact supp_slU Q.En.psc.par (inferInstanceAs (IsEmpty Empty)) (fun _ b => b.elim) (Q.outE o) G hwE (supp_pushJ _ _ G (tree_slS Q.D G hc h0 Q.I.d (Q.outE o).st))
  · rw [e]; exact supp_endRow Q.En G (fun b => hb _ _) hcE (Q.outE o)
  · exact tree_rowsAt Q.D G hw hc h0 Q.I.d (Q.outE o).st r h

end Links

/-! ### The pull-back -/

section Pull
variable (E : Type) [Field E]

theorem ldLkpSupp_sum : Spec.ldLkpSupp_sum E := fun _ _ _ _ ι hι c hc m =>
  Fintype.sum_of_injective ι hι (fun n => c (ι n) * m (ι n)) (fun j => c j * m j)
    (fun j hj => by show c j * m j = 0; rw [hc j hj, zero_mul]) fun _ => rfl

theorem ldLkpSupp_row_pull : Spec.ldLkpSupp_row_pull E := fun J N _ _ ι hι r hr m => by
  unfold Row.Holds Row.pull
  rw [ldLkpSupp_sum E J N ι hι r.cf hr m]

theorem ldLkpSupp_rows_pull : Spec.ldLkpSupp_rows_pull E := fun J N _ _ ι hι rs hrs m => by
  unfold RowsHold
  simp only [List.forall_mem_map]
  exact forall₂_congr fun r hr => ldLkpSupp_row_pull E J N ι hι r (hrs r hr) m

theorem ldLkpSupp_cl_pull : Spec.ldLkpSupp_cl_pull E := fun J N _ _ ι hι c hc k f m => by
  unfold MCl.Holds MCl.pull
  rw [ldLkpSupp_sum E J N ι hι c.mf hc m]

end Pull

/-! ### The read-out -/

section Asm
variable (E : Type) [Field E] [Fintype E]

theorem supp_fK (A : LkAsm E) (G : A.J → Prop) (h : A.PlacesIn G) (x : A.X2) : SuppIn G (A.fK x) :=
  fun j hj => if_neg fun e : j = A.cS false => hj (e ▸ h.cS false)

theorem supp_formT (A : LkAsm E) (G : A.J → Prop) (h : A.PlacesIn G)
    (x : A.X4) (θ : Fin (A.w + 0) → Bool) : SuppIn G (A.formT x θ) := by
  intro j hj
  unfold LkAsm.formT
  split_ifs with h1 h2
  · exact if_neg fun e : j = A.cAt (numLE θ) true => hj (e ▸ h.cAt _ true)
  · exact supp_pushJ _ _ G (tie_slS A.H.tie G h.cS h.cAt (A.n + 1) (A.o4 x).2) j hj
  · rfl

theorem supp_numRow (A : LkAsm E) (G : A.J → Prop) (h : A.PlacesIn G) : SuppIn G A.numRow.cf := by
  classical
  intro i hi
  have hne : ∀ u j, A.bAt u j ≠ i := fun u j e => hi (e ▸ h.bAt u j)
  show (∑ u ∈ Finset.range (2 ^ A.d), ∑ j ∈ Finset.range (A.n + 1), if A.bAt u j = i then
        (2 : E) ^ j
      else 0) = 0
  simp [hne]

theorem ldLkpSupp_rows : Spec.ldLkpSupp_rows E := by
  intro A G h o r hr
  have hr' : r = A.numRow ∨ r ∈ A.rows2 (A.o4 (A.Q.oldT o)) ∨
      r ∈ A.rows4 (A.Q.oldT o) ∨ r ∈ A.rowsB o := by
    have : r ∈ A.numRow :: (A.rows2 (A.o4 (A.Q.oldT o)) ++ (A.rows4 (A.Q.oldT o) ++ A.rowsB o)) :=
      hr
    simpa only [List.mem_cons, List.mem_append] using this
  rcases hr' with e | h2 | h4 | hB
  · rw [e]; exact supp_numRow E A G h
  · exact tie_rowsAt A.H.tie G h.wS h.cS h.wAt h.cAt (A.n + 1) _ r h2
  · exact tree_rowsAt (A.IK.setV (A.v' + 1)).DK G h.wK h.cK
      (fun st _ => supp_fK E A G h st) (A.v' + 1) _ r h4
  · exact supp_rowsT A.Q G h.bAt h.wT h.cT (supp_formT E A G h) h.wE h.cE h.wB h.cB o r hB

theorem ldLkpSupp_form : Spec.ldLkpSupp_form E := by
  intro A G h o j hj
  show - pushJ ((A.IK.setV (A.v' + 1)).DK.lv (A.v' + 1)).toJ
        (((A.IK.setV (A.v' + 1)).DK.lv (A.v' + 1)).T.slS (A.Q.oldT o).2) j = 0
  exact neg_eq_zero.2
    (supp_pushJ _ _ G
      (tree_slS (A.IK.setV (A.v' + 1)).DK G h.cK (fun st _ => supp_fK E A G h st)
        (A.v' + 1) (A.Q.oldT o).2)
      j hj)

theorem ldLkpSupp_out : Spec.ldLkpSupp_out E := fun A N _ ι hι h o k f m =>
  ⟨ldLkpSupp_cl_pull E A.J N ι hι _ (ldLkpSupp_form E A _ h o) k f m,
    ldLkpSupp_rows_pull E A.J N ι hι _ (ldLkpSupp_rows E A _ h o) m⟩

end Asm
end Cb
