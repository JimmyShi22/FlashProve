-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLkpAsm2PullProofs.lean: the proofs of the statements of Cb/Ld/LdLkpAsm2Pull.lean (the
assembled lookup `LkAsm2` (Cb/Ld/LdLkpAsm2.lean): the rest of the interface). Among them auxiliary
lemmas: the support of a row with an unrevealed map (`supp_slUB`), of the closing's row (`LkEndU`,
Cb/Ld/LdLkpEndU.lean; inside `supp2_rowsB`), of forms and rows; the chain before the read-out
(`A.chainA`) is `BkA.Plain` (Cb/Ld/LdLkpFormat.lean) and hands the state on (`LkAsm2.plain2`,
`LkAsm2.pass2`).
Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdLkpAsm2Pull
import Cb.Ld.LdLkpAsm2Proofs
import Cb.Ld.LdLkpSuppProofs
import Cb.Ld.LdLkpMultProofs
import Cb.Ld.LdLkpAsmMore
import Cb.Ld.LdLkpFormatAsm
import Cb.Ld.LdLkpAsmIdxProofs

set_option autoImplicit false

namespace Cb
open Iop IOR Hiop Prob Cb.LdLkp Cb.Lkp

section
variable {E : Type} [Field E]

/-- the row on the hiding polynomial's coefficients, with maps that stay unrevealed -/
theorem supp_slUB (Y : PscPar E) (rowB : (st : Y.St) → Y.B → HPt (Y.vars st) → Y.J → E) (o : Y.Out)
    (G : Y.J → Prop) (hw : ∀ i, G (Y.wAt i)) (hs : SuppIn G (Y.slS o.st))
    (hb : ∀ b X, SuppIn G (rowB o.st b X)) : SuppIn G (Y.slU rowB o) := by
  intro j hj
  unfold PscPar.slU
  have h1 : ∀ i, Y.wAt (pIx Y.fmt (Y.dat o.st) i) ≠ j := fun i e => hj (e ▸ hw _)
  have h2 : ∀ b, rowB o.st b (Y.hp o.st o.pt) j = 0 := fun b => hb b _ j hj
  rw [hs j hj]
  simp [h1, h2]

end

section
variable (E : Type) [Field E] [Fintype E]

theorem ldLkpAsm2_muValid : Spec.ldLkpAsm2_muValid E := fun A hW st m hin hv lam =>
  ⟨ldLkpMult_mid E (A.v' + 1) A.d A.w (A.n + 1) (A.key st m) (A.tab st) (A.H.bit m) hW hin.1 hv lam,
    trivial⟩

theorem ldLkpAsm2_len : Spec.ldLkpAsm2_len E := by
  intro A o
  show (A.rows2 (A.oR (A.o4 (A.oldT o))) ++
      (A.rows4 (A.oldT o) ++ (A.rowsB o ++ [A.numRow]))).length = A.nRows
  have h2 : (A.rows2 (A.oR (A.o4 (A.oldT o)))).length = A.n + 1 := A.H.tie.rowsAt_len E (A.n + 1) _
  have h4 : (A.rows4 (A.oldT o)).length = A.v' + 1 :=
    (A.IK.setV (A.v' + 1)).DK.rowsAt_len E (A.v' + 1) _
  have hB : (A.rowsB o).length = A.d + 3 :=
    (List.length_append (as := A.D.rowsAt A.d (A.outE o).st)).trans
      (congrArg (· + 3) (A.D.rowsAt_len E A.d _))
  rw [List.length_append, List.length_append, List.length_append, h2, h4, hB]
  rfl

theorem ldLkpAsm2_out_len : Spec.ldLkpAsm2_out_len E := by
  intro A Ex M Wp Kc msg x y τ xo h
  obtain ⟨o, _, ho⟩ := Option.bind_eq_some_iff.mp h
  rw [← Option.some.inj ho]
  exact ldLkpAsm2_len E A o

theorem ldLkpAsm2_sub_len : Spec.ldLkpAsm2_sub_len E := by
  intro A S E₀ Kc Wp msg x y τ xo h
  obtain ⟨x', hx', rfl⟩ := Option.map_eq_some_iff.mp h
  exact ldLkpAsm2_out_len E A E₀ S.Msg Wp Kc msg _ _ _ _ hx'

theorem ldLkpAsm2_ok_valid : Spec.ldLkpAsm2_ok_valid E := fun p _ A S E₀ Kc Wp R0 msg hA =>
  ldLkpAsm2_ok E p A A.ValidMu S E₀ Kc Wp R0 msg hA (ldLkpAsm2_muValid E A hA.1)

theorem ldLkpAsm2_ok_first : Spec.ldLkpAsm2_ok_first E := fun p _ A S E₀ Kc Wp R0 msg hA =>
  ldLkpAsm2_ok E p A A.H.lkb.IsMult S E₀ Kc Wp R0 msg hA (ldLkpHead2_mu E p A.H hA)

theorem supp2_fK (A : LkAsm2 E) (G : A.J → Prop) (h : A.PlacesIn G) (x : A.X2) :
    SuppIn G (A.fK x) :=
  fun j hj => if_neg fun e : j = A.cS false => hj (e ▸ h.cS false)

theorem supp2_formT (A : LkAsm2 E) (G : A.J → Prop) (h : A.PlacesIn G)
    (x : A.X2) (θ : Fin (A.w + 0) → Bool) : SuppIn G (A.formT x θ) := by
  intro j hj
  unfold LkAsm2.formT
  split_ifs with h1 h2
  · exact if_neg fun e : j = A.cAt (numLE θ) true => hj (e ▸ h.cAt _ true)
  · exact supp_pushJ _ _ G (tie_slS A.H.tie G h.cS h.cAt (A.n + 1) x.2) j hj
  · rfl

theorem supp2_numRow (A : LkAsm2 E) (G : A.J → Prop) (h : A.PlacesIn G) : SuppIn G A.numRow.cf := by
  classical
  intro i hi
  have hne : ∀ u j, A.bAt u j ≠ i := fun u j e => hi (e ▸ h.bAt u j)
  show (∑ u ∈ Finset.range (2 ^ A.d), ∑ j ∈ Finset.range (A.n + 1), if A.bAt u j = i then
        (2 : E) ^ j
      else 0) = 0
  simp [hne]

theorem supp2_inc0 (A : LkAsm2 E) (G : A.J → Prop) (h : A.PlacesIn G) :
    ∀ st ϱ, SuppIn G (A.D.inc0 st ϱ) := fun st ϱ j hj =>
  Finset.sum_eq_zero fun θ _ => by
    show Alg.eqk ϱ θ * A.formT (A.oR (A.o4 st)) θ j = 0
    rw [supp2_formT E A G h (A.oR (A.o4 st)) θ j hj, mul_zero]

theorem supp2_rowsB (A : LkAsm2 E) (G : A.J → Prop) (h : A.PlacesIn G) (o : A.XB) :
    RowsSupp G (A.rowsB o) := by
  classical
  intro r hr
  rcases List.mem_append.1 hr with hf | hr'
  · exact tree_rowsAt A.D G h.wT h.cT (supp2_inc0 E A G h) A.d (A.outE o).st r hf
  rcases List.mem_cons.1 hr' with e | hr'
  · rw [e]
    refine supp_slUB A.En.par A.En.rowB (A.En.outOf (A.outE o)) G h.wE
      (supp_pushJ _ _ G (tree_slS A.D G h.cT (supp2_inc0 E A G h) A.d (A.outE o).st))
      fun _ X j hj => ?_
    have h1 : ∀ b, A.En.tAt b ≠ j := fun b e => hj (e ▸ h.bAt _ _)
    show (∑ b, if A.En.tAt b = j then _ else 0) = (0 : E)
    simp [h1]
  rcases List.mem_cons.1 hr' with e | hr'
  · rw [e]; exact supp_slU A.Bt.zc.next.par (inferInstanceAs (IsEmpty Empty)) (fun _ b => b.elim) o G h.wB fun _ _ => rfl
  rcases List.mem_cons.1 hr' with e | hr'
  · rw [e]; exact supp_bitRow A.Bt G (fun b => h.bAt _ _) h.cB o
  · exact absurd hr' List.not_mem_nil

theorem ldLkpAsm2_suppRows : Spec.ldLkpAsm2_suppRows E := by
  intro A G h o r hr
  have hr' : r ∈ A.rows2 (A.oR (A.o4 (A.oldT o))) ∨ r ∈ A.rows4 (A.oldT o) ∨
      r ∈ A.rowsB o ∨ r = A.numRow := by
    have : r ∈
        A.rows2 (A.oR (A.o4 (A.oldT o))) ++ (A.rows4 (A.oldT o) ++ (A.rowsB o ++ [A.numRow])) := hr
    simpa only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] using this
  rcases hr' with h2 | h4 | hB | e
  · exact tie_rowsAt A.H.tie G h.wS h.cS h.wAt h.cAt (A.n + 1) _ r h2
  · exact tree_rowsAt (A.IK.setV (A.v' + 1)).DK G h.wK h.cK
      (fun st _ => supp2_fK E A G h (A.oR st)) (A.v' + 1) _ r h4
  · exact supp2_rowsB E A G h o r hB
  · rw [e]; exact supp2_numRow E A G h

theorem ldLkpAsm2_suppForm : Spec.ldLkpAsm2_suppForm E := by
  intro A G h o j hj
  show - pushJ ((A.IK.setV (A.v' + 1)).DK.lv (A.v' + 1)).toJ
        (((A.IK.setV (A.v' + 1)).DK.lv (A.v' + 1)).T.slS (A.oldT o).2) j = 0
  exact neg_eq_zero.2
    (supp_pushJ _ _ G
      (tree_slS (A.IK.setV (A.v' + 1)).DK G h.cK (fun st _ => supp2_fK E A G h (A.oR st))
        (A.v' + 1) (A.oldT o).2)
      j hj)

theorem ldLkpAsm2_suppOut : Spec.ldLkpAsm2_suppOut E := fun A N _ ι hι h o k f m =>
  ⟨ldLkpSupp_cl_pull E A.J N ι hι _ (ldLkpAsm2_suppForm E A _ h o) k f m,
    ldLkpSupp_rows_pull E A.J N ι hι _ (ldLkpAsm2_suppRows E A _ h o) m⟩

/-! ### formats -/

theorem LdLkp.LkAsm2.plain_forest
    (A : LkAsm2 E) (Ex : ExtSpec) (M Wp Kc : Type) (msg : M → A.J → E) :
    ∀ l, (A.forest Ex M Wp Kc msg l).Plain
  | 0 => plain_postM (plain_segK Ex M Wp Kc A.IK A.v' (fun x => A.tK (A.oR x)) msg) A.enterT
  | l + 1 => plain_seq (plain_forest A Ex M Wp Kc msg l) (plain_lev Ex M Wp Kc A.D msg l)

theorem LdLkp.LkAsm2.pass_forest
    (A : LkAsm2 E) (Ex : ExtSpec) (M Wp Kc : Type) (msg : M → A.J → E) :
    ∀ l, (A.forest Ex M Wp Kc msg l).R.Passes id fun x => A.o4 (A.D.root l x.2).1
  | 0 => (pass_segK Ex M Wp Kc A.IK A.v' (fun x => A.tK (A.oR x)) msg).post _ _ fun o x' e => by
      obtain rfl := Option.some.inj e
      rfl
  | l + 1 =>
    (pass_forest A Ex M Wp Kc msg l).seq
      (passes_map (pass_lev Ex M Wp Kc A.D msg l) fun s => A.o4 s.1)

/-- the chain before the read-out is plain -/
theorem LdLkp.LkAsm2.plain2 (A : LkAsm2 E) (Ex : ExtSpec) (M Wp Kc : Type) (msg : M → A.J → E) :
    (A.chainA Ex M Wp Kc msg).Plain :=
  plain_seq (plain_seq
      (plain_seq (plain_seq (plain_head Ex M Wp Kc A.H msg) (plain_draw _ _ _))
        (A.plain_forest E Ex M Wp Kc msg A.d))
      (plain_core A.En.par Ex Kc M Wp fun w => msg w.1))
    (plain_seq (plain_draw _ _ _) (plain_psc A.Bt.zc.next.par Ex Kc M Wp fun w => msg w.1))

/-- the bit test hands on whatever is read off its state -/
theorem pass_bitAny {Rc : Type} (B : LkBit E) (Ex : ExtSpec) (f : B.St → Rc) :
    (B.zc.toIn.chainAt Ex).Passes f fun o : B.zc.next.par.Out => f o.st.1 :=
  (Passes.draw _ _ Ex f (fun x : E × B.zc.next.St => f x.2.1) fun _ _ => rfl).seq
    (passes_map (psc_passes B.zc.next.par Ex) fun s : B.zc.next.St => f s.1)

section Pass
variable (A : LkAsm2 E) (Ex : ExtSpec) (M Wp Kc : Type) (msg : M → A.J → E)

theorem LdLkp.LkAsm2.pass_a :
    ((A.H.headA Ex M Wp Kc msg).seq (A.R.rootA Ex M Wp Kc)).R.Passes id fun x : A.XR =>
      (A.b2 (A.oR x)).1 :=
  (pass_head Ex M Wp Kc A.H msg).seq
    (Passes.draw _ _ Ex (fun x : A.X2 => (A.b2 x).1)
      (fun x : A.XR => (A.b2 (A.oR x)).1) fun _ _ => rfl)

theorem LdLkp.LkAsm2.pass_b :
    (A.forest Ex M Wp Kc msg A.d).R.Passes (fun x : A.XR => (A.b2 (A.oR x)).1) fun x =>
      (A.b2 (A.oR (A.o4 (A.D.root A.d x.2).1))).1 :=
  passes_map (A.pass_forest E Ex M Wp Kc msg A.d) fun x => (A.b2 (A.oR x)).1

theorem LdLkp.LkAsm2.pass_c :
    (A.endA Ex M Wp Kc msg).R.Passes (fun x => (A.b2 (A.oR (A.o4 (A.D.root A.d x.2).1))).1)
      fun z : A.XE => (A.b2 (A.oR (A.o4 (A.D.root A.d z.st).1))).1 :=
  passes_map (core_passes A.En.par Ex) fun s => (A.b2 (A.oR (A.o4 (A.D.root A.d s).1))).1

theorem LdLkp.LkAsm2.pass_d :
    (A.bitA Ex M Wp Kc msg).R.Passes (fun z : A.XE => (A.b2 (A.oR (A.o4 (A.D.root A.d z.st).1))).1)
      fun o : A.XB => (A.b2 (A.oR (A.o4 (A.oldT o)))).1 :=
  pass_bitAny E A.Bt Ex fun z : A.XE => (A.b2 (A.oR (A.o4 (A.D.root A.d z.st).1))).1

/-- the chain before the read-out hands the state on -/
theorem LdLkp.LkAsm2.pass2 :
    (A.chainA Ex M Wp Kc msg).R.Passes id fun o => (A.b2 (A.oR (A.o4 (A.oldT o)))).1 :=
  (((A.pass_a E Ex M Wp Kc msg).seq (A.pass_b E Ex M Wp Kc msg)).seq
      (A.pass_c E Ex M Wp Kc msg)).seq
    (A.pass_d E Ex M Wp Kc msg)

end Pass

/-- an auxiliary lemma: the output claim on the named entries -/
theorem LdLkp.LkAsm2.outN_iff (A : LkAsm2 E) (N : Type) [Fintype N] (ι : N → A.J)
    (hι : Function.Injective ι) (hP : A.PlacesIn fun j => j ∈ Set.range ι)
    (o : A.XB) (m : A.J → E) :
    A.lk.out id (A.entN ι) (A.rdN ι o) m ↔ A.lk.out id id (A.rd o) m := by
  obtain ⟨h1, h2⟩ := ldLkpAsm2_suppOut E A N ι hι hP o (A.v' + 1) (A.key (A.rd o).1 m) m
  exact and_congr h1 (and_congr h2 Iff.rfl)

theorem LdLkp.LkAsm2.passN (A : LkAsm2 E) (N : Type) (ι : N → A.J) (Ex : ExtSpec)
    (M Wp Kc : Type) (msg : M → A.J → E) :
    (A.baseN ι Ex M Wp Kc msg).R.Passes id fun x' => x'.1 :=
  (A.pass2 E Ex M Wp Kc msg).post _ _ fun o x' e => by
    obtain rfl := Option.some.inj e
    rfl

theorem ldLkpAsm2N_base : Spec.ldLkpAsm2N_base E := by
  intro p _ A N _ ι Mu Ex Kc M Wp R0 msg hι hP hA hMu
  have g := A.chain_good E p Mu Ex Kc M Wp R0 msg hA hMu
  unfold BkA.Good at g ⊢
  refine goodAt_postMap Kc M _ _ _ Ex Ex Wp Wp _ _ _ _ _ _ _ (A.rdN ι) g ?_ ?_ ?_ ?_
  · intro o y w h
    exact ⟨h.1,
      (A.outN_iff E N ι hι hP o _).mpr
        ((A.out_iff o _).mpr ⟨⟨⟨⟨h.2.1.1.1.1, trivial⟩, h.2.1.1.2⟩, h.2.1.2⟩, h.2.2⟩)⟩
  · exact fun _ _ h => h
  · exact fun _ => rfl
  · intro o y w _ h
    exact ⟨h.1, (A.out_iff o _).mp ((A.outN_iff E N ι hι hP o _).mp h.2)⟩

theorem ldLkpAsm2N_ok : Spec.ldLkpAsm2N_ok E := by
  intro p _ A N _ ι Mu S E₀ Kc Wp R0 msg hι hP hA hMu
  exact sigLift_goodB E S Kc _ _ Wp Wp E₀ E₀ _ _ _ _ _ _
    (ldLkpAsm2N_base E p A N ι Mu E₀ Kc S.Msg Wp R0 msg hι hP hA hMu)

theorem ldLkpAsm2N_plain : Spec.ldLkpAsm2N_plain E := fun A _ ι Ex M Wp Kc msg =>
  plain_postM (A.plain2 E Ex M Wp Kc msg) (A.rdN ι)

theorem ldLkpAsm2N_idx : Spec.ldLkpAsm2N_idx E := by
  intro p _ A N _ ι Mu C S rc R0 msg hι hP hA hMu
  exact idxLift_goodB E C S Unit _ _ Unit Unit _ _ _ _ rc (fun x => rc x.1) (fun _ _ _ wp => wp) _
    (fun x y τ x' h => congrArg rc (A.passN E N ι C.E0 (C.Msg × S.Msg) Unit Unit msg x y τ x' h))
    (ldLkpAsm2N_plain E A N ι C.E0 (C.Msg × S.Msg) Unit Unit msg).copies.copy
    (ldLkpAsm2N_base E p A N ι Mu C.E0 Unit (C.Msg × S.Msg) Unit R0 msg hι hP hA hMu)

theorem ldLkpAsm2N_plainI : Spec.ldLkpAsm2N_plainI E := by
  intro A N ι C M msg
  have h := ldLkpAsm2N_plain E A N ι C.E0 (C.Msg × M) Unit Unit msg
  refine ⟨h.copies, fun w x c ρ => ?_, h.budAll, fun w x => h.free (idxIn C w) x⟩
  show ((((A.baseN ι C.E0 (C.Msg × M) Unit Unit msg).H.mapW (idxIn C) fun w o =>
        (w.1, (w.2.1, o.2))).strat
      w x c).run ρ).2.2 = w
  rw [Honest.mapW_run]

theorem ldLkpAsm2N_idxStep : Spec.ldLkpAsm2N_idxStep E := fun A N ι C S msg =>
  lift_idxStep S (ldLkpAsm2N_plainI E A N ι C S.Msg msg)

theorem ldLkpAsm2N_passes : Spec.ldLkpAsm2N_passes E := fun A N ι C S msg =>
  lift_passes (b := A.baseIN ι C S.Msg msg) S (A.passN E N ι C.E0 (C.Msg × S.Msg) Unit Unit msg)

theorem ldLkpAsm2N_same : Spec.ldLkpAsm2N_same E := fun A N ι C S msg =>
  lift_keepsW S (ldLkpAsm2N_plainI E A N ι C S.Msg msg)

theorem ldLkpAsm2N_len : Spec.ldLkpAsm2N_len E := by
  intro A N ι Ex M Wp Kc msg x y τ xo h
  obtain ⟨o, _, ho⟩ := Option.bind_eq_some_iff.mp h
  rw [← Option.some.inj ho]
  show ((A.rd o).2.2.map (Row.pull ι)).length = A.nRows
  rw [List.length_map]
  exact ldLkpAsm2_len E A o

end
end Cb
