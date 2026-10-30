-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLkpAsm2Proofs.lean: the proofs of the statements of Cb/Ld/LdLkpAsm2.lean (the assembled
lookup, `LkAsm2`).

The theorems are "ldLkpAsm2_* : Cb.Spec.ldLkpAsm2_*"; before them auxiliary definitions and lemmas:
the claims that wait at each joint by name (`PKc`, `PTc`, `Opn`, `Num`, `Bts`, `S1`, `Φ1`, `ΨK`,
`ΨT`), the junctions between the parts, `enter_iff` (the claim at the point, read again after the
keys' side, is the forest's claim at level 0), the chain before the read-out (`chain_good`).

The parts, in order (the head of Cb/Ld/LdLkpAsm2.lean tells them under "The protocol, in order", the
read-out at `A.rd`): the head (first challenge λ, the tie); the point for the table's products; the
keys' side (the keys' tree); the table's forest; the closing (of the table's factor); the bit test;
last the read-out (`A.rd`). States are nested: `A.X2` after the head, `A.XR` after the point, `A.X4`
after the keys' side, `A.XE` after the closing, `A.XB` at the end.

Main names (statements and hypotheses: Cb/Ld/LdLkpAsm2.lean):
  `ldLkpAsm2_base`: `BkA.Good` of the whole chain at the base (`A.baseA`).
  `ldLkpAsm2_ok`: `SubR.OK` of the chain lifted over a signature (`A.sub`).
  `ldLkpAsm2_rounds`: the number of rounds.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdLkpAsm2
import Cb.Ld.LdLkpAsmProofs
import Cb.Ld.LdLkpEndUProofs
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop IOR Hiop Prob Cb.LdLkp Cb.Lkp Finset

section
variable {E : Type} [Field E] [Fintype E]

namespace LdLkp
namespace LkAsm2
variable (A : LkAsm2 E)

/-- the claims that wait after the head, by name -/
def PKc (x : A.X2) (m : A.J → E) : Prop :=
  keyProd (A.v' + 1) (A.key (A.b2 x).1 m) (A.b2 x).2 + m (A.cS false) * (A.H.tie.bK A.n x.2).1 =
    (A.H.tie.bK A.n x.2).2
def PTc (x : A.X2) (m : A.J → E) : Prop :=
  ∀ j < A.n,
    A.H.PT (A.b2 x) m j + m (A.cAt j true) * (A.H.tie.bT A.n x.2 j).1 = (A.H.tie.bT A.n x.2 j).2
def Opn (x : A.X2) (m : A.J → E) : Prop := A.H.tie.claim (A.n + 1) x m
def Num (m : A.J → E) : Prop := NumKeys (A.v' + 1) A.d (A.n + 1) (A.H.bit m)
def Bts (m : A.J → E) : Prop := Bits A.d A.w (A.H.bit m)

/-- the claim at the point -/
def S1 (x : A.XR) (m : A.J → E) : Prop :=
  ((A.I1.DT2 A.n).lv 0).T.SumHolds x fun j => m (((A.I1.DT2 A.n).lv 0).toJ j)

/-- `Φ1`, `ΨK`, `ΨT`: what rides past the point; past the keys' side; past the table's side.
P: what the honest side knows more -/
def Φ1 (P : A.St → (A.J → E) → Prop) (x : A.X2) (m : A.J → E) : Prop :=
  ((A.H.RestOn (A.b2 x) m ∧ P (A.b2 x).1 m) ∧ RowsHold (A.rows2 x) m) ∧ A.PKc x m
def ΨK (P : A.St → (A.J → E) → Prop) (x : A.XR) (m : A.J → E) : Prop :=
  ((A.H.RestOn (A.b2 (A.oR x)) m ∧ P (A.b2 (A.oR x)).1 m) ∧ RowsHold (A.rows2 (A.oR x)) m) ∧
  A.S1 x m
def ΨT (P : A.St → (A.J → E) → Prop) (x : A.X4) (m : A.J → E) : Prop :=
  ((A.Num m ∧ P (A.b2 (A.oR (A.o4 x))).1 m) ∧ RowsHold (A.rows2 (A.oR (A.o4 x))) m) ∧
  RowsHold (A.rows4 x) m ∧
  (A.clK x).Holds (A.v' + 1) (A.key (A.b2 (A.oR (A.o4 x))).1 m) m

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

open Classical in
/-- If n + 1 ≤ 2^w: the claims on the products of the table at the counting positions are the claims
that the point takes; at the idle positions nothing is claimed. -/
theorem roots_iff (hW : A.n + 1 ≤ 2 ^ A.w) (x : A.X2) (m : A.J → E) :
    (A.PTc x m ∧ A.Opn x m) ↔ A.R.Holds x m := by
  have hU : ∀ θ : Fin (A.w + 0) → Bool,
      numLE θ < A.n + 1 → A.R.D.U x m 0 θ = A.H.PT (A.b2 x) m (numLE θ) := fun θ hθ =>
    (ldLkpInst2_root E A.I1 A.n x m θ).trans (ldLkpInst2_count E A.I1 A.n _ m _ _ hθ)
  have hI : ∀ θ : Fin (A.w + 0) → Bool, A.n + 1 ≤ numLE θ → A.R.D.U x m 0 θ = 1 := fun θ hθ =>
    (ldLkpInst2_root E A.I1 A.n x m θ).trans (ldLkpInst2_idle E A.I1 A.n _ m _ _ hθ)
  have hO : A.Opn x m ↔
      A.H.PT (A.b2 x) m A.n +
          ∑ j, pushJ (A.H.tie.lv (A.n + 1)).toJ ((A.H.tie.lv (A.n + 1)).T.slS x.2) j * m j =
        x.1 := by
    have hq : A.H.tie.Q (A.b2 x) m A.n = A.H.PT (A.b2 x) m A.n := ldLkpHead_open E A.H (A.b2 x) m
    rw [ldLkpP_push, ← hq]
    exact Iff.rfl
  constructor
  · rintro ⟨hT, hOp⟩ (θ : Fin (A.w + 0) → Bool)
    show A.R.D.U x m 0 θ + ∑ j, A.formT x θ j * m j = A.tgtT x θ
    by_cases h1 : numLE θ < A.n
    · have ef : A.formT x θ =
        fun j =>
          if j = A.cAt (numLE θ) true then (A.H.tie.bT A.n x.2 (numLE θ)).1 else 0 := if_pos h1
      have et : A.tgtT x θ = (A.H.tie.bT A.n x.2 (numLE θ)).2 := if_pos h1
      rw [hU θ (by omega), ef, et, sum_one]
      exact hT _ h1
    · by_cases h2 : numLE θ = A.n
      · have ef : A.formT x θ =
            pushJ (A.H.tie.lv (A.n + 1)).toJ ((A.H.tie.lv (A.n + 1)).T.slS x.2) :=
          (if_neg h1).trans (if_pos h2)
        have et : A.tgtT x θ = x.1 := (if_neg h1).trans (if_pos h2)
        rw [hU θ (by omega), ef, et, h2]
        exact hO.mp hOp
      · have ef : A.formT x θ = 0 := (if_neg h1).trans (if_neg h2)
        have et : A.tgtT x θ = 1 := (if_neg h1).trans (if_neg h2)
        rw [hI θ (by omega), ef, et]
        simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero, add_zero]
  · intro h
    have h' : ∀ θ : Fin (A.w + 0) → Bool, A.R.D.U x m 0 θ + ∑ j, A.formT x θ j * m j = A.tgtT x θ :=
      h
    refine ⟨fun j hj => ?_, hO.mpr ?_⟩
    · obtain ⟨θ, rfl⟩ := numLE_surj (k := A.w + 0) (c := j) (by show j < 2 ^ A.w; omega)
      have ef : A.formT x θ =
        fun j =>
          if j = A.cAt (numLE θ) true then (A.H.tie.bT A.n x.2 (numLE θ)).1 else 0 := if_pos hj
      have et : A.tgtT x θ = (A.H.tie.bT A.n x.2 (numLE θ)).2 := if_pos hj
      have := h' θ
      rw [hU θ (by omega), ef, et, sum_one] at this
      exact this
    · obtain ⟨θ, hθ⟩ := numLE_surj (k := A.w + 0) (c := A.n) (by show A.n < 2 ^ A.w; omega)
      have h1 : ¬ numLE θ < A.n := by omega
      have ef : A.formT x θ = pushJ (A.H.tie.lv (A.n + 1)).toJ ((A.H.tie.lv (A.n + 1)).T.slS x.2) :=
        (if_neg h1).trans (if_pos hθ)
      have et : A.tgtT x θ = x.1 := (if_neg h1).trans (if_pos hθ)
      have := h' θ
      rw [hU θ (by omega), ef, et, hθ] at this
      exact this

/-- junction 1: if n + 1 ≤ 2^w, what the head leaves is what the point takes -/
theorem junction1 (hW : A.n + 1 ≤ 2 ^ A.w) (P : A.St → (A.J → E) → Prop) (x : A.X2) (m : A.J → E) :
    (((A.H.RestOn (A.b2 x) m ∧ P (A.b2 x).1 m) ∧ A.H.tie.Done A.n x.2 m) ∧
      A.H.tie.claim (A.n + 1) x m) ↔
    (A.Φ1 P x m ∧ A.R.Holds x m) := by
  rw [← A.roots_iff hW x m]
  constructor
  · rintro ⟨⟨hRP, hr, hk, ht⟩, ho⟩
    exact ⟨⟨⟨hRP, hr⟩, hk⟩, ht, ho⟩
  · rintro ⟨⟨⟨hRP, hr⟩, hk⟩, ht, ho⟩
    exact ⟨⟨hRP, hr, hk, ht⟩, ho⟩

/-- junction 2: what the point leaves is what the keys' side takes -/
theorem junction2 (P : A.St → (A.J → E) → Prop) (x : A.XR) (m : A.J → E) :
    ((A.Φ1 P ((A.I1.DT2 A.n).root 0 x.2).1 m ∧ RowsHold ((A.I1.DT2 A.n).rowsAt 0 x.2) m) ∧
      ((A.I1.DT2 A.n).lv 0).T.SumHolds x fun j => m (((A.I1.DT2 A.n).lv 0).toJ j)) ↔
    (A.ΨK P x m ∧
      keyProd (A.v' + 1) (A.IK.key (A.IK.st x) m) (A.IK.lam x) + ∑ j, A.IK.fK x j * m j =
        A.tK (A.oR x)) := by
  have hs : ∑ j, A.IK.fK x j * m j = m (A.cS false) * (A.H.tie.bK A.n (A.oR x).2).1 := sum_one _ _ _
  rw [hs]
  constructor
  · rintro ⟨⟨⟨hRr, hk⟩, _⟩, h1⟩
    exact ⟨⟨hRr, h1⟩, hk⟩
  · rintro ⟨⟨hRr, h1⟩, hk⟩
    exact ⟨⟨⟨hRr, hk⟩, fun r hr => absurd hr List.not_mem_nil⟩, h1⟩

/-- the claim at the point, read again after the keys' side, is the forest's claim at level 0 -/
theorem enter_iff (x : A.X4) (m : A.J → E) :
    (A.D.lv 0).T.SumHolds (A.enterT x) (fun j => m ((A.D.lv 0).toJ j)) ↔ A.S1 (A.o4 x) m :=
  (ldLkpP_sum E A.D (ldLkpInst2_step E A.IT A.n) 0 (A.enterT x) m).trans
    (ldLkpP_sum E (A.I1.DT2 A.n) (ldLkpInst2_step E A.I1 A.n) 0 (A.o4 x) m).symm

/-- the rows of the table's side say: the bit test's output rows, the closing's end claim, the rows
of the forest -/
theorem rowsB_iff (o : A.XB) (m : A.J → E) :
    RowsHold (A.rowsB o) m ↔
    A.Bt.zc.next.par.OutHolds o m ∧
    A.En.par.MidHolds (A.outE o) m ∧
    RowsHold (A.D.rowsAt A.d (A.outE o).st) m := by
  rw [ldLkpBit_rows E A.Bt o m, ldLkpEndU_row E A.En (A.outE o) m]
  refine (rowsHold_append (A.D.rowsAt A.d (A.outE o).st) _ m).trans ?_
  constructor
  · rintro ⟨h1, h2⟩
    have hE := h2
      ⟨A.En.par.slU A.En.rowB (A.En.outOf (A.outE o)), A.En.par.tU (A.En.outOf (A.outE o))⟩
      List.mem_cons_self
    have hU := h2 ⟨A.Bt.zc.next.par.slU (fun _ b => b.elim) o, A.Bt.zc.next.par.tU o⟩
      (List.mem_cons_of_mem _ List.mem_cons_self)
    have hV := h2 ⟨A.Bt.zc.next.par.slE A.Bt.rowA () o, o.vals ()⟩
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
    exact ⟨⟨hU, hV⟩, hE, h1⟩
  · rintro ⟨⟨hU, hV⟩, hE, h1⟩
    refine ⟨h1, fun r hr => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hE
    · exact hU
    · exact hV

/-- the read-out -/
theorem out_iff (o : A.XB) (m : A.J → E) :
    A.lk.out id id (A.rd o) m ↔ (A.ΨT (fun _ _ => True) (A.oldT o) m ∧ RowsHold (A.rowsB o) m) := by
  have e : RowsHold (A.rd o).2.2 m ↔
      A.Num m ∧
      RowsHold (A.rows2 (A.oR (A.o4 (A.oldT o)))) m ∧
      RowsHold (A.rows4 (A.oldT o)) m ∧
      RowsHold (A.rowsB o) m := by
    show RowsHold
        (A.rows2 (A.oR (A.o4 (A.oldT o))) ++ (A.rows4 (A.oldT o) ++ (A.rowsB o ++ [A.numRow]))) m ↔
      _
    rw [rowsHold_append, rowsHold_append, rowsHold_append, rowsHold_cons, A.num_iff]
    exact ⟨fun h => ⟨h.2.2.2.1, h.1, h.2.1, h.2.2.1⟩,
      fun h => ⟨h.2.1, h.2.2.1, h.2.2.2, h.1, fun r hr => absurd hr List.not_mem_nil⟩⟩
  constructor
  · rintro ⟨hc, hr, _⟩
    obtain ⟨hn, h2, h4, hB⟩ := e.mp hr
    exact ⟨⟨⟨⟨hn, trivial⟩, h2⟩, h4, hc⟩, hB⟩
  · rintro ⟨⟨⟨⟨hn, _⟩, h2⟩, h4, hc⟩, hB⟩
    exact ⟨hc, e.mpr ⟨hn, h2, h4, hB⟩, trivial⟩

end LkAsm2
end LdLkp
end

section
variable (E : Type) [Field E] [Fintype E]

/-- what rides through the forest: the caller's joint, ΨT, and "all bits are bits" -/
def LdLkp.LkAsm2.A0 (A : LkAsm2 E) {Ex : ExtSpec} {Kc M Wp : Type}
    (R0 : Rels Kc A.St Ex (M × Wp)) (msg : M → A.J → E) (Mu : A.St → (A.J → E) → Prop) :
    Rels Kc (A.D.lv 0).T.St Ex (M × Wp) :=
  cj R0 msg (fun s => (A.b2 (A.oR (A.o4 s.1))).1) (fun s m => A.ΨT Mu s.1 m ∧ A.Bts m)
    fun s m => A.ΨT (fun _ _ => True) s.1 m ∧ A.Bts m

/-- the keys' side, the step into the forest, the levels below l -/
theorem LdLkp.LkAsm2.forest_good (A : LkAsm2 E) (Mu : A.St → (A.J → E) → Prop) (Ex : ExtSpec)
    (Kc M Wp : Type) (R0 : Rels Kc A.St Ex (M × Wp)) (msg : M → A.J → E) (l : ℕ) :
    (A.forest Ex M Wp Kc msg l).Good
      (cj R0 msg (fun x => (A.b2 (A.oR x)).1)
        (fun x m =>
          A.ΨK Mu x m ∧
          keyProd (A.v' + 1) (A.IK.key (A.IK.st x) m) (A.IK.lam x) + ∑ j, A.IK.fK x j * m j =
            A.tK (A.oR x)) fun x m =>
              A.ΨK (fun _ _ => True) x m ∧
              keyProd (A.v' + 1) (A.IK.key (A.IK.st x) m) (A.IK.lam x) + ∑ j, A.IK.fK x j * m j =
                A.tK (A.oR x))
      (A.D.jtAt msg (A.A0 E R0 msg Mu) l) := by
  induction l with
  | zero =>
    have g := ldLkpSegK_good E A.IK A.v' (fun x => A.tK (A.oR x)) Ex Kc A.St M Wp R0 msg
      (fun x => (A.b2 (A.oR x)).1) (A.ΨK Mu) (A.ΨK fun _ _ => True)
    unfold BkA.Good at g ⊢
    rw [show A.D.jtAt msg (A.A0 E R0 msg Mu) 0 = _
        from ldLkpK_tree E A.D Ex Kc A.St M Wp R0 msg (fun s => (A.b2 (A.oR (A.o4 s.1))).1)
          (fun s m => A.ΨT Mu s.1 m ∧ A.Bts m)
          (fun s m => A.ΨT (fun _ _ => True) s.1 m ∧ A.Bts m) 0]
    refine goodAt_postMap Kc M _ _ _ Ex Ex Wp Wp _ _ _ _ _ _ _ A.enterT g ?_ ?_ ?_ ?_
    · intro x y w h
      obtain ⟨hR, ⟨⟨⟨⟨⟨hb, hn⟩, hP⟩, hr2⟩, h1⟩, hr4⟩, hc⟩ := h
      exact ⟨hR,
        ⟨⟨⟨⟨⟨hn, hP⟩, hr2⟩, hr4, hc⟩, hb⟩, fun r hr => absurd hr List.not_mem_nil⟩,
        (A.enter_iff x _).mpr h1⟩
    · exact fun _ _ h => h
    · exact fun _ => rfl
    · intro x y w _ h
      obtain ⟨hR, ⟨⟨⟨⟨⟨hn, hP⟩, hr2⟩, hr4, hc⟩, hb⟩, _⟩, h1⟩ := h
      exact ⟨hR, ⟨⟨⟨⟨⟨hb, hn⟩, hP⟩, hr2⟩, (A.enter_iff x _).mp h1⟩, hr4⟩, hc⟩
  | succ l ih =>
    exact segT_seq ih
      (ldLkpP_level E A.D Ex M Wp Kc msg (A.A0 E R0 msg Mu) l (ldLkpInst2_step E A.IT A.n))

/-- the chain before the read-out -/
theorem LdLkp.LkAsm2.chain_good (p : ℕ) [CharP E p] (A : LkAsm2 E) (Mu : A.St → (A.J → E) → Prop)
    (Ex : ExtSpec) (Kc M Wp : Type) (R0 : Rels Kc A.St Ex (M × Wp)) (msg : M → A.J → E)
    (hA : A.H.lkb.Adm p) (hMu : A.H.MuOn Mu) :
    (A.chainA Ex M Wp Kc msg).Good (cj R0 msg id (A.lk.inP Mu) A.lk.inR)
      (cj R0 msg (fun o => (A.b2 (A.oR (A.o4 (A.oldT o)))).1)
        (fun o m => A.ΨT Mu (A.oldT o) m ∧ RowsHold (A.rowsB o) m)
        fun o m => A.ΨT (fun _ _ => True) (A.oldT o) m ∧ RowsHold (A.rowsB o) m) := by
  -- the head
  have g1 := ldLkpHead2_good E p A.H Mu Ex Kc M Wp R0 msg hA hMu
  -- the point
  let R1 : Rels Kc A.X2 Ex (M × Wp) :=
    cj R0 msg (fun x => (A.b2 x).1) (A.Φ1 Mu) (A.Φ1 fun _ _ => True)
  have g2 : (A.R.rootA Ex M Wp Kc).Good
      ⟨fun st y w => R1.rel st y w ∧ A.R.Holds st (msg w.1),
        fun a w => R1.relR a w ∧ A.R.Holds a.1 (msg w.1),
        R1.on, R1.core⟩
      ((A.I1.DT2 A.n).jtAt msg (A.R.toIn.ride R1) 0) :=
    ldLkpRoot_good E A.R Ex M Wp Kc R1 msg (ldLkpInst2_step E A.I1 A.n) fun _ _ _ => rfl
  have e1 : cj R0 msg (fun x : A.X2 => (A.b2 x).1)
        (fun x m =>
          ((A.H.RestOn (A.b2 x) m ∧ Mu (A.b2 x).1 m) ∧ A.H.tie.Done A.n x.2 m) ∧
          A.H.tie.claim (A.n + 1) x m)
        (fun x m =>
          (A.H.RestOn (A.b2 x) m ∧ A.H.tie.Done A.n x.2 m) ∧ A.H.tie.claim (A.n + 1) x m) =
      (⟨fun st y w => R1.rel st y w ∧ A.R.Holds st (msg w.1),
        fun a w => R1.relR a w ∧ A.R.Holds a.1 (msg w.1),
        R1.on,
        R1.core⟩ : Rels Kc A.X2 Ex (M × Wp)) :=
    (ldLkpK_congr E Kc A.St M Wp A.J A.X2 Ex R0 msg (fun x => (A.b2 x).1) _ _
        (fun x m => A.Φ1 Mu x m ∧ A.R.Holds x m)
        (fun x m => A.Φ1 (fun _ _ => True) x m ∧ A.R.Holds x m) (fun x m => A.junction1 hA.1 Mu x m)
        (fun x m =>
          Iff.trans (by simp only [and_true]) (A.junction1 hA.1 (fun _ _ => True) x m))).trans
      (ldLkpK_and E Kc A.St M Wp A.J A.X2 Ex R0 msg (fun x => (A.b2 x).1) (A.Φ1 Mu)
        (A.Φ1 fun _ _ => True) (fun x m => A.R.Holds x m) fun x m => A.R.Holds x m).symm
  have e2 : (A.I1.DT2 A.n).jtAt msg (A.R.toIn.ride R1) 0 =
      cj R0 msg (fun x : A.XR => (A.b2 (A.oR x)).1)
        (fun x m =>
          A.ΨK Mu x m ∧
          keyProd (A.v' + 1) (A.IK.key (A.IK.st x) m) (A.IK.lam x) + ∑ j, A.IK.fK x j * m j =
            A.tK (A.oR x)) fun x m =>
              A.ΨK (fun _ _ => True) x m ∧
              keyProd (A.v' + 1) (A.IK.key (A.IK.st x) m) (A.IK.lam x) + ∑ j, A.IK.fK x j * m j =
                A.tK (A.oR x) :=
    (ldLkpK_tree E (A.I1.DT2 A.n) Ex Kc A.St M Wp R0 msg (fun s => (A.b2 s.1).1)
        (fun s m => A.Φ1 Mu s.1 m) (fun s m => A.Φ1 (fun _ _ => True) s.1 m) 0).trans
      (ldLkpK_congr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (fun x m => A.junction2 Mu x m)
        (fun x m => A.junction2 (fun _ _ => True) x m))
  -- the keys' side and the forest
  have g3 := A.forest_good E Mu Ex Kc M Wp R0 msg A.d
  -- the closing
  let A1 : Rels Kc (A.D.lv A.d).T.St Ex (M × Wp) := A.D.ride msg (A.A0 E R0 msg Mu) A.d
  have g4 : (A.endA Ex M Wp Kc msg).Good
      (A.En.relsIn A1 fun w => msg w.1) (A.En.par.baseMid A1 fun w => msg w.1) :=
    ldLkpEndU_goodAt E A.En Ex M Wp Kc A1 msg
  have e3 : A.D.jtAt msg (A.A0 E R0 msg Mu) A.d = A.En.relsIn A1 fun w => msg w.1 :=
    ldLkpInst2_top E A.IT A.n A.wE Ex M Wp Kc msg (A.A0 E R0 msg Mu)
  -- the bit test
  let R2 : Rels Kc A.XE Ex (M × Wp) :=
    cj R0 msg (fun z : A.XE => (A.b2 (A.oR (A.o4 (A.D.root A.d z.st).1))).1)
      (fun z m =>
        (A.ΨT Mu (A.D.root A.d z.st).1 m ∧ RowsHold (A.D.rowsAt A.d z.st) m) ∧
        A.En.par.MidHolds z m) fun z m =>
          (A.ΨT (fun _ _ => True) (A.D.root A.d z.st).1 m ∧ RowsHold (A.D.rowsAt A.d z.st) m) ∧
          A.En.par.MidHolds z m
  have g5 : (A.bitA Ex M Wp Kc msg).Good
      ⟨fun st y w => R2.rel st y w ∧ A.Bt.AllBits (msg w.1),
        fun a w => R2.relR a w ∧ A.Bt.AllBits (msg w.1),
        R2.on, R2.core⟩
      (A.Bt.zc.next.par.baseOut (A.Bt.zc.toIn.ride R2) fun w => msg w.1) :=
    ldLkpBit_goodAt E A.Bt Ex M Wp Kc R2 msg
  have hb : ∀ m, A.Bt.AllBits m ↔ A.Bts m := fun m => ldLkpInst_bits E A.IT _ A.wB A.cB m
  obtain ⟨r1, r2, r3, r4⟩ := ldLkpP_ride E A.D Ex M Wp Kc msg (A.A0 E R0 msg Mu) A.d
  have e4 : A.En.par.baseMid A1 (fun w => msg w.1) =
      (⟨fun st y w => R2.rel st y w ∧ A.Bt.AllBits (msg w.1),
        fun a w => R2.relR a w ∧ A.Bt.AllBits (msg w.1),
        R2.on,
        R2.core⟩ : Rels Kc A.XE Ex (M × Wp)) := by
    refine LdLkp.rels_ext (funext fun z => funext fun y => funext fun w => propext ?_)
      (funext fun a => funext fun w => propext ?_) (funext fun a => propext (r3 a.1.st a.2)) r4
    · show A1.rel z.st y w ∧ A.En.par.MidHolds z (msg w.1) ↔ _
      rw [r1]
      exact ⟨fun h => ⟨⟨h.1.1.1, ⟨h.1.1.2.1, h.1.2⟩, h.2⟩, (hb _).2 h.1.1.2.2⟩,
        fun h => ⟨⟨⟨h.1.1, h.1.2.1.1, (hb _).1 h.2⟩, h.1.2.1.2⟩, h.1.2.2⟩⟩
    · show A1.relR (a.1.st, a.2) w ∧ A.En.par.MidHolds a.1 (msg w.1) ↔ _
      rw [r2]
      exact ⟨fun h => ⟨⟨h.1.1.1, ⟨h.1.1.2.1, h.1.2⟩, h.2⟩, (hb _).2 h.1.1.2.2⟩,
        fun h => ⟨⟨⟨h.1.1, h.1.2.1.1, (hb _).1 h.2⟩, h.1.2.1.2⟩, h.1.2.2⟩⟩
  have e5 : A.Bt.zc.next.par.baseOut (A.Bt.zc.toIn.ride R2) (fun w => msg w.1) =
      cj R0 msg (fun o => (A.b2 (A.oR (A.o4 (A.oldT o)))).1)
        (fun o m => A.ΨT Mu (A.oldT o) m ∧ RowsHold (A.rowsB o) m)
        fun o m => A.ΨT (fun _ _ => True) (A.oldT o) m ∧ RowsHold (A.rowsB o) m := by
    refine LdLkp.rels_ext (funext fun o => funext fun y => funext fun w => propext ?_)
      (funext fun a => funext fun w => propext ?_) rfl rfl
    · show R2.rel (A.outE o) y w ∧ A.Bt.zc.next.par.OutHolds o (msg w.1) ↔
        R0.rel (A.b2 (A.oR (A.o4 (A.oldT o)))).1 y w ∧
        A.ΨT Mu (A.oldT o) (msg w.1) ∧
        RowsHold (A.rowsB o) (msg w.1)
      rw [A.rowsB_iff]
      exact ⟨fun h => ⟨h.1.1, h.1.2.1.1, h.2, h.1.2.2, h.1.2.1.2⟩,
        fun h => ⟨⟨h.1, ⟨h.2.1, h.2.2.2.2⟩, h.2.2.2.1⟩, h.2.2.1⟩⟩
    · show R2.relR (A.outE a.1, a.2) w ∧ A.Bt.zc.next.par.OutHolds a.1 (msg w.1) ↔
        R0.relR ((A.b2 (A.oR (A.o4 (A.oldT a.1)))).1, a.2) w ∧
        A.ΨT (fun _ _ => True) (A.oldT a.1) (msg w.1) ∧
        RowsHold (A.rowsB a.1) (msg w.1)
      rw [A.rowsB_iff]
      exact ⟨fun h => ⟨h.1.1, h.1.2.1.1, h.2, h.1.2.2, h.1.2.1.2⟩,
        fun h => ⟨⟨h.1, ⟨h.2.1, h.2.2.2.2⟩, h.2.2.2.1⟩, h.2.2.1⟩⟩
  rw [e2] at g2
  rw [e3] at g3
  rw [e4] at g4
  rw [e5] at g5
  exact segT_seq (segT_seq (segT_seq (segT_seq (e1 ▸ g1) g2) g3) g4) g5

theorem ldLkpAsm2_base : Spec.ldLkpAsm2_base E := by
  intro p _ A Mu Ex Kc M Wp R0 msg hA hMu
  have g := A.chain_good E p Mu Ex Kc M Wp R0 msg hA hMu
  unfold BkA.Good at g ⊢
  refine goodAt_postMap Kc M _ _ _ Ex Ex Wp Wp _ _ _ _ _ _ _ A.rd g ?_ ?_ ?_ ?_
  · intro o y w h
    exact ⟨h.1, (A.out_iff o _).mpr ⟨⟨⟨⟨h.2.1.1.1.1, trivial⟩, h.2.1.1.2⟩, h.2.1.2⟩, h.2.2⟩⟩
  · exact fun _ _ h => h
  · exact fun _ => rfl
  · intro o y w _ h
    exact ⟨h.1, (A.out_iff o _).mp h.2⟩

theorem ldLkpAsm2_ok : Spec.ldLkpAsm2_ok E := by
  intro p _ A Mu S E₀ Kc Wp R0 msg hA hMu
  exact sigLift_goodB E S Kc _ _ Wp Wp E₀ E₀ _ _ _ _ _ _
    (ldLkpAsm2_base E p A Mu E₀ Kc S.Msg Wp R0 msg hA hMu)

theorem LdLkp.LkAsm2.forest_len
    (A : LkAsm2 E) (Ex : ExtSpec) (M Wp Kc : Type) (msg : M → A.J → E) (l : ℕ) :
    (A.forest Ex M Wp Kc msg l).R.shape.length =
      (∑ i ∈ Finset.range (A.v' + 1), (0 + i + 3 + 1)) +
        ∑ i ∈ Finset.range l, (A.w + i + 3 + 1) := by
  induction l with
  | zero =>
      rw [Finset.sum_range_zero]
      exact ldLkpSegK_rounds E A.IK A.v' (fun x => A.tK (A.oR x)) Ex M Wp Kc msg
  | succ l ih =>
      have hl : (A.D.levA Ex Wp Kc msg l).R.shape.length = A.w + l + 3 + 1 := by
        have e : (A.D.levA Ex Wp Kc msg l).R.shape =
            ((A.D.lv l).T.par.psc Ex).shape ++ (A.D.lineA Ex M Wp Kc l).R.shape := rfl
        rw [e, List.length_append, psc_our_len E (A.D.lv l).T Ex, A.D.fmt_len l]
        rfl
      have e : (A.forest Ex M Wp Kc msg (l + 1)).R.shape =
          (A.forest Ex M Wp Kc msg l).R.shape ++ (A.D.levA Ex Wp Kc msg l).R.shape := rfl
      rw [e, List.length_append, ih, hl, Finset.sum_range_succ (fun i => A.w + i + 3 + 1) l]
      exact Nat.add_assoc _ _ _

theorem ldLkpAsm2_rounds : Spec.ldLkpAsm2_rounds E := by
  intro A Ex M Wp Kc msg
  have e : (A.baseA Ex M Wp Kc msg).R.shape =
      ((((A.H.headA Ex M Wp Kc msg).R.shape ++ [IOR.drawRound A.R.toIn.ev.D]) ++
            (A.forest Ex M Wp Kc msg A.d).R.shape) ++
          (A.En.par.core Ex).shape) ++
        ([IOR.drawRound A.Bt.zc.toIn.ev.D] ++ (A.Bt.zc.next.par.psc Ex).shape) := rfl
  rw [e, List.length_append, List.length_append, List.length_append, List.length_append,
    List.length_append, ldLkpHead_rounds E A.H Ex M Wp Kc msg, A.forest_len E Ex M Wp Kc msg A.d,
    ldLkpEndU_len E A.En Ex, psc_our_len E A.Bt.zc.next Ex]
  show _ + (1 + ((List.replicate (A.w + A.d) (pfCube E 2)).length + 3)) = _
  rw [List.length_replicate]
  rfl

end
end Cb
