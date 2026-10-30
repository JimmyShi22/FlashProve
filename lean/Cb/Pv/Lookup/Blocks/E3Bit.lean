-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Lookup/Blocks/E3Bit.lean: the bit test of a lookup, with an order for the variables of its
sumcheck: names.

Definitions, statements (in `Cb.Spec`) and proofs.
ZeroCube (Cb/Ld/LdZero.lean) and LkBit (Cb/Ld/LdLkpBit.lean) have the field sg: the j-th variable (j
from 0, in the order of their rounds) of the sumcheck that follows the draw is coordinate sg j and
has its weight at coordinate sg j of the drawn point (ZeroCubeP.vars_at). This file has the names
under which the files of Cb/Pv/Lookup use them: ZeroCubeP and LkBitP are these two records, and
LkInst.bitBP is the bit test of a lookup at a given order. Each statement with P in its name is the
statement of the same name without it (Cb/Ld/LdZero.lean, Cb/Ld/LdLineAt.lean, Cb/Ld/LdLkpBit.lean),
written out once more, and is proved by it; `Spec.ldLkpInst_bitsP` is `Spec.ldLkpInst_bits`
(Cb/Ld/LdLkpInst.lean) said of bitBP at every order.

Main names:
  `Spec.ldZeroP_psc_goodAt`: the zerocheck on the cube, then the sumcheck, are good (`GoodAt`,
    Cb/Ld/LdSigLift.lean) if `Z.co.OK`, `Z.next.DegX`, `Z.next.DegY`.
  `Spec.ldLkpBitP_goodAt`: the bit test, without a premise: from "every entry of the table is 0 or
    1" to the sumcheck's two rows (`Spec.ldLkpBitP_rows`, `Spec.ldLkpBitP_row`).
  `Spec.ldLkpBitP_err`: the draw's bound on the number of bad points: k |E|^(k-1) of |E|^k.
Limits: the form over a signature, the number of rounds and the table indexed by numbers
(`Spec.ldLkpBit_good`, `Spec.ldLkpBit_len`, `Spec.ldLkpBit_num`, Cb/Ld/LdLkpBit.lean) are not
restated here.
Not claimed: which element on the wire is which coordinate of the drawn point; the point is drawn as
one value.

-/
import Cb.Ld.LdLkpBitProofs
import Cb.Ld.LdLkpInstProofs

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop

/-- The statement of `Cb.mle_perm` (Cb/Ld/LdLineProofs.lean), proved here again under a name of its
own. -/
theorem mle_permB {K : Type} [CommRing K] {k : ℕ} (σ : Equiv.Perm (Fin k)) (t : (Fin k → Bool) → K)
    (x : Fin k → K) :
    Alg.mle t (fun i => x (σ.symm i)) =
      Alg.mle (fun b : Fin k → Bool => t fun v => b (σ.symm v)) x := by
  have h := Alg.mle_equiv σ t (fun i => x (σ.symm i))
  simp only [Equiv.symm_apply_apply] at h
  exact h.symm

/-- The list of the variables at the equality weights z: entry j is the cube variable weighted at
z j. -/
theorem pVars_eqsB {E : Type} [Field E] [Fintype E] (n : ℕ) : ∀ (k : ℕ) (z : Fin k → E),
    pVars (List.replicate k (pfCube E n)) (pdEqs E n k z) =
      List.ofFn fun j : Fin k => (pfCube E n).var (pdEq E n (z j))
  | 0, _ => rfl
  | k + 1, z => by
    rw [List.ofFn_succ]
    exact congrArg (fun t => (pfCube E n).var (pdEq E n (z 0)) :: t)
      (pVars_eqsB n k fun i => z i.succ)

noncomputable section

/-- `ZeroCube` (Cb/Ld/LdZero.lean), under the name that the files of Cb/Pv/Lookup use -/
abbrev ZeroCubeP (E : Type) [Field E] [Fintype E] := ZeroCube E
/-- `LkBit` (Cb/Ld/LdLkpBit.lean), under the name that the files of Cb/Pv/Lookup use -/
abbrev LkBitP (E : Type) [Field E] [Fintype E] := LkBit E

/-- The bit test of the lookup's instance, in the order σ of its w + d variables: `I.bitB` with σ in
the place of `I.oB`, which is not read. -/
def LdLkp.LkInst.bitBP {E : Type} [Field E] [Fintype E] (I : LdLkp.LkInst E) (Sb : Type)
    (σ : Equiv.Perm (Fin (I.w + I.d)))
    (wB : PIdx (List.replicate (I.w + I.d) (pfCube E 2) ++ [pDummy E 2]) → I.J) (cB : I.J) :
    LkBitP E :=
  { I.bitB Sb wB cB with sg := σ }

namespace Spec
open IOR
variable (E : Type) [Field E] [Fintype E]

def ldZeroP_link : Prop := ∀ Z : ZeroCubeP E, Z.toIn.Link
def ldZeroP_back : Prop := ∀ Z : ZeroCubeP E, Z.toIn.Back
def ldZeroP_ok : Prop := ∀ Z : ZeroCubeP E, Z.co.OK → Z.toIn.ev.OK
def ldZeroP_all : Prop := ∀ (Z : ZeroCubeP E) st m, Z.toIn.AllHold st m ↔ Z.ZeroHolds st m
def ldZeroP_vars : Prop := ∀ Z : ZeroCubeP E, Z.next.VarsOK ∧ Z.next.ValInj

def ldZeroP_psc_goodAt : Prop :=
  ∀ (Z : ZeroCubeP E) (Ex : ExtSpec) (M Wp Kc : Type)
      (R0 : Rels Kc Z.St Ex (M × Wp)) (msg : M → Z.J → E),
    Z.co.OK → Z.next.DegX → Z.next.DegY →
    GoodAt (Z.toIn.chainAt Ex) (Z.toIn.chainAtH Ex M Wp msg)
      ⟨fun st y w => R0.rel st y w ∧ Z.ZeroHolds st (msg w.1),
        fun a w => R0.relR a w ∧ Z.ZeroHolds a.1 (msg w.1),
        R0.on, R0.core⟩
      (Z.next.par.baseOut (Z.toIn.ride R0) fun w => msg w.1)
      (fun _ _ _ wp => wp) (Z.toIn.chainAtN Ex Kc)

def ldLkpBitP_zero : Prop := ∀ (B : LkBitP E) st m, B.zc.ZeroHolds st m ↔ B.AllBits m
def ldLkpBitP_degX : Prop := ∀ B : LkBitP E, B.zc.next.DegX
def ldLkpBitP_degY : Prop := ∀ B : LkBitP E, B.zc.next.DegY

/-- The bit test at the base. -/
def ldLkpBitP_goodAt : Prop :=
  ∀ (B : LkBitP E) (Ex : ExtSpec) (M Wp Kc : Type)
      (R0 : Rels Kc B.St Ex (M × Wp)) (msg : M → B.J → E),
    GoodAt (B.zc.toIn.chainAt Ex) (B.zc.toIn.chainAtH Ex M Wp msg)
      ⟨fun st y w => R0.rel st y w ∧ B.AllBits (msg w.1),
        fun a w => R0.relR a w ∧ B.AllBits (msg w.1), R0.on, R0.core⟩
      (B.zc.next.par.baseOut (B.zc.toIn.ride R0) fun w => msg w.1)
      (fun _ _ _ wp => wp) (B.zc.toIn.chainAtN Ex Kc)

/-- The output rows are linear rows with public targets. -/
def ldLkpBitP_lin : Prop :=
  ∀ B : LkBitP E, B.zc.next.par.LinA B.rowA ∧ B.zc.next.par.LinB fun _ b => b.elim
def ldLkpBitP_rows : Prop :=
  ∀ (B : LkBitP E) (o : B.zc.next.par.Out) (m : B.J → E),
    B.zc.next.par.OutHolds o m ↔
    (B.zc.next.par.slU fun _ b => b.elim).Holds (B.zc.next.par.tU o, o) m ∧
    (B.zc.next.par.slE B.rowA ()).Holds (o.vals (), o) m

/-- The row on the table: extension of the table at γ, plus β times the inner mask, is the revealed
value. -/
def ldLkpBitP_row : Prop :=
  ∀ (B : LkBitP E) (o : B.zc.next.par.Out) (m : B.J → E),
    B.zc.next.par.EHolds o m () ↔
    B.Y m (B.zc.fn o.st.2.2 (B.zc.next.ini o.st (B.zc.next.par.hp o.st o.pt))) +
        m B.cAt * B.zc.next.lst o.st (B.zc.next.par.hp o.st o.pt) = o.vals ()

def ldLkpBitP_err : Prop := ∀ B : LkBitP E, B.zc.toIn.ev.err = B.k * Fintype.card E ^ (B.k - 1)

def ldLkpInst_bitsP : Prop :=
  ∀ (I : LdLkp.LkInst E) Sb σ wB cB (m : I.J → E),
    (I.bitBP Sb σ wB cB).AllBits m ↔ Cb.Lkp.Bits I.d I.w (I.bit m)

end Spec
end

section
variable (E : Type) [Field E] [Fintype E]

theorem ldZeroP_link : Spec.ldZeroP_link E := ldZero_link E
theorem ldZeroP_back : Spec.ldZeroP_back E := ldZero_back E
theorem ldZeroP_ok : Spec.ldZeroP_ok E := ldZero_ok E
theorem ldZeroP_all : Spec.ldZeroP_all E := ldZero_all E
theorem ldZeroP_vars : Spec.ldZeroP_vars E := ldZero_vars E

/-- place j of the list of variables has its weight at coordinate sg j of the drawn point -/
theorem ZeroCubeP.vars_at (Z : ZeroCubeP E) (s : Z.next.St) :
    Z.next.vars s = List.ofFn fun j : Fin Z.k => (pfCube E Z.n).var (pdEq E Z.n (s.2.2 (Z.sg j))) :=
  pVars_eqsB Z.n Z.k (Z.zS s.2.2)

theorem ldZeroP_psc_goodAt : Spec.ldZeroP_psc_goodAt E := ldZero_psc_goodAt E
theorem ldLkpBitP_zero : Spec.ldLkpBitP_zero E := ldLkpBit_zero E
theorem ldLkpBitP_degX : Spec.ldLkpBitP_degX E := ldLkpBit_degX E
theorem ldLkpBitP_degY : Spec.ldLkpBitP_degY E := ldLkpBit_degY E

theorem LkBitP.zero_eq (B : LkBitP E) : B.zc.ZeroHolds = fun _ m => B.AllBits m :=
  funext fun st => funext fun m => propext (ldLkpBitP_zero E B st m)

theorem ldLkpBitP_goodAt : Spec.ldLkpBitP_goodAt E := ldLkpBit_goodAt E
theorem ldLkpBitP_row : Spec.ldLkpBitP_row E := ldLkpBit_row E
theorem ldLkpBitP_lin : Spec.ldLkpBitP_lin E := ldLkpBit_lin E
theorem ldLkpBitP_rows : Spec.ldLkpBitP_rows E := ldLkpBit_rows E
theorem ldLkpBitP_err : Spec.ldLkpBitP_err E := ldLkpBit_err E

theorem ldLkpInst_bitsP : Spec.ldLkpInst_bitsP E := fun I Sb _ wB cB m =>
  ldLkpInst_bits E I Sb wB cB m

end
end Cb
