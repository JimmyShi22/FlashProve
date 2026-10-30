-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLkpBit.lean: the bit test of the lookup: "every entry of a table on the cube is 0 or 1", as
a zerocheck followed by the sumcheck for a polynomial summand.

Definitions and statements (in `Cb.Spec`). Proofs: Cb/Ld/LdLkpBitProofs.lean.
In the lookup the table has the bits in which the multiplicities are written (`bitB`,
Cb/Ld/LdLkpInst.lean).
`GoodAt` (Cb/Ld/LdSigLift.lean) has among its fields completeness in the sense of `Honest.Acc`
(Ior/Honest.lean) and, for each fixed tuple of messages, round-by-round knowledge soundness (`Know`,
Ior/Know.lean).

The claim. Among the entries m : J → E of the oracle messages there is a table on the cube in k
variables: the entry of the corner b is at `tAt b`. Claim: m (tAt b) (m (tAt b) - 1) = 0 for all
corners b.
The protocol is the zerocheck on the cube (`ZeroCube`, Cb/Ld/LdZero.lean) for one function, G(x) =
Y(x) (Y(x) - 1), Y the multilinear extension of the table, followed by the sumcheck
(Cb/Ld/LdPsc.lean) with equality weights at the verifier's point: one revealed map (Y), degree 2 in
each of the k variables, degree 2 in the dummy variable. 1 + (k + 3) rounds (`Spec.ldLkpBit_len`).
It ends in the sumcheck's two rows with public targets: the row on the hiding polynomial's
coefficients, and one linear row on the table under an inner mask: Y(γ) + β c = v
(`Spec.ldLkpBit_row`).

Main names:
  `B.zc`: the parameters of the zerocheck.
  `Spec.ldLkpBit_zero`: its claim is the claim above.
  `Spec.ldLkpBit_degX`, `Spec.ldLkpBit_degY`: the degrees of the summand: stated here, proved in
    Cb/Ld/LdLkpBitProofs.lean, so that nothing is left as a hypothesis.
  `Spec.ldLkpBit_goodAt`: at the base, that is, between joints in which the tuple of messages, here
    of any type, is a part of the witness. It says `GoodAt` (above: for each fixed tuple of
    messages) of the protocol, from the joint (R0 and the claim) to the joint (R0 and the two rows).
    R0 is any joint; it rides along (`PscIn.ride`, Cb/Ld/LdZero.lean). The identity extracts; no
    hypothesis is left beyond those of its statement.
  `Spec.ldLkpBit_good`: the same over a signature of oracle messages with samples: all of
    `IOR.GoodT` but zero knowledge. `GoodB` is `IOR.GoodT` without its clause on zero knowledge.
  `B.rowA`, `Spec.ldLkpBit_lin`, `Spec.ldLkpBit_rows`: the two output rows as linear forms on the
    entries with public targets.
  `Spec.ldLkpBit_err`: the zerocheck's bound on the number of bad points: k |E|^(k-1) of |E|^k.
Where the table stands (`tAt`), where the block's own masks stand (`wAt`, `cAt`) are parameters.
So is the order of the sumcheck's rounds (`sg`): its j-th variable (j from 0) is coordinate `sg` j
of the table's corners, weighted at that coordinate of the verifier's point; by default the j-th
variable is coordinate j.

Notation: γ: the point at which the extension of the table is taken; β: the factor of the inner
mask; c: the inner mask (the entry at `cAt`); v: the revealed value.

Limits: this file says nothing on zero knowledge (the item "masked messages" of the sumcheck:
Cb/Ld/LdPscZk.lean). That `tAt`, `wAt`, `cAt` name different entries is not needed here; it is a
condition of the masked item.
Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdZeroPsc
import Cb.Ld.LdLineAt
import Cb.Gen.LkpAlg

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop

noncomputable section

/-- The parameters of the bit test. -/
structure LkBit (E : Type) [Field E] [Fintype E] where
  St : Type
  J : Type
  [finJ : Fintype J]
  /-- the number of variables of the table, and where its entries stand -/
  k : ℕ
  tAt : (Fin k → Bool) → J
  /-- own masks -/
  wAt : PIdx (List.replicate k (pfCube E 2) ++ [pDummy E 2]) → J
  cAt : J
  /-- the order of the rounds (`ZeroCube.sg`, Cb/Ld/LdZero.lean): the j-th variable of the sumcheck
  (j from 0, in the order of their rounds) is coordinate sg j; by default the j-th variable is
  coordinate j -/
  sg : Equiv.Perm (Fin k) := Equiv.refl _

attribute [instance] LkBit.finJ

namespace LkBit
variable {E : Type} [Field E] [Fintype E] (B : LkBit E)

/-- The claim. -/
def AllBits (m : B.J → E) : Prop := ∀ b, m (B.tAt b) * (m (B.tAt b) - 1) = 0

/-- the multilinear extension of the table -/
def Y (m : B.J → E) (x : Fin B.k → E) : E := Alg.mle (fun b => m (B.tAt b)) x

/-- The zerocheck. -/
def zc : ZeroCube E where
  St := B.St
  J := B.J
  k := B.k
  n := 2
  Tt := Unit
  co := Evader.one E
  A := Unit
  B := Empty
  F := fun _ m _ x => B.Y m x
  Fb := fun _ _ b _ => b.elim
  S0 := fun _ _ _ v => v () * (v () - 1)
  S1 := fun _ _ _ _ b => b.elim
  DY := 2
  wAt := B.wAt
  cAt := fun _ => B.cAt
  sg := B.sg

open Classical in
/-- the row on the table as a linear form on the entries: the equality weights at the places of the
table, the last challenge at the inner mask -/
def rowA (s : B.zc.next.par.St) (_ : B.zc.next.par.A) (X : HPt (B.zc.next.par.vars s)) (j : B.J) :
    E :=
  (∑ b, if B.tAt b = j then Alg.eqk (B.zc.fn s.2.2 (B.zc.next.ini s X)) b else 0) +
    if j = B.cAt then B.zc.next.lst s X else 0

end LkBit

namespace Spec
open IOR
variable (E : Type) [Field E] [Fintype E]

def ldLkpBit_zero : Prop := ∀ (B : LkBit E) st m, B.zc.ZeroHolds st m ↔ B.AllBits m
def ldLkpBit_degX : Prop := ∀ B : LkBit E, B.zc.next.DegX
def ldLkpBit_degY : Prop := ∀ B : LkBit E, B.zc.next.DegY

/-- The bit test at the base. -/
def ldLkpBit_goodAt : Prop :=
  ∀ (B : LkBit E) (Ex : ExtSpec) (M Wp Kc : Type)
      (R0 : Rels Kc B.St Ex (M × Wp)) (msg : M → B.J → E),
    GoodAt (B.zc.toIn.chainAt Ex) (B.zc.toIn.chainAtH Ex M Wp msg)
      ⟨fun st y w => R0.rel st y w ∧ B.AllBits (msg w.1),
        fun a w => R0.relR a w ∧ B.AllBits (msg w.1), R0.on, R0.core⟩
      (B.zc.next.par.baseOut (B.zc.toIn.ride R0) fun w => msg w.1)
      (fun _ _ _ wp => wp) (B.zc.toIn.chainAtN Ex Kc)

/-- The output rows are linear rows with public targets. -/
def ldLkpBit_lin : Prop :=
  ∀ B : LkBit E, B.zc.next.par.LinA B.rowA ∧ B.zc.next.par.LinB fun _ b => b.elim
def ldLkpBit_rows : Prop :=
  ∀ (B : LkBit E) (o : B.zc.next.par.Out) (m : B.J → E),
    B.zc.next.par.OutHolds o m ↔
    (B.zc.next.par.slU fun _ b => b.elim).Holds (B.zc.next.par.tU o, o) m ∧
    (B.zc.next.par.slE B.rowA ()).Holds (o.vals (), o) m

/-- The bit test over a signature. -/
def ldLkpBit_good : Prop :=
  ∀ (B : LkBit E) (S : Sig E) (E₀ : ExtSpec) (Wp Kc : Type)
      (R0 : Rels Kc B.St E₀ (S.Msg × Wp)) (msg : S.Msg → B.J → E),
    GoodB (B.zc.toIn.chain S E₀) (B.zc.toIn.chainH S E₀ Wp msg)
      (S.over ⟨fun st y w => R0.rel st y w ∧ B.AllBits (msg w.1),
        fun a w => R0.relR a w ∧ B.AllBits (msg w.1), R0.on, R0.core⟩)
      (S.over (B.zc.next.par.baseOut (B.zc.toIn.ride R0) fun w => msg w.1))
      (fun _ _ w => w) (B.zc.toIn.chainN S E₀ Kc)

/-- The row on the table: extension of the table at γ, plus β times the inner mask, is the revealed
value. -/
def ldLkpBit_row : Prop :=
  ∀ (B : LkBit E) (o : B.zc.next.par.Out) (m : B.J → E),
    B.zc.next.par.EHolds o m () ↔
    B.Y m (B.zc.fn o.st.2.2 (B.zc.next.ini o.st (B.zc.next.par.hp o.st o.pt))) +
        m B.cAt * B.zc.next.lst o.st (B.zc.next.par.hp o.st o.pt) = o.vals ()

def ldLkpBit_err : Prop := ∀ B : LkBit E, B.zc.toIn.ev.err = B.k * Fintype.card E ^ (B.k - 1)
def ldLkpBit_len : Prop :=
  ∀ (B : LkBit E) (S : Sig E) (E₀ : ExtSpec), (B.zc.toIn.chain S E₀).shape.length = 1 + (B.k + 3)

/-- For a table indexed by numbers: T + w variables, any numbering of the corners by pairs (u, j):
the claim says `Cb.Lkp.Bits`. -/
def ldLkpBit_num : Prop :=
  ∀ (B : LkBit E) (T w : ℕ) (num : (Fin B.k → Bool) ≃ Fin (2 ^ T) × Fin (2 ^ w))
      (M : ℕ → ℕ → E) (m : B.J → E),
    (∀ b, m (B.tAt b) = M (num b).1 (num b).2) → (B.AllBits m ↔ Cb.Lkp.Bits T w M)

end Spec
end
end Cb
