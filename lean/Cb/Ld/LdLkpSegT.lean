-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLkpSegT.lean: the table's side of the lookup as one block at the base.

Definitions and statements (in `Cb.Spec`). Proofs: Cb/Ld/LdLkpSegTProofs.lean.
The lookup is the sub-protocol for the claim that every key is an entry of a table (`Lk.inR`,
Cb/Ld/LdLkp.lean). This file has the part of it that treats the table: it reduces the claims on the
products over the table, one for each bit position, and the claim that all bits are bits
(`LkInst.bit`, `LkInst.lam`, Cb/Ld/LdLkpInst.lean), to linear rows on the entries.
`BkA.Good` (Cb/Ld/LdLkpTreeP.lean) is `GoodAt` (Cb/Ld/LdSigLift.lean) with the identity as
extractor: among its fields, completeness in the sense of `Honest.Acc` (Ior/Honest.lean) and, for
each fixed tuple of messages, round-by-round knowledge soundness (`Know`, Ior/Know.lean).
At the base means between joints in which the tuple of messages is a part of the witness (`BkA`,
Cb/Ld/LdLkpTreeP.lean), before the lift over a signature (Cb/Ld/LdSigLift.lean).

What comes in. For each of the 2^w bit positions θ a claim on the product over the table, (product
of 1 + bit (λ - 1 - entry)) + < form_θ, entries > = tgt_θ (forms and targets read off the state:
Cb/Ld/LdLkpRoot.lean), and the claim that all bits are bits (`Cb.Lkp.Bits`).
The block, four parts in a row (`Cb.BkA.seq`), each with its own theorem; nothing about them is
assumed:
   1. the point of the forest (`RootP`, Cb/Ld/LdLkpRoot.lean): 1 round;
   2. the forest, levels 0 .. d - 1 (Cb/Ld/LdLkpTreeP.lean at `I.DT` of Cb/Ld/LdLkpInst.lean: a
      sumcheck and a line step a level): (w + l + 3) + 1 rounds at level l;
   3. the closing of the forest's top claim (`LkEnd`, Cb/Ld/LdLkpEnd.lean): w + d + 3 rounds;
   4. the bit test: a zerocheck and a sumcheck (`LkBit`, Cb/Ld/LdLkpBit.lean): 1 + (w + d + 3)
      rounds.
d = 0 is allowed (no level).
What comes out. Linear rows with public targets on the entries, read off the last explicit part
(`rowsT`): of the bit test its row on the hiding polynomial's coefficients and its row on the bits;
of the closing the same two; of each level of the forest the row on the hiding polynomial's
coefficients.
The joints have the form of Cb/Ld/LdLkpKit.lean (`cj`): a riding joint R0 of the caller, read at pr
of the state with which the side was entered (`oldT`), and claims on (explicit part, entries). Ψ,
ΨR: whatever else waits or is done; it rides along.

Main names:
  `SegTab`: the data: `I : LkInst E` (which has the forms of the claims on the products: `I.formT`);
    the targets of these claims; the places of the own masks of the closing and of the bit test.
  `Spec.ldLkpSegT_good`: at the base, for any type of tuples, any R0, pr, Ψ, ΨR, without hypothesis
    beyond those of its statement: from (Ψ, all bits are bits, the claims on the products) to (Ψ at
    the old state, all rows of `rowsT`): `Q.segT` is `BkA.Good`, that is `GoodAt`:
      perfectly complete together with `plain_segT` (Cb/Ld/LdLkpFormatAsm.lean: a theorem, without
        hypothesis beyond those of its statement; its field `free`, with b for `Q.segT`:
        `∀ w x, b.H.withheld w x = ∅`);
      knowledge sound for each fixed tuple of messages on the statements with R0's condition (the
        field `on` of `cj`);
      the identity extracts.
    The relaxed relations have ΨR in place of Ψ.
  `Spec.ldLkpSegT_len`: the number of rounds. Nothing is merged.

Notation:
  `Q`: of type `SegTab E`: the data; `I`: `Q.I`, of type `LkInst E` (Cb/Ld/LdLkpInst.lean);
  `w`, `d`: `I.w`, `I.d`, of type ℕ: 2^w bit positions; the forest's levels 0 .. d - 1;
  `I.X`: the states that the chain has reached; `I.J`: of type `Type`, finite: `m : I.J → E` are the
    entries;
  `Q.tgt`: the targets of the claims on the products, read off the state (their forms: `I.formT`);
  `Q.wE`, `Q.cE`, `Q.wB`, `Q.cB`: own masks of the closing and of the bit test;
  `R0`: a joint (`IOR.Rels`, Ior/Chain.lean);
  `cj R0 msg pr Φ ΦR`: a riding joint, and claims on the entries (Cb/Ld/LdLkpKit.lean), with the
    fields
    `rel`: `R0.rel (pr x) y w ∧ Φ x (msg w.1)`;
    `relR`: `R0.relR (pr a.1, a.2) w ∧ ΦR a.1 (msg w.1)`;
    `on`: `R0.on (pr a.1, a.2)`; `core`: `R0.core`;
  `pr`: of type `I.X → St`; `Ψ`, `ΨR`: of type `I.X → (I.J → E) → Prop`; `msg`: of type
    `M → I.J → E`;
  `Kc`, `M`, `Wp`, `St`: of type `Type`; `Ex`: of type `ExtSpec`.

Limits: this file says nothing on zero knowledge (the item "masked messages" of the chain).
It does not say who states the claims on the products.
Errors are the parts' errors in a row, by definition of the numbers.
Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdLkpInst
import Cb.Ld.LdLkpRoot
import Cb.Ld.LdLkpKit

set_option autoImplicit false

namespace Cb.LdLkp
open Iop IOR Hiop Prob Cb.Lkp

noncomputable section

/-- The data. -/
structure SegTab (E : Type) [Field E] [Fintype E] where
  I : LkInst E
  /-- the targets of the claims on the products, read off the state (their forms: I.formT) -/
  tgt : I.X → (Fin (I.w + 0) → Bool) → E
  /-- own masks of the closing and of the bit test -/
  wE : PIdx (List.replicate (I.w + I.d) (pfCube E 2) ++ [pDummy E 1]) → I.J
  cE : I.J
  wB : PIdx (List.replicate (I.w + I.d) (pfCube E 2) ++ [pDummy E 2]) → I.J
  cB : I.J

namespace SegTab
variable {E : Type} [Field E] [Fintype E] (Q : SegTab E)

/-- the forest; the point of the forest; the closing; the bit test (its states: the closing's
outputs) -/
abbrev D : TreeP E := Q.I.DT
def R : RootP E := ⟨Q.I.DT, Q.I.formT, Q.tgt⟩
def En : LkEnd E := Q.I.endB Q.wE Q.cE
def Bt : LkBit E := Q.I.bitB Q.En.psc.par.Out Q.wB Q.cB

/-- the explicit parts after the closing and after the bit test -/
abbrev XE : Type := Q.En.psc.par.Out
abbrev XB : Type := Q.Bt.zc.next.par.Out

/-- the closing's output, and the state with which the side was entered, read off the last explicit
part -/
def outE (o : Q.XB) : Q.XE := o.st.1
def oldT (o : Q.XB) : Q.I.X := (Q.D.root Q.I.d (Q.outE o).st).1

/-- The rows. -/
def rowsT (o : Q.XB) : List (Row E Q.I.J) :=
  ⟨Q.Bt.zc.next.par.slU (fun _ b => b.elim) o, Q.Bt.zc.next.par.tU o⟩ ::
    ⟨Q.Bt.zc.next.par.slE Q.Bt.rowA () o, o.vals ()⟩ ::
  ⟨Q.En.psc.par.slU (fun _ b => b.elim) (Q.outE o), Q.En.psc.par.tU (Q.outE o)⟩ ::
    ⟨Q.En.psc.par.slE Q.En.rowA () (Q.outE o), (Q.outE o).vals ()⟩ ::
  Q.D.rowsAt Q.I.d (Q.outE o).st

variable (Ex : ExtSpec) {M : Type} (Wp Kc : Type) (msg : M → Q.I.J → E)

/-- The point of the forest, and the levels below l. -/
def forest : (l : ℕ) → BkA Kc M Q.I.X (E × (Q.D.lv l).T.St) Ex Wp
  | 0 => Q.R.rootA Ex M Wp Kc
  | l + 1 => (forest l).seq (Q.D.levA Ex Wp Kc msg l)

/-- The closing. -/
def endA : BkA Kc M (E × (Q.D.lv Q.I.d).T.St) Q.XE Ex Wp :=
  ⟨Q.En.psc.par.psc Ex, Q.En.psc.par.hon Ex fun w => msg w.1, Q.En.psc.par.nums Ex Kc⟩

/-- The bit test. -/
def bitA : BkA Kc M Q.XE Q.XB Ex Wp :=
  ⟨Q.Bt.zc.toIn.chainAt Ex, Q.Bt.zc.toIn.chainAtH Ex M Wp msg, Q.Bt.zc.toIn.chainAtN Ex Kc⟩

/-- The table's side. -/
def segT : BkA Kc M Q.I.X Q.XB Ex Wp :=
  ((Q.forest Ex Wp Kc msg Q.I.d).seq (Q.endA Ex Wp Kc msg)).seq (Q.bitA Ex Wp Kc msg)

end SegTab
end
end Cb.LdLkp

namespace Cb.Spec
open Iop IOR Hiop Prob Cb.LdLkp Cb.Lkp
variable (E : Type) [Field E] [Fintype E]

/-- The table's side, at the base. -/
def ldLkpSegT_good : Prop :=
  ∀ (Q : SegTab E) (Ex : ExtSpec) (M Wp Kc St : Type) (R0 : Rels Kc St Ex (M × Wp))
      (msg : M → Q.I.J → E) (pr : Q.I.X → St) (Ψ ΨR : Q.I.X → (Q.I.J → E) → Prop),
    (Q.segT Ex Wp Kc msg).Good
      (cj R0 msg pr (fun x m => Ψ x m ∧ Bits Q.I.d Q.I.w (Q.I.bit m) ∧ Q.R.Holds x m)
        fun x m => ΨR x m ∧ Bits Q.I.d Q.I.w (Q.I.bit m) ∧ Q.R.Holds x m)
      (cj R0 msg (fun o => pr (Q.oldT o)) (fun o m => Ψ (Q.oldT o) m ∧ RowsHold (Q.rowsT o) m)
        fun o m => ΨR (Q.oldT o) m ∧ RowsHold (Q.rowsT o) m)

/-- The number of rounds. -/
def ldLkpSegT_len : Prop :=
  ∀ (Q : SegTab E) (Ex : ExtSpec) (M Wp Kc : Type) (msg : M → Q.I.J → E),
    (Q.segT Ex Wp Kc msg).R.shape.length =
      (1 + ∑ l ∈ Finset.range Q.I.d, (Q.I.w + l + 3 + 1)) +
        (Q.I.w + Q.I.d + 3) + (1 + (Q.I.w + Q.I.d + 3))

end Cb.Spec
