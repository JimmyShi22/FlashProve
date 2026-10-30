-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Gen/FullErr.lean: the honest side of a block without its knowledge side, by other numbers instead
of a second frame: the list of round errors of a block is overwritten from outside by the full list
(each entry: the number of all values of that round's verifier message); reduction, honest side,
extractor and all other numbers stay the same terms.

In standard terms: in the record of a reduction's properties the errors of round-by-round knowledge
soundness are replaced by the trivial ones: every value of a verifier message may be bad,
probability 1.

Definitions, statements (in `Cb.Spec`) and proofs. Framework only: no protocol occurs. Nothing
assumed beyond the hypotheses of the statements and whatever the arguments hold as proofs.
A list of round errors (`Err`, Iop/Rbr.lean) has for each round a count of values of the verifier
message. The field know of the records below (`PieceTr` and `TailTr` inside their field good) is
round-by-round knowledge soundness at the errors `P.err` (`Reduction.Know`, Ior/Know.lean). A block
is a reduction with its honest side, extractor and numbers (`IOR.Nums`, Ior/Chain.lean). `GoodT` is
in Ior/KnowCollGood.lean, `GoodB` in Ior/Masked.lean, `PieceTr` (a piece of a chain) and `TailTr` (a
tail) in Cb/Ld/LdTowerKit.lean.

Why: the records from which the library draws completeness, formats and hiding of a block (`GoodT`,
`GoodB`, `PieceTr`, `TailTr`) hold the knowledge side in one field, know, beside the honest and
neutral ones. (`GoodB` is `GoodT` without its field exact.) Where know at the true errors needs a
fact that is only assumed (agreement of codes), the whole record is had only under that fact, and
with it completeness and hiding. At the full list know says nothing (the count of bad verifier
messages is at most their number): so a record at the full list is the honest half, in the form that
all rules of the frame take. That is so with a round (`Spec.doomed_full`, below).

Main names:
  `Spec.doomed_full`: `Doomed s e bad` → `Doomed s (Err.full s) bad` (`Doomed`: Iop/Rbr.lean), for
    every shape. With a round the conclusion holds of itself; without one the two propositions are
    the same, so a step without rounds keeps its plain implication.
  `P.full`: pBad, pHid, bud, cov are P's own.
  `Spec.goodT_full`, `Spec.goodB_full`, `Spec.pieceTr_full`, `Spec.tailTr_full`: each of the four
    records at the numbers P → the same at `P.full`. `Spec.ldBlock_full`, `Spec.ldEnd_full` (B :
    `LdBlock`, Z : `LdEnd`, Cb/Ld/LdTower.lean): B.OK t t' → B.full.OK t t'; Z.OK t → Z.full.OK t.
  `Spec.ldFull_seq`, `Spec.ldFull_cons`: (B₁.seq B₂).full = (B₁.full.seq B₂.full).full and
    (B.cons Z).full = (B.full.cons Z.full).full, by unfolding: "one after the other" reads the two
    error lists in the field err alone.
  `ldFull_seqOf`, `ldFull_consOf`: so: blocks that are equal but for their errors have composites
    that are equal but for theirs.

Limits: X.full.OK says of X: point structures, locality, the honest prover is accepted outside the
two withheld sets, the chances of the public bad set and of a cover of the hidden withheld set
(`H.Hid`) are below pBad, pHid, exactness of the honest views within the budgets, what the formats
bear (and the fields `onOut`, `keeps`, `noHid`, `noTie` or `tied`): and nothing on the chance of a
cheating prover. That is so in a block that has a round (a block without a round keeps its plain
implication). This file does not say that a block has X.full.OK without X.OK: that is for each kind
of block (a fold: at counts that are the number of all field elements). It says nothing on a
protocol. It says nothing on numerals.
Terms: lean/GLOSSARY.md: agreement, block, budget, chain, cover, error, fold, full list, honest
side, joint, numbers (of a reduction), piece, public bad set, round-by-round knowledge soundness,
step without rounds, trivial statement, withheld.
-/
import Cb.Ld.LdTower
import Ior.Masked

set_option autoImplicit false

namespace Iop
open Prob

/-- the full list: each entry is the number of all values of that round's verifier message -/
def Err.full : (s : Shape) → Err s
  | [] => ()
  | r :: s => (Fintype.card r.Chal, Err.full s)

namespace IOR
variable {K Xi Xo : Type} {Ei Eo : ExtSpec}

/-- the numbers of a block with the full list for its errors; all other numbers are its own -/
def Nums.full {R : IOR Xi Ei Xo Eo} (P : Nums K R) : Nums K R := { P with err := Err.full R.shape }

end IOR
end Iop

namespace Cb
open Iop Prob Iop.IOR

variable {E : Type} [Field E] [Fintype E] {a b c : LdJoint E}

/-- a block between two joints, its errors overwritten by the full list -/
def LdBlock.full (B : LdBlock a b) : LdBlock a b := { B with N := B.N.full }
/-- a block to the trivial statement, its errors overwritten by the full list -/
def LdEnd.full (Z : LdEnd a) : LdEnd a := { Z with N := Z.N.full }

namespace Spec

def doomed_full : Prop :=
  ∀ (s : Shape) (e : Err s) (bad : Tr s → Prop), Doomed s e bad → Doomed s (Err.full s) bad

def goodT_full : Prop :=
  ∀ (K Xi Xo Wi Wo : Type) (Ei Eo : ExtSpec) (R : IOR Xi Ei Xo Eo) (H : R.Honest Wi Wo)
      (A : Rels K Xi Ei Wi) (B : Rels K Xo Eo Wo)
      (ext : Xi × Ei.Str → Tr R.shape → Wo → Wi) (P : Nums K R),
    GoodT R H A B ext P → GoodT R H A B ext P.full

def goodB_full : Prop :=
  ∀ (K Xi Xo Wi Wo : Type) (Ei Eo : ExtSpec) (R : IOR Xi Ei Xo Eo) (H : R.Honest Wi Wo)
      (A : Rels K Xi Ei Wi) (B : Rels K Xo Eo Wo)
      (ext : Xi × Ei.Str → Tr R.shape → Wo → Wi) (P : Nums K R),
    GoodB R H A B ext P → GoodB R H A B ext P.full

def pieceTr_full : Prop :=
  ∀ (K Xi Xo Wi Wo : Type) (Ei Eo : ExtSpec) (R : IOR Xi Ei Xo Eo) (H : R.Honest Wi Wo)
      (A : Rels K Xi Ei Wi) (B : Rels K Xo Eo Wo) (ext : Xi × Ei.Str → Tr R.shape → Wo → Wi)
      (P : Nums K R) (qi : Finset Ei.Pos → Prop) (qo : Finset Eo.Pos → Prop),
    PieceTr R H A B ext P qi qo → PieceTr R H A B ext P.full qi qo

def tailTr_full : Prop :=
  ∀ (K Xi Xo Wi Wo : Type) (Ei : ExtSpec) (Q : IOR Xi Ei Xo extNone) (H : Q.Honest Wi Wo)
      (A : Rels K Xi Ei Wi) (B : Rels K Xo extNone Wo) (ext : Xi × Ei.Str → Tr Q.shape → Wo → Wi)
      (P : Nums K Q) (qi : Finset Ei.Pos → Prop),
    TailTr Q H A B ext P qi → TailTr Q H A B ext P.full qi

def ldBlock_full : Prop :=
  ∀ (E : Type) [Field E] [Fintype E] (a b : LdJoint E) (B : LdBlock a b) (t t' : ℕ),
    B.OK t t' → B.full.OK t t'

def ldEnd_full : Prop :=
  ∀ (E : Type) [Field E] [Fintype E] (a : LdJoint E) (Z : LdEnd a) (t : ℕ), Z.OK t → Z.full.OK t

def ldFull_seq : Prop :=
  ∀ (E : Type) [Field E] [Fintype E] (a b c : LdJoint E) (B₁ : LdBlock a b) (B₂ : LdBlock b c),
    (B₁.seq B₂).full = (B₁.full.seq B₂.full).full

def ldFull_cons : Prop :=
  ∀ (E : Type) [Field E] [Fintype E] (a b : LdJoint E) (B : LdBlock a b) (Z : LdEnd b),
    (B.cons Z).full = (B.full.cons Z.full).full

end Spec

theorem doomed_full : Spec.doomed_full
  | [], _, _, h => h
  | _ :: _, _, _, _ => fun _ => cnt_le_card _

theorem goodT_full : Spec.goodT_full := fun _ _ _ _ _ _ _ _ _ _ _ _ _ h =>
  { point := h.point, isLocal := h.isLocal, acc := h.acc, onOut := h.onOut, keeps := h.keeps,
    prBad := h.prBad, cover := h.cover, prCov := h.prCov,
    know := fun x hx => doomed_full _ _ _ (h.know x hx), exact := h.exact }

theorem goodB_full : Spec.goodB_full := fun _ _ _ _ _ _ _ _ _ _ _ _ _ h =>
  { point := h.point, isLocal := h.isLocal, acc := h.acc, onOut := h.onOut, keeps := h.keeps,
    prBad := h.prBad, cover := h.cover, prCov := h.prCov,
    know := fun x hx => doomed_full _ _ _ (h.know x hx) }

theorem pieceTr_full : Spec.pieceTr_full := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h =>
  { good := goodT_full _ _ _ _ _ _ _ _ _ _ _ _ _ h.good,
    noHid := h.noHid, noTie := h.noTie, bears := h.bears }

theorem tailTr_full : Spec.tailTr_full := fun _ _ _ _ _ _ _ _ _ _ _ _ _ h =>
  { good := goodT_full _ _ _ _ _ _ _ _ _ _ _ _ _ h.good,
    noHid := h.noHid, tied := h.tied, bears := h.bears }

theorem ldBlock_full : Spec.ldBlock_full := fun _ _ _ _ _ _ _ _ h =>
  pieceTr_full _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h

theorem ldEnd_full : Spec.ldEnd_full := fun _ _ _ _ _ _ h => tailTr_full _ _ _ _ _ _ _ _ _ _ _ _ _ h

theorem ldFull_seq : Spec.ldFull_seq := fun _ _ _ _ _ _ _ _ => rfl

theorem ldFull_cons : Spec.ldFull_cons := fun _ _ _ _ _ _ _ => rfl

/-- blocks that are equal but for their errors have composites that are equal but for theirs -/
theorem ldFull_seqOf {B₁ B₁' : LdBlock a b} {B₂ B₂' : LdBlock b c}
    (h₁ : B₁.full = B₁'.full) (h₂ : B₂.full = B₂'.full) :
    (B₁.seq B₂).full = (B₁'.seq B₂').full := by
  rw [ldFull_seq, ldFull_seq E a b c B₁', h₁, h₂]

theorem ldFull_consOf {B B' : LdBlock a b} {Z Z' : LdEnd b}
    (hB : B.full = B'.full) (hZ : Z.full = Z'.full) :
    (B.cons Z).full = (B'.cons Z').full := by
  rw [ldFull_cons, ldFull_cons E a b B', hB, hZ]

end Cb
