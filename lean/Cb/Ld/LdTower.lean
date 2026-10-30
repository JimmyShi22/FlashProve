-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdTower.lean: the proximity test beyond unique decoding, put together: one stage (fold, then
code switch) as one block, and the tower: stages, then an end block (say the base case).

In standard terms: a joint is the claim "the word is an encoding under C (for knowledge soundness:
lies within e long positions of one) whose message meets the linear equation that sl and the
statement give"; a tower, as one block to the trivial statement, has the form of an interactive
oracle proof (Ior/Ior.lean: `IOR.toInteractiveOracleProof`); what it has under `T.OK`: `Spec.ldTower_end`.

Definitions and statements (each a `Prop` in `Cb.Spec`). The proofs are in Cb/Ld/LdTowerProofs.lean;
six statements (`Spec.ldTower_switch`, `Spec.ldTower_base`, `Spec.ldTower_stage`,
`Spec.ldTower_tail`, `Spec.ldTower_end`, `Spec.ldTower_run`) are proved there each from one of the
two blocks' own theorems (`Spec.ldSwitch_goodT`, `Spec.ldBase_good`) as a hypothesis, and outright
in Cb/Ld/LdTowerMain.lean.

The joints are those of Cb/Ld/LdRel.lean.
  `LdJoint E`: the data of a joint: long positions P (not empty), a code `C : LdCode E P`, a form sl
    with its states, a radius e (a count of long positions). `a.rels`: the joint of a chain (core
    trivial).
  `LdBlock a b`: the data of a block from the joint a to the joint b: an IOR, its honest side, its
    extractor (it may read the statement and the transcript), its numbers.
  `B.OK t t'`: B is a piece of a chain (Cb/Ld/LdTowerKit.lean: `PieceTr`: the bundle `IOR.GoodT`;
    nothing hidden is withheld; nothing is tied; budgets): if what follows needs at most t' long
    positions of the output word, the block is simulated from at most t long positions of the input
    word.
  `LdEnd a`, `Z.OK t`: a block to the trivial statement: the data; the end block is a tail of a
    chain (Cb/Ld/LdTowerKit.lean: `TailTr`, with `Z.R` for its Q: `GoodT`; nothing hidden is
    withheld; the verifier reads all that is tied to its positions; Q bears "nothing follows"
    (`IOR.Bears`, Ior/Bears.lean)): at most t long positions of the input word are needed.
The blocks. The sets of long positions (P, P') are not empty, as in every joint.
  `ldSwBlock D e e' L t'`: the code switch of Cb/Ld/LdSwitch.lean, from `D.jIn e` to `D.jOut e'`.
    `Spec.ldTower_switch`: under that file's hypotheses (`D.Hyp e' L t'`) it is OK D.t t'.
  `ldBaseEnd a t cov d bad L2`: the base case of Cb/Ld/LdBase.lean at the joint a.
    `Spec.ldTower_base`: under that file's hypotheses (`a.BaseHyp d bad L2`) it is OK t.
  The fold is a parameter here: any block F into the joint at which the switch starts. Nothing of it
  is used but "F.OK t t". (A fold as a block: `ldSumBlock`, Cb/Ld/LdTowerSum.lean.)
  `ldSplit`: a step without rounds that cuts the form. A fold asks for a pair of forms, a switch
    leaves one batched form: this step stands between them.
  `ldCutThen G`: the joints of a tower carry one batched form, so every F after the first stage is
    "cut, then fold".
  `ldPlace`: how a switch fills the next stage's code: after a fold the word has three parts (the
    folded main word, the folded old mask, the new mask). The main word's message goes to the next
    main component; all the rest (the two masks' messages, the three encoding randomnesses, the pad)
    goes to the next mask component.

One stage: `ldStage D F e' L t'`. `Spec.ldTower_stage`: if F is OK D.t D.t, and the switch's
hypotheses hold, the stage is OK D.t t', from the joint a to `D.jOut e'`, and
  rounds: those of F and 2 more (a fold over k variables has k + 1: k + 3);
  errors: those of F, then the two of the switch, in a row; none is added to another;
  radii: the input and the middle joint have one radius a.e; the output has its own, e', any number;
  extractor: the switch's (cut the new message), then F's, where F's verifier does not reject;
  honest-verifier zero knowledge: exact; against what follows reading at most t' long positions of
  the new word; the simulator is given at most D.t long positions of the input word.
The tower: `LdTower a`. The joints are part of the types, so only towers whose stages fit can be
written down.
  `T.toEnd`: the whole test as one block to the trivial statement; `T.q`: the long positions of the
    input word that are needed; `T.rounds`.
  `T.OK`: for each stage: F.OK D.t D.t, the switch's hypotheses at t' = what the rest of the tower
    needs (rest.q); for the end block: OK.
  `Spec.ldTower_tail`: T.OK → T.toEnd.OK T.q.
  `Spec.ldTower_end`: so, under `T.OK`, the whole test: strings (`Shape.IsPoint`), local
    (`IOR.IsLocal`), complete outside a public set; round-by-round knowledge soundness from the
    relaxation of the first joint at its radius, errors in a row; exact honest-verifier zero
    knowledge; the simulator is given at most T.q long positions of the input word.
A run that ends as a block: `LdRun a b`: stages, then any last block into the joint b (say a switch
of another kind): for chains that do not end in the trivial statement.
`Spec.ldTower_run`: R.OK t' → R.toBlock.OK R.q t'; `Spec.ldTower_run_rounds`.

Limits: where the ranges of the radii stand: a stage's radius has to lie below the distances, under
their transformations, of the stage's main and mask codes: that is a hypothesis of the fold's own
theorem, so here it is inside F.OK; for the base case it is `BaseHyp.lt` (a.e < d, d the threshold
of the corrector of erasures, any number: that it is a distance is not asked). The switch asks no
range of e and e': of e nothing; of e' a list size (`LdSw.Hyp.list : D.Cout.ListAt e' L`, L any
number, which goes into the errors).
DECLARED DIFFERENCES to the paper that this protocol builds on (lean/CREDITS.md), beside those of
Cb/Ld/LdRel.lean, Cb/Ld/LdSwitch.lean, Cb/Ld/LdBase.lean.
(1) The fold is abstract here.
(2) Codes, transformations, numbers of rows are any: the text's tower has one main and one mask code
    a stage, the mask read under a repetition, and powers of two; that is an instance (`ldPlace`;
    `LdCode.il`, `pair`, `rep`), not built here.
(3) Cutting the batched form is a step of its own, without rounds.
(4) Zero knowledge is exact, with budgets of positions, where the text adds statistical errors and
    speaks of uniform positions. (Zero knowledge here: `IOR.Honest.Exact`, Ior/Honest.lean.)
(5) No running times, no communication, no count of native queries (a long position costs what the
    transformation reads: `LdCode.LocalLE`).
(6) The text's completeness is perfect; "complete outside a public set" is this library's slot:
    the switch and the base case withhold nothing, so the set is empty as soon as every F's is
    (`Spec.ldTower_stage`: pBad is F's).
(7) The base case's first error is (exceptional coefficients of the code) + (list of the doubled
    code); for a main and a mask code side by side the first unfolds into a sum (Cb/Ld/LdRel.lean:
    `Spec.ld_mca_pair`): an instance.
(8) A tower may have no stage at all.

Limits: this file does not say that towers with T.OK exist. It fixes no parameters.
It says nothing on the sizes of the errors.
It says nothing on further reads of the test's own oracles by a distinguisher
(Cb/Ld/LdTowerKit.lean).
It says nothing on how a protocol uses the test.
The composition restates, in our own words, a construction of that text (lean/CREDITS.md).

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdTowerKit
import Cb.Ld.LdSwitch
import Cb.Ld.LdBase
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop IOR

/-! ## Joints and blocks -/

/-- A joint: the data. -/
structure LdJoint (E : Type) where
  P  : Type
  [finP : Fintype P]
  [neP : Nonempty P]
  C  : LdCode E P
  St : Type
  sl : Slf E St C.J
  /-- the radius of the relaxation: a count of long positions -/
  e  : ℕ

attribute [instance] LdJoint.finP LdJoint.neP

section
variable {E : Type} [Field E] [Fintype E]

namespace LdJoint
variable (a : LdJoint E)

abbrev X : Type := E × a.St
abbrev W : Type := a.C.N.Wit

/-- The joint of a chain. -/
def rels : IOR.Rels Unit a.X a.C.ext a.W := a.C.rels a.sl a.e fun _ => ()

/-- at most t long positions -/
def atMost (t : ℕ) : Finset a.C.ext.Pos → Prop := fun S => S.card ≤ t

end LdJoint

/-- A block between two joints: the data. -/
structure LdBlock (a b : LdJoint E) where
  R   : IOR a.X a.C.ext b.X b.C.ext
  H   : R.Honest a.W b.W
  ext : a.X × a.C.ext.Str → Tr R.shape → b.W → a.W
  N   : IOR.Nums Unit R

/-- A block to the trivial statement: the data. -/
structure LdEnd (a : LdJoint E) where
  R   : IOR a.X a.C.ext Unit extNone
  H   : R.Honest a.W Unit
  ext : a.X × a.C.ext.Str → Tr R.shape → Unit → a.W
  N   : IOR.Nums Unit R

variable {a b c : LdJoint E}

/-- The block is a piece of a chain: from at most t' long positions of the output word to at most t
of the input word. -/
def LdBlock.OK (B : LdBlock a b) (t t' : ℕ) : Prop :=
  PieceTr B.R B.H a.rels b.rels B.ext B.N (a.atMost t) (b.atMost t')

/-- The end block is a tail of a chain. -/
def LdEnd.OK (Z : LdEnd a) (t : ℕ) : Prop := TailTr Z.R Z.H a.rels trivRels Z.ext Z.N (a.atMost t)

/-- one block after the other -/
def LdBlock.seq (B₁ : LdBlock a b) (B₂ : LdBlock b c) : LdBlock a c :=
  ⟨B₁.R.seq B₂.R, B₁.H.seq B₂.H, IOR.extSeq B₁.R B₂.R B₁.ext B₂.ext 0, B₁.N.seq B₂.N⟩

def LdBlock.cons (B : LdBlock a b) (Z : LdEnd b) : LdEnd a :=
  ⟨B.R.seq Z.R, B.H.seq Z.H, IOR.extSeq B.R Z.R B.ext Z.ext 0, B.N.seq Z.N⟩

/-! ## The code switch and the base case as blocks -/

section Switch
variable {P P' St : Type} [Fintype P] [Nonempty P] [Fintype P'] [Nonempty P'] (D : LdSw E P P' St)

/-- the joints of a code switch -/
def LdSw.jIn (e : ℕ) : LdJoint E := ⟨P, D.Cin, St, D.sl, e⟩
def LdSw.jOut (e' : ℕ) : LdJoint E := ⟨P', D.Cout, D.St', D.sl', e'⟩

/-- The code switch as a block. -/
def ldSwBlock (e e' L t' : ℕ) : LdBlock (D.jIn e) (D.jOut e') :=
  ⟨ldSwitch D, ldSwitchHon D fun _ => True, fun _ _ w' => D.back w',
    ldSwNums D Unit (fun _ => True) e L t'⟩

/-- the hypotheses of the code switch (Cb/Ld/LdSwitch.lean) -/
structure LdSw.Hyp (e' L t' : ℕ) : Prop where
  laws  : D.Cin.Laws
  reads : D.Cout.Reads
  list  : D.Cout.ListAt e' L
  okO   : D.Zo.OK
  okB   : D.Zb.OK
  priv  : D.Zo.PrivateSim E
  zk    : D.Cout.Zk t'

end Switch

/-- The base case as an end block. -/
def ldBaseEnd (a : LdJoint E) (t : ℕ) (cov : a.C.NP → a.P) (d bad L2 : ℕ) : LdEnd a :=
  ⟨ldBaseIOR a.C a.sl t cov, ldBaseHon a.C a.sl t cov,
    ldBaseExt a.C t d, ldBaseNums a.C a.sl t cov a.e bad L2⟩

/-- the hypotheses of the base case (Cb/Ld/LdBase.lean) -/
structure LdJoint.BaseHyp (a : LdJoint E) (d bad L2 : ℕ) : Prop where
  laws   : a.C.Laws
  transp : a.C.Transparent
  lt     : a.e < d
  mca    : a.C.MCAat a.e bad
  list   : (a.C.il Bool).ListAt a.e L2

/-! ## Cutting a form; filling the next stage's code -/

/-- the two parts of a form on coordinates J₁ ⊕ J₂ -/
def Slf.left {St J₁ J₂ : Type} (sl : Slf E St (J₁ ⊕ J₂)) : Slf E St J₁ := fun st j => sl st (.inl j)
def Slf.right {St J₁ J₂ : Type} (sl : Slf E St (J₁ ⊕ J₂)) : Slf E St J₂ := fun st j =>
  sl st (.inr j)

section Split
variable {P St : Type} [Fintype P] [Nonempty P] (C₁ C₂ : LdCode E P)
  (sl : Slf E St (C₁.J ⊕ C₂.J)) (e : ℕ)

/-- the joint with one form on both codes' message coordinates, and the joint with the form cut in
two -/
def ldWhole : LdJoint E := ⟨P, C₁.pair C₂, St, sl, e⟩
def ldCut : LdJoint E := ⟨P, C₁.pair C₂, St × St, sl.left.pair sl.right, e⟩

/-- The step without rounds that cuts the form: the state is doubled. -/
def ldSplit : LdBlock (ldWhole C₁ C₂ sl e) (ldCut C₁ C₂ sl e) :=
  ⟨IOR.pure (fun x => some (x.1, (x.2, x.2))) (ExtMap.id _),
    IOR.Honest.pure _ _ fun xw => ((xw.1.1, (xw.1.2, xw.1.2)), xw.2),
    fun _ _ w => w,
    IOR.Nums.pure Unit _ _⟩

variable {C₁ C₂ sl e} in
/-- Cut, then G. -/
def ldCutThen {b : LdJoint E} (G : LdBlock (ldCut C₁ C₂ sl e) b) :
    LdBlock (ldWhole C₁ C₂ sl e) b :=
  (ldSplit C₁ C₂ sl e).seq G

end Split

/-- How a switch fills the next stage's code: the main word's message to the next main component
(pm); the two masks' messages, the three encoding randomnesses and the pad to the next mask
component (pz). -/
def ldPlace {J Js Jw Q Qs Qw Qo M₂ Z₂ : Type} (pm : J ≃ M₂)
    (pz : ((Js ⊕ Jw) ⊕ (Q ⊕ (Qs ⊕ Qw))) ⊕ Qo ≃ Z₂) :
    ((J ⊕ (Js ⊕ Jw)) ⊕ (Q ⊕ (Qs ⊕ Qw))) ⊕ Qo ≃ M₂ ⊕ Z₂ :=
  (((Equiv.sumCongr (Equiv.sumAssoc J (Js ⊕ Jw) (Q ⊕ (Qs ⊕ Qw))) (Equiv.refl Qo)).trans
      (Equiv.sumAssoc J ((Js ⊕ Jw) ⊕ (Q ⊕ (Qs ⊕ Qw))) Qo))).trans
    (Equiv.sumCongr pm pz)

/-! ## One stage; the tower -/

/-- One stage: a fold (any block into the switch's input joint, at the input's radius), then the
code switch. -/
def ldStage {P' StM : Type} [Fintype P'] [Nonempty P'] (D : LdSw E a.P P' StM)
    (F : LdBlock a (D.jIn a.e)) (e' L t' : ℕ) : LdBlock a (D.jOut e') :=
  F.seq (ldSwBlock D a.e e' L t')

end

/-- A tower: the data. -/
inductive LdTower {E : Type} [Field E] [Fintype E] : LdJoint E → Type 1
  | base (a : LdJoint E) (Z : LdEnd a) (t : ℕ) : LdTower a
  | step (a : LdJoint E) {P' StM : Type} [Fintype P'] [Nonempty P'] (D : LdSw E a.P P' StM)
      (F : LdBlock a (D.jIn a.e)) (e' L : ℕ) (rest : LdTower (D.jOut e')) : LdTower a

namespace LdTower
variable {E : Type} [Field E] [Fintype E]

/-- the long positions of the input word that are needed -/
def q : {a : LdJoint E} → LdTower a → ℕ
  | _, .base _ _ t => t
  | _, @LdTower.step _ _ _ _ _ _ _ _ D _ _ _ _ => D.t

/-- The whole test as one block to the trivial statement. -/
def toEnd : {a : LdJoint E} → LdTower a → LdEnd a
  | _, .base _ Z _ => Z
  | _, @LdTower.step _ _ _ _ _ _ _ _ D F e' L rest => (ldStage D F e' L rest.q).cons rest.toEnd

/-- the number of rounds -/
def rounds : {a : LdJoint E} → LdTower a → ℕ
  | _, .base _ Z _ => Z.R.shape.length
  | _, @LdTower.step _ _ _ _ _ _ _ _ _ F _ _ rest => F.R.shape.length + 2 + rest.rounds

/-- The conditions. -/
def OK : {a : LdJoint E} → LdTower a → Prop
  | _, .base _ Z t => Z.OK t
  | _, @LdTower.step _ _ _ _ _ _ _ _ D F e' L rest => F.OK D.t D.t ∧ D.Hyp e' L rest.q ∧ rest.OK

end LdTower

/-- A run that ends as a block: the data. -/
inductive LdRun {E : Type} [Field E] [Fintype E] : LdJoint E → LdJoint E → Type 1
  | last (a b : LdJoint E) (B : LdBlock a b) (t : ℕ) : LdRun a b
  | step (a b : LdJoint E) {P' StM : Type} [Fintype P'] [Nonempty P'] (D : LdSw E a.P P' StM)
      (F : LdBlock a (D.jIn a.e)) (e' L : ℕ) (rest : LdRun (D.jOut e') b) : LdRun a b

namespace LdRun
variable {E : Type} [Field E] [Fintype E]

def q : {a b : LdJoint E} → LdRun a b → ℕ
  | _, _, .last _ _ _ t => t
  | _, _, @LdRun.step _ _ _ _ _ _ _ _ _ D _ _ _ _ => D.t

/-- The whole run as one block. -/
def toBlock : {a b : LdJoint E} → LdRun a b → LdBlock a b
  | _, _, .last _ _ B _ => B
  | _, _, @LdRun.step _ _ _ _ _ _ _ _ _ D F e' L rest => (ldStage D F e' L rest.q).seq rest.toBlock

def rounds : {a b : LdJoint E} → LdRun a b → ℕ
  | _, _, .last _ _ B _ => B.R.shape.length
  | _, _, @LdRun.step _ _ _ _ _ _ _ _ _ _ F _ _ rest => F.R.shape.length + 2 + rest.rounds

/-- the conditions; t': what follows the run needs of its output word -/
def OK (t' : ℕ) : {a b : LdJoint E} → LdRun a b → Prop
  | _, _, .last _ _ B t => B.OK t t'
  | _, _, @LdRun.step _ _ _ _ _ _ _ _ _ D F e' L rest =>
    F.OK D.t D.t ∧ D.Hyp e' L rest.q ∧ rest.OK t'

end LdRun

namespace Spec

/-- Under `D.Hyp e' L t'`, P and P' not empty, the code switch is a piece: from at most t' long
positions of the new word to at most D.t of the input word. -/
def ldTower_switch : Prop :=
  ∀ (E P P' St : Type) [Field E] [Fintype E] [Fintype P] [Nonempty P] [Fintype P'] [Nonempty P']
      (D : LdSw E P P' St) (e e' L t' : ℕ),
    D.Hyp e' L t' → (ldSwBlock D e e' L t').OK D.t t'

/-- Under `a.BaseHyp d bad L2`, the base case is a tail: at most t long positions of the input
word. -/
def ldTower_base : Prop :=
  ∀ (E : Type) [Field E] [Fintype E] (a : LdJoint E) (t : ℕ) (cov : a.C.NP → a.P) (d bad L2 : ℕ),
    a.BaseHyp d bad L2 → (ldBaseEnd a t cov d bad L2).OK t

/-- For P not empty, cutting the form is a piece, and changes neither claim nor word nor witness
(word and witness: by the definition `ldSplit`). -/
def ldTower_split : Prop :=
  ∀ (E P St : Type) [Field E] [Fintype E] [Fintype P] [Nonempty P] (C₁ C₂ : LdCode E P)
      (sl : Slf E St (C₁.J ⊕ C₂.J)) (e t : ℕ),
    (ldSplit C₁ C₂ sl e).OK t t ∧
    (ldSplit C₁ C₂ sl e).R.shape = [] ∧
    ∀ (τ : E) (st : St) (m : C₁.J ⊕ C₂.J → E),
      (sl.left.pair sl.right).Holds (τ, (st, st)) m ↔ sl.Holds (τ, st) m

/-- Where each kind of coordinate lands. -/
def ldTower_place : Prop :=
  ∀ (J Js Jw Q Qs Qw Qo M₂ Z₂ : Type) (pm : J ≃ M₂) (pz : ((Js ⊕ Jw) ⊕ (Q ⊕ (Qs ⊕ Qw))) ⊕ Qo ≃ Z₂),
    (∀ j, ldPlace pm pz (.inl (.inl (.inl j))) = .inl (pm j)) ∧
    (∀ j, ldPlace pm pz (.inl (.inl (.inr j))) = .inr (pz (.inl (.inl j)))) ∧
    (∀ r, ldPlace pm pz (.inl (.inr r)) = .inr (pz (.inl (.inr r)))) ∧
    (∀ o, ldPlace pm pz (.inr o) = .inr (pz (.inr o)))

/-- Cut, then G (P not empty): OK as G is; the same rounds, the same errors. -/
def ldTower_cutThen : Prop :=
  ∀ (E P St : Type) [Field E] [Fintype E] [Fintype P] [Nonempty P] (C₁ C₂ : LdCode E P)
      (sl : Slf E St (C₁.J ⊕ C₂.J)) (e : ℕ) (b : LdJoint E)
      (G : LdBlock (ldCut C₁ C₂ sl e) b) (t t' : ℕ),
    G.OK t t' →
    (ldCutThen G).OK t t' ∧
    (ldCutThen G).R.shape = G.R.shape ∧
    HEq (ldCutThen G).N.err G.N.err ∧
    (ldCutThen G).N.pBad = G.N.pBad

/-- Under the hypotheses below, blocks compose -/
def ldTower_seq : Prop :=
  ∀ (E : Type) [Field E] [Fintype E] (a b c : LdJoint E) (B₁ : LdBlock a b)
      (B₂ : LdBlock b c) (t₁ t₂ t₃ : ℕ),
    B₁.OK t₁ t₂ → B₂.OK t₂ t₃ → (B₁.seq B₂).OK t₁ t₃

def ldTower_cons : Prop :=
  ∀ (E : Type) [Field E] [Fintype E] (a b : LdJoint E) (B : LdBlock a b) (Z : LdEnd b) (t₁ t₂ : ℕ),
    B.OK t₁ t₂ → Z.OK t₂ → (B.cons Z).OK t₁

/-- Fold, then code switch, as one block. -/
def ldTower_stage : Prop :=
  ∀ (E : Type) [Field E] [Fintype E] (a : LdJoint E) (P' StM : Type) [Fintype P'] [Nonempty P']
      (D : LdSw E a.P P' StM) (F : LdBlock a (D.jIn a.e)) (e' L t' : ℕ),
    F.OK D.t D.t → D.Hyp e' L t' →
    (ldStage D F e' L t').OK D.t t' ∧
    (ldStage D F e' L t').R.shape.length = F.R.shape.length + 2 ∧
    (ldStage D F e' L t').N.err = Err.app (t := D.sh) F.N.err (D.W.err1 L, (D.W.err2 a.e L, ())) ∧
    (ldStage D F e' L t').N.pBad = F.N.pBad ∧
    ∀ x (τ₁ : Tr F.R.shape) (τ₂ : Tr D.sh) y w', F.R.red.out x τ₁ = some y →
      (ldStage D F e' L t').ext x (Tr.app τ₁ τ₂) w' = F.ext x τ₁ (D.back w')

/-- Under `T.OK`, a tower is a tail of a chain. -/
def ldTower_tail : Prop :=
  ∀ (E : Type) [Field E] [Fintype E] (a : LdJoint E) (T : LdTower a), T.OK → T.toEnd.OK T.q

/-- What the whole test has. -/
def ldTower_end : Prop :=
  ∀ (E : Type) [Field E] [Fintype E] (a : LdJoint E) (T : LdTower a), T.OK →
    Nonempty T.toEnd.R.shape.IsPoint ∧
    T.toEnd.R.IsLocal ∧
    T.toEnd.H.Acc (Con a.C.N a.sl.Holds) (fun _ _ _ => True) ∧
    (∀ w x, T.toEnd.H.Hid w x = ∅) ∧
    prRho T.toEnd.H.Bad ≤ T.toEnd.N.pBad ∧
    T.toEnd.R.red.Know (fun _ => True) (ConL a.C.N a.e a.sl.Holds) (fun _ _ => True)
      T.toEnd.ext T.toEnd.N.err ∧
    T.toEnd.H.Exact (Con a.C.N a.sl.Holds) (fun _ S => S = ∅) ∧
    T.toEnd.R.Tied ∧
    ∀ ρ, (T.toEnd.R.given ρ ∅).card ≤ T.q ∧ T.toEnd.R.extReads ρ ⊆ T.toEnd.R.given ρ ∅

/-- the number of rounds; the errors of a tower that begins with a stage: the stage's, then the
rest's -/
def ldTower_rounds : Prop :=
  ∀ (E : Type) [Field E] [Fintype E] (a : LdJoint E) (T : LdTower a),
    T.toEnd.R.shape.length = T.rounds

def ldTower_err : Prop :=
  ∀ (E : Type) [Field E] [Fintype E] (a : LdJoint E) (P' StM : Type) [Fintype P'] [Nonempty P']
      (D : LdSw E a.P P' StM) (F : LdBlock a (D.jIn a.e)) (e' L : ℕ) (rest : LdTower (D.jOut e')),
    (LdTower.step a D F e' L rest).toEnd.N.err =
      Err.app (Err.app (t := D.sh) F.N.err (D.W.err1 L, (D.W.err2 a.e L, ()))) rest.toEnd.N.err

/-- Under `R.OK t'`, a run is a piece of a chain. -/
def ldTower_run : Prop :=
  ∀ (E : Type) [Field E] [Fintype E] (a b : LdJoint E) (R : LdRun a b) (t' : ℕ),
    R.OK t' → R.toBlock.OK R.q t'

def ldTower_run_rounds : Prop :=
  ∀ (E : Type) [Field E] [Fintype E] (a b : LdJoint E) (R : LdRun a b),
    R.toBlock.R.shape.length = R.rounds

end Spec
end Cb
