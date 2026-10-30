-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLkp.lean: a lookup argument inside an interactive oracle proof: the interface that its
callers use, and the first steps of one instantiation by products.

Definitions and statements (each a `Prop` in `Cb.Spec`); the proofs are in Cb/Ld/LdLkpProofs.lean.
Mathematics: Cb/Gen/LkpAlg.lean and Cb/Gen/GpAlg.lean. The tree: Cb/Ld/LdLkpTree.lean.

In standard terms: a lookup argument: 2^v keys are claimed to be entries of a table with 2^d entries
(`InTable`, Cb/Gen/LkpAlg.lean). In part 2 an oracle message holds, in bits, the multiplicities of
the table's entries among the keys. At a random λ the claim becomes three clauses (`Mid`, same
file): all are bits; the multiplicities sum to the number of keys, in E; the product of the λ - key
equals a product of powers of products over the table, one for each bit position that counts. The
keys' product and each of the 2^w products over the table is the root of a binary tree of partial
products (`Tree`, Cb/Ld/LdLkpTree.lean), on whose levels the claims are made. An error is a count of
bad values of the verifier message, no probability.

Main names:
1. The sub-protocol, whatever its instantiation. A claim reads the explicit part, further oracles
that are not sampled (an encoded index, decoded by the statement) and the messages: M = `Ms S E₀`
(Cb/Ld/LdLkpTree.lean).
  `Lk`: the data of a lookup claim: 2^v keys `key st m`, any function of the public state and of
    what a claim reads, never sent; a table of 2^d entries of E, which may depend on the public
    state (a table shifted by a challenge); `more`: what else is claimed and rides along.
  `L.inR`: the claim, relaxed. It does not mention the multiplicities.
  `L.inP mult`: the claim, exact. Where the vector of the multiplicities is and in which form is a
    parameter (the predicate mult); the caller has sent it.
  `L.out res ent`: the output claim, over what is read at the end (M'; res gives back what was read
    at the start): explicit part (st, masked claim, rows): the multilinear extension of the keys at
    the point, plus the mask form, is the public target; and the rows hold, and `more`. By type rows
    and mask form read `ent m'` only: the entries named by N (the multiplicities, masks, what the
    lookup itself has sent).
  `Sub`, `Sub.OK`: a block with all its data, from a signature S to a signature S' (S' = S if the
    lookup sends no oracle), and what is asked of it: `IOR.GoodB` (Ior/Masked.lean: the bundle
    without its clause on zero knowledge) from the claim to the output claim; the condition "on",
    and "hon", what else holds on the honest side only and is handed on (`jt2`,
    Cb/Ld/LdLkpTree.lean: the further witness accounts for the further oracles; the multiplicities
    of a later lookup), are parameters of the caller; both joints are in the form `cf`
    (Ior/KnowCollGood.lean), in which "collision-free" may fail with a bad event: so a lookup that
    sends oracles, with samples, is covered. Its numbers are the sub-protocol's list of parameters.
    `GoodB` is `IOR.GoodT` without its clause on zero knowledge. `IOR.GoodT` (likewise `IOR.Good`,
    Ior/Chain.lean) bundles what is asked of one reduction, with its honest side, between two
    joints, at given numbers; among its clauses: completeness between the honest relations, outside
    sets of verifier randomness whose probabilities further clauses bound by the numbers;
    round-by-round knowledge soundness (`Know`) between the relaxed relations, on the input joint's
    set of statements, with a given extractor, at the numbers' list of errors; and one on
    honest-verifier zero knowledge.
  `rideJ`, `SubR`, `SubR.OK`: the case that sends no oracle, in the form in which the blocks of a
    chain are stated: beside any base joint R0 that rides along, with its own exact and relaxed
    relation, condition and core of any type (a chain that holds a block with a secretly withheld
    set has a core other than Unit). `Spec.ldLkp_sub_of_subR`: at the joint R0 that holds the
    caller's "on" and "hon" it gives `Sub.OK` with S' = S.
2. Multiplicities in bits, product trees.
  `LkB`: further data: 2^w bit positions of which the first W count; `bit m u j`: where the bits are
    (a parameter); `ent`: the entries that rows and mask forms may read.
  `Roots`, `T.roots`, `rootNx`: for a forest of 2^g trees: each product has a masked target; the
    verifier draws a point of g coordinates, in a round of its own; the new claim is the masked
    claim on level 0 at that point.
The statements:
  `Spec.ldLkp_lambda_fwd`, `Spec.ldLkp_lambda_cnt`: on vectors, for fixed messages, if `B.Adm p`
    (for the count: p the characteristic of E): if every key is an entry of the table (`B.inR`), the
    honest bits give `B.mid` at every λ; if a key is outside the table, `B.mid` holds for at most
    2^v - 1 values of λ.
  `Spec.ldLkp_lambda`: if `B.Adm p`, p the characteristic of E: the first challenge is a piece of a
    chain (`Piece`, Ior/Tail.lean) from the claim to `B.mid`: one round, no prover message, λ from
    all of E, error 2^v - 1, perfectly complete, the identity extracts.
  `Spec.ldLkp_root_fwd`, `Spec.ldLkp_root_cnt`, `Spec.ldLkp_root`: the point of a forest: from
    `T.roots` to `T.lev 0`: one round, error g |E|^(g-1).
  `Spec.ldLkp_rootsK`, `Spec.ldLkp_rootsT`: what level 0 of the keys' tree and the roots of the
    table's forest say: the left side of the identity in `B.mid`, and the products of which its
    right side is made, with masked targets.
  `Spec.ldLkp_endK`: extension of λ - key at z, plus mask form, is τ ⇔ extension of the keys at z,
    minus the mask form, is λ - τ.
  `Spec.ldLkp_endT`: the top of the table's forest is a masked claim on the vector (λ - 1 - entry) ·
    bit, with the target less 1: a sum with a public coefficient and the bits.

Limits: how the two sides of the identity are tied together (square-and-multiply on a short vector
that is sent after λ, or on virtual scalars), who states the masked targets of the roots, the test
that the bits are bits, and the closing of the table's end claim are not here: a write-up of
ours leaves the first two open, and all are sumchecks on other summands. So no block is shown to
be `Sub.OK` in this file (the four parts and `SubR.OK` of the whole: `LkAsm2`, `Spec.ldLkpAsm2_ok`,
Cb/Ld/LdLkpAsm2.lean, under its hypotheses).
Zero knowledge is not in `Sub.OK`. The item of this instantiation is "masked messages"
(Ior/Masked.lean) for a chain of masked blocks and blocks without prover message; a rule for such
chains is not in this file. Whoever calls a lookup takes that item as a further hypothesis.
By type a claim may read the word of a further oracle. Where an encoded index is plugged in, keys
and "more" are to read it through its decoding only, and "no collision for the index" belongs in
"on": that is the caller's matter.
The table's entries may lie anywhere in E (a text that has them in the smaller field asks for less).

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdLkpTree
import Cb.Gen.LkpAlg

set_option autoImplicit false

namespace Cb.LdLkp
open Blocks Finset Cb.Gp Cb.Lkp Iop IOR

/-! ## 1. The sub-protocol -/

/-- The data of a lookup claim. -/
structure Lk (E St M : Type) where
  v    : ℕ
  d    : ℕ
  key  : St → M → ℕ → E
  tab  : St → ℕ → E
  more : St → M → Prop

namespace Lk
variable {E St M : Type} [Field E] (L : Lk E St M)

/-- The claim, relaxed. -/
def inR : St → M → Prop := fun st m => InTable L.v L.d (L.key st m) (L.tab st) ∧ L.more st m

/-- The claim, exact: `L.inR`, and the vector that an oracle message holds is the multiplicities. -/
def inP (mult : St → M → Prop) : St → M → Prop := fun st m => L.inR st m ∧ mult st m

/-- The output claim. -/
def out {M' N : Type} [Fintype N] (res : M' → M) (ent : M' → N → E) :
    TX St E N → M' → Prop := fun x m' =>
  x.2.1.Holds L.v (L.key x.1 (res m')) (ent m') ∧ RowsHold x.2.2 (ent m') ∧ L.more x.1 (res m')

end Lk

/-- A lookup sub-protocol: the data. S: the oracle messages at the start; S': at the end. -/
structure Sub {E : Type} [Field E] (S S' : Sig E) (E₀ : ExtSpec) (St N Wp : Type) where
  R   : IOR (St × S.Smp) (Ex S E₀) (TX St E N × S'.Smp) (Ex S' E₀)
  H   : R.Honest (S.Wit × Wp) (S'.Wit × Wp)
  ext : (St × S.Smp) × (Ex S E₀).Str → Tr R.shape → S'.Wit × Wp → S.Wit × Wp
  P   : Nums Unit R

/-- What is asked of a lookup sub-protocol. -/
def Sub.OK {E : Type} [Field E] {S S' : Sig E} {E₀ : ExtSpec} {St N Wp : Type} [Fintype N]
    (B : Sub S S' E₀ St N Wp) (L : Lk E St (Ms S E₀)) (mult : St → Ms S E₀ → Prop)
    (on : St × E₀.Str → Prop) (hon : St → Ms S E₀ → Wp → Prop) (res : Ms S' E₀ → Ms S E₀)
    (ent : Ms S' E₀ → N → E) : Prop :=
  GoodB B.R B.H (jt2 S E₀ Wp on hon (L.inP mult) L.inR).cf
    (jt S' E₀ Wp (onFst on) (honFst fun st m' wp => hon st (res m') wp) (L.out res ent)).cf
    B.ext B.P

/-- A claim beside a joint that rides along: R0, a base joint on (state, further oracles, (messages,
further witness)), with its own condition and core. -/
@[reducible] def rideJ {E : Type} [Field E] (S : Sig E) {E₀ : ExtSpec} {Kc St Wp X : Type}
    (R0 : Rels Kc St E₀ (S.Msg × Wp)) (pr : X → St) (P PR : X → Ms S E₀ → Prop) :
    Rels Kc X E₀ (S.Msg × Wp) :=
  ⟨fun x y w => R0.rel (pr x) y w ∧ P x (y, w.1),
    fun a w => R0.relR (pr a.1, a.2) w ∧ PR a.1 (a.2, w.1),
    fun a => R0.on (pr a.1, a.2),
    R0.core⟩

/-- A lookup that sends no oracle: the data, with a core of any type. -/
structure SubR {E : Type} [Field E] (S : Sig E) (E₀ : ExtSpec) (Kc St N Wp : Type) where
  R   : IOR (St × S.Smp) (Ex S E₀) (TX St E N × S.Smp) (Ex S E₀)
  H   : R.Honest (S.Wit × Wp) (S.Wit × Wp)
  ext : (St × S.Smp) × (Ex S E₀).Str → Tr R.shape → S.Wit × Wp → S.Wit × Wp
  P   : Nums Kc R

/-- What is asked of it, beside a joint R0 that rides along. -/
def SubR.OK {E : Type} [Field E] {S : Sig E} {E₀ : ExtSpec} {Kc St N Wp : Type} [Fintype N]
    (B : SubR S E₀ Kc St N Wp) (L : Lk E St (Ms S E₀)) (mult : St → Ms S E₀ → Prop)
    (R0 : Rels Kc St E₀ (S.Msg × Wp)) (ent : Ms S E₀ → N → E) : Prop :=
  GoodB B.R B.H (S.over (rideJ S R0 id (L.inP mult) L.inR))
    (S.over (rideJ S R0 Prod.fst (L.out id ent) (L.out id ent))) B.ext B.P

/-! ## 2. Multiplicities in bits, product trees -/

/-- A lookup claim with multiplicities in bits. -/
structure LkB (E St M N : Type) extends Lk E St M where
  w   : ℕ
  W   : ℕ
  bit : M → ℕ → ℕ → E
  ent : M → N → E

namespace LkB
variable {E St M N : Type} [Field E] (B : LkB E St M N)

/-- The bits are the honest ones (`Cb.Lkp.hbit`), at u < 2^d, j < 2^w. -/
def IsMult : St → M → Prop := fun st m =>
  ∀ u < 2 ^ B.d, ∀ j < 2 ^ B.w, B.bit m u j = hbit B.v B.W (B.key st m) (B.tab st) u j

/-- The conditions on numbers; p is the characteristic where a statement says so. Notation: W is the
number of bit positions that count, 2^w a power of two that is at least that number; a text that
writes w for the first and another letter for the logarithm means the same. -/
def Adm (p : ℕ) : Prop := B.W ≤ 2 ^ B.w ∧ 2 ^ B.v < 2 ^ B.W ∧ 2 ^ B.d * (2 ^ B.W - 1) < p

/-- The claim after the first challenge λ (`Cb.Lkp.Mid`): all are bits; the multiplicities sum to
the number of keys, in E; the product of λ - key is the product over the W bit positions j that
count of (product over the table of 1 + bit (λ - 1 - entry))^(2^j); and `more`. -/
def mid : St × E → M → Prop := fun x m =>
  Mid B.v B.d B.w B.W (B.key x.1 m) (B.tab x.1) (B.bit m) x.2 ∧ B.more x.1 m

/-- the same on the honest side -/
def midP : St × E → M → Prop := fun x m => B.mid x m ∧ B.IsMult x.1 m

/-- The keys' tree: one product of the 2^v factors λ - key. -/
def treeK (more : St × E → M → Prop) : Tree E (St × E) M N :=
  ⟨0, B.v, fun x m => facK (B.key x.1 m) x.2, B.ent, more⟩

/-- The table's forest: 2^w products of the 2^d factors 1 + bit (λ - 1 - entry). -/
def treeT (more : St × E → M → Prop) : Tree E (St × E) M N :=
  ⟨B.w, B.d, fun x m => facT B.w (B.tab x.1) (B.bit m) x.2, B.ent, more⟩

end LkB

/-- Masked targets of the products of a forest. -/
structure Roots (E N : Type) where
  hf : ℕ → N → E
  ht : ℕ → E

/-- The masked claim on level 0 at a point of g coordinates. -/
def Roots.at {E N : Type} [Field E] (h : Roots E N) (g : ℕ) (ϱ : Fin g → E) : MCl E N :=
  ⟨nat ϱ, fun i => ∑ θ ∈ range (2 ^ g), eqN g 0 (nat ϱ) θ * h.hf θ i,
    ∑ θ ∈ range (2 ^ g), eqN g 0 (nat ϱ) θ * h.ht θ⟩

abbrev RX (St E N : Type) : Type := St × Roots E N × List (Row E N)

def rootNx {St E N : Type} [Field E] (g : ℕ) : RX St E N → (Fin g → E) → TX St E N := fun x ϱ =>
  (x.1, x.2.1.at g ϱ, x.2.2)

/-- Every product of the forest has its masked target. -/
def Tree.roots {E St M N : Type} [Field E] [Fintype N] (T : Tree E St M N) :
    RX St E N → M → Prop := fun x m =>
  (∀ θ < 2 ^ T.g, lvl T.g T.n (T.fac x.1 m) 0 θ + ∑ i, x.2.1.hf θ i * T.ent m i = x.2.1.ht θ) ∧
  RowsHold x.2.2 (T.ent m) ∧
  T.more x.1 m

section Blocks
variable {E : Type} [Field E] [Fintype E] (S : Sig E) (E₀ : ExtSpec) (St N Wp : Type)

/-- The first challenge. -/
abbrev lamR : IOR (St × S.Smp) (Ex S E₀) ((St × E) × S.Smp) (Ex S E₀) :=
  IOR.draw E (S.drawNx Prod.mk) (Ex S E₀)
abbrev lamH : (lamR S E₀ St).Honest (S.Wit × Wp) (S.Wit × Wp) :=
  Honest.draw E (S.drawNx Prod.mk) (Ex S E₀) (S.Wit × Wp)
abbrev lamP (err : ℕ) : Nums Unit (lamR S E₀ St) :=
  Nums.draw Unit E (S.drawNx Prod.mk) (Ex S E₀) err

/-- The point of a forest. -/
abbrev rootR (g : ℕ) : IOR (RX St E N × S.Smp) (Ex S E₀) (TX St E N × S.Smp) (Ex S E₀) :=
  IOR.draw (Fin g → E) (S.drawNx (rootNx g)) (Ex S E₀)
abbrev rootH (g : ℕ) : (rootR S E₀ St N g).Honest (S.Wit × Wp) (S.Wit × Wp) :=
  Honest.draw (Fin g → E) (S.drawNx (rootNx g)) (Ex S E₀) (S.Wit × Wp)
abbrev rootP (g : ℕ) : Nums Unit (rootR S E₀ St N g) :=
  Nums.draw Unit (Fin g → E) (S.drawNx (rootNx g)) (Ex S E₀) (g * Fintype.card E ^ (g - 1))

end Blocks
end Cb.LdLkp

namespace Cb.Spec
open Blocks Finset Prob Cb.Gp Cb.Lkp Cb.LdLkp Iop IOR

/-- States: a lookup that sends no oracle, good beside the joint that holds the caller's "on" and
"hon", is a lookup sub-protocol. -/
def ldLkp_sub_of_subR : Prop :=
  ∀ (E : Type) [Field E] (S : Sig E) (E₀ : ExtSpec) (St N Wp : Type) [Fintype N]
      (B : SubR S E₀ Unit St N Wp) (L : Lk E St (Ms S E₀)) (mult : St → Ms S E₀ → Prop)
      (on : St × E₀.Str → Prop) (hon : St → Ms S E₀ → Wp → Prop) (ent : Ms S E₀ → N → E),
    B.OK L mult ⟨fun st y w => hon st (y, w.1) w.2, fun _ _ => True, on, fun _ => ()⟩ ent →
    (⟨B.R, B.H, B.ext, B.P⟩ : Sub S S E₀ St N Wp).OK L mult on hon id ent

def ldLkp_lambda_fwd : Prop :=
  ∀ (E St M N : Type) [Field E] (B : LkB E St M N) (p : ℕ) (st : St) (m : M) (lam : E),
    B.Adm p → B.inP B.IsMult st m → B.midP (st, lam) m

/-- The first challenge, for a fixed tuple of messages. -/
def ldLkp_lambda_cnt : Prop :=
  ∀ (E St M N : Type) [Field E] [Fintype E] (p : ℕ) [CharP E p]
      (B : LkB E St M N) (st : St) (m : M),
    B.Adm p → cnt (fun lam : E => B.mid (st, lam) m ∧ ¬ B.inR st m) ≤ 2 ^ B.v - 1

/-- States, if `B.Adm p`, p the characteristic of E: the first challenge is a piece of a chain. -/
def ldLkp_lambda : Prop :=
  ∀ (E : Type) [Field E] [Fintype E] (p : ℕ) [CharP E p] (S : Sig E) (E₀ : ExtSpec)
      (St N Wp : Type) (B : LkB E St (Ms S E₀) N) (on : St × E₀.Str → Prop)
      (hon : St → Ms S E₀ → Wp → Prop) (q : Finset (Ex S E₀).Pos → Prop),
    B.Adm p →
    Piece (lamR S E₀ St) (lamH S E₀ St Wp) (jt2 S E₀ Wp on hon (B.inP B.IsMult) B.inR)
      (jt2 S E₀ Wp (onFst on) (honFst hon) B.midP B.mid) (fun _ _ w => w)
      (lamP S E₀ St (2 ^ B.v - 1)) q q

def ldLkp_root_fwd : Prop :=
  ∀ (E St M N : Type) [Field E] [Fintype N] (T : Tree E St M N) (x : RX St E N)
      (m : M) (ϱ : Fin T.g → E),
    T.roots x m → T.lev 0 (rootNx T.g x ϱ) m

def ldLkp_root_cnt : Prop :=
  ∀ (E St M N : Type) [Field E] [Fintype E] [Fintype N] (T : Tree E St M N) (x : RX St E N) (m : M),
    cnt (fun ϱ : Fin T.g → E => T.lev 0 (rootNx T.g x ϱ) m ∧ ¬ T.roots x m) ≤
      T.g * Fintype.card E ^ (T.g - 1)

/-- States that the point of a forest is a piece of a chain. -/
def ldLkp_root : Prop :=
  ∀ (E : Type) [Field E] [Fintype E] (S : Sig E) (E₀ : ExtSpec) (St N Wp : Type)
      [Fintype N] (T : Tree E St (Ms S E₀) N) (on : St × E₀.Str → Prop)
      (hon : St → Ms S E₀ → Wp → Prop) (q : Finset (Ex S E₀).Pos → Prop),
    Piece (rootR S E₀ St N T.g) (rootH S E₀ St N Wp T.g)
      (jt S E₀ Wp (onFst on) (honFst hon) T.roots) (jt S E₀ Wp (onFst on) (honFst hon) (T.lev 0))
      (fun _ _ w => w) (rootP S E₀ St N T.g) q q

/-- Level 0 of the keys' tree: the product of λ - key, with a masked target. -/
def ldLkp_rootsK : Prop :=
  ∀ (E St M N : Type) [Field E] [Fintype N] (B : LkB E St M N) (more : St × E → M → Prop)
      (x : TX (St × E) E N) (m : M),
    (B.treeK more).lev 0 x m ↔
    keyProd B.v (B.key x.1.1 m) x.1.2 + ∑ i, x.2.1.mf i * B.ent m i = x.2.1.tg ∧
    RowsHold x.2.2 (B.ent m) ∧
    more x.1 m

/-- The roots of the table's forest: the products over the table, one for each bit position, with
masked targets. -/
def ldLkp_rootsT : Prop :=
  ∀ (E St M N : Type) [Field E] [Fintype N] (B : LkB E St M N) (more : St × E → M → Prop)
      (x : RX (St × E) E N) (m : M),
    (B.treeT more).roots x m ↔
    (∀ j < 2 ^ B.w,
      tabProd B.d (B.tab x.1.1) (B.bit m) x.1.2 j + ∑ i, x.2.1.hf j i * B.ent m i = x.2.1.ht j) ∧
    RowsHold x.2.2 (B.ent m) ∧
    more x.1 m

/-- States that the top of the keys' tree is the output claim, after a change of sign. -/
def ldLkp_endK : Prop :=
  ∀ (E St M N : Type) [Field E] [Fintype N] (B : LkB E St M N) (x : TX (St × E) E N) (m : M),
    (B.treeK fun y m => B.more y.1 m).lev B.v x m ↔
    B.out id B.ent (x.1.1, ⟨x.2.1.pt, fun i => - x.2.1.mf i, x.1.2 - x.2.1.tg⟩, x.2.2) m

/-- The top of the table's forest: a masked claim on (λ - 1 - entry) · bit. -/
def ldLkp_endT : Prop :=
  ∀ (E St M N : Type) [Field E] [Fintype N] (B : LkB E St M N) (more : St × E → M → Prop)
      (x : TX (St × E) E N) (m : M),
    (B.treeT more).lev B.d x m ↔
    (⟨x.2.1.pt, x.2.1.mf, x.2.1.tg - 1⟩ : MCl E N).Holds (B.d + B.w)
      (fun X => (x.1.2 - 1 - B.tab x.1.1 (X / 2 ^ B.w)) * B.bit m (X / 2 ^ B.w) (X % 2 ^ B.w))
      (B.ent m) ∧
    RowsHold x.2.2 (B.ent m) ∧
    more x.1 m

end Cb.Spec
