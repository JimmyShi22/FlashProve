-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLkpChain.lean: a chain of any number of blocks of one kind of statement, and a round in
which the verifier draws a value, over oracle messages with samples.

Definitions, statements (in `Iop.Spec` and `Cb.Spec`) and proofs. No particular protocol occurs
here.
Many statements of this library are written twice: a definition in the namespace `Spec` states a
proposition, and a theorem of the same name outside that namespace proves it (lean/GLOSSARY.md).

Why: a product tree has one block for each level, and their number is a parameter. The rules for
chains (Ior/KnowCollGood.lean: `goodT_seq`; Ior/Masked.lean: `goodB_seq`) join two blocks. Here they
are iterated, for blocks (`IOR.Bk`) that lead from a kind of statements to the same kind (explicit
part X, oracles Ex, witness W); what is claimed may change from joint to joint.

Main names:
  `Bk.seq`, `Bk.chain b d n` (d: the value of the composed extractors where an earlier verifier
    rejects).
  `Bk.GoodB`, `Bk.GoodT`: the bundles of Ior/Masked.lean (`IOR.GoodB`: `IOR.GoodT` without its
    clause on zero knowledge) and Ior/KnowCollGood.lean, for a block. `IOR.GoodT` (likewise
    `IOR.Good`, Ior/Chain.lean) bundles what is asked of one reduction, with its honest side,
    between two joints, at given numbers; among its clauses: completeness between the honest
    relations, outside sets of verifier randomness whose probabilities further clauses bound by the
    numbers; round-by-round knowledge soundness (`Know`) between the relaxed relations, on the input
    joint's set of statements, with a given extractor, at the numbers' list of errors; and one on
    honest-verifier zero knowledge. In this file's statements the two bundles stand as hypotheses
    and as conclusions.
  `Iop.Spec.bk_chain_goodB`, `Iop.Spec.bk_chain_goodT`: if b l leads from the joint A l to the joint
    A (l + 1), for all l ≤ n, then the chain leads from A 0 to A (n + 1).
  `Iop.Spec.bk_chain_rounds`, `Iop.Spec.bk_chain_pBad`, `Iop.Spec.bk_chain_pHid`: its number of
    rounds and its two probabilities are the sums. (Its errors are the blocks' errors in a row, by
    definition: `Nums.seq`.) `P.pBad` is a number of the structure `Nums`; the clause `prBad` of
    `Good` asks that the probability of the set `H.Bad`, over the verifier's uniform randomness, is
    at most it. `P.cov k` is a set of verifier randomness for each value k of the core; `Good` asks
    that, for every w and x, in the relation or not, `H.Hid w x` lies in `P.cov (A.core w)`
    (`cover`), and that every `P.cov k` has probability at most `P.pHid` (`prCov`). In this file
    these clauses stand inside the two bundles, and inside `Piece` (its field `good`: `IOR.Good`),
    which `Cb.Spec.sig_draw` concludes; `Iop.Spec.bk_chain_pBad` and `Iop.Spec.bk_chain_pHid` are
    equations on the two numbers alone.
A round in which the verifier draws a value (`IOR.draw` of Ior/Draw.lean), on statements over a
signature S of oracle messages with samples (Cb/Ld/LdSig.lean: `S.over A`):
  At a base joint (a joint in which the tuple of messages is a part of the witness) the messages are
  a witness: they are named later than the challenge, and no count of bad values holds there: for
  the blocks whose challenge enters the new claim, at every value of the challenge some tuple meets
  the new claim without meeting the old one (an argument in words, no theorem here: the head of
  Cb/Ld/LdSigLift.lean). Over S the relaxed relation says "the messages are the decoding" (`S.decs`,
  Cb/Ld/LdSig.lean), a function of the statement. So:
  `Cb.Spec.sig_draw`: under the hypotheses of its statement (among them `[Nonempty D]`;
    `∀ st y w β, A.rel st y w → A'.rel (nx st β) y w`;
    `∀ st y β, A.on (st, y) → A'.on (nx st β, y)`; `∀ w, A'.core w = A.core w`), if for each fixed
    tuple of messages at most err values β lead from a false claim to a true one, then drawing β is
    a piece of a chain from `S.over A` to `S.over A'`, with the one error err, the identity as
    extractor, perfectly complete, nothing to simulate. Collision-free (`S.CF`, in the field `on` of
    `S.over`) is handed on; it is not used.

Notation:
  `A`, `A'`, `A l`: joints (`IOR.Rels`, Ior/Chain.lean), with the fields
    `rel`: the relation of the honest side;
    `relR`: its relaxation: what knowledge soundness speaks of;
    `on`: the statements of which knowledge soundness speaks;
    `core`;
  `b l`: of type `Bk K X Ex W`: a block from a kind of statements to the same kind, with all its
    data: the reduction (`R`), its honest side (`H`), its extractor (`ext`), its numbers (`P`);
  `q`: of type `Finset (E₀.prod S.ext).Pos → Prop`: a predicate on sets of positions;
  `Piece`: `IOR.Piece` (Ior/Tail.lean);
  `K`, `Kc`, `X`, `W`, `St`, `St'`, `Wp`, `D`: of type `Type`; `Ex`, `E₀`: of type `ExtSpec`.

Limits: this file says nothing on how err compares with the number of values.
The rules are conditional; they give no protocol.
Terms: lean/GLOSSARY.md.
-/
import Ior.Masked
import Ior.Draw
import Cb.Ld.LdSig
import Cb.Ld.LdTowerKit
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Iop
open Prob
open scoped ENNReal

namespace IOR

/-- A block from a kind of statements to the same kind, with all its data. -/
structure Bk (K X : Type) (Ex : ExtSpec) (W : Type) where
  R   : IOR X Ex X Ex
  H   : R.Honest W W
  ext : X × Ex.Str → Tr R.shape → W → W
  P   : Nums K R

namespace Bk
variable {K X : Type} {Ex : ExtSpec} {W : Type}

def GoodB (b : Bk K X Ex W) (A B : Rels K X Ex W) : Prop := IOR.GoodB b.R b.H A B b.ext b.P
def GoodT (b : Bk K X Ex W) (A B : Rels K X Ex W) : Prop := IOR.GoodT b.R b.H A B b.ext b.P

/-- Two blocks in a row. -/
def seq (a b : Bk K X Ex W) (d : W) : Bk K X Ex W :=
  ⟨a.R.seq b.R, a.H.seq b.H, IOR.extSeq a.R b.R a.ext b.ext d, a.P.seq b.P⟩

/-- The blocks b 0, .., b n in a row. -/
def chain (b : ℕ → Bk K X Ex W) (d : W) : ℕ → Bk K X Ex W
  | 0 => b 0
  | n + 1 => (chain b d n).seq (b (n + 1)) d

end Bk
end IOR

namespace Spec
open IOR

def bk_chain_goodB : Prop :=
  ∀ (K X : Type) (Ex : ExtSpec) (W : Type) (b : ℕ → Bk K X Ex W) (d : W)
      (A : ℕ → Rels K X Ex W) (n : ℕ),
    (∀ l ≤ n, (b l).GoodB (A l) (A (l + 1))) → (Bk.chain b d n).GoodB (A 0) (A (n + 1))

def bk_chain_goodT : Prop :=
  ∀ (K X : Type) (Ex : ExtSpec) (W : Type) (b : ℕ → Bk K X Ex W) (d : W)
      (A : ℕ → Rels K X Ex W) (n : ℕ),
    (∀ l ≤ n, (b l).GoodT (A l) (A (l + 1))) → (Bk.chain b d n).GoodT (A 0) (A (n + 1))

def bk_chain_rounds : Prop :=
  ∀ (K X : Type) (Ex : ExtSpec) (W : Type) (b : ℕ → Bk K X Ex W) (d : W) (n : ℕ),
    (Bk.chain b d n).R.shape.length = ∑ l ∈ Finset.range (n + 1), (b l).R.shape.length

def bk_chain_pBad : Prop :=
  ∀ (K X : Type) (Ex : ExtSpec) (W : Type) (b : ℕ → Bk K X Ex W) (d : W) (n : ℕ),
    (Bk.chain b d n).P.pBad = ∑ l ∈ Finset.range (n + 1), (b l).P.pBad

def bk_chain_pHid : Prop :=
  ∀ (K X : Type) (Ex : ExtSpec) (W : Type) (b : ℕ → Bk K X Ex W) (d : W) (n : ℕ),
    (Bk.chain b d n).P.pHid = ∑ l ∈ Finset.range (n + 1), (b l).P.pHid

end Spec

open IOR

theorem bk_chain_goodB : Spec.bk_chain_goodB := by
  intro K X Ex W b d A n
  induction n with
  | zero => exact fun h => h 0 (Nat.le_refl 0)
  | succ n ih =>
    intro h
    exact goodB_seq K X X X Ex Ex Ex _ _ W W W _ _ (A 0) (A (n + 1)) (A (n + 1 + 1)) _ _ d _ _
      (ih fun l hl => h l (Nat.le_succ_of_le hl)) (h (n + 1) (Nat.le_refl _))

theorem bk_chain_goodT : Spec.bk_chain_goodT := by
  intro K X Ex W b d A n
  induction n with
  | zero => exact fun h => h 0 (Nat.le_refl 0)
  | succ n ih =>
    intro h
    exact goodT_seq K X X X Ex Ex Ex _ _ W W W _ _ (A 0) (A (n + 1)) (A (n + 1 + 1)) _ _ d _ _
      (ih fun l hl => h l (Nat.le_succ_of_le hl)) (h (n + 1) (Nat.le_refl _))

theorem bk_chain_rounds : Spec.bk_chain_rounds := by
  intro K X Ex W b d n
  induction n with
  | zero => simp [Bk.chain]
  | succ n ih =>
    rw [Finset.sum_range_succ, ← ih]
    exact List.length_append

theorem bk_chain_pBad : Spec.bk_chain_pBad := by
  intro K X Ex W b d n
  induction n with
  | zero => simp [Bk.chain]
  | succ n ih =>
    rw [Finset.sum_range_succ, ← ih]
    rfl

theorem bk_chain_pHid : Spec.bk_chain_pHid := by
  intro K X Ex W b d n
  induction n with
  | zero => simp [Bk.chain]
  | succ n ih =>
    rw [Finset.sum_range_succ, ← ih]
    rfl

end Iop

namespace Cb
open Iop Prob Hiop Cb.Ood IOR

/-- The new explicit part over a signature: the samples stay. -/
def Sig.drawNx {E : Type} (S : Sig E) {St St' D : Type} (nx : St → D → St') :
    St × S.Smp → D → St' × S.Smp :=
  fun x β => (nx x.1 β, x.2)

namespace Spec

/-- Drawing a value, over oracle messages with samples. -/
def sig_draw : Prop :=
  ∀ (E : Type) [Field E] (S : Sig E) (Kc St St' Wp D : Type) [Fintype D] [Nonempty D] (E₀ : ExtSpec)
      (nx : St → D → St') (A : Rels Kc St E₀ (S.Msg × Wp)) (A' : Rels Kc St' E₀ (S.Msg × Wp))
      (err : ℕ) (q : Finset (E₀.prod S.ext).Pos → Prop),
    (∀ st y w β, A.rel st y w → A'.rel (nx st β) y w) →
    (∀ st y β, A.on (st, y) → A'.on (nx st β, y)) → (∀ w, A'.core w = A.core w) →
    (∀ st y (m : S.Msg), A.on (st, y) →
      cnt (fun β => ∃ wp, A'.relR (nx st β, y) (m, wp) ∧ ¬ A.relR (st, y) (m, wp)) ≤ err) →
    Piece (IOR.draw D (S.drawNx nx) (E₀.prod S.ext))
      (Honest.draw D (S.drawNx nx) (E₀.prod S.ext) (S.Wit × Wp)) (S.over A) (S.over A')
      (fun _ _ w => w) (Nums.draw Kc D (S.drawNx nx) (E₀.prod S.ext) err) q q

end Spec

theorem sig_draw : Spec.sig_draw := by
  intro E _ S Kc St St' Wp D _ _ E₀ nx A A' err q hfw hon hcore hbw
  refine piece_draw Kc _ _ (E₀.prod S.ext) (S.Wit × Wp) D (S.drawNx nx) (S.over A) (S.over A')
    err q ?_ ?_ (fun w => hcore _) ?_
  · intro x y w β h
    exact ⟨h.1, h.2.1, hfw _ _ _ β h.2.2⟩
  · intro x y β h
    exact ⟨h.1, hon _ _ β h.2⟩
  · intro x y h
    by_cases hw : ∃ β w, (S.over A').relR (S.drawNx nx x β, y) w
    · obtain ⟨β₀, w₀, h₀⟩ := hw
      refine (cnt_mono fun β hβ => ?_).trans (hbw x.1 y.1 (S.msgs w₀.1) h.2)
      obtain ⟨w, h1, h2⟩ := hβ
      have hm : S.msgs w.1 = S.msgs w₀.1 :=
        funext fun i => Option.some.inj ((h1.1 i).symm.trans (h₀.1 i))
      refine ⟨w.2, ?_, fun hA => h2 ⟨h1.1, ?_⟩⟩
      · rw [← hm]
        exact h1.2
      · rw [hm]
        exact hA
    · exact (le_of_eq (cnt_false fun β hβ => hw ⟨β, hβ.choose, hβ.choose_spec.1⟩)).trans
        (Nat.zero_le _)

end Cb
