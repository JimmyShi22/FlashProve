-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
  Compile/Batch/NeedTable.lean: which blocks of an answer are marked as needed, for the oracles of
  the compiled scheme. Definitions, and lemmas that tie them together (words of this library:
  lean/GLOSSARY.md).

  The oracles of the compiled scheme are typed: one oracle for each kind of query
  (Compile/Batch/Oracles.lean). A wire record (Iop/BatchWire.lean) says, among other things, how the
  blocks of a Fiat-Shamir answer give the challenge of a round. A query encoding (`Rom.OracleCoding`;
  Compile/Batch/ImplOf.lean) writes a typed query with the number of a block as a string, so that
  one oracle on strings serves for all.
  The typed Fiat-Shamir oracle has one range for all rounds: K blocks and a chaining value. The
  number of blocks that a round needs is a parameter: nb t i, for round i of protocol t. Hypothesis
  `QueryLayout.NB W nb`: the challenge of round i of protocol t is a function of the blocks below nb t i.
  It is a property of the wire record, that is, of the way in which challenges are sampled from hash
  output; it is proved here for no wire record (the statement for the generic wire record is not in
  this file); for the wire records of the block samplers (`QueryLayout.ofDraws`, which
  Iop/BatchWireDraw.lean calls the generic wire record of the verifier) it is proved in
  Compile/Batch/NeedDraws.lean (`nb_ofDraws`).
  Which blocks are marked: at a Fiat-Shamir query of round i of protocol t, of whichever of the
  formats (F1) to (F5) (`Head`, Compile/Batch/Oracles.lean), the blocks number 0, .., nb t i − 1 and
  number K, the chaining value. At every other oracle (leaf, node, the two oracles of request trees,
  g, the auxiliary oracle `other`): all, that is, the one block; an answer of the oracle `ann` has
  none.
  Under `QueryLayout.NB W nb` the marked blocks contain those that are read, and may be more: what is not
  marked is not read (Compile/Batch/NeedBlocks.lean); what is marked may go unread. The table cannot
  depend on an answer: so with a way of sampling that rejects and tries again, the blocks of all
  attempts are marked, and queried in every run (`OComp.overOneN`, Rom/OverOneN.lean), also where an
  implementation would make the later calls only after a rejection.
    Part 1  `agree nb`: the relation on typed answers; `need nb`: the same as a table of blocks,
            typed on the numbers of blocks of Compile/Batch/ImplOf.lean; `need_one`,
            `agree_of_need`
    Part 2  `WireRB.ReadsBelow`, `RoundsQueryLayout.ReadsFrom`, `QueryLayout.NB W nb`: the hypothesis; `mono`
    Part 3  `Std m`: the hypothesis on m; `needOf nb m : Rom.Need m`: the table for any query
            encoding (`std_implOf`, `needOf_eq`, `needOf_one`, `agree_of_Agree`)
    Part 4  `readsBelow_firstBlocks`: the first b blocks of an answer (`firstBlocks`) are a function
            of the blocks below b. The table of the generic wire record and the theorem on it are
            not in this file. For `QueryLayout.ofDraws`: `nbD`, `nb_ofDraws`,
            Compile/Batch/NeedDraws.lean.
  Limits: nothing on any algorithm. For a round number i beyond the rounds of the protocol, nb t i
  is whatever the parameter says.
-/
import Compile.Batch.ImplOf
import Compile.NeedBlocks
import Iop.BatchWireOf

open Rom Iop

namespace Compile.Batch
namespace Need

/-! ## Part 1 -/

section Typed
variable {I X : Type} {lam K : ℕ} {L : BatchProtocol I X} (nb : Tag → ℕ → ℕ)

/-- Two typed answers agree on what is needed. -/
def agree : (o : OracleName) → domOf lam L o → rngOf lam K o → rngOf lam K o → Prop
  | .leaf, _, r, r' => r = r'
  | .node, _, r, r' => r = r'
  | .rleaf, _, r, r' => r = r'
  | .rnode, _, r, r' => r = r'
  | .fb t, q, r, r' => r.2 = r'.2 ∧ ∀ j : Fin K, j.val < nb t q.round → r.1 j = r'.1 j
  | .g _, _, r, r' => r = r'
  | .ann, _, r, r' => r = r'
  | .other, _, r, r' => r = r'
  | .fbw t _, q, r, r' => r.2 = r'.2 ∧ ∀ j : Fin K, j.val < nb t q.round → r.1 j = r'.1 j

/-- The blocks of an answer that are needed: all, except at a Fiat-Shamir query: there the chaining
value (number K) and the blocks below nb t (round). A ghost name `fbw t k`
(Compile/Batch/Oracles.lean) is treated as `fb t`, the oracle for which it stands: so
`OComp.FactorsBy (agree nb)` carries over from a program with ghost names to the program with `fb t`
written back (`facBy_realQ`, Compile/Batch/NeedBlocks.lean). -/
def need : (o : OracleName) → domOf lam L o → Fin (blk K o) → Bool
  | .fb t, q, j => decide (j.val = K ∨ j.val < nb t q.round)
  | .fbw t _, q, j => decide (j.val = K ∨ j.val < nb t q.round)
  | _, _, _ => true

/-- at an oracle with one block, that block is needed -/
theorem need_one (o : OracleName) (q : domOf lam L o) (h : blk K o = 1) (j : Fin (blk K o)) :
    need (K := K) nb o q j = true := by
  cases o with
  | fb t =>
    have hK : K = 0 := by
      have : K + 1 = 1 := h
      omega
    have hj : j.val < K + 1 := j.2
    exact decide_eq_true (Or.inl (by omega))
  | fbw t k =>
    have hK : K = 0 := by
      have : K + 1 = 1 := h
      omega
    have hj : j.val < K + 1 := j.2
    exact decide_eq_true (Or.inl (by omega))
  | leaf => rfl
  | node => rfl
  | rleaf => rfl
  | rnode => rfl
  | g t => rfl
  | ann => rfl
  | other => rfl

/-- answers whose needed blocks are equal agree -/
theorem agree_of_need (o : OracleName) (q : domOf lam L o) (r r' : rngOf lam K o)
    (h : ∀ j, need nb o q j = true → rngEquiv lam K o r j = rngEquiv lam K o r' j) :
    agree nb o q r r' := by
  cases o with
  | fb t =>
    refine ⟨?_, fun j hj => ?_⟩
    · have h1 : Fin.snoc (α := fun _ : Fin (K + 1) => Dig lam) r.1 r.2 (Fin.last K) =
          Fin.snoc (α := fun _ : Fin (K + 1) => Dig lam) r'.1 r'.2 (Fin.last K) :=
        h (Fin.last K) (decide_eq_true (Or.inl rfl))
      rwa [Fin.snoc_last, Fin.snoc_last] at h1
    · have h1 : Fin.snoc (α := fun _ : Fin (K + 1) => Dig lam) r.1 r.2 j.castSucc =
          Fin.snoc (α := fun _ : Fin (K + 1) => Dig lam) r'.1 r'.2 j.castSucc :=
        h j.castSucc (decide_eq_true (Or.inr hj))
      rwa [Fin.snoc_castSucc, Fin.snoc_castSucc] at h1
  | fbw t k =>
    refine ⟨?_, fun j hj => ?_⟩
    · have h1 : Fin.snoc (α := fun _ : Fin (K + 1) => Dig lam) r.1 r.2 (Fin.last K) =
          Fin.snoc (α := fun _ : Fin (K + 1) => Dig lam) r'.1 r'.2 (Fin.last K) :=
        h (Fin.last K) (decide_eq_true (Or.inl rfl))
      rwa [Fin.snoc_last, Fin.snoc_last] at h1
    · have h1 : Fin.snoc (α := fun _ : Fin (K + 1) => Dig lam) r.1 r.2 j.castSucc =
          Fin.snoc (α := fun _ : Fin (K + 1) => Dig lam) r'.1 r'.2 j.castSucc :=
        h j.castSucc (decide_eq_true (Or.inr hj))
      rwa [Fin.snoc_castSucc, Fin.snoc_castSucc] at h1
  | leaf => exact (rngEquiv lam K .leaf).injective (funext fun j => h j rfl)
  | node => exact (rngEquiv lam K .node).injective (funext fun j => h j rfl)
  | rleaf => exact (rngEquiv lam K .rleaf).injective (funext fun j => h j rfl)
  | rnode => exact (rngEquiv lam K .rnode).injective (funext fun j => h j rfl)
  | g t => exact (rngEquiv lam K (.g t)).injective (funext fun j => h j rfl)
  | ann => exact (rngEquiv lam K .ann).injective (funext fun j => h j rfl)
  | other => exact (rngEquiv lam K .other).injective (funext fun j => h j rfl)

end Typed

end Need
end Compile.Batch

/-! ## Part 2 -/

namespace Iop
variable {lam K : ℕ}

/-- the challenge of the round is a function of the blocks below n -/
def WireRB.ReadsBelow {r : Round} {a : RAnn r} (w : WireRB lam K r a) (n : ℕ) : Prop :=
  ∀ b b' : Fin K → Dig lam, (∀ j : Fin K, j.val < n → b j = b' j) → w.chal b = w.chal b'

/-- the same for all rounds of a shape; i is the number of the first -/
def RoundsQueryLayout.ReadsFrom (nbf : ℕ → ℕ) : (s : Shape) → (A : RoundSplits s) → RoundsQueryLayout lam K s A → ℕ → Prop
  | [], _, _, _ => True
  | _ :: s, (_, A), (w, W), i => w.ReadsBelow (nbf i) ∧ RoundsQueryLayout.ReadsFrom nbf s A W (i + 1)

theorem RoundsQueryLayout.ReadsFrom.mono {nbf nbf' : ℕ → ℕ} (h : ∀ i, nbf i ≤ nbf' i) :
    ∀ {s : Shape} {A : RoundSplits s} {W : RoundsQueryLayout lam K s A} {i : ℕ},
      RoundsQueryLayout.ReadsFrom nbf s A W i → RoundsQueryLayout.ReadsFrom nbf' s A W i
  | [], _, _, _, _ => trivial
  | _ :: _, (_, _), (_, _), i, H =>
    ⟨fun b b' e => H.1 b b' fun j hj => e j (lt_of_lt_of_le hj (h i)), RoundsQueryLayout.ReadsFrom.mono h H.2⟩

/-- In round i of protocol t the challenge is a function of the blocks below nb t i. -/
structure QueryLayout.NB {I X : Type} {L : BatchProtocol I X} (W : QueryLayout lam L) (nb : Compile.Tag → ℕ → ℕ) :
    Prop where
  T : RoundsQueryLayout.ReadsFrom (nb .test) _ _ W.T.sh 0
  Lk : RoundsQueryLayout.ReadsFrom (nb .link) _ _ W.Lk.sh 0
  B : RoundsQueryLayout.ReadsFrom (nb .onl) _ _ W.B.sh 0

theorem QueryLayout.NB.mono {I X : Type} {L : BatchProtocol I X} {W : QueryLayout lam L} {nb nb' : Compile.Tag → ℕ → ℕ}
    (H : W.NB nb) (h : ∀ t i, nb t i ≤ nb' t i) : W.NB nb' :=
  ⟨H.T.mono (h .test), H.Lk.mono (h .link), H.B.mono (h .onl)⟩

end Iop

namespace Compile.Batch
namespace Need

/-! ## Part 3. The same in blocks, for a query encoding -/

section Code
variable {I X : Type} {lam : ℕ} {L : BatchProtocol I X} {K : ℕ}

/-- The query encoding splits an answer as Compile/Batch/ImplOf.lean does: one block at leaf, node,
the oracles of request trees, g and the auxiliary oracle `other`; none at ann; at a Fiat-Shamir
oracle the K blocks in their order, then the chaining value. -/
structure Std (m : OracleCoding (spec lam K L) lam) : Prop where
  blocks : ∀ o, m.blocks o = blk K o
  rng : ∀ o r (j : Fin (m.blocks o)), m.rng o r j = rngEquiv lam K o r (Fin.cast (blocks o) j)

theorem std_implOf (c : StrCode (RealPts lam K L)) {cG : StrCode (GhostPts lam K L)} :
    Std (implOf lam K L c cG) :=
  ⟨fun _ => rfl, fun _ _ _ => rfl⟩

/-- The blocks that are needed, for any query encoding; its value does not use the encoding: it
reads the oracle, the round of the query and the number of the block. At a Fiat-Shamir query: the
chaining value (number K) and the blocks below nb t (round); everywhere else: all. -/
def needOf (nb : Tag → ℕ → ℕ) (m : OracleCoding (spec lam K L) lam) : Rom.Need m := fun o q j =>
  match o, q with
  | .fb t, q => decide (j.val = K ∨ j.val < nb t (q : FbIn lam L t).round)
  | .fbw t _, q => decide (j.val = K ∨ j.val < nb t (q : FbIn lam L t).round)
  | _, _ => true

theorem needOf_eq (nb : Tag → ℕ → ℕ) {m : OracleCoding (spec lam K L) lam} (hm : Std m) (o : OracleName)
    (q : domOf lam L o) (j : Fin (m.blocks o)) :
    needOf nb m o q j = need nb o q (Fin.cast (hm.blocks o) j) := by
  cases o <;> rfl

/-- For `Std m`: at an oracle with one block, that block is needed. -/
theorem needOf_one (nb : Tag → ℕ → ℕ) {m : OracleCoding (spec lam K L) lam} (hm : Std m) (o : OracleName)
    (q : domOf lam L o) (j : Fin (m.blocks o)) (h : m.blocks o = 1) : needOf nb m o q j = true := by
  rw [needOf_eq nb hm]
  exact need_one nb o q ((hm.blocks o).symm.trans h) _

/-- For `Std m`: answers that agree on the needed blocks (`Agree`) agree as typed answers
(`agree`). -/
theorem agree_of_Agree (nb : Tag → ℕ → ℕ) {m : OracleCoding (spec lam K L) lam} (hm : Std m) (o : OracleName)
    (q : domOf lam L o) (r r' : rngOf lam K o) (h : Agree m (needOf nb m) o q r r') :
    agree nb o q r r' := by
  refine agree_of_need nb o q r r' fun j hj => ?_
  have h1 := h (Fin.cast (hm.blocks o).symm j) (by rw [needOf_eq nb hm]; exact hj)
  rw [hm.rng, hm.rng] at h1
  exact h1

end Code

/-! ## Part 4. The first b blocks of an answer -/

section OfPoint
variable {lam K : ℕ}

theorem readsBelow_firstBlocks
    (b : ℕ) (u u' : Fin K → Dig lam) (h : ∀ j : Fin K, j.val < b → u j = u' j) :
    firstBlocks lam K b u = firstBlocks lam K b u' := by
  funext i
  show (if h : i.val < K then u ⟨i.val, h⟩ else fun _ => false) =
    if h : i.val < K then u' ⟨i.val, h⟩ else fun _ => false
  by_cases hi : i.val < K
  · rw [dif_pos hi, dif_pos hi]
    exact h ⟨i.val, hi⟩ i.2
  · rw [dif_neg hi, dif_neg hi]


variable {I X : Type}


end OfPoint

end Need
end Compile.Batch
