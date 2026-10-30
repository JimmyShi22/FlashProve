-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/CutImpl.lean: the oracles after the splitting step and the state-expansion step,
implemented by one hash function on bit strings (`Rom.OracleCoding`), explicitly (words of this library:
lean/GLOSSARY.md).

Compile/Batch/CutFit.lean and Compile/Batch/CutLinks.lean apply the two steps (Rom/SpecCut.lean,
Rom/StateFirst.lean) to the typed oracles of the compiled scheme. This file is the counterpart of
Compile/Batch/ImplOf.lean and of the last part of Compile/Batch/Ser.lean.

The family `specCS lam K L` has, for each oracle o of the scheme, a first oracle inl (inl o) and a
second oracle inl (inr o), and the oracle dr = inr (). A Fiat-Shamir oracle with K = K' + 2 hash
blocks is split: its first oracle answers with block 0, which, under `Test0`
(Compile/Batch/SpecOneCall.lean), holds the proof-of-work bits, its second with a state of two
blocks (the chaining value and the last block), from which the blocks 1, .., K' are expanded through
dr : (state, counter) → one block. No other oracle is split: its first oracle answers as before, and
its second is trivial (its only answer is the unit value).

  `blkCS K`, `rngCS`
      The number of hash blocks in an answer, and an answer as the tuple of its blocks; of a state
      first the half that is passed on, then the other.
  `PtsCS`, `RealPtsCS`, `ptsCSEquiv`
      A point is an oracle, a query and the number of a block of the answer. `RealPtsCS` has the
      points of all oracles except the auxiliary oracle `other` and the ghost names `fbw t k` (never
      queried by the scheme); a trivial oracle has no point. The points of `other` and the ghost
      points are treated as in Compile/Batch/ImplOf.lean.
  `implCS lam K L c cG`
      The query encoding, from explicit injective encodings c of `RealPtsCS` and cG of the ghost
      points (data: `Rom.StrCode`) and the bijection `Rom.StrCode.hotel`. `codeCS_real`: the
      encodings of the points in `RealPtsCS` do not depend on cG: true :: c.put ..
  `serRealCS D`, `codeRealCS D`, `implRealCS D`
      The encoding as a term in the serializers D (Iop/SerB.lean): the format of
      Compile/Batch/Ser.lean, where the sixth case 11111 is divided: 111110 the oracle g, 1111110 a
      state's query with the number of its half, 1111111 the oracle dr: the two halves of the state
      as 2 lam raw bits, then the counter in binary (self-delimiting). In the docstrings on the
      format, "the tag" is `D.tag`, the tag of the parameter set, and "the protocol" is the value t
      of `Tag`. The ghost points are encoded as in Compile/Batch/Ser.lean (`codeGhost`).

`nFront`, `nRest`, `frontEq`, `restEq` go by cases 0, 1, K' + 2, as `cutFb` and `restLink` do: no
cast along an equation K = K' + 2 occurs.

Limits: no choice is made in the data of `implCS`; but Lean's list of the axioms that it depends on
names `Classical.choice`, because proofs inside the definitions use it, and that the values of the
definitions do not use it is not checked in this library. Over the one hash function a state is two
calls, each on the whole query, and the first block is a third, on the same query under another case
of the format; the implementation's hash returns a state in one call. How the implementation writes
(number, counter, attempt) of an expansion query is not modelled: the counter is a natural number.
Nothing on any scheme, on counts or on the two steps themselves. That the encodings of the points
which both families have agree with those of Compile/Batch/Ser.lean is not stated (the case of a
Fiat-Shamir block differs in the number of bits for the block's number).
"The implementation" in this file's comments is not the released programs: what is said of it need
not hold of them (lean/LIMITS.md, L1).
-/
import Compile.Batch.CutLinks
import Compile.Batch.Ser

set_option autoImplicit false

namespace Compile.Batch
open Iop Rom

variable {I X : Type}

/-- the family of oracles after the two steps -/
abbrev specCS (lam K : ℕ) (L : BatchProtocol I X) : OSpec :=
  stSpec (cutSpec (spec lam K L) (cutFS lam K L)) lam (linksS lam K L)

/-- the hash blocks in the answer of the first oracle of a Fiat-Shamir oracle: block 0, or (nothing
is split) the whole answer -/
def nFront : ℕ → ℕ
  | 0 => 1
  | 1 => 2
  | _ + 2 => 1

/-- the hash blocks in the answer of the second oracle of a Fiat-Shamir oracle: a state, or (nothing
is split) none -/
def nRest : ℕ → ℕ
  | 0 => 0
  | 1 => 0
  | _ + 2 => 2

/-- the number of hash blocks (of lam bits) in an answer -/
def blkCS (K : ℕ) : (OracleName ⊕ OracleName) ⊕ Unit → ℕ
  | .inl (.inl (.fb _)) => nFront K
  | .inl (.inl .leaf) => 1
  | .inl (.inl .node) => 1
  | .inl (.inl .rleaf) => 1
  | .inl (.inl .rnode) => 1
  | .inl (.inl (.g _)) => 1
  | .inl (.inl .ann) => 0
  | .inl (.inl .other) => 1
  | .inl (.inl (.fbw _ _)) => K + 1
  | .inl (.inr (.fb _)) => nRest K
  | .inl (.inr .leaf) => 0
  | .inl (.inr .node) => 0
  | .inl (.inr .rleaf) => 0
  | .inl (.inr .rnode) => 0
  | .inl (.inr (.g _)) => 0
  | .inl (.inr .ann) => 0
  | .inl (.inr .other) => 0
  | .inl (.inr (.fbw _ _)) => 0
  | .inr _ => 1

/-- an answer without a block -/
def unitEq (lam : ℕ) : Unit ≃ (Fin 0 → Fin lam → Bool) :=
  ⟨fun _ i => i.elim0, fun _ => (), fun _ => rfl, fun _ => funext fun i => i.elim0⟩

/-- the answer of the first oracle of a Fiat-Shamir oracle as the tuple of its blocks; where nothing
is split the chaining value is the last block, as in Compile/Batch/ImplOf.lean -/
def frontEq (lam : ℕ) : (K : ℕ) → (cutFb lam K).Front ≃ (Fin (nFront K) → Fin lam → Bool)
  | 0 => (Equiv.prodComm _ _).trans (Fin.snocEquiv fun _ : Fin (0 + 1) => Dig lam)
  | 1 => (Equiv.prodComm _ _).trans (Fin.snocEquiv fun _ : Fin (1 + 1) => Dig lam)
  | _ + 2 => (Equiv.funUnique (Fin 1) (Dig lam)).symm

/-- the answer of the second oracle of a Fiat-Shamir oracle as the tuple of its blocks -/
def restEq (lam : ℕ) : (K : ℕ) → (restLink lam K).Ans ≃ (Fin (nRest K) → Fin lam → Bool)
  | 0 => unitEq lam
  | 1 => unitEq lam
  | _ + 2 => (finTwoArrowEquiv (Dig lam)).symm

/-- an answer as the tuple of its blocks -/
def rngCS (lam K : ℕ) (L : BatchProtocol I X) :
    (x : (OracleName ⊕ OracleName) ⊕ Unit) → (specCS lam K L).Rng x ≃ (Fin (blkCS K x) → Fin lam → Bool)
  | .inl (.inl (.fb _)) => frontEq lam K
  | .inl (.inl .leaf) => (Equiv.funUnique (Fin 1) (Dig lam)).symm
  | .inl (.inl .node) => (Equiv.funUnique (Fin 1) (Dig lam)).symm
  | .inl (.inl .rleaf) => (Equiv.funUnique (Fin 1) (Dig lam)).symm
  | .inl (.inl .rnode) => (Equiv.funUnique (Fin 1) (Dig lam)).symm
  | .inl (.inl (.g _)) => (Equiv.funUnique (Fin 1) (Dig lam)).symm
  | .inl (.inl .ann) => unitEq lam
  | .inl (.inl .other) => (Equiv.funUnique (Fin 1) (Dig lam)).symm
  | .inl (.inl (.fbw _ _)) => (Equiv.prodComm _ _).trans (Fin.snocEquiv fun _ : Fin (K + 1) => Dig lam)
  | .inl (.inr (.fb _)) => restEq lam K
  | .inl (.inr .leaf) => unitEq lam
  | .inl (.inr .node) => unitEq lam
  | .inl (.inr .rleaf) => unitEq lam
  | .inl (.inr .rnode) => unitEq lam
  | .inl (.inr (.g _)) => unitEq lam
  | .inl (.inr .ann) => unitEq lam
  | .inl (.inr .other) => unitEq lam
  | .inl (.inr (.fbw _ _)) => unitEq lam
  | .inr _ => (Equiv.funUnique (Fin 1) (Dig lam)).symm

/-- all points: an oracle, a query, the number of a block of the answer -/
abbrev PtsCS (lam K : ℕ) (L : BatchProtocol I X) : Type :=
  Σ x : (OracleName ⊕ OracleName) ⊕ Unit, (specCS lam K L).Dom x × Fin (blkCS K x)

/-- The points of all oracles except `other` and `fbw`: those of Compile/Batch/ImplOf.lean, with the
blocks of the first oracle in the place of the blocks of a Fiat-Shamir answer; a Fiat-Shamir query
with the number of a half of its state; the points of dr. -/
abbrev RealPtsCS (lam K : ℕ) (L : BatchProtocol I X) : Type :=
  LeafIn L ⊕ (Bits × Bits) ⊕ Bits ⊕ (Bits × Bits) ⊕ (Σ t : Tag, FbIn lam L t × Fin (nFront K)) ⊕
    (Σ t : Tag, JoiningRoundQuery lam L t) ⊕ (Σ t : Tag, FbIn lam L t × Fin (nRest K)) ⊕ ((Dig lam × Dig lam) × ℕ)

def ptsCSTo (lam K : ℕ) (L : BatchProtocol I X) :
    PtsCS lam K L → RealPtsCS lam K L ⊕ (GhostPts lam K L ⊕ List Bool)
  | ⟨.inl (.inl .leaf), q, _⟩ => .inl (.inl q)
  | ⟨.inl (.inl .node), q, _⟩ => .inl (.inr (.inl q))
  | ⟨.inl (.inl .rleaf), q, _⟩ => .inl (.inr (.inr (.inl q)))
  | ⟨.inl (.inl .rnode), q, _⟩ => .inl (.inr (.inr (.inr (.inl q))))
  | ⟨.inl (.inl (.fb t)), q, j⟩ => .inl (.inr (.inr (.inr (.inr (.inl ⟨t, q, j⟩)))))
  | ⟨.inl (.inl (.g t)), q, _⟩ => .inl (.inr (.inr (.inr (.inr (.inr (.inl ⟨t, q⟩))))))
  | ⟨.inl (.inl .ann), _, j⟩ => j.elim0
  | ⟨.inl (.inl .other), s, _⟩ => .inr (.inr s)
  | ⟨.inl (.inl (.fbw t k)), q, j⟩ => .inr (.inl ⟨t, k, q, j⟩)
  | ⟨.inl (.inr (.fb t)), q, j⟩ => .inl (.inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨t, q, j⟩)))))))
  | ⟨.inl (.inr .leaf), _, j⟩ => j.elim0
  | ⟨.inl (.inr .node), _, j⟩ => j.elim0
  | ⟨.inl (.inr .rleaf), _, j⟩ => j.elim0
  | ⟨.inl (.inr .rnode), _, j⟩ => j.elim0
  | ⟨.inl (.inr (.g _)), _, j⟩ => j.elim0
  | ⟨.inl (.inr .ann), _, j⟩ => j.elim0
  | ⟨.inl (.inr .other), _, j⟩ => j.elim0
  | ⟨.inl (.inr (.fbw _ _)), _, j⟩ => j.elim0
  | ⟨.inr _, p, _⟩ => .inl (.inr (.inr (.inr (.inr (.inr (.inr (.inr p)))))))

def ptsCSOf (lam K : ℕ) (L : BatchProtocol I X) :
    RealPtsCS lam K L ⊕ (GhostPts lam K L ⊕ List Bool) → PtsCS lam K L
  | .inl (.inl q) => ⟨.inl (.inl .leaf), q, (0 : Fin 1)⟩
  | .inl (.inr (.inl q)) => ⟨.inl (.inl .node), q, (0 : Fin 1)⟩
  | .inl (.inr (.inr (.inl q))) => ⟨.inl (.inl .rleaf), q, (0 : Fin 1)⟩
  | .inl (.inr (.inr (.inr (.inl q)))) => ⟨.inl (.inl .rnode), q, (0 : Fin 1)⟩
  | .inl (.inr (.inr (.inr (.inr (.inl ⟨t, q, j⟩))))) => ⟨.inl (.inl (.fb t)), q, j⟩
  | .inl (.inr (.inr (.inr (.inr (.inr (.inl ⟨t, q⟩)))))) => ⟨.inl (.inl (.g t)), q, (0 : Fin 1)⟩
  | .inl (.inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨t, q, j⟩))))))) => ⟨.inl (.inr (.fb t)), q, j⟩
  | .inl (.inr (.inr (.inr (.inr (.inr (.inr (.inr p))))))) => ⟨.inr (), p, (0 : Fin 1)⟩
  | .inr (.inr s) => ⟨.inl (.inl .other), s, (0 : Fin 1)⟩
  | .inr (.inl ⟨t, k, q, j⟩) => ⟨.inl (.inl (.fbw t k)), q, j⟩

def ptsCSEquiv (lam K : ℕ) (L : BatchProtocol I X) :
    PtsCS lam K L ≃ RealPtsCS lam K L ⊕ (GhostPts lam K L ⊕ List Bool) where
  toFun := ptsCSTo lam K L
  invFun := ptsCSOf lam K L
  left_inv := fun x => by
    rcases x with ⟨x, q, j⟩
    rcases x with (o | o) | u
    · cases o with
      | leaf => have : j = (0 : Fin 1) := @Subsingleton.elim (Fin 1) _ j 0; subst this; rfl
      | node => have : j = (0 : Fin 1) := @Subsingleton.elim (Fin 1) _ j 0; subst this; rfl
      | rleaf => have : j = (0 : Fin 1) := @Subsingleton.elim (Fin 1) _ j 0; subst this; rfl
      | rnode => have : j = (0 : Fin 1) := @Subsingleton.elim (Fin 1) _ j 0; subst this; rfl
      | fb t => rfl
      | g t => have : j = (0 : Fin 1) := @Subsingleton.elim (Fin 1) _ j 0; subst this; rfl
      | ann => exact j.elim0
      | other => have : j = (0 : Fin 1) := @Subsingleton.elim (Fin 1) _ j 0; subst this; rfl
      | fbw t k => rfl
    · cases o with
      | fb t => rfl
      | leaf => exact j.elim0
      | node => exact j.elim0
      | rleaf => exact j.elim0
      | rnode => exact j.elim0
      | g t => exact j.elim0
      | ann => exact j.elim0
      | other => exact j.elim0
      | fbw t k => exact j.elim0
    · have : j = (0 : Fin 1) := @Subsingleton.elim (Fin 1) _ j 0; subst this; rfl
  right_inv := fun y => by
    rcases y with ((q | (q | (q | (q | (⟨t, q, j⟩ | (⟨t, q⟩ | (⟨t, q, j⟩ | p))))))) | (⟨t, k, q,
        j⟩ | s)) <;> rfl

/-- how a point is encoded as a bit string -/
def codeCSEquiv (lam K : ℕ) (L : BatchProtocol I X)
    (c : StrCode (RealPtsCS lam K L)) (cG : StrCode (GhostPts lam K L)) :
    PtsCS lam K L ≃ List Bool :=
  (ptsCSEquiv lam K L).trans ((Equiv.sumCongr (Equiv.refl _) cG.hotel).trans c.hotel)

/-- The family after the two steps, implemented by one hash function. -/
def implCS (lam K : ℕ) (L : BatchProtocol I X) (c : StrCode (RealPtsCS lam K L))
    (cG : StrCode (GhostPts lam K L)) : OracleCoding (specCS lam K L) lam where
  blocks := blkCS K
  rng := rngCS lam K L
  code := fun x q j => codeCSEquiv lam K L c cG ⟨x, q, j⟩
  inv := (codeCSEquiv lam K L c cG).symm
  inv_code := fun x => (codeCSEquiv lam K L c cG).symm_apply_apply x
  code_inv := fun s => (codeCSEquiv lam K L c cG).apply_symm_apply s

/-- The encodings of the points in `RealPtsCS` do not depend on cG, the encoding of the ghost
points. -/
theorem codeCS_real (lam K : ℕ) (L : BatchProtocol I X) (c : StrCode (RealPtsCS lam K L))
    (cG : StrCode (GhostPts lam K L)) (x : RealPtsCS lam K L) :
    codeCSEquiv lam K L c cG (ptsCSOf lam K L (.inl x)) = true :: c.put x := by
  rcases x with (q | (q | (q | (q | (⟨t, q, j⟩ | (⟨t, q⟩ | (⟨t, q, j⟩ | p))))))) <;> rfl

variable {lam K : ℕ} {L : BatchProtocol I X}

/-- the first oracle of an oracle that is not split has the blocks of Compile/Batch/ImplOf.lean -/
theorem blkCS_whole (o : OracleName) (h : (cutFS lam K L o).isWhole = true) :
    blkCS K (.inl (.inl o)) = blk K o := by
  cases o with
  | fb t =>
    match K, h with
    | 0, _ => rfl
    | 1, _ => rfl
  | leaf => rfl
  | node => rfl
  | rleaf => rfl
  | rnode => rfl
  | g t => rfl
  | ann => rfl
  | other => rfl
  | fbw t k => rfl

/-- The first oracle of an oracle that is not split has as many blocks as the oracle has under a
query encoding with `Need.Std` of the scheme's own family. -/
theorem blocks_implCS (c : StrCode (RealPtsCS lam K L)) (cG : StrCode (GhostPts lam K L))
    {m : OracleCoding (spec lam K L) lam} (hm : Need.Std m) (o : OracleName)
    (h : (cutFS lam K L o).isWhole = true) :
    (implCS lam K L c cG).blocks (.inl (.inl o)) = m.blocks o :=
  (blkCS_whole o h).trans (hm.blocks o).symm

/-- the second oracle of an oracle that is not split is trivial: its answer has no block -/
theorem blkCS_idle (o : OracleName) (h : (cutFS lam K L o).isWhole = true) :
    blkCS K (.inl (.inr o)) = 0 := by
  cases o with
  | fb t =>
    match K, h with
    | 0, _ => rfl
    | 1, _ => rfl
  | leaf => rfl
  | node => rfl
  | rleaf => rfl
  | rnode => rfl
  | g t => rfl
  | ann => rfl
  | other => rfl
  | fbw t k => rfl

/-- The first part of a split answer is one block -/
theorem blkCS_front (K' : ℕ) (t : Tag) : blkCS (K' + 2) (.inl (.inl (.fb t))) = 1 := rfl
/-- A state is two blocks -/
theorem blkCS_state (K' : ℕ) (t : Tag) : blkCS (K' + 2) (.inl (.inr (.fb t))) = 2 := rfl
/-- an answer of dr is one block -/
theorem blkCS_dr (K : ℕ) (u : Unit) : blkCS K (.inr u) = 1 := rfl

/-! ## The encoding from serializers -/

/-- The serializer of the points in `RealPtsCS`. -/
def serRealCS (D : SerLHB L) (lam K : ℕ) : Ser (RealPtsCS lam K L) :=
  Ser.tagged D.tag
    (Ser.sum (serLeafIn D)
      (Ser.sum (Ser.prod serBits serBits)
        (Ser.sum serBits
          (Ser.sum (Ser.prod serBits serBits)
            (Ser.sum (Ser.sigma serTag fun t => Ser.prod (serFbIn D lam t) (Ser.fin (nFront K)))
              (Ser.sum (Ser.sigma serTag fun t => serGIn D lam t)
                (Ser.sum (Ser.sigma serTag fun t => Ser.prod (serFbIn D lam t) (Ser.fin (nRest K)))
                  (Ser.prod (Ser.prod (serDig lam) (serDig lam)) Ser.natG))))))))

/-- the injective encoding as bit strings, with its parser -/
def codeRealCS (D : SerLHB L) (lam K : ℕ) : StrCode (RealPtsCS lam K L) :=
  (serRealCS D lam K).toStrCode

/-- Every string of the encoding begins with the tag of the parameter set. -/
theorem tag_prefixCS (D : SerLHB L) (lam K : ℕ) (x : RealPtsCS lam K L) :
    D.tag <+: (codeRealCS D lam K).put x := by
  show D.tag <+: (serRealCS D lam K).put x
  rw [serRealCS, Ser.put_tagged]
  exact List.prefix_append _ _

/-! the cases of the format that differ from Compile/Batch/Ser.lean, as equations -/

/-- a block of the first oracle of a Fiat-Shamir oracle: the tag, 11110, the protocol, the query,
the number of the block -/
theorem put_front (D : SerLHB L) (lam K : ℕ) (t : Tag) (q : FbIn lam L t) (j : Fin (nFront K)) :
    (codeRealCS D lam K).put (.inr (.inr (.inr (.inr (.inl ⟨t, q, j⟩))))) =
      D.tag ++ (true :: true :: true :: true :: false ::
          (Ser.sigma serTag fun t => Ser.prod (serFbIn D lam t) (Ser.fin (nFront K))).put
            ⟨t, q, j⟩) := by
  show (serRealCS D lam K).put _ = _
  rw [serRealCS, Ser.put_tagged]
  rfl

/-- a query to g: the tag, 111110, the protocol, the query -/
theorem put_g (D : SerLHB L) (lam K : ℕ) (t : Tag) (q : JoiningRoundQuery lam L t) :
    (codeRealCS D lam K).put (.inr (.inr (.inr (.inr (.inr (.inl ⟨t, q⟩)))))) =
      D.tag ++ (true :: true :: true :: true :: true :: false ::
          (Ser.sigma serTag fun t => serGIn D lam t).put ⟨t, q⟩) := by
  show (serRealCS D lam K).put _ = _
  rw [serRealCS, Ser.put_tagged]
  rfl

/-- a half of a state: the tag, 1111110, the protocol, the query, the number of the half -/
theorem put_state (D : SerLHB L) (lam K : ℕ) (t : Tag) (q : FbIn lam L t) (j : Fin (nRest K)) :
    (codeRealCS D lam K).put (.inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨t, q, j⟩))))))) =
      D.tag ++ (true :: true :: true :: true :: true :: true :: false ::
          (Ser.sigma serTag fun t => Ser.prod (serFbIn D lam t) (Ser.fin (nRest K))).put
            ⟨t, q, j⟩) := by
  show (serRealCS D lam K).put _ = _
  rw [serRealCS, Ser.put_tagged]
  rfl

/-- a query to dr: the tag, 1111111, the state, the counter -/
theorem put_dr (D : SerLHB L) (lam K : ℕ) (p : (Dig lam × Dig lam) × ℕ) :
    (codeRealCS D lam K).put (.inr (.inr (.inr (.inr (.inr (.inr (.inr p))))))) =
      D.tag ++ (true :: true :: true :: true :: true :: true :: true ::
          (Ser.prod (Ser.prod (serDig lam) (serDig lam)) Ser.natG).put p) := by
  show (serRealCS D lam K).put _ = _
  rw [serRealCS, Ser.put_tagged]
  rfl

/-- The family after the two steps, implemented by one hash function, as a term in the serializers
D. -/
def implRealCS (D : SerLHB L) (lam K : ℕ) : OracleCoding (specCS lam K L) lam :=
  implCS lam K L (codeRealCS D lam K) (codeGhost D lam K)

end Compile.Batch
