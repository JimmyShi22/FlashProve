-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/Size.lean: for the sizes of a verification key and of a proof of the compiled scheme,
in bits: what is serialized of a slot's proof string, and what of its format matters for its size.
(Words of this library: lean/GLOSSARY.md.)

This file does not define the serializations of whole keys and proofs, their sizes or the bounds
(for pruned Merkle paths: Compile/Batch/SizeO.lean).

  `encB`   what is serialized of a slot's proof string; injective if the wire record is well-formed
           (`encB_injective`)
  `cRoots`   an upper bound on the number of roots that the chain of a slot takes: a sum over the
             rounds
  `SizeNums`, `SizeNums.Within`
      the numbers from which the bounds are made; the serializers keep to the widths

That a slot's proof string that the compiled verifier with the strict-format check (`verifyOneProtocol`)
accepts has `FitsB` is proved, under hypotheses, in Compile/Batch/SizeAccepted.lean.

Format of a slot's proof string (`BT`, `encB`): the Fiat-Shamir salt; the roots; the plain parts,
round by round; for each round the list of its opened positions, first those of the shared
component, then those of the slot's, each in the order of the leaves of its tree; the opened
external positions (the lists: `EntS`, `EntE`, Compile/Size.lean); then the request root, the slot
number and the request path. The roots are counted by the flags of the wire record (`cRoots`): a
root only for a component that has a tree (Iop/BatchWire.lean: `has0`, `hasJ`), the shared one only
in shared rounds.

Three clauses of `FitsB` are not tight: the root of a slot's component that has a tree is counted in
every shared round (only the joining round takes it); every path of a round is counted with the
larger of the depths of its two trees; a request path of depthReq digests is counted for Test and
Link too, where the strict-format check wants it empty.

Notation: the arguments of `FitsB`: `sMT`, `sFS`, `depthReq`: natural numbers: in its clauses:
`t.1.length ≤ sFS` (`salt`), `x.2.salt.length ≤ sMT` (`ext`), `t.2.2.2.2.2.2.1 ≤ 2 ^ depthReq - 1`
(`slot`), `t.2.2.2.2.2.2.2.length ≤ depthReq` (`path`); `wq`: a `ProtocolQueryLayout lam K Q`
(Iop/BatchWire.lean); `o`: an `OpenList Q.loc.shape` (Iop/SerS.lean): "For each round a number: how
many positions of its oracle are opened at most"; `eN`: an `ExtNums` (Compile/Size.lean), with the
fields `n`, `x`, `d`: "the numbers of the external openings: how many at most; the bits of
(position, symbol); the depth of the trees"; `lam`: a natural number: "Digests have `lam` bits";
`K`: a natural number: an answer of `fb t` "is K hash blocks, from which the challenge is made, and
a chaining value" (both: the head of Compile/Batch/Oracles.lean).
-/
import Compile.Size
import Compile.Batch.Star
import Iop.SerB

set_option autoImplicit false

namespace Compile.Batch
open Iop Rom
open Ser (gam)

variable {I X : Type} {lam K : ℕ} {L : BatchProtocol I X}

/-! ## Part 1. The serialization -/

/-- the opened positions of one component of one round, in the order of the leaves of its tree -/
def entriesC {r : Round} (posAt : ℕ → Option r.Pos) (depth : ℕ)
    (g : (p : r.Pos) → Option (Opening lam (r.Sym p))) : List (EntR lam r) :=
  (List.range (2 ^ depth)).filterMap fun j => (posAt j).bind fun p => (g p).map fun op => ⟨p, op⟩

/-- The opened positions of one component with a list of trees, from tree number k on: in the order
of the trees, and in each tree in the order of its leaves (`entriesC`). `posAt k j`: the position at
leaf j of tree number k. -/
def entriesTrees {r : Round} (posAt : ℕ → ℕ → Option r.Pos)
    (g : (p : r.Pos) → Option (Opening lam (r.Sym p))) : ℕ → List ℕ → List (EntR lam r)
  | _, [] => []
  | k, d :: ds => entriesC (posAt k) d g ++ entriesTrees posAt g (k + 1) ds

theorem entriesTrees_one {r : Round} (posAt : ℕ → ℕ → Option r.Pos)
    (g : (p : r.Pos) → Option (Opening lam (r.Sym p))) (k d : ℕ) :
    entriesTrees posAt g k [d] = entriesC (posAt k) d g := by
  simp [entriesTrees]

theorem entriesTrees_nil {r : Round} (posAt : ℕ → ℕ → Option r.Pos)
    (g : (p : r.Pos) → Option (Opening lam (r.Sym p))) (k : ℕ) :
    entriesTrees posAt g k [] = [] := rfl

/-- A component that has its one tree, or none: `entriesC`, under the law that a component without a
tree has no position. -/
theorem entriesTrees_ite {r : Round} (posAt : ℕ → ℕ → Option r.Pos)
    (g : (p : r.Pos) → Option (Opening lam (r.Sym p))) (k : ℕ) (has : Bool) (d : ℕ)
    (h : has = false → ∀ j, posAt k j = none) :
    entriesTrees posAt g k (if has then [d] else []) = entriesC (posAt k) d g := by
  cases has with
  | true => exact entriesTrees_one posAt g k d
  | false =>
    have h0 := h rfl
    simp [entriesTrees, entriesC, h0]

/-- the opened positions of one round: the shared component, then the slot's -/
def entriesRB {r : Round} {a : RAnn r} (w : WireRB lam K r a)
    (g : (p : r.Pos) → Option (Opening lam (r.Sym p))) : List (EntR lam r) :=
  entriesC w.posAt0 w.depth0 g ++ entriesC w.posAtJ w.depthJ g

def entriesSB :
    (s : Shape) → (A : RoundSplits s) → RoundsQueryLayout lam K s A →
    ((p : OPos s) → Option (Opening lam (OSym s p))) → EntS lam s
  | [], _, _, _ => ()
  | _ :: s, (_, A), (w, W), g =>
    (entriesRB w fun p => g (.inl p), entriesSB s A W fun p => g (.inr p))

/-- what is serialized of a proof string -/
abbrev BT (lam : ℕ) {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E) : Type :=
  Bits × List (Dig lam) × Plains Q.loc.shape × EntS lam Q.loc.shape × List (EntE lam E) ×
    Dig lam × ℕ × List (Dig lam)

section B

variable {Y : Type} {E : ExtSpec} {Q : BatchInteractiveOracleProof Y E}

def encB (wq : ProtocolQueryLayout lam K Q) (π : OneProtocolProof lam Q) : BT lam Q :=
  (π.salt, π.roots, π.plains, entriesSB Q.loc.shape Q.ann wq.sh π.opens, entriesE wq.ext π.ext,
    π.rtreq, π.slot, π.path)

end B

/-! ### What is serialized determines the proof string (if the wire record is well-formed) -/

theorem mem_entriesC {r : Round} (posAt : ℕ → Option r.Pos) (depth : ℕ)
    (g : (p : r.Pos) → Option (Opening lam (r.Sym p))) (p : r.Pos) (op : Opening lam (r.Sym p)) :
    (⟨p, op⟩ : EntR lam r) ∈ entriesC posAt depth g ↔
    (∃ j < 2 ^ depth, posAt j = some p) ∧ g p = some op := by
  unfold entriesC
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨j, hj, hjp⟩
    obtain ⟨p', hp', hq⟩ := Option.bind_eq_some_iff.1 hjp
    obtain ⟨op', hop, he⟩ := Option.map_eq_some_iff.1 hq
    cases he
    exact ⟨⟨j, List.mem_range.1 hj, hp'⟩, hop⟩
  · rintro ⟨⟨j, hj, hp⟩, h⟩
    exact ⟨j, List.mem_range.2 hj, by rw [hp, Option.bind_some, h, Option.map_some]⟩

/-- The pair of a position p and an opening op is in the list of the opened positions of a
component, from tree number k on, exactly if p stands at a leaf of one of these trees and g has the
opening op at p. i counts the trees from k: tree number k + i has the depth ds[i]. -/
theorem mem_entriesTrees {r : Round} (posAt : ℕ → ℕ → Option r.Pos)
    (g : (p : r.Pos) → Option (Opening lam (r.Sym p))) (p : r.Pos) (op : Opening lam (r.Sym p)) :
    ∀ (k : ℕ) (ds : List ℕ),
      (⟨p, op⟩ : EntR lam r) ∈ entriesTrees posAt g k ds ↔
      (∃ i d, ds[i]? = some d ∧ ∃ j < 2 ^ d, posAt (k + i) j = some p) ∧ g p = some op
  | _, [] => by simp [entriesTrees]
  | k, d :: ds => by
      rw [entriesTrees, List.mem_append, mem_entriesC, mem_entriesTrees posAt g p op (k + 1) ds]
      constructor
      · rintro (⟨⟨j, hj, hp⟩, h⟩ | ⟨⟨i, e, he, j, hj, hp⟩, h⟩)
        · exact ⟨⟨0, d, rfl, j, hj, hp⟩, h⟩
        · exact ⟨⟨i + 1, e, he, j, hj, by rwa [show k + (i + 1) = k + 1 + i by omega]⟩, h⟩
      · rintro ⟨⟨i, e, he, j, hj, hp⟩, h⟩
        cases i with
        | zero =>
          cases Option.some.inj he
          exact Or.inl ⟨⟨j, hj, hp⟩, h⟩
        | succ i =>
          exact Or.inr ⟨⟨i, e, he, j, hj, by rwa [show k + 1 + i = k + (i + 1) by omega]⟩, h⟩

theorem mem_entriesRB {r : Round} {a : RAnn r} {w : WireRB lam K r a} (hw : w.OKG)
    (g : (p : r.Pos) → Option (Opening lam (r.Sym p))) (p : r.Pos) (op : Opening lam (r.Sym p)) :
    (⟨p, op⟩ : EntR lam r) ∈ entriesRB w g ↔ g p = some op := by
  unfold entriesRB
  rw [List.mem_append, mem_entriesC, mem_entriesC]
  constructor
  · rintro (h | h) <;> exact h.2
  · intro h
    cases hown : a.own p with
    | false => exact Or.inl ⟨⟨w.place p, hw.place_lt0 p hown, hw.posAt0_place p hown⟩, h⟩
    | true => exact Or.inr ⟨⟨w.place p, hw.place_ltJ p hown, hw.posAtJ_place p hown⟩, h⟩

theorem entriesRB_injective {r : Round} {a : RAnn r} {w : WireRB lam K r a} (hw : w.OKG)
    {g g' : (p : r.Pos) → Option (Opening lam (r.Sym p))} (h : entriesRB w g = entriesRB w g') :
    g = g' := by
  funext p
  refine Option.ext fun op => ?_
  rw [← mem_entriesRB hw g, ← mem_entriesRB hw g', h]

theorem entriesSB_injective :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A), RoundsQueryLayout.OKG s A W →
      ∀ {g g' : (p : OPos s) → Option (Opening lam (OSym s p))},
        entriesSB s A W g = entriesSB s A W g' → g = g'
  | [], _, _, _, _, _, _ => funext fun p => (show Empty from p).elim
  | _ :: s, (_, A), (_, W), hW, g, g', h => by
      have h1 := entriesRB_injective hW.1 (congrArg Prod.fst h)
      have h2 := entriesSB_injective s A W hW.2 (congrArg Prod.snd h)
      funext p
      cases p with
      | inl p => exact congrFun h1 p
      | inr p => exact congrFun h2 p

theorem encB_injective {Y : Type} {E : ExtSpec} {Q : BatchInteractiveOracleProof Y E}
    {wq : ProtocolQueryLayout lam K Q} (hwq : wq.OKG) :
    Function.Injective (encB wq) := by
  rintro ⟨s, r, pl, o, e, q, j, pa⟩ ⟨s', r', pl', o', e', q', j', pa'⟩ h
  simp only [encB, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl, h4, h5, rfl, rfl, rfl⟩ := h
  rw [entriesSB_injective _ _ _ hwq.sh h4, entriesE_injective hwq.ext h5]

/-! ### Serializers of positions of encoded indices -/

section Scheme

variable (W : QueryLayout lam L) (D : SerLHB L)

/-- positions of one encoded index; of a parent and a child -/
def serPos1 (L : BatchProtocol I X) : Ser (Fin L.wordLength) := Ser.fin L.wordLength
@[inherit_doc serPos1] def serPos2 (L : BatchProtocol I X) : Ser (Fin L.wordLength ⊕ Fin L.wordLength) :=
  Ser.sum (Ser.fin L.wordLength) (Ser.fin L.wordLength)




end Scheme

/-! ## Part 2. The conditions `FitsB`, and the numbers for the bounds -/

/-- the wire record of a round with one depth, the larger of the two: only its depth is read, by
`FitsEnt` (Compile/Size.lean) -/
def flatR {r : Round} {a : RAnn r} (w : WireRB lam K r a) : WireR lam K r :=
  ⟨w.pt, max w.depth0 w.depthJ, w.place, w.posAtJ, w.chal⟩

def flatS : (s : Shape) → (A : RoundSplits s) → RoundsQueryLayout lam K s A → WireS lam K s
  | [], _, _ => ()
  | _ :: s, (_, A), (w, W) => (flatR w, flatS s A W)

/-- An upper bound on the roots that enter the chain of a slot, summed over the rounds: the root of
the slot's component, and in a shared round also that of the shared component; each only if the
component has a tree. -/
def cRoots : (s : Shape) → (A : RoundSplits s) → RoundsQueryLayout lam K s A → ℕ
  | [], _, _ => 0
  | _ :: s, (a, A), (w, W) =>
    (match a.kind with | .lo => 0 | .sh => w.has0.toNat) + w.hasJ.toNat + cRoots s A W

/-- at most two for each round -/
theorem cRoots_le : ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A), cRoots s A W ≤ 2 * s.length
  | [], _, _ => Nat.le_refl _
  | _ :: s, (a, A), (w, W) => by
      have h := cRoots_le s A W
      have h0 : (match a.kind with | .lo => 0 | .sh => w.has0.toNat) ≤ 1 := by
        cases a.kind
        · exact Bool.toNat_le _
        · exact Nat.zero_le _
      have hJ := Bool.toNat_le w.hasJ
      show (match a.kind with | .lo => 0 | .sh => w.has0.toNat) + w.hasJ.toNat + cRoots s A W ≤
        2 * (s.length + 1)
      omega

section B

variable {Y : Type} {E : ExtSpec} {Q : BatchInteractiveOracleProof Y E}

/-- The conditions on the format of a proof string that matter for its size. -/
structure FitsB (sMT sFS : ℕ) (wq : ProtocolQueryLayout lam K Q) (depthReq : ℕ) (o : OpenList Q.loc.shape)
    (eN : ExtNums) (t : BT lam Q) : Prop where
  salt : t.1.length ≤ sFS
  roots : t.2.1.length ≤ cRoots Q.loc.shape Q.ann wq.sh
  ent : FitsEnt sMT Q.loc.shape (flatS Q.loc.shape Q.ann wq.sh) o t.2.2.2.1
  extN : t.2.2.2.2.1.length ≤ eN.n
  ext : ∀ x ∈ t.2.2.2.2.1, x.2.salt.length ≤ sMT ∧ x.2.path.length ≤ eN.d
  slot : t.2.2.2.2.2.2.1 ≤ 2 ^ depthReq - 1
  path : t.2.2.2.2.2.2.2.length ≤ depthReq


end B

/-! ### The numbers for the bounds -/

/-- The numbers from which the bounds are made: the widths that the serializers keep to, and the
numbers of opened positions, round by round, for the three protocols; the bits of a symbol of an
encoded index. -/
structure SizeNums (L : BatchProtocol I X) where
  bT : BitsS L.offline.shape
  bL : BitsS L.link.shape
  bO : BitsS L.onlineBatch.loc.shape
  oT : OpenList L.offline.shape
  oL : OpenList L.link.shape
  oO : OpenList L.onlineBatch.loc.shape
  /-- positions of the external strings that the verifiers of Test, of Link and of a slot read at
  most -/
  eT : ℕ
  eL : ℕ
  eO : ℕ
  sgBits : ℕ

section Scheme

variable (W : QueryLayout lam L) (D : SerLHB L) (p : Params) (Z : SizeNums L)

def SizeNums.extT : ExtNums := ⟨Z.eT, Nat.clog 2 L.wordLength + Z.sgBits, W.depth⟩
def SizeNums.extL : ExtNums := ⟨Z.eL, Nat.clog 2 L.wordLength + 1 + Z.sgBits, W.depth⟩
def SizeNums.extO : ExtNums := ⟨Z.eO, Nat.clog 2 L.wordLength + Z.sgBits, W.depth⟩

/-- The serializers keep to the widths. -/
structure SizeNums.Within : Prop where
  T : SerS.Within _ D.T Z.bT
  Lk : SerS.Within _ D.Lk Z.bL
  O : SerS.Within _ D.O Z.bO
  sg : ∀ a, (D.sg.put a).length ≤ Z.sgBits




variable {W D p Z}

theorem ext1_le (hZ : Z.Within D) (q : Fin L.wordLength) (a : L.Symbol) :
    ((serPos1 L).put q).length + (D.sg.put a).length ≤ Nat.clog 2 L.wordLength + Z.sgBits :=
  Nat.add_le_add (le_of_eq (Ser.length_put_fin _ _)) (hZ.sg a)

theorem ext2_le (hZ : Z.Within D) (q : Fin L.wordLength ⊕ Fin L.wordLength) (a : L.Symbol) :
    ((serPos2 L).put q).length + (D.sg.put a).length ≤ Nat.clog 2 L.wordLength + 1 + Z.sgBits := by
  refine Nat.add_le_add (le_of_eq ?_) (hZ.sg a)
  cases q with
  | inl q => exact (Ser.length_put_inl _ _ q).trans (by rw [Ser.length_put_fin])
  | inr q => exact (Ser.length_put_inr _ _ q).trans (by rw [Ser.length_put_fin])


end Scheme

end Compile.Batch
