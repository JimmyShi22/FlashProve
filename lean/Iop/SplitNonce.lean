-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Iop/SplitNonce.lean: a plan of splits that gives every proof-of-work nonce a separate round.

Definitions and lemmas, for every list of rounds and every list of numbers of proof-of-work bits
(`GBits`, Iop/GBits.lean); no number occurs.

Why. Proof-of-work bits are added last among the protocol transformers (Iop/Grind.lean): a round
with b > 0 bits gets the nonce into the plain part (words of this library: lean/GLOSSARY.md) of its
own prover message. So the Fiat-Shamir query of a proof-of-work attempt contains the round's full
prover message beside the nonce. A program may instead hash the message first, into a state, and
then hash (digest of the state, nonce) at every attempt. That form is reached before the bits are
added, by a split (Iop/Split.lean, Iop/BatchSplit.lean): every round that is to get proof-of-work
bits is split in two; the first part is the whole prover message, with the empty challenge; the
remainder is a round with the empty prover message and the old challenge. The bits go with the
remainder (`GBits.split`). When they are then added, the prover message of the remainder is only the
nonce.
  `RCut.allFirst r`, `ACut.allFirst a`: the split with everything in the first part, and its
      annotation in a protocol with slots (Iop/Batch.lean)
  `SPlan.nonce g`, `APlan.nonce g A`: the plan (a round with 0 bits stays; a round with b + 1 bits
      is split by `RCut.allFirst`, and the remainder stays) and its annotation. `SPlan.nonce_ok`,
      `APlan.nonce_ok` (for a coherent A), `APlan.nonce_fit` (wherever A has the format,
      Iop/BatchFmt.lean): the conditions on plans hold
  `GBits.split P g`, `OpenList.nonceF g o`: numbers of bits, and flags (for pruned Merkle paths, as
      in Iop/RecutFlags.lean), along the plan
  `Round.Bare r`, `GBits.Bare g`: "the prover message of r is empty: Orc = Unit, Pos = Empty, Plain
      = Unit, as equations between types"; "every round with a test is bare" (a test: proof-of-work
      bits)
  `GBits.bare_nonce`, `GBits.noChal_nonce`: what the plan achieves
  `SPlan.nonceKits`, `SPlan.nonceKitsB`, `APlan.nonceAKits`, `BatchProtocol.nonceKits`: the further data of
      the new rounds (`RKit`, `AKit`, Iop/SplitData.lean): no new datum
`GBits.split` has the cases `keep` and `cut` of `GBits.recut` (Iop/GrindRecut.lean). The remainder
gets the flag 0, where `OpenList.recutF` (Iop/RecutFlags.lean) lets both parts inherit: the
remainder has no position, so its flag does nothing, and the number of flagged rounds stays the
same.

Limits:
- The plan looks only at the number of proof-of-work bits: a round with bits whose prover message is
  already empty is split all the same, and gets an idle round before it; so the plan applied twice
  splits twice.
- Nothing on any protocol, on the compiler (Compile/) or on a program.
- What an attempt's query then contains depends on the compiler's queries (the statements on it are
  not in this library): no message of another round, except for what the prover writes into the bits
  of the nonce: the nonce is that round's own prover message, and its value is bound by no
  statement.
- The number of rounds grows by the number of rounds with bits, so every number of the compiler that
  counts rounds changes.
-/
import Iop.SplitKit
import Iop.SplitData
import Iop.GBitsSumF
import Iop.GBitsLe
import Iop.Sizes
import Iop.RecutFlags

set_option autoImplicit false

namespace Iop

/-! ## 1. The split with everything in the first part -/

/-- The whole prover message first; the remainder is the empty message, and then the challenge. -/
def RCut.allFirst (r : Round) : RCut r where
  OrcA := r.Orc
  OrcB := Unit
  PosA := r.Pos
  PosB := Empty
  PlainA := r.Plain
  PlainB := Unit
  orc := (Equiv.prodPUnit r.Orc).symm
  pos := Equiv.sumEmpty r.Pos Empty
  plain := (Equiv.prodPUnit r.Plain).symm
  rdA := fun o p => r.rd o p
  rdB := fun _ p => p.elim

theorem RCut.allFirst_ok (r : Round) : (RCut.allFirst r).OK := ⟨fun _ _ => rfl, fun _ p => p.elim⟩

variable {r : Round}

/-- The annotation of `RCut.allFirst`: the first part has the kind and the components of the old
round; both components of the remainder are empty. -/
def ACut.allFirst (a : RAnn r) : ACut (RCut.allFirst r) a where
  kind := a.kind
  A := ⟨a.M0, a.Mj, a.split, a.P0, a.Pj, a.pl0, a.plj, a.plain, a.own⟩
  B := ⟨Unit, Unit, Equiv.refl (Unit × Unit), Unit, Unit, fun _ => (), fun _ => (),
    (Equiv.punitProd Unit).symm, fun p => p.elim⟩
  m0 := (Equiv.prodPUnit a.M0).symm
  mj := (Equiv.prodPUnit a.Mj).symm

theorem ACut.allFirst_ok {a : RAnn r} (h : a.Coherent) : (ACut.allFirst a).OK where
  join := fun _ _ => rfl
  ownA := fun _ => rfl
  ownB := fun p => p.elim
  plainA := fun m0 mj => h.plain_join m0 mj
  plainB := fun _ _ => rfl

/-- the remainder has no slot's component, and no shared one -/
theorem ACut.allFirst_noSlot (a : RAnn r) : (ACut.allFirst a).ann2.NoSlot :=
  ⟨fun p => p.elim, inferInstanceAs (Subsingleton Unit)⟩
theorem ACut.allFirst_noShared (a : RAnn r) : (ACut.allFirst a).ann2.NoShared :=
  ⟨fun p => p.elim, inferInstanceAs (Subsingleton Unit)⟩

/-! ## 2. The plan -/

/-- The plan: a round without proof-of-work bits stays; a round with such bits is split by
`RCut.allFirst`. -/
def SPlan.nonce : {s : Shape} → GBits s → SPlan s
  | [], _ => .nil
  | r :: _, (0, g) => .keep r (SPlan.nonce g)
  | r :: _, (_ + 1, g) => .cut (RCut.allFirst r) (.keep _ (SPlan.nonce g))

/-- The annotation of `SPlan.nonce`. -/
def APlan.nonce : {s : Shape} → (g : GBits s) → (A : RoundSplits s) → APlan (SPlan.nonce g) A
  | [], _, _ => PUnit.unit
  | _ :: _, (0, g), (_, A) => APlan.nonce g A
  | _ :: _, (_ + 1, g), (a, A) => ⟨ACut.allFirst a, APlan.nonce g A⟩

theorem SPlan.nonce_ok : ∀ {s : Shape} (g : GBits s), (SPlan.nonce g).OK
  | [], _ => trivial
  | _ :: _, (0, g) => SPlan.nonce_ok g
  | r :: _, (_ + 1, g) => ⟨RCut.allFirst_ok r, SPlan.nonce_ok g⟩

theorem APlan.nonce_ok :
    ∀ {s : Shape} (g : GBits s) (A : RoundSplits s),
      A.Coherent → APlan.OK (SPlan.nonce g) A (APlan.nonce g A)
  | [], _, _, _ => trivial
  | _ :: _, (0, g), (_, A), h => APlan.nonce_ok g A h.2
  | _ :: _, (_ + 1, g), (_, A), h => ⟨ACut.allFirst_ok h.1, APlan.nonce_ok g A h.2⟩

/-- The number of splits is the number of rounds with proof-of-work bits. -/
theorem SPlan.cuts_nonce : ∀ {s : Shape} (g : GBits s), (SPlan.nonce g).cuts = g.count
  | [], _ => rfl
  | _ :: _, (0, g) => (SPlan.cuts_nonce g).trans (Nat.zero_add _).symm
  | _ :: _, (_ + 1, g) => (congrArg (· + 1) (SPlan.cuts_nonce g)).trans (Nat.add_comm _ _)

/-- The plan fits the format wherever the annotation has the format. -/
theorem APlan.nonce_fit :
    ∀ {s : Shape} (g : GBits s) (A : RoundSplits s) (ph : FPhase),
      RoundSplits.FmtFrom s A ph → APlan.Fit (SPlan.nonce g) A (APlan.nonce g A) ph
  | [], _, _, _, _ => trivial
  | _ :: s, (0, g), (a, A), ph, h => by
      show APlan.Fit (SPlan.nonce g) A (APlan.nonce g A) (FPhase.after a.kind ph)
      refine APlan.nonce_fit g A _ ?_
      cases hk : a.kind <;> cases ph <;> simp only [RoundSplits.FmtFrom, hk] at h <;> first | exact h.2 | exact h
  | _ :: s, (_ + 1, g), (a, A), ph, h => by
      show FPhase.fit a.kind a.kind ph (ACut.allFirst a).ann2.NoSlot
          (ACut.allFirst a).ann1.NoShared ∧
        APlan.Fit (SPlan.nonce g) A (APlan.nonce g A) (FPhase.after a.kind (FPhase.after a.kind ph))
      cases hk : a.kind <;> cases ph <;> simp only [RoundSplits.FmtFrom, hk] at h <;>
        first
          | exact h.elim
          | exact ⟨trivial, APlan.nonce_fit g A _ h.2⟩
          | exact ⟨ACut.allFirst_noSlot a, APlan.nonce_fit g A _ h⟩

/-! ## 3. Numbers of proof-of-work bits along any plan of splits, and flags along the plan -/

/-- The numbers of proof-of-work bits on the new list of rounds: they stay with the part that keeps
the challenge. -/
def GBits.split : {s : Shape} → (P : SPlan s) → GBits s → GBits P.shape
  | _, .nil => fun _ => ()
  | _, .keep _ P => fun (z : ℕ × GBits _) => (z.1, GBits.split P z.2)
  | _, .cut (s := s) c P =>
    fun (z : ℕ × GBits s) => (0, GBits.split P (show GBits (c.snd :: s) from z))

/-- Every sum over the rounds with proof-of-work bits is preserved. -/
theorem GBits.sumF_split {M : Type} [AddCommMonoid M] (f : ℕ → M) {s : Shape} (P : SPlan s) :
    ∀ g : GBits s, GBits.sumF f (g.split P) = GBits.sumF f g := by
  induction P with
  | nil => intro _; rfl
  | keep r P ih => exact fun g => congrArg ((if g.1 = 0 then 0 else f g.1) + ·) (ih g.2)
  | cut c P ih =>
      intro g
      show (if (0 : ℕ) = 0 then 0 else f 0) + GBits.sumF f (GBits.split P _) = _
      rw [if_pos rfl, zero_add]
      exact ih g

theorem GBits.count_split {s : Shape} (P : SPlan s) (g : GBits s) :
    (g.split P).count = g.count := by
  rw [GBits.count_eq_sumF, GBits.count_eq_sumF, GBits.sumF_split]

theorem GBits.AllLe.split {n : ℕ} {s : Shape} (P : SPlan s) :
    ∀ g : GBits s, g.AllLe n → (g.split P).AllLe n := by
  induction P with
  | nil => intro _ _; trivial
  | keep r P ih => exact fun g h => ⟨h.1, ih g.2 h.2⟩
  | cut c P ih => exact fun g h => ⟨Nat.zero_le n, ih g h⟩

/-- Flags along the plan: the first part, which has all positions of the round, has the round's
flag; the remainder, which has no position, has the flag 0. -/
def OpenList.nonceF : {s : Shape} → (g : GBits s) → OpenList s → OpenList (SPlan.nonce g).shape
  | [], _, _ => ()
  | _ :: _, (0, g), (n, o) => (n, OpenList.nonceF g o)
  | _ :: _, (_ + 1, g), (n, o) => (n, 0, OpenList.nonceF g o)

/-- The flags that are not 0 are the old ones, in the old order. -/
theorem OpenList.nonceF_filter :
    ∀ {s : Shape} (g : GBits s) (o : OpenList s),
      (OpenList.nonceF g o).toList.filter (· ≠ 0) = o.toList.filter (· ≠ 0)
  | [], _, _ => rfl
  | _ :: _, (0, g), (n, o) => by
      show (n :: (OpenList.nonceF g o).toList).filter (· ≠ 0) = (n :: o.toList).filter (· ≠ 0)
      rw [List.filter_cons, List.filter_cons, OpenList.nonceF_filter g o]
  | _ :: _, (_ + 1, g), (n, o) => by
      show (n :: 0 :: (OpenList.nonceF g o).toList).filter (· ≠ 0) = (n :: o.toList).filter (· ≠ 0)
      have e : (0 :: (OpenList.nonceF g o).toList).filter (· ≠ 0) = o.toList.filter (· ≠ 0) :=
        (List.filter_cons_of_neg (by decide)).trans (OpenList.nonceF_filter g o)
      have c : ∀ l l' : List ℕ, l.filter (· ≠ 0) = l'.filter (· ≠ 0) →
          (n :: l).filter (· ≠ 0) = (n :: l').filter (· ≠ 0) :=
        fun l l' h => by rw [List.filter_cons, List.filter_cons, h]
      exact c _ _ e

/-- no flag before the plan, no flag after it -/
theorem OpenList.nonceF_zero :
    ∀ {s : Shape} (g : GBits s), OpenList.nonceF g (OpenList.zero s) = OpenList.zero _
  | [], _ => rfl
  | _ :: _, (0, g) => congrArg (Prod.mk 0) (OpenList.nonceF_zero g)
  | _ :: _, (_ + 1, g) =>
    congrArg (fun x => ((0, 0, x) : ℕ × ℕ × OpenList _)) (OpenList.nonceF_zero g)

/-! ## 4. What the plan achieves -/

/-- The prover message of the round is empty, as equations between types. -/
def Round.Bare (r : Round) : Prop := r.Orc = Unit ∧ r.Pos = Empty ∧ r.Plain = Unit

/-- Every round with proof-of-work bits has the empty prover message. -/
def GBits.Bare : {s : Shape} → GBits s → Prop
  | [], _ => True
  | r :: _, (b, g) => (b ≠ 0 → r.Bare) ∧ GBits.Bare g

/-- After the plan every round with proof-of-work bits has the empty prover message. -/
theorem GBits.bare_nonce : ∀ {s : Shape} (g : GBits s), (g.split (SPlan.nonce g)).Bare
  | [], _ => trivial
  | _ :: _, (0, g) => ⟨fun h => absurd rfl h, GBits.bare_nonce g⟩
  | _ :: _, (_ + 1, g) => ⟨fun h => absurd rfl h, fun _ => ⟨rfl, rfl, rfl⟩, GBits.bare_nonce g⟩

/-- Every round with proof-of-work bits comes directly after a round without such bits whose
challenge has one value; `first`: may the first round have bits? -/
def GBits.NoChalBefore : {s : Shape} → GBits s → Bool → Prop
  | [], _, _ => True
  | r :: _, (b, g), first =>
    (b ≠ 0 → first = true) ∧
    GBits.NoChalBefore g (decide (b = 0) && decide (Fintype.card r.Chal = 1))

theorem GBits.noChal_nonce :
    ∀ {s : Shape} (g : GBits s) (first : Bool), (g.split (SPlan.nonce g)).NoChalBefore first
  | [], _, _ => trivial
  | _ :: _, (0, g), _ => ⟨fun h => absurd rfl h, GBits.noChal_nonce g _⟩
  | _ :: _, (_ + 1, g), _ => ⟨fun h => absurd rfl h, fun _ => rfl, GBits.noChal_nonce g _⟩

/-- `GBits.split` along the plan, written out at a round with proof-of-work bits, and at one
without. -/
theorem GBits.split_nonce_succ {s : Shape} (b : ℕ) (g : GBits s) :
    GBits.split (SPlan.nonce (s := r :: s) (b + 1, g)) (b + 1, g) =
      ((0, b + 1, g.split (SPlan.nonce g)) : ℕ × ℕ × GBits (SPlan.nonce g).shape) := rfl
theorem GBits.split_nonce_zero {s : Shape} (g : GBits s) :
    GBits.split (SPlan.nonce (s := r :: s) (0, g)) (0, g) =
      ((0, g.split (SPlan.nonce g)) : ℕ × GBits (SPlan.nonce g).shape) := rfl

/-! ## 5. The further data: no new datum -/

/-- the first part has the data of the round -/
def RKit.allFirstFst (K : RKit r) : RKit (RCut.allFirst r).fst where
  pt := ⟨K.pt.finPos, K.pt.decPos, K.pt.ofSyms, K.pt.rd_ofSyms, K.pt.ofSyms_rd, K.pt.zero⟩
  np := K.np
  ser := K.ser

/-- Sanity lemma: the numbering and the two serializers of the first part are the round's own. -/
theorem RKit.allFirstFst_np (K : RKit r) : K.allFirstFst.np = K.np := rfl
theorem RKit.allFirstFst_ser (K : RKit r) : K.allFirstFst.ser = K.ser := rfl

theorem card_empty_zero : Fintype.card Empty = 0 := Fintype.card_eq_zero

/-- the remainder has the data of an empty message -/
def RKit.allFirstSnd (r : Round) : RKit (RCut.allFirst r).snd where
  pt := ⟨inferInstanceAs (Fintype Empty), inferInstanceAs (DecidableEq Empty), fun _ => (),
    fun _ p => p.elim, fun _ => rfl, fun p => p.elim⟩
  np := (Equiv.equivOfIsEmpty Empty (Fin 0)).trans (finCongr card_empty_zero.symm)
  ser := (haveI : IsEmpty (Σ p : (RCut.allFirst r).snd.Pos, (RCut.allFirst r).snd.Sym p) := ⟨fun z => Empty.elim z.1⟩; Ser.ofIsEmpty _, Ser.unit)

/-- The further data of the plan, for an ordinary IOP: from the `IsPoint` data, numberings and
serializers of the old list of rounds. -/
def SPlan.nonceKits :
    {s : Shape} → (g : GBits s) → (pts : s.IsPoint) → s.NumPos pts → SerS s → (SPlan.nonce g).Kits
  | [], _, _, _, _ => ()
  | _ :: _, (0, g), (_, pts), (_, nps), (_, e) => SPlan.nonceKits g pts nps e
  | r :: _, (_ + 1, g), (pt, pts), (np, nps), (a, e) =>
    (RKit.allFirstFst ⟨pt, np, a⟩, RKit.allFirstSnd r, SPlan.nonceKits g pts nps e)

/-- the positions of the two components are all positions -/
theorem RAnn.card_parts (a : RAnn r) (pt : r.IsPoint) :
    a.cardJ pt + a.card0 pt = @Fintype.card r.Pos pt.finPos := by
  letI := pt.finPos
  exact Fintype.card_sum.symm.trans (Fintype.card_congr (sumOfBool a.own))

/-- a numbering of all positions of a round from the numberings of its two components: the slot's
first. (The compiler does not read it in a protocol with slots; `RKit` has the field.) -/
def numOfParts (a : RAnn r) (pt : r.IsPoint)
    (n0 : {p : r.Pos // a.own p = false} ≃ Fin (a.card0 pt))
    (nJ : {p : r.Pos // a.own p = true} ≃ Fin (a.cardJ pt)) :
    r.Pos ≃ Fin (@Fintype.card r.Pos pt.finPos) :=
  ((sumOfBool a.own).symm.trans (Equiv.sumCongr nJ n0)).trans
    (finSumFinEquiv.trans (finCongr (a.card_parts pt)))

/-- The further data of the plan, for a protocol with slots. -/
def SPlan.nonceKitsB :
    {s : Shape} → (g : GBits s) → (A : RoundSplits s) → (pts : s.IsPoint) →
    s.NumPosB A pts → SerS s → (SPlan.nonce g).Kits
  | [], _, _, _, _, _ => ()
  | _ :: _, (0, g), (_, A), (_, pts), (_, _, nps), (_, e) => SPlan.nonceKitsB g A pts nps e
  | r :: _, (_ + 1, g), (a, A), (pt, pts), (n0, nJ, nps), (x, e) =>
    (RKit.allFirstFst ⟨pt, numOfParts a pt n0 nJ, x⟩,
      RKit.allFirstSnd r,
      SPlan.nonceKitsB g A pts nps e)

/-- the data of the two empty components of the remainder -/
def AKit.allFirstSnd (a : RAnn r) : AKit (ACut.allFirst a).ann2 (RKit.allFirstSnd r).pt :=
  letI := (RKit.allFirstSnd r).pt.finPos
  ⟨numNone _ fun p _ => p.elim, numNone _ fun p _ => p.elim, (Ser.unit, Ser.unit)⟩

/-- The further data of the annotation: the first part has the numberings and serializers of the old
round's components. -/
def APlan.nonceAKits :
    {s : Shape} → (g : GBits s) → (A : RoundSplits s) → (pts : s.IsPoint) → (nps : s.NumPosB A pts) →
    (e : SerS s) → SerA s A →
    APlan.Kits (SPlan.nonce g) (SPlan.nonceKitsB g A pts nps e) A (APlan.nonce g A)
  | [], _, _, _, _, _, _ => ()
  | _ :: _, (0, g), (_, A), (_, pts), (_, _, nps), (_, e), (_, y) =>
    APlan.nonceAKits g A pts nps e y
  | _ :: _, (_ + 1, g), (a, A), (_, pts), (n0, nJ, nps), (_, e), (x, y) =>
    (⟨n0, nJ, x⟩, AKit.allFirstSnd a, APlan.nonceAKits g A pts nps e y)

variable {I X : Type}

/-- All further data of the three plans of a record of protocols, from the record's own data. -/
def BatchProtocol.nonceKits (L : BatchProtocol I X) (gT : GBits L.offline.shape) (gL : GBits L.link.shape)
    (gB : GBits L.onlineBatch.loc.shape) {pT : L.offline.shape.IsPoint} {pL : L.link.shape.IsPoint}
    {pB : L.onlineBatch.loc.shape.IsPoint} (ax : L.Aux pT pL pB) (D : SerLHB L) :
    L.SplitKits (SPlan.nonce gT) (SPlan.nonce gL) (SPlan.nonce gB) (APlan.nonce gB L.onlineBatch.ann) where
  T := SPlan.nonceKits gT pT ax.posT D.T
  Lk := SPlan.nonceKits gL pL ax.posL D.Lk
  B := SPlan.nonceKitsB gB L.onlineBatch.ann pB ax.posB D.O
  A := APlan.nonceAKits gB L.onlineBatch.ann pB ax.posB D.O D.A

/-! ## 6. An `OpenList` on a list of rounds whose challenges are computed by samplers
(`Shape.pull`), as one on the list itself -/

def OpenList.unpull : (s : Shape) → (σ : Samplers s) → OpenList (Shape.pull s σ) → OpenList s
  | [], _, _ => ()
  | _ :: s, (_, σs), (n, o) => (n, OpenList.unpull s σs o)

theorem OpenList.unpull_pull :
    ∀ (s : Shape) (σ : Samplers s) (o : OpenList s), OpenList.unpull s σ (OpenList.pull s σ o) = o
  | [], _, _ => rfl
  | _ :: s, (_, σs), (n, o) => congrArg (Prod.mk n) (OpenList.unpull_pull s σs o)

theorem OpenList.pull_unpull :
    ∀ (s : Shape) (σ : Samplers s) (o : OpenList (Shape.pull s σ)),
      OpenList.pull s σ (OpenList.unpull s σ o) = o
  | [], _, _ => rfl
  | _ :: s, (_, σs), (n, o) => congrArg (Prod.mk n) (OpenList.pull_unpull s σs o)

end Iop
