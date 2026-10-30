--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K14/Law/MemberKey.lean: A CLAUSE OF THE PROMISE THAT THE ROW OF THE EIGHT CAN BEAR AT
ALL NINE BORDERS: "the stored table has no collision at the key's seeds, and the key fits the stored
table's shape": the two things that the law of "LIN point" asks under the promise
(Johnson/Desc/K14/Law/PointKey2.lean: hcoll, hfit) ARE THE CLAUSE, and every one of the eight blocks
keeps it.

  key_of_blocks   at each of the eight blocks a yes leaves the key in the small record.
  PrmK            the clause: it reads the stored table's columns off the oracle string's first
                  component, and the record's key: nothing else.
  keepK           a yes of a piece that holds one of the eight blocks keeps it: a stretch leaves the
                  stored table (tabOf_imp), the block leaves the key.
  hcollK, hfitK   the two premises of point_goodInY2, by the clause's make.
  hdetVK          two pinned witnesses have one other vector: by the pin's form.

What is not claimed. THAT ANY STATEMENT MEETS PrmK IS NOT SHOWN: no stored table is exhibited; that
a stored table has no collision at its key's seeds, but for the priced seeds, is the law of the
place where the record's seed is drawn: another kind's. hdetVK moves its debt to the chain's end: to
whoever shows there that the witness which the closing tests' extractor lays has the decoder's
words. The letters err, eM, rank of the typed data stay. Nothing on the count of the bad points, on
g, on the written rounds or on the sending kind's premises. No soundness of a verifier.

-/
import Johnson.Desc.K14.Law.Member
import Johnson.Desc.K14.Law.PointKey2

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain
open Iop Prob Run OnBytes.Maker OnBytes.Flat
open OnBytes.Means (Words)
open VerifiableInference.Desc (Grows Block)
open VerifiableInference.Desc.Ground
open VerifiableInference.Desc.Sound (Frame Piece)
open _root_.Run.PQ (CK)

/-- **At each of the eight blocks a yes leaves the key**; two codes. -/
theorem key_of_blocks (P : P14) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hbl : blocks P = some [b1, b2, b3, b4, b5, b6, b7, b8])
    (hS : P.S.sharedSplitNeeded = true) :
    ∀ b ∈ [b1, b2, b3, b4, b5, b6, b7, b8], ∀ d rs gs d', b.decide d rs gs = .ok d' →
      d'.loc.key = d.loc.key := by
  obtain ⟨⟨sentU, _, hs2⟩, hs5⟩ := send_of_blocks P b1 b2 b3 b4 b5 b6 b7 b8 hbl
  have hq := quiet_of_blocks P b1 b2 b3 b4 b5 b6 b7 b8 hbl
  intro b hb d rs gs d' h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · obtain ⟨_, _, _, hk, _, _⟩ := linPoint_inv P.par d d' rs
      (point_of_blocks P _ b2 b3 b4 b5 b6 b7 b8 hbl d rs gs d' h)
    exact hk
  · obtain ⟨ft, ids, a1, a2, r, _, cl, k⟩ := hs2 d rs gs d' h
    obtain ⟨_, o, mask, _, l⟩ := behindU_inv P.par a2 d' ids k
    rw [l, cl, (onward_recvP ft d a1 _ ids r).2]
  · rw [(onward_laysRec P.par d d' rs (hq.1 d rs gs d' h)).2]
  · have k := loc_of_blocks P b1 b2 b3 _ b5 b6 b7 b8 hbl d rs gs d' h
    obtain ⟨r4, cols, hr, hg⟩ := loc_one _ _ _ _ _ k
    rw [hr, hg] at k
    rw [(onward_loc P.par d d' r4 cols k).2]
  · obtain ⟨ft, ids, a1, a2, r, _, cl, k⟩ := hs5 d rs gs d' h
    obtain ⟨_, o, sp, _, l⟩ := behindOmega_inv P.par a2 d' ids k
    rw [l, cl, (onward_recvP ft d a1 _ ids r).2]
  · rw [(onward_joins P.par d d' rs (hq.2 d rs gs d' h)).2]
  · have k := zeta_of_blocks P b1 b2 b3 b4 b5 b6 _ b8 hbl d rs gs d' h
    obtain ⟨r7, hr⟩ := linZeta_one _ _ _ k
    rw [hr] at k
    rw [linZeta_inv d d' r7 k]
  · have k := decidesBySplit_of_blocks P b1 b2 b3 b4 b5 b6 b7 _ hbl d rs gs d' h
    obtain ⟨r8, hr⟩ := split_one _ _ _ _ hS k
    rw [hr] at k
    rw [(onward_split P.par d d' r8 hS k).2]

variable {W : Type} {F : Frame}

/-- **The promise**: the stored table has no collision at the key's seeds; the key fits the
shape. -/
def PrmK (P : P14) (err eM : Nat)
    (rank : ((Fin P.par.S.fold.index.v → Bool) →
      Fin (P.par.S.fold.index.code.r + P.par.S.fold.index.code.ell) → GE) → Nat)
    (x : St × F.E.Str) : Prop :=
  ¬ (ixOf2 P.par.S.fold err eM rank).Coll
      (tabF OnBytes.Model.Reading.gl P.par.S.fold.index (tabOf x.2))
      (seedsFn OnBytes.Model.Reading.gl P.par.S.fold.index x.1.loc.key) ∧
    x.1.loc.key.fits P.par.S.fold.index = true

/-- **A yes of a piece that holds a block which leaves the key keeps the promise.** -/
theorem keepK {C : CK} (P : P14) (err eM : Nat)
    (rank : ((Fin P.par.S.fold.index.v → Bool) →
      Fin (P.par.S.fold.index.code.r + P.par.S.fold.index.code.ell) → GE) → Nat)
    (pc : Piece C F St Unit W)
    (hk : ∀ d rs gs d', pc.b.decide d rs gs = .ok d' → d'.loc.key = d.loc.key) :
    ∀ a τ b, pc.ior.red.out a τ = some b → PrmK P err eM rank a → PrmK P err eM rank b := by
  intro a τ b hout ha
  obtain ⟨hy, gs, hd⟩ := piece_yes pc a τ b hout
  unfold PrmK at ha ⊢
  rw [hy, tabOf_imp, hk _ _ gs _ hd]
  exact ha

variable (rg : W → Words GE) (wv : W → Nat → GE) (D : St × F.E.Str → Words GE)
  (DV : St × F.E.Str → Nat → GE)

/-- point_goodInY2's hcoll, by the promise's make. -/
theorem hcollK (P : P14) (err eM : Nat)
    (rank : ((Fin P.par.S.fold.index.v → Bool) →
      Fin (P.par.S.fold.index.code.r + P.par.S.fold.index.code.ell) → GE) → Nat) :
    ∀ a : St × F.E.Str, PrmK P err eM rank a → ¬ (ixOf2 P.par.S.fold err eM rank).Coll
      (tabF OnBytes.Model.Reading.gl P.par.S.fold.index (tabOf a.2))
      (seedsFn OnBytes.Model.Reading.gl P.par.S.fold.index a.1.loc.key) :=
  fun _ h => h.1

/-- point_goodInY2's hfit, by the promise's make. -/
theorem hfitK (P : P14) (err eM : Nat)
    (rank : ((Fin P.par.S.fold.index.v → Bool) →
      Fin (P.par.S.fold.index.code.r + P.par.S.fold.index.code.ell) → GE) → Nat) :
    ∀ a : St × F.E.Str, PrmK P err eM rank a → a.1.loc.key.fits P.par.S.fold.index = true :=
  fun _ h => h.2

/-- point_goodInY2's hdetV, by the pin's form. -/
theorem hdetVK (Prm : St × F.E.Str → Prop) :
    ∀ (x : St × F.E.Str) w w', Prm x → PinF rg wv D DV x w → PinF rg wv D DV x w' →
      wv w = wv w' :=
  fun _ _ _ _ h h' => h.2.trans h'.2.symm

end Desc.K14.Law
