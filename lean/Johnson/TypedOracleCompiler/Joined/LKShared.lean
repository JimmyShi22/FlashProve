-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/TypedOracleCompiler/Joined/LKShared.lean: a typed list of bare blocks, run once by the shared part of a
batch: if every block is a link with keys, the list's one block is one.

Rules alone. No clause of any block is shown here.


A typed list of bare blocks (`KObj.LK`, Johnson/E/KObj/Blocks.lean) describes a stretch of a
protocol for one instance; `LK.blk` makes one block of it: one reduction, one extractor, one list of
errors. In a batch of at most N instances a stretch may be run once for all, by the shared part of
the prover, under shared verifier messages. Then a round's error counts the verifier messages that
are bad for some slot. It is the error for one instance if the slots have the same bad messages.
The library says this with keys (`ldk_LinkB`, Cb/Ld/LdLinBProofs.lean): a link is knowledge sound
for the vectors of statements with one key, and takes them to vectors with one key. This file has
the same over `LK`, in the list's own bracketing: so the reduction of which the batch's clause
speaks is the very reduction of the list for one instance.

Main names:
  `KObj.shAn s`: the annotation in which only the shared part speaks and all verifier messages are
    shared.
  `KObj.KK A`: a key at a joint: a function of the statement (the library's `JKey`, over `JK`).
  `KObj.BK.LinkB b An N kA kB`: the block b under the annotation An is knowledge sound, at its own
    list of errors, for the vectors with one key kA (`KnowBInto`, Ior/KnowWideB.lean), and takes
    them to vectors with one key kB. `KObj.BK.LinkSh`: that at `shAn`.
  `KObj.BK.linkB_seq`, `KObj.BK.linkSh_seq`: two in a row.
  `KObj.LK.KeyedSh N l kA kB`: every block of l is a `LinkSh`, along some keys between.
  `KObj.BK.LinkB.finer`, `KObj.LK.keyedSh_finer`: a finer key in front.
  `KObj.LK.keyedSh_app`: two lists in a row.
  `KObj.LK.linkSh_blk`: then `l.blk d` is a `LinkSh` from kA to kB.

Limits: all that such a clause says hangs on which vectors have one key (the head of
Ior/BatchSeq.lean). A block is charged its own field `err`: where a round's error for a batch is
larger than for one instance, the list must hold a block with that larger error.

Terms: lean/GLOSSARY.md.
-/
import Johnson.E.KObj.Blocks
import Ior.KnowWideB
import Cb.Ld.LdLinBProofs
import Iop.SplitUnderJoin

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace KObj
open Iop Prob IOR

/-- The annotation in which only the shared part speaks and every verifier message is shared. -/
abbrev shAn (s : Shape) : RoundSplits s := RoundSplits.const (RAnn.ofShared .sh) s

/-- A key at a joint: what the statements of one batch have in common there. -/
structure KK (A : JK) : Type 1 where
  κ : Type
  key : A.X × A.E.Str → κ

/-- A bare block as a link of a batch, under any annotation: knowledge sound, at the block's own
list of errors, for the vectors with one key; and such vectors are taken to vectors with one key. -/
structure BK.LinkB {A B : JK} (b : BK A B) (An : RoundSplits b.R.shape) (N : ℕ) (kA : KK A) (kB : KK B) :
    Prop where
  know : b.R.KnowBInto An N (SameKey kA.key) A.on B.on A.relR B.relR b.ext b.err
  adm : ∀ a, SameKey kA.key a → ∀ τ : BTr N b.R.shape An,
    SameKey kB.key fun j => (a j).bind fun aj => b.R.red.out aj (τ.slot j)

/-- The same, run once by the shared part. -/
abbrev BK.LinkSh {A B : JK} (b : BK A B) (N : ℕ) (kA : KK A) (kB : KK B) : Prop :=
  b.LinkB (shAn b.R.shape) N kA kB

/-- A finer key in front: fewer vectors have one key. -/
theorem BK.LinkB.finer {A B : JK} {b : BK A B} {An : RoundSplits b.R.shape} {N : ℕ} {kA : KK A} {kB : KK B}
    (h : b.LinkB An N kA kB) (kA' : KK A) (F : kA'.κ → kA.κ)
    (hF : ∀ a, kA.key a = F (kA'.key a)) : b.LinkB An N kA' kB := by
  have hs : ∀ a : Fin N → Option (A.X × A.E.Str), SameKey kA'.key a → SameKey kA.key a :=
    fun a ha j j' aj aj' hj hj' => by rw [hF aj, hF aj', ha j j' aj aj' hj hj']
  exact ⟨knowB_conseq _ _ _ _ _ _ b.R An N _ _ _ _ _ _ _ _ _ _ h.know hs (fun _ ha => ha)
    (fun _ _ _ hw => hw) (fun _ _ hw => hw), fun a ha => h.adm a (hs a ha)⟩

/-- Two links in a row are a link. -/
theorem BK.linkB_seq {A B C : JK} (b : BK A B) (c : BK B C) (d : A.W) {An : RoundSplits b.R.shape}
    {Cn : RoundSplits c.R.shape} {N : ℕ} {kA : KK A} {kB : KK B} {kC : KK C} (hb : b.LinkB An N kA kB)
    (hc : c.LinkB Cn N kB kC) : (b.seq c d).LinkB (RoundSplits.app An Cn) N kA kC where
  know := by
    refine knowBInto_seq_ext _ _ _ _ _ _ _ _ _ b.R c.R An Cn N _ _ A.on B.on C.on A.relR B.relR
      C.relR b.ext c.ext _ b.err c.err hb.know hc.know hb.adm fun a τ x w hx => ?_
    have hx' : Option.map (fun xo => (xo, b.R.imp a.2 (Tr.fst τ)))
        (b.R.out a.1 a.2 (Tr.fst τ)) = some x := hx
    show IOR.extSeq b.R c.R b.ext c.ext d a τ w = _
    simp only [IOR.extSeq, Reduction.extSeq]
    rw [hx']
  adm := ldk_adm_seq b.R c.R An Cn hb.adm hc.adm

/-- The same where only the shared part speaks. -/
theorem BK.linkSh_seq {A B C : JK} (b : BK A B) (c : BK B C) (d : A.W) {N : ℕ} {kA : KK A}
    {kB : KK B} {kC : KK C} (hb : b.LinkSh N kA kB) (hc : c.LinkSh N kB kC) :
    (b.seq c d).LinkSh N kA kC := by
  have h := BK.linkB_seq b c d hb hc
  have e : shAn (b.seq c d).R.shape = RoundSplits.app (shAn b.R.shape) (shAn c.R.shape) :=
    RoundSplits.const_app _ b.R.shape c.R.shape
  show (b.seq c d).LinkB (shAn (b.seq c d).R.shape) N kA kC
  rw [e]
  exact h

namespace LK

/-- Every block of the list is such a link, along some keys between. -/
def KeyedSh (N : ℕ) : {A B : JK} → LK A B → KK A → KK B → Prop
  | _, _, .one b, kA, kB => b.LinkSh N kA kB
  | _, _, .snoc (B := B) l b, kA, kC => ∃ kB : KK B, l.KeyedSh N kA kB ∧ b.LinkSh N kB kC

variable {N : ℕ}

theorem keyedSh_one {A B : JK} (b : BK A B) (kA : KK A) (kB : KK B) :
    (LK.one b).KeyedSh N kA kB ↔ b.LinkSh N kA kB := by rw [KeyedSh]
theorem keyedSh_snoc {A B C : JK} (l : LK A B) (b : BK B C) (kA : KK A) (kC : KK C) :
    (l.snoc b).KeyedSh N kA kC ↔ ∃ kB : KK B, l.KeyedSh N kA kB ∧ b.LinkSh N kB kC := by
  rw [KeyedSh]

/-- A finer key in front of a list. -/
theorem keyedSh_finer {A B : JK} (l : LK A B) (kA kA' : KK A) (F : kA'.κ → kA.κ)
    (hF : ∀ a, kA.key a = F (kA'.key a)) :
    ∀ kB : KK B, l.KeyedSh N kA kB → l.KeyedSh N kA' kB := by
  induction l with
  | one b =>
    intro kB h
    exact (keyedSh_one b kA' kB).2 (((keyedSh_one b kA kB).1 h).finer kA' F hF)
  | snoc l b ih =>
    intro kC h
    obtain ⟨kB, h1, h2⟩ := (keyedSh_snoc l b kA kC).1 h
    exact (keyedSh_snoc l b kA' kC).2 ⟨kB, ih kB h1, h2⟩

/-- Two lists in a row. -/
theorem keyedSh_app {A B C : JK} (l : LK A B) (m : LK B C) (kA : KK A) (kB : KK B) :
    ∀ kC : KK C, l.KeyedSh N kA kB → m.KeyedSh N kB kC → (l.app m).KeyedSh N kA kC := by
  induction m with
  | one b =>
    intro kC h1 h2
    rw [app_one, keyedSh_snoc]
    exact ⟨kB, h1, (keyedSh_one b kB kC).1 h2⟩
  | snoc m b ih =>
    intro kC h1 h2
    obtain ⟨k, h3, h4⟩ := (keyedSh_snoc m b kB kC).1 h2
    rw [app_snoc, keyedSh_snoc]
    exact ⟨k, ih k h1 h3, h4⟩

/-- **The list's one block is a link of the batch**: the same reduction, extractor and errors as for
one instance (`LK.blk`). -/
theorem linkSh_blk {A B : JK} (l : LK A B) (d : A.W) (kA : KK A) :
    ∀ kB : KK B, l.KeyedSh N kA kB → (l.blk d).LinkSh N kA kB := by
  induction l with
  | one b =>
    intro kB h
    rw [blk_one]
    exact (keyedSh_one b kA kB).1 h
  | snoc l b ih =>
    intro kC h
    obtain ⟨kB, h1, h2⟩ := (keyedSh_snoc l b kA kC).1 h
    rw [blk_snoc]
    exact BK.linkSh_seq _ b d (ih kB h1) h2

end LK

end KObj
