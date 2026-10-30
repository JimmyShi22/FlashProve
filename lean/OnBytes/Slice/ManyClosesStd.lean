-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/ManyClosesStd.lean: the hypothesis on the rounds after the link's fifth, for a chain
of any number of stages, at the standard readings of the first tree.

OnBytes/Slice/ManyCloses.lean proves `Closes` at the batching's round and a chain's rounds. It asks
the batching's statement (`BatSem`) and two facts on how the link's rows and the first tree are
read. This file takes the standard readings of OnBytes/Slice/SemLib.lean (`rowsX`, `col1`) and the
batching's error count for lists of one member, and derives these three from facts on public sizes
and rounds.

Main theorem: `closes_many_std`.
Asked there: the first stage's sizes are in order; the field, the order of rows and the length of a
row are as the batching's block asks; the chain's first radius is at most the radius of a folded
row's oracle message and below half the first stage's distance; the first six rounds send and draw
what the link and the batching do; the first tree has the group's width and positions; each block of
the chain is taken off; the decision's yes in the written protocol gives the chain's yes in the
field.
Not claimed. That any decision's yes gives the yes in the field. Nothing on the sizes of the error
counts.

-/
import OnBytes.Slice.BatAt
import OnBytes.Slice.ManyCloses

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Prob Cb Cb.Ood Run

/-- The rounds after the fifth close the link, where they are the batching's round dA and the rounds
of a chain from the link's first stage on, at the standard readings of the link's rows and of the
first tree. c' is the chain c, written from the stage s1 on. What is asked of the blocks, and the
conclusion, speak of c'; what is asked of the decision speaks of c. The masking word of the first
stage, which no chain with a step reads, is set to the first word. More is asked than is needed: of
the record that `batOK_of` makes with hf and hh the proof keeps only the part that does not rest on
them, and of hd it takes only what the batching's round sends and draws. -/
theorem closes_many_std (S : Sz) (t₀ : ℕ) (d1 d2 d3 d4 d5 dA : PQ.RD) (xs : List PQ.XO)
    (dec : PQ.View → Bool) (s1 : Sg) (hs : S.sg t₀ = s1) (c : Chain (S.sg t₀)) (c' : Chain s1)
    (hcc : HEq c c') (hsz : s1.Sized) (hf : S.P.fld = .two) (hh : S.P.high = true)
    (hl : S.P.C.l = 2 ^ S.P.aP) (he : c'.rad ≤ S.eU) (h2 : 2 * c'.rad < s1.d)
    (hd : BatDraws S d1 d2 d3 d4 d5 dA) (hW : PQ.colW d2.tree = Fmt.M2.widthOf S.P.mems 1)
    (hN : PQ.posN d2.tree = 2 ^ S.P.C.a) (hc : c'.Holds)
    (hsem : ∀ (y : S.lk.E0.Str) m0 c0 m1 c1 m2 c2 m3 c3 m4 c4 m5 c5 mA cA (b : c.Bl),
      (written S d1 d2 d3 d4 d5 (dA :: c.rds) xs dec).accept () y
        (m0, c0, m1, c1, m2, c2, m3, c3, m4, c4, m5, c5, mA, cA, c.trL b) = true →
      c.Acc (sumStm S t₀ (rowsX S t₀ (st4 S d1 d2 d3 d4 d5 y c1 m2 c2 m3 c4 c5).1).1
          (rowsX S t₀ (st4 S d1 d2 d3 d4 d5 y c1 m2 c2 m3 c4 c5).1).2 (drawnE dA cA))
        (wordIn (S.sg t₀) (col1 S d2 m2.1)) (wordFr (S.sg t₀) (col1 S d2 m2.1))
        (wordIn (S.sg t₀) (col1 S d2 m2.1)) b) :
    Closes S d1 d2 d3 d4 d5 (dA :: c'.rds) xs dec (batErr S 1 dA, c'.errL) := by
  have hsz0 : (S.sg t₀).Sized := hs ▸ hsz
  have h20 : 2 * c'.rad < (S.sg t₀).d := hs ▸ h2
  exact closes_many_at d1 d2 d3 d4 d5 dA xs dec s1 hs c c' hcc _ (rowsX S t₀)
    (fun o => wordIn (S.sg t₀) (col1 S d2 o)) (fun o => wordFr (S.sg t₀) (col1 S d2 o))
    (fun o => wordIn (S.sg t₀) (col1 S d2 o))
    (batSem_of S t₀ c'.rad _ 1 (batOK_of S t₀ c'.rad hsz0 hf hh hl he (by omega)).toSemOK
      (Sg.list_cIn hsz0 h20) d2 dA hd.rA)
    hc (isRows_rowsX S t₀ hl) (stdReads_word S t₀ s1 s1 d2 d2 d2 d2 d2 hW hN) hsem

end OnBytes.Slice
