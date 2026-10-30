-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/ScriptLotsPads.lean: beside ScriptLots.lean: THE SECOND TENANT's
PADS, AND THE LISTS' PUBLIC FACES. Four definitions, six theorems.

Why. The frame's authors' join of all senders' lots (Honest/Thread/Join.lean)
has a test that asks of every seat a lot for its message and one for
its pad; `testPadLots` has one a switch, at the first tenant alone.

  `freshAt`   what rides in switch τ's tree beside the next stage's message: the next fold's fresh
                 table; at the last switch the masking word's mask row. Of the part's own coins
                 alone, by reading: no theorem here says so
  `testPadTxtB`, `testPadLotsB`, `testPl`   the second tenant's pad: at the library's `padB`'s place
                 in a mask row that tenant's own entry; one lot a switch; both tenants' lots in one
                 list
  `freshAt_psAt`   the pad's text reads the very table of which the message's text is made
  `packedN_beyond`   beyond its used places the library's packing is 0
  `nums_testMsgLots`, `seats_testPl`, `testPl_length`   the lists' public faces: the messages'
                 numbers, the pads' seats; the count
  `padPlace_beyond_LFull`   at the written record's first four switches the number Z.l - 1 lies
                 beyond the packing's used places

After which convention. The shared sending's (Honest/K1/ScriptAt.lean): at `padB`'s places the same
rows at no data. The second tenant's rows hold no data: so its pad's text is the message's own entry
there.

Limits.
- What ScriptLots.lean's head says a law over coins has to mind holds here; its first limit too: for
  a job whose first fresh table came earlier alone.
- `runs_L_at_laid` (AtFullSide/K12/RunsAtLaidL.lean): the book's fact that lends the carried runs
  (what the two parts spend; of what they carry, how many runs and the last one or two): by the
  book, in scope, at the full size. It is not imported here and occurs in no statement here.
- WHAT THE PAD's TEXT HOLDS. With a mask row `padB` names the last place of the last mask row. At a
  switch that is not the last the table there is the packing: where that place lies beyond the used
  places the entry is 0 by the format: no coin stands there, and the text answers that 0. At the
  last switch it is one coin of the own cut. THE TWO HALVES ARE NOT JOINED HERE: `packedN_beyond` is
  on the packing, `padPlace_beyond_LFull` on numbers of the record; that `padB`'s place at sh₁ is (2
  ^ h - 1, Z.l - 1) hangs on the letters codes and sh₁; no statement says that the text answers 0.
- sh₁ is a letter: at a shape that is not the tenant's, `padB`'s place may lie beyond the message's
  fences: there the message's text is mute and the pad's is not, and at the last switch it would
  read a coin of a tail.
- In the written record these tenants are not sampled: said here without a theorem; of the last
  switch's masking word nothing is said. Whether any law reads their pads is not known here.
- No control stands beside the six.
- It moves no count. Nothing on completeness, soundness or hiding.
Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.ScriptLotsAtL
import Johnson.Prover.Link.BodyPack

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace ProofFile.Honest.K12
open OnBytes OnBytes.Slice Cb
open VerifiableInference.Desc (padB)
open Johnson.Prover.Link
open H2K.Pub (sgOf)
open ProofFile.Honest.FirstThread (TreeLot MsgLot PadLot)

variable {Bk : ProverCoinCounts} {W X : Type}

/-- **What rides in switch τ's tree beside the next stage's message**: the next fold's fresh table;
at the last switch the masking word's mask row. No input and no challenge is among its arguments. Of
the part's own coins alone, by reading (its term is handed `C.hide` too): none of this is a theorem
here. -/
def freshAt (stages : List Fmt.M1.Stage) (C : TestCoins) (τ : ℕ) : ℕ → ℕ → GE :=
  if τ + 2 == stages.length then ((coinsOf stages C.hide C.rest).new τ).fM
  else packedN (sgOf (stages.getD (τ + 1) default))
    ((coinsOf stages C.hide C.rest).W (sgOf (stages.getD (τ + 1) default)) (τ + 1))

/-- **The pad of the second tenant**: at the library's `padB`'s place in a mask row: that tenant's
own entry there. sh₁ τ: the tenant's shape, a letter. -/
def testPadTxtB (ch : ℕ) (J : TestJob W X) (codes : OnBytes.Codes) (sh₁ : ℕ → OnBytes.OracleShape)
    (τ : ℕ) :
    Coins Bk → Bool → ℕ → ℕ → Option GE :=
  fun k mask b q =>
    if mask && padB codes (sh₁ τ) mask b q then
      (handedRest ch J k).map fun c => freshAt J.p.nums.stages (restCoins J c) τ b q
    else none

/-- The second tenants' lots of pads: one a switch. -/
def testPadLotsB (ch : ℕ) (J : TestJob W X) (codes : OnBytes.Codes) (sh₁ : ℕ → OnBytes.OracleShape)
    (t₀ : ℕ) :
    List (PadLot Bk W) :=
  (List.range (J.p.nums.stages.length - 1)).map fun τ => ⟨t₀ + τ, 1, fun k _ => testPadTxtB ch J
    codes sh₁ τ k⟩

/-- **pl**: both tenants' lots of pads. -/
def testPl (ch : ℕ) (J : TestJob W X) (codes : OnBytes.Codes) (sh sh₁ : ℕ → OnBytes.OracleShape)
    (t₀ : ℕ) :
    List (PadLot Bk W) :=
  testPadLots ch J codes sh t₀ ++ testPadLotsB ch J codes sh₁ t₀

/-- **The pad's text reads the very table of which the message's text is made.** -/
theorem freshAt_psAt (J : TestJob W X) (w : W) (fr : Front X) (C : TestCoins) (D : ℕ → Fmt.Drawn)
    (τ : ℕ) :
    (psAt J w fr C D (τ + 1)).fM = freshAt J.p.nums.stages C τ := by
  cases h : (τ + 2 == J.p.nums.stages.length) <;>
    simp [psAt, aNext, nextPS, freshAt, h]

/-- **Beyond its used places the library's packing is 0.** -/
theorem packedN_beyond (s : Sg) (Wc : HIdx (sVars GE 2 (s.h + s.g)) → GE) (b j : ℕ)
    (hj : s.h + 2 * s.g + 1 ≤ j) :
    packedN s Wc b j = 0 := by
  unfold packedN
  split
  · rename_i h
    unfold packed pkAt placeV
    refine Finset.sum_eq_zero fun c _ => if_neg fun e => ?_
    have h1 : hidePlace s.h s.g c = j := congrArg Fin.val e
    have h2 := hidePlace_lt s.h s.g c
    omega
  · rfl

/-- The public face of ml: the numbers. -/
theorem nums_testMsgLots (ch : ℕ) (J : TestJob W X) (own₀ : X) (n₀ t₀ : ℕ) (arr : ℕ → ℕ → ℕ)
    (ok : W → List Fmt.Drawn → (ℕ → Stretch) → Bool) :
    (testMsgLots (Bk := Bk) ch J own₀ n₀ t₀ arr ok).map (·.n) =
      (List.range (J.p.nums.stages.length - 1)).flatMap fun τ =>
        [arr (t₀ + τ) 0, arr (t₀ + τ) 1] := by
  simp [testMsgLots, List.map_flatMap]

/-- The public face of pl: the seats. -/
theorem seats_testPl (ch : ℕ) (J : TestJob W X) (codes : OnBytes.Codes)
    (sh sh₁ : ℕ → OnBytes.OracleShape) (t₀ : ℕ) :
    (testPl (Bk := Bk) ch J codes sh sh₁ t₀).map (fun L => (L.j, L.t)) =
      (List.range (J.p.nums.stages.length - 1)).map (fun τ => (t₀ + τ, 0)) ++
        (List.range (J.p.nums.stages.length - 1)).map fun τ => (t₀ + τ, 1) := by
  simp [testPl, testPadLots, testPadLotsB, Function.comp_def]

/-- Two lots of pads a switch. -/
theorem testPl_length (ch : ℕ) (J : TestJob W X) (codes : OnBytes.Codes)
    (sh sh₁ : ℕ → OnBytes.OracleShape) (t₀ : ℕ) :
    (testPl (Bk := Bk) ch J codes sh sh₁ t₀).length = 2 * (J.p.nums.stages.length - 1) := by
  unfold testPl testPadLotsB
  rw [List.length_append, testPadLots_length, List.length_map, List.length_range]
  omega

/-- At the written record's first four switches the number Z.l - 1 lies beyond the packing's used
places. On the stages' numbers alone: no `padB`, no codes, no shape stands in it. -/
theorem padPlace_beyond_LFull :
    ∀ τ < 4, (sgOf (H2K.Member.piLFull.nums.stages.getD (τ + 1) default)).h +
      2 * (sgOf (H2K.Member.piLFull.nums.stages.getD (τ + 1) default)).g + 1 ≤
        (H2K.Member.piLFull.nums.stages.getD (τ + 1) default).Z.l - 1 := by
  decide +kernel

end ProofFile.Honest.K12

end

#print axioms ProofFile.Honest.K12.freshAt
#print axioms ProofFile.Honest.K12.testPadTxtB
#print axioms ProofFile.Honest.K12.testPadLotsB
#print axioms ProofFile.Honest.K12.testPl
#print axioms ProofFile.Honest.K12.freshAt_psAt
#print axioms ProofFile.Honest.K12.packedN_beyond
#print axioms ProofFile.Honest.K12.nums_testMsgLots
#print axioms ProofFile.Honest.K12.seats_testPl
#print axioms ProofFile.Honest.K12.testPl_length
#print axioms ProofFile.Honest.K12.padPlace_beyond_LFull
