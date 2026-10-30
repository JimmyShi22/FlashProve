-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Slice/SeedsBridge.lean: the one probability that OnBytes/TypedOracleCompiler/Slice/Plain3XSeeds.lean
asks for its second lane is bounded, at the record's own terms, by a term that is not evaluated;
`x3_judge_seeds` is stated with that hypothesis gone; the two typed queries of the seeds' protocol
are written as the strings of the table's name and of the seeds' round; and under a law on a page
the seed of the typed chain is the seed under the oracle.

`x3_judge_seeds` asks: for every string y and every first message, the probability over a uniform
verifier's message of the drawing round that `badS y` is true of the value drawn is at most εs. The
kit of verifier's messages is a variable there, and of a variable kit's record of draws nothing can
be said. Here the kit is the library's "challenges as hash blocks" (`ckP .two`, Run/PlanPull.lean);
the value is `seedOfDrawn lg s` of the record (OnBytes/Slice/SeedDrawn.lean); the test is
`DecR.badK` and the language `DecR.LgK` (OnBytes/Slice/DecoderRecTyped.lean) at `decRec T v eM lg
s`. The bound is that of `collRaw_pr` (OnBytes/Slice/SeedBias.lean): the count of seeds WITH the
factor for the draw's bias.

Main definitions.
 `atBlocks G`           the stretches G with the kit `ckP .two`.
 `fbAt m g tg q`        the answer of the chain oracle at a query, in the family read out of g
                        through m.
 `SeedsPage m tg name q₀ q₁`   A LAW ON AN IMPLEMENTATION: the first query's tail is g's answer at
                        the string of the name; block i of the drawing round's answer is g's answer
                        at the string of block i + 1 of the seeds' round.
Main theorems.
 `hpr_record`           THE PROBABILITY, in the letters of `x3_judge_seeds`, for a kit C with C =
                        `ckP .two`.
 `x3_judge_record`      `x3_judge_seeds` with that hypothesis gone.
 `x3_judge_record_chalP`   the same at `atBlocks G`, the library's wire `chalP .two K` and the entry
                        `seedEntry lg s`: three hypotheses more are gone.
 `firstPN_seedFirst`, `nameOf_tableName`, `firstPN_key`   what the first code of
                        OnBytes/TypedOracleCompiler/Run/FirstName.lean writes at the first query with one outer root
                        is the bits of `seedFirst` (OnBytes/Slice/SeedAsked.lean) of the table's
                        name at that root; of THE KEY'S name, at a key with that root.
 `secondPS_blockStr`    what the second code (OnBytes/TypedOracleCompiler/Run/SeedRound.lean) writes at the drawing
                        round's query is the bits of `blockStr` (OnBytes/Slice/SeedRow.lean) at the
                        chain value and the block's number in the format's row.
 `seedUnder_of_page`    UNDER `SeedsPage` THE SEED OF THE TYPED CHAIN IS THE SEED UNDER THE ORACLE
                        (`seedUnder`, OnBytes/Slice/SeedWhich.lean).

Asked by `x3_judge_record`: a way to decide whether two seeds are equal (an instance; any serves);
the kit is `ckP .two`; the six conditions of `collRaw_pr` (the radius within the Johnson bound among
them); the entry's round draws `roundDraws lg s`; the bound is at most εs; AND STILL: for each
record x the protocol `Plain3 G (dec x)` is round-by-round sound for `LgK` at x, with counts at most
εs; no tree is deeper than 63; the wiring is lawful; the drawing round's verifier's messages are
exactly uniform under `chal`. `x3_judge_record_chalP` asks 0 < s and that K is at least the number
of blocks in the place of the second, the fourth and the last.

Not claimed. NO SOUNDNESS IS PROVED: it is a hypothesis, and nobody has met it. NO IMPLEMENTATION IS
SHOWN TO OBEY `SeedsPage`: no page with the seeds' tag is written. `seedUnder_of_page` speaks of
what the wire and the kit make of two typed answers; that the judge's run of the typed chain
computes that value: `x3_run_seed` (OnBytes/TypedOracleCompiler/Slice/SeedsBridgeRun.lean), under the same law on a
page. That the depth of the stretches' stored table is the code's: at another length `badK` is false
everywhere and `LgK` holds of nothing (`DecR.badK_of_len`, `DecR.not_lgK_of_len`). That the judge
ever says yes. One εs stands above both lanes' errors, and where `JudgeAtAsk` is used the count is
multiplied. No number is evaluated. Nothing on proof of work. What the heads of Plain3XSeeds.lean,
SeedDrawn.lean and DecoderRecTyped.lean do not claim. The compiler under OnBytes/TypedOracleCompiler/ is the one
that `innerCompiledVerifier` is made with; it builds on definitions of Compile/.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Slice.Plain3XSeeds
import OnBytes.TypedOracleCompiler.Run.FirstName
import OnBytes.TypedOracleCompiler.Run.SeedRound
import OnBytes.Slice.SeedDrawn
import OnBytes.Slice.DecoderRecTyped

set_option autoImplicit false

noncomputable section

namespace TypedOracleCompiler.Slice
open Rom Prob _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run (ckP chalP digToBytes bytesToBits bitsToBytes blockNo)
open Cb Cb.Ood
open OnBytes.Slice (DecR decRec recZ seedBS seedOfDrawn roundDraws collRaw_pr_ckP rawOf seedFirst
  GE NZ blockStr seedEntry dsOf_seedEntry chalP_unif_seeds seedUnder seedUnder_of_blocks)
open scoped ENNReal

/-! ## The one probability -/

section
variable (T : _root_.Fmt.M1.Code) (v eM lg s : ℕ)

/-- THE PROBABILITY THAT THE SECOND LANE ASKS, AT THE LIBRARY'S KIT "CHALLENGES AS HASH BLOCKS":
for every typed string y and every first message: over a uniform verifier's message of the seeds'
round, the record does not single one table out of y's list, at the seeds read off the format's
record of what the round draws, with probability at most the bound of `collRaw_pr`. -/
theorem hpr_record (C : PQ.CK) (hC : C = ckP .two) (E : ExtSpec) (ha : T.a ≤ 32)
    (hk : T.r + T.l ≤ 2 ^ T.a) (he : eM < 2 ^ T.a - (T.r + T.l) + 1)
    (hJ : InJohnson (2 ^ T.a) (2 ^ T.a - (T.r + T.l) + 1) eM) (h3 : 3 * s ≤ T.l)
    (hl : T.l - 3 * s ≤ 2 ^ lg) (e : _root_.Fmt.Entry)
    (h : _root_.Fmt.dsOf { e with work := 0 } .seeds = roundDraws lg s) {n : ℕ}
    (y : Fin n → PQ.SgX) (c0 : (PQ.s0 C).up.Chal) :
    pr (unif (PQ.roundS C (dSeed e)).up.Chal)
        {c | DecR.badK (D := decRec T v eM lg s) (Equiv.refl _) id y
          (seedOfDrawn lg s (drawnT C (dSeed e) E (c0, c, ()))) = true} ≤
      kapSl 128 ^ (seedBS lg s).b *
        ((((listMax (2 ^ T.a) (2 ^ T.a - (T.r + T.l) + 1) eM).choose 2 * (recZ T.l lg s).err : ℕ) :
          ℝ≥0∞) / Fintype.card (recZ T.l lg s).D) := by
  subst hC
  have e1 : {c : (PQ.roundS (ckP .two) (dSeed e)).up.Chal |
      DecR.badK (D := decRec T v eM lg s) (Equiv.refl _) id y
        (seedOfDrawn lg s (drawnT (ckP .two) (dSeed e) E (c0, c, ()))) = true} =
      {c | (decRec T v eM lg s).collRaw (rawOf (Equiv.refl _) y)
        (seedOfDrawn lg s [(ckP .two).dr { e with work := 0 } .seeds c])} := by
    ext c
    have hb := DecR.badK_false (D := decRec T v eM lg s) (Equiv.refl _) id y
      (seedOfDrawn lg s [(ckP .two).dr { e with work := 0 } .seeds c])
    constructor
    · intro ht
      by_contra hn
      have hf := hb.2 hn
      have ht' : DecR.badK (D := decRec T v eM lg s) (Equiv.refl _) id y
        (seedOfDrawn lg s [(ckP .two).dr { e with work := 0 } .seeds c]) = true := ht
      rw [hf] at ht'
      cases ht'
    · intro hc
      show DecR.badK (D := decRec T v eM lg s) (Equiv.refl _) id y
        (seedOfDrawn lg s [(ckP .two).dr { e with work := 0 } .seeds c]) = true
      by_contra hn
      exact hb.1 (Bool.not_eq_true _ ▸ hn) hc
  rw [e1]
  exact collRaw_pr_ckP T v eM lg s ha hk he hJ h3 hl { e with work := 0 } h _

end

/-! ## The judge, with that hypothesis gone -/

section
variable {An X : Type} (T : _root_.Fmt.M1.Code) (v eM lg s : ℕ)
  [DecidableEq (Fin s → (Fin lg → GE) × NZ)] (G : Stretches)
  (dec : An × (Fin s → (Fin lg → GE) × NZ) → PQ.View → PQ.View → PQ.View → Bool)
  (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → G.C.Ch e k) (o : G.Ones) (salt : ℕ)
  (d : Fin s → (Fin lg → GE) × NZ)
  (e : _root_.Fmt.Entry) (embE : PQ.SgX → List Bool) (prjE : List Bool → Option PQ.SgX)

/-- `x3_judge_seeds` AT THE RECORD'S OWN TERMS, WITH ITS PROBABILITY SHOWN. The kit is the
library's "challenges as hash blocks"; the seeds are read off the format's record of what the round
draws (`seedOfDrawn`); the language is the key's, record by record, with the way out (`DecR.LgK`);
the second lane's test is `DecR.badK`. What is still asked: see the file's head. -/
theorem x3_judge_record (hC : G.C = ckP .two)
    (an : An → (decRec T v eM lg s).ix.Row × (decRec T v eM lg s).Z.S → GE)
    (A : (decRec T v eM lg s).Claims X) (ha : T.a ≤ 32) (hk : T.r + T.l ≤ 2 ^ T.a)
    (he : eM < 2 ^ T.a - (T.r + T.l) + 1)
    (hJ : InJohnson (2 ^ T.a) (2 ^ T.a - (T.r + T.l) + 1) eM) (h3 : 3 * s ≤ T.l)
    (hl : T.l - 3 * s ≤ 2 ^ lg)
    (hd : _root_.Fmt.dsOf { e with work := 0 } .seeds = roundDraws lg s) (sMT sFS : ℕ)
    (R : Reading (Strings.strung (LX3 G dec (earlyWith d) (TS G e))) embE) (ε : Err G.sh)
    (εs : ℝ≥0∞)
    (hS : ∀ x, (Plain3 G (dec x)).Sound
      (fun _ => DecR.LgK (D := decRec T v eM lg s) (Equiv.refl _) an id A x) ε)
    (hb : Err.Below ε εs) (hs : G.Shallow) (hw : (wq3X G dec K chal o).OKG)
    (hc : (unif (Fin K → Dig 256)).map (chal (dSeed e).entry (dSeed e).kind) =
      unif (G.C.Ch (dSeed e).entry (dSeed e).kind))
    (hε : kapSl 128 ^ (seedBS lg s).b *
      ((((listMax (2 ^ T.a) (2 ^ T.a - (T.r + T.l) + 1) eM).choose 2 * (recZ T.l lg s).err : ℕ) :
        ℝ≥0∞) / Fintype.card (recZ T.l lg s).D) ≤ εs) :
    JudgeAtAsk
      (WXo G dec K chal o salt d (TS G e) embE prjE (wTS G K chal e) (embST G.C e _)
        (prjST G.C e _))
      (judgeOff
        (ZXo G dec K chal o salt d (TS G e) embE prjE (wTS G K chal e) (embST G.C e _)
          (prjST G.C e _))
        (testWritten G dec K chal o salt d (TS G e) embE prjE (wTS G K chal e) (embST G.C e _)
          (prjST G.C e _))
        [] default [] (plainsT G.C (dSeed e) _) (seedOfS G e (seedOfDrawn lg s)) sMT sFS R
        (DecR.LgK (D := decRec T v eM lg s) (Equiv.refl _) an id A)
        (DecR.badK (D := decRec T v eM lg s) (Equiv.refl _) id)) εs
      (preSeed
        (testWritten G dec K chal o salt d (TS G e) embE prjE (wTS G K chal e) (embST G.C e _)
          (prjST G.C e _))
        [] default [] (plainsT G.C (dSeed e) _)
        (ZXo G dec K chal o salt d (TS G e) embE prjE (wTS G K chal e) (embST G.C e _)
          (prjST G.C e _))) :=
  x3_judge_seeds G dec K chal o salt d e embE prjE (seedOfDrawn lg s) sMT sFS R _ _ ε εs hS hb hs
    hw hc fun y c0 =>
      (hpr_record T v eM lg s G.C hC _ ha hk he hJ h3 hl e hd y c0).trans hε

end

/-! ## At the library's kit, wire and an entry: three hypotheses gone -/

/-- The stretches with the library's kit "challenges as hash blocks" in the place of their kit. -/
abbrev atBlocks (G : Stretches) : Stretches := { G with C := ckP .two }

section
variable {An X : Type} (T : _root_.Fmt.M1.Code) (v eM lg s : ℕ)
  [DecidableEq (Fin s → (Fin lg → GE) × NZ)] (G : Stretches)
  (dec : An × (Fin s → (Fin lg → GE) × NZ) → PQ.View → PQ.View → PQ.View → Bool)
  (K : ℕ) (o : (atBlocks G).Ones) (salt : ℕ) (d : Fin s → (Fin lg → GE) × NZ)
  (embE : PQ.SgX → List Bool) (prjE : List Bool → Option PQ.SgX)

/-- `x3_judge_record` AT THE LIBRARY'S KIT `ckP .two`, ITS WIRE `chalP .two K` AND THE ENTRY
`seedEntry lg s`: that the kit is that kit, that the round draws the seeds, and that the round's
verifier's messages are exactly uniform are no hypotheses. Asked in their place: 0 < s, and
K is at least the number of blocks of the seeds' sampler. -/
theorem x3_judge_record_chalP (hs0 : 0 < s) (hK : (seedBS lg s).b ≤ K)
    (an : An → (decRec T v eM lg s).ix.Row × (decRec T v eM lg s).Z.S → GE)
    (A : (decRec T v eM lg s).Claims X) (ha : T.a ≤ 32) (hk : T.r + T.l ≤ 2 ^ T.a)
    (he : eM < 2 ^ T.a - (T.r + T.l) + 1)
    (hJ : InJohnson (2 ^ T.a) (2 ^ T.a - (T.r + T.l) + 1) eM) (h3 : 3 * s ≤ T.l)
    (hl : T.l - 3 * s ≤ 2 ^ lg) (sMT sFS : ℕ)
    (R : Reading (Strings.strung (LX3 (atBlocks G) dec (earlyWith d)
      (TS (atBlocks G) (seedEntry lg s)))) embE) (ε : Err (atBlocks G).sh) (εs : ℝ≥0∞)
    (hS : ∀ x, (Plain3 (atBlocks G) (dec x)).Sound
      (fun _ => DecR.LgK (D := decRec T v eM lg s) (Equiv.refl _) an id A x) ε)
    (hb : Err.Below ε εs) (hs : (atBlocks G).Shallow)
    (hw : (wq3X (atBlocks G) dec K (chalP .two K) o).OKG)
    (hε : kapSl 128 ^ (seedBS lg s).b *
      ((((listMax (2 ^ T.a) (2 ^ T.a - (T.r + T.l) + 1) eM).choose 2 * (recZ T.l lg s).err : ℕ) :
        ℝ≥0∞) / Fintype.card (recZ T.l lg s).D) ≤ εs) :
    JudgeAtAsk
      (WXo (atBlocks G) dec K (chalP .two K) o salt d (TS (atBlocks G) (seedEntry lg s)) embE prjE
        (wTS (atBlocks G) K (chalP .two K) (seedEntry lg s)) (embST (ckP .two) (seedEntry lg s) _)
        (prjST (ckP .two) (seedEntry lg s) _))
      (judgeOff
        (ZXo (atBlocks G) dec K (chalP .two K) o salt d (TS (atBlocks G) (seedEntry lg s)) embE
          prjE (wTS (atBlocks G) K (chalP .two K) (seedEntry lg s))
          (embST (ckP .two) (seedEntry lg s) _) (prjST (ckP .two) (seedEntry lg s) _))
        (testWritten (atBlocks G) dec K (chalP .two K) o salt d
          (TS (atBlocks G) (seedEntry lg s)) embE prjE
          (wTS (atBlocks G) K (chalP .two K) (seedEntry lg s))
          (embST (ckP .two) (seedEntry lg s) _) (prjST (ckP .two) (seedEntry lg s) _))
        [] default [] (plainsT (ckP .two) (dSeed (seedEntry lg s)) _)
        (seedOfS (atBlocks G) (seedEntry lg s) (seedOfDrawn lg s)) sMT sFS R
        (DecR.LgK (D := decRec T v eM lg s) (Equiv.refl _) an id A)
        (DecR.badK (D := decRec T v eM lg s) (Equiv.refl _) id)) εs
      (preSeed
        (testWritten (atBlocks G) dec K (chalP .two K) o salt d
          (TS (atBlocks G) (seedEntry lg s)) embE prjE
          (wTS (atBlocks G) K (chalP .two K) (seedEntry lg s))
          (embST (ckP .two) (seedEntry lg s) _) (prjST (ckP .two) (seedEntry lg s) _))
        [] default [] (plainsT (ckP .two) (dSeed (seedEntry lg s)) _)
        (ZXo (atBlocks G) dec K (chalP .two K) o salt d (TS (atBlocks G) (seedEntry lg s)) embE
          prjE (wTS (atBlocks G) K (chalP .two K) (seedEntry lg s))
          (embST (ckP .two) (seedEntry lg s) _) (prjST (ckP .two) (seedEntry lg s) _))) :=
  x3_judge_record T v eM lg s (atBlocks G) dec K (chalP .two K) o salt d (seedEntry lg s) embE prjE
    rfl an A ha hk he hJ h3 hl (dsOf_seedEntry lg s hs0) sMT sFS R ε εs hS hb hs hw
    (chalP_unif_seeds lg s K (seedEntry lg s) (dsOf_seedEntry lg s hs0) hK) hε

end

/-! ## The typed first query's string is the string of the table's name -/

section
variable {I X : Type} (L : BatchProtocolWithLeafBody I X) (t : Tag) (p0 : PlainPart (shapeOf L t) (annOf L t))
  (isP0 : PlainPart (shapeOf L t) (annOf L t) → Bool) (pd : Dig 256)
  (hp : ∀ p, isP0 p = true ↔ p = p0)

/-- What the first code of the seeds' protocol writes at the first query with the one outer root
cm is the bits of `seedFirst` of the table's name at that root. -/
theorem firstPN_seedFirst (cm : Dig 256) (cfg : ByteArray)
    (a message tail logRows answers saltBytes : ℕ)
    (hz : digToBytes pd = _root_.Fmt.zero32) (hc : cfg.size < 2 ^ 31) :
    (FirstName.firstPN (FirstName.restOf cfg a message tail logRows answers saltBytes) L t p0 isP0
        pd hp _root_.Fmt.recordLabel).put ⟨0, .f1 [cm] none [], [], p0⟩ =
      some (bytesToBits (seedFirst
        (_root_.Fmt.tableName (digToBytes cm) cfg a message tail logRows answers saltBytes))) :=
  FirstName.firstPN_name L t p0 isP0 pd hp cm cfg a message tail logRows answers saltBytes hz hc

/-- The name of a key's table is the format's name at the key's root, its configuration digest and
the six numbers of its shape. -/
theorem nameOf_tableName (k : OnBytes.Tie.IdKey) :
    OnBytes.Key.nameOf k.1 k.2.1 k.2.2 =
      _root_.Fmt.tableName k.2.2.root k.2.1 k.1.code.logN k.1.code.ell k.1.code.r k.1.v k.1.answers
        k.1.saltBytes := rfl

/-- So at a key whose root is the bytes of cm it is the bits of `seedFirst` of THE KEY'S name.
-/
theorem firstPN_key (cm : Dig 256) (k : OnBytes.Tie.IdKey) (hr : k.2.2.root = digToBytes cm)
    (hz : digToBytes pd = _root_.Fmt.zero32) (hc : k.2.1.size < 2 ^ 31) :
    (FirstName.firstPN (FirstName.restOf k.2.1 k.1.code.logN k.1.code.ell k.1.code.r k.1.v
        k.1.answers k.1.saltBytes) L t p0 isP0 pd hp _root_.Fmt.recordLabel).put
        ⟨0, .f1 [cm] none [], [], p0⟩ =
      some (bytesToBits (seedFirst (OnBytes.Key.nameOf k.1 k.2.1 k.2.2))) := by
  rw [nameOf_tableName, hr]
  exact firstPN_seedFirst L t p0 isP0 pd hp cm _ _ _ _ _ _ _ hz hc

end

/-! ## The typed drawing round's strings are the strings of the seeds' round -/

section
variable {I X : Type} (L : BatchProtocolWithLeafBody I X) (tg : Tag) (p1 : PlainPart (shapeOf L tg) (annOf L tg))
  (isP1 : PlainPart (shapeOf L tg) (annOf L tg) → Bool) (hp : ∀ p, isP1 p = true ↔ p = p1)

/-- What the second code of the seeds' protocol writes at the drawing round's query with the chain
value ρ, for the typed block j, is the bits of `blockStr` at the start ρ and the block's number in
the format's row. The typed block K is block 0, the typed block k below K is block k + 1
(`SeedRound.blockNo_last`, `SeedRound.blockNo_cast`). -/
theorem secondPS_blockStr (K : ℕ) (hK : K < 2 ^ 48) (ρ : List Bool) (hρ : ρ.length = 256)
    (j : Fin (K + 1)) :
    (SeedRound.secondPS L tg p1 isP1 hp K).put (⟨1, .f2 none ρ, [], p1⟩, j) =
      some (bytesToBits (blockStr (bitsToBytes ρ) (blockNo 0 K j))) :=
  SeedRound.secondPS_put L tg p1 isP1 hp K hK ρ hρ j

end

/-! ## The seed of the typed chain is the seed under the oracle, under a law on a page -/

section
variable {I X : Type} {L : BatchProtocolWithLeafBody I X} {K : ℕ}

/-- The answer of the chain oracle of the tag tg at the query q, in the family that is read out of
the oracle g through the implementation m: K blocks and a tail. -/
def fbAt (m : OracleCoding (typedOracleFamily 256 K L) 256) (g : Fam (rom 256)) (tg : Tag) (q : FbIn 256 L tg) :
    Batch.FsAns 256 K := readBlocks m g (OracleName.fb tg) q

/-- A law on an implementation, at the seeds' tag and a table's name: in the family that is read
out of an oracle g, the tail of the answer at the first query q₀ is g's answer at the string of the
name, and block i of the answer at the drawing round's query behind a chain value ρ is g's answer at
the string of block i + 1 of the seeds' round at the start ρ. NO IMPLEMENTATION IS SHOWN TO OBEY IT.
An implementation that makes an answer block by block of g's answers at its codes obeys it if its
codes there are `FirstName.firstPN`'s and `SeedRound.secondPS`'s (`firstPN_key`,
`secondPS_blockStr`): by reading. -/
structure SeedsPage (m : OracleCoding (typedOracleFamily 256 K L) 256) (tg : Tag) (name : ByteArray)
    (q₀ : FbIn 256 L tg) (q₁ : Bits → FbIn 256 L tg) : Prop where
  /-- the first query's tail -/
  first : ∀ g : Fam (rom 256), (fbAt m g tg q₀).2 = g () (bytesToBits (seedFirst name))
  /-- the drawing round's blocks -/
  round : ∀ (g : Fam (rom 256)) (ρ : Dig 256) (i : Fin K),
    (fbAt m g tg (q₁ (List.ofFn ρ))).1 i =
      g () (bytesToBits (blockStr (digToBytes ρ) (i.val + 1)))

/-- UNDER THAT LAW THE SEED OF THE TYPED CHAIN IS THE SEED UNDER THE ORACLE: the seeds off the
record of what the library's wire and kit make of the typed answer at the drawing round's query,
behind the link of the typed answer at the first query, in the family read out of g, are the seed of
the key's table under g. -/
theorem seedUnder_of_page (m : OracleCoding (typedOracleFamily 256 K L) 256) (tg : Tag) (k : OnBytes.Tie.IdKey)
    (q₀ : FbIn 256 L tg) (q₁ : Bits → FbIn 256 L tg)
    (hm : SeedsPage m tg (OnBytes.Key.nameOf k.1 k.2.1 k.2.2) q₀ q₁) (lg s : ℕ)
    (e : _root_.Fmt.Entry) (h : _root_.Fmt.dsOf e .seeds = roundDraws lg s)
    (hK : (seedBS lg s).b ≤ K) (g : Fam (rom 256)) :
    seedUnder lg s k g =
      some (seedOfDrawn lg s [(ckP .two).dr e .seeds (chalP .two K e .seeds
        (fbAt m g tg (q₁ (Batch.link (fbAt m g tg q₀)))).1)]) :=
  seedUnder_of_blocks lg s K e h hK k g _ fun i =>
    (hm.round g (fbAt m g tg q₀).2 i).trans (by
      rw [hm.first g]
      rfl)

end

end TypedOracleCompiler.Slice
