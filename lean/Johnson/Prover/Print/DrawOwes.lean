-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Print/DrawOwes.lean: WHAT THE PRINTER ASKS OF THE PROVER's DRAW FOR A REQUEST (Draw,
Johnson/Prover/All/Defs.lean), AS ONE RECORD; AND A WRITTEN DRAW THAT MEETS IT BY MAKE, AT EVERY RAW
VALUE. For all data.

Main names.
  DrawNums     public numbers: the bytes of a leaf's own salt; the three binding shapes; the numbers
    of the joining round and of the seam of the two whole files; the entry file's number of rounds.
  Runs4, Runs4.Fit   (run2, run3) of the key file's byte coins and of the proof file's; each of the
    four has 32 bytes and passes the format's test runOk.
  DrawOwes N c runs bcT bcL bcB d   the three coins of d are coinsOf of the three byte coins ·
    CoinsPrint of the two whole files' · the entry's lengths · d.n < 2^64 · each of the copy's
    leaves' salts is leafSalt c o with N.salt bytes o · runs d.κ are the byte coins' four values.
  DrawRaw, drawAt mk N c x   what a draw is made of; THE WRITTEN DRAW: the byte coins in their tidy
    form (OnBytes/Prover/Print/Tidy.lean), the number modulo 2^64, the salts laid as leafSalt c of
    fitBytes; its κ := mk κ₀ (the four run values): mk is a letter: how the strategies' coins hold
    them.
  drawOwes_drawAt   N.salt ≤ 64 · runs (mk k r) = r at all k and at the r WITH Runs4.Fit (a finite
    set: so it can be met where Kap is finite) → DrawOwes N c runs … (drawAt mk N c x): AT EVERY x
    AND c.
  length_salts      under DrawOwes, at c of 32 bytes: each salt has 256 + 8 * N.salt bits.

NOT IN THE RECORD: what is not the draw's: the tables' words, caps, depths, widths; that the entry's
binding shape has depth 0 (a clause on N).

drawAt IS NOT ONE TO ONE: several raw values give one draw.

Limits. Definitions, lengths and equations. Nothing on how any program draws the raw value, and
nothing is said of its distribution. That a strategy sends the values that its κ holds is not said
here. Nothing on soundness or completeness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.All.Defs
import OnBytes.Prover.Print.Tidy
import OnBytes.Maker.TablesBack

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Prover.Print

open _root_.Run (leafSalt)
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open OnBytes.Prover OnBytes.Prover.Print

/-- Public numbers. -/
structure DrawNums where
  salt : ℕ
  sT : OnBytes.Params.LinBindingShape
  sL : OnBytes.Params.LinBindingShape
  sB : OnBytes.Params.LinBindingShape
  nJT : ℕ
  n3T : ℕ
  nL : ℕ
  nJB : ℕ
  n3B : ℕ

/-- (run2, run3) of the key file's byte coins, and of the proof file's. -/
abbrev Runs4 : Type := (ByteArray × ByteArray) × (ByteArray × ByteArray)

/-- Each of the four has 32 bytes and passes the format's test runOk. -/
structure Runs4.Fit (r : Runs4) : Prop where
  sizeT2 : r.1.1.size = 32
  sizeT3 : r.1.2.size = 32
  sizeB2 : r.2.1.size = 32
  sizeB3 : r.2.2.size = 32
  okT2 : _root_.Fmt.runOk r.1.1 = true
  okT3 : _root_.Fmt.runOk r.1.2 = true
  okB2 : _root_.Fmt.runOk r.2.1 = true
  okB3 : _root_.Fmt.runOk r.2.2 = true

variable {I X : Type} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape} {aL : RoundSplits L.link.shape}

/-- **What the printer asks of a draw.** -/
structure DrawOwes {Kap : Type} (N : DrawNums) (c : ByteArray) (runs : Kap → Runs4)
    (bcT bcL bcB : ByteCoins (typedOracleCarrier L Bd aT aL)) (d : Draw 256 L Bd aT aL Kap) : Prop where
  formT : d.coT = coinsOf N.nJT N.n3T N.sT.logLeaves bcT
  formL : d.coL = coinsOf N.nL N.nL N.sL.logLeaves bcL
  formB : d.coB = coinsOf N.nJB N.n3B N.sB.logLeaves bcB
  coT : CoinsPrint bcT N.salt N.sT
  coB : CoinsPrint bcB N.salt N.sB
  coL : bcL.Fit N.salt N.sL
  number : d.n < 2 ^ 64
  salts : ∀ j, ∃ o : ByteArray, o.size = N.salt ∧ d.s j = leafSalt c o
  same : runs d.κ = ((bcT.run2, bcT.run3), (bcB.run2, bcB.run3))

/-- What a draw is made of. -/
structure DrawRaw (L : HolographicProtocol I X) (Bd : Type) (aT : RoundSplits L.offline.shape) (aL : RoundSplits L.link.shape)
    (Kap₀ : Type) where
  r : L.EncodingRandomness
  own : ℕ → ByteArray
  n : ℕ
  κ₀ : Kap₀
  bT : ByteCoins (typedOracleCarrier L Bd aT aL)
  bL : ByteCoins (typedOracleCarrier L Bd aT aL)
  bB : ByteCoins (typedOracleCarrier L Bd aT aL)

/-- **The written draw.** -/
def drawAt {Kap₀ Kap : Type} (mk : Kap₀ → Runs4 → Kap) (N : DrawNums) (c : ByteArray)
    (x : DrawRaw L Bd aT aL Kap₀) : Draw 256 L Bd aT aL Kap where
  r := x.r
  s := fun j => leafSalt c (fitBytes N.salt (x.own j))
  n := x.n % 2 ^ 64
  κ := mk x.κ₀ (((x.bT.tidy N.salt N.sT).run2, (x.bT.tidy N.salt N.sT).run3),
    ((x.bB.tidy N.salt N.sB).run2, (x.bB.tidy N.salt N.sB).run3))
  coT := coinsOf N.nJT N.n3T N.sT.logLeaves (x.bT.tidy N.salt N.sT)
  coL := coinsOf N.nL N.nL N.sL.logLeaves (x.bL.tidy N.salt N.sL)
  coB := coinsOf N.nJB N.n3B N.sB.logLeaves (x.bB.tidy N.salt N.sB)

/-- **THE WRITTEN DRAW MEETS THE RECORD, AT EVERY RAW VALUE.** -/
theorem drawOwes_drawAt {Kap₀ Kap : Type} (mk : Kap₀ → Runs4 → Kap) (runs : Kap → Runs4)
    (hmk : ∀ k r, Runs4.Fit r → runs (mk k r) = r) (N : DrawNums) (c : ByteArray)
    (x : DrawRaw L Bd aT aL Kap₀) (h : N.salt ≤ 64) :
    DrawOwes N c runs (x.bT.tidy N.salt N.sT) (x.bL.tidy N.salt N.sL) (x.bB.tidy N.salt N.sB)
      (drawAt mk N c x) where
  formT := rfl
  formL := rfl
  formB := rfl
  coT := coinsPrint_tidy _ _ _ h
  coB := coinsPrint_tidy _ _ _ h
  coL := (coinsPrint_tidy _ _ _ h).fit
  number := Nat.mod_lt _ (Nat.two_pow_pos 64)
  salts := fun _ => ⟨_, size_fitBytes _ _, rfl⟩
  same := hmk _ _
    ⟨(coinsPrint_tidy N.salt N.sT x.bT h).fit.run2, (coinsPrint_tidy N.salt N.sT x.bT h).fit.run3,
      (coinsPrint_tidy N.salt N.sB x.bB h).fit.run2, (coinsPrint_tidy N.salt N.sB x.bB h).fit.run3,
      (coinsPrint_tidy N.salt N.sT x.bT h).ok2, (coinsPrint_tidy N.salt N.sT x.bT h).ok3,
      (coinsPrint_tidy N.salt N.sB x.bB h).ok2, (coinsPrint_tidy N.salt N.sB x.bB h).ok3⟩

/-- The salts' lengths. -/
theorem DrawOwes.length_salts {Kap : Type} {N : DrawNums} {c : ByteArray} {runs : Kap → Runs4}
    {bcT bcL bcB : ByteCoins (typedOracleCarrier L Bd aT aL)} {d : Draw 256 L Bd aT aL Kap}
    (h : DrawOwes N c runs bcT bcL bcB d) (hc : c.size = 32) (j : ℕ) :
    (d.s j).length = 256 + 8 * N.salt := by
  obtain ⟨o, ho, e⟩ := h.salts j
  rw [e, OnBytes.Maker.length_leafSalt, hc, ho]

end Johnson.Prover.Print

#print axioms Johnson.Prover.Print.DrawNums
#print axioms Johnson.Prover.Print.Runs4.Fit
#print axioms Johnson.Prover.Print.DrawOwes
#print axioms Johnson.Prover.Print.DrawRaw
#print axioms Johnson.Prover.Print.drawAt
#print axioms Johnson.Prover.Print.drawOwes_drawAt
#print axioms Johnson.Prover.Print.DrawOwes.length_salts
