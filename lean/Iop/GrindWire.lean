-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Iop/GrindWire.lean: the wire records of an `BatchProtocol` with proof-of-work bits (`BatchProtocol.grind`,
Iop/BatchGrind.lean), built from the wire records of the `BatchProtocol` without them. An `BatchProtocol`
(Iop/Batch.lean), below called a record of protocols, holds an encoder, a decoder and the protocols
Test, Link and Batch; what a wire record is, the next paragraph tells. Data, and the conditions on
them. (Words of this library: lean/GLOSSARY.md.)

A wire record (`QueryLayout`, Iop/BatchWire.lean) holds what the compiler needs beside a record of
protocols in order to write down the compiled verifier; the compiled prover needs `WireBP`
(Iop/BatchWireP.lean) besides. For each round, among other things: how K hash blocks of λ bits
(below: blocks) give the challenge (condition: uniform blocks give a uniform challenge).
For a round with proof-of-work bits it also has a record (`GrW`) that tells the honest prover's
search for a nonce where these bits are, how a number is encoded as a nonce, and how many nonces it
may try.
`BatchProtocol.grind` (Iop/BatchGrind.lean) comes after challenges have been derived from blocks. So the new
wire record is built from any wire record of the old record of protocols:
  K + 1 blocks in the place of K.
  A round with b ≥ 1 such bits:  block 0 gives them (its first b bits: `testBits`; the others are
                                 discarded), blocks 1, .., K give the old challenge as blocks 0, ..,
                                 K − 1 did. So whether an attempt succeeds is seen from the first
                                 block only (of the blocks as `chalGrind` takes them: in its case
                                 `b + 1` the bits are `testBits lam (b + 1) (u 0)`; where these
                                 blocks come from is not said: Limits).
  A round without such bits:     blocks 0, .., K − 1 give the challenge as before; the last block is
                                 not read.
  The record `GrW` is where the nonce is: for the slot's query in a local round (`grJ`), for the
  shared query in a shared round, the joining round included (`gr0`); there is none in a round
  without proof-of-work bits.
  (By the kind only: in a shared round for which the compiled verifier has no query, which
  `RoundSplits.Fmt` excludes, the record is not used in the compiled prover's run: the compiler asks no
  query there and writes no nonce.)
  Records `GrW` that the old wire record may have (its conditions allow them) are not copied: the
  new one has exactly the records of g. So `grind` is not to be applied twice.
The number b of proof-of-work bits is data of the record of protocols only (the list g); a record
`GrW` repeats it (field `b`). What the wire record adds is `GrData W`: `mo` (`GrW` calls it `more`),
`enc`, `dec`.
The conditions ask b ≤ n ≤ λ in every round (`GBits.AllLe n`, Iop/GBitsLe.lean): then the
proof-of-work bits are exactly uniform and independent of the old challenge: no sampler, no bias
(that for b > λ the condition is false is not proved in this library);
and that the numbers tried with at most n such bits are decoded to themselves (`GrData.OK D n`). The
bound n is there because W is finite in a scheme: with a rule like mo b = 2^(b + 7) − 1, nonces of
64 bits decode to the numbers tried only for small b.
Main theorems: `QueryLayout.OKG.grind` (well-formed), `RoundsQueryLayout.pass_grind`, `WireBP.OK.grind`,
`BatchProtocol.Opens.grind`.
Notation: λ: in Lean `lam : ℕ`; `W : Type`: the type of nonces (`GrData.enc : ℕ → W`: the nonce for
a number); `g : GBits s` (Iop/GBits.lean): for each round a number of proof-of-work bits; `gT`,
`gL`, `gB`: of the types `GBits L.offline.shape`, `GBits L.link.shape`, `GBits L.onlineBatch.loc.shape`; `Kind`
(Iop/Batch.lean): a round is called shared (`sh`) or local (`lo`) after its verifier message;
`a : RAnn r` (there): the annotation of one round r of the local shape: its kind, and the splitting
of a prover message of the local transcript into (m_0, m_j); `A : RoundSplits s` (there): the annotation of
a shape; `k.b0 b`, `k.bJ b : ℕ` (`Kind.b0`, `Kind.bJ`, Iop/BatchGrind.lean): the number of
proof-of-work bits that counts for the shared component of a prover message: b in a shared round, 0
in a local one; the number that counts for the slot's component: b in a local round, 0 in a shared
one; `WireRB lam K r a`: a structure (Iop/BatchWire.lean): for one round of a batch IOP;
`RoundsQueryLayout lam K s A : Type` (there): a `WireRB` for each round of s; `ProtocolQueryLayout lam K Q`: a structure
(there), for `Q : BatchInteractiveOracleProof X E`: its fields: `sh : RoundsQueryLayout lam K Q.loc.shape Q.ann`, `ext`, `decO`,
`nOpen`, `maxDepth`; `WirePB Q H`: a structure (Iop/BatchWireP.lean): its fields: `coin0`, `coin`,
`decW`; `QueryLayout.OKG` (Iop/BatchWire.lean): the laws of a wire whose rounds may have tests;
`WireRB.OKG` (there): the laws of the wire of a round that may have a test; a test (`GrW`, there):
"grinding", proof of work; `E : ExtSpec` (Iop/InteractiveOracleProof.lean): external strings: oracles that are fixed
before the first message; `ν : GNon W s` (Iop/Grind.lean): a nonce for each round;
`Rho.pass g ρ : Bool` (there): all proof-of-work bits are 0; `Rho.strip g ρ : Rho s` (there): the
stripped verifier randomness, of the old list of rounds; `Rho.fill g ρ : Rho (s.grind W g)`, for
`ρ : Rho s` (there): all proof-of-work bits are 0; `no : OpenNums` (Iop/WireOf.lean): bounds on the
numbers of positions that the three verifiers open, external ones included.
Limits. Nothing is said on where the blocks come from, and nothing on how many of them an
implementation computes: that a failed attempt costs the first block only is a property of a rule
for reading blocks, which is no part of a wire record. That the records `GrW` fit the record of
protocols in the sense that the compiler asks: Compile/Batch/FitGrind.lean. At g = 0 everywhere the
new wire record is not the old one (K + 1 blocks, one unread), and no statement here ties the two
compiled schemes.
-/
import Iop.BatchGrindProofs
import Iop.GBitsLe
import Iop.BatchWireOK
import Iop.BatchWireP

namespace Iop
open Prob

variable {W : Type} [Inhabited W] {lam K : ℕ}

/-! ## The proof-of-work records -/

/-- What the wire record adds to the numbers of proof-of-work bits. -/
structure GrData (W : Type) where
  /-- in a round with b proof-of-work bits the honest prover tries the nonces for 0, .., mo b: at
  most mo b + 1 attempts -/
  mo : ℕ → ℕ
  /-- the nonce for a number -/
  enc : ℕ → W
  /-- the number that a nonce encodes -/
  dec : W → ℕ

/-- The numbers that are tried in a round with at most n proof-of-work bits are decoded to
themselves: so their nonces differ from each other. -/
def GrData.OK {W : Type} (D : GrData W) (n : ℕ) : Prop :=
  ∀ b k, b ≤ n → k ≤ D.mo b → D.dec (D.enc k) = k

/-- The record `GrW` of a round with b + 1 proof-of-work bits, for old challenges C and the old
plain part P of the component that gets the nonce. -/
def GrW.ofBits (D : GrData W) (b : ℕ) (C P : Type) :
    GrW (GChal (b + 1) C) (GPlain W (b + 1) P) where
  b := b + 1
  tst := GChal.test
  set := fun z c => GChal.mk (b + 1) (GChal.old c) z
  more := D.mo (b + 1)
  put := fun k p => GPlain.mk (b + 1) (GPlain.old p) (D.enc k)
  get := fun p => D.dec (GPlain.nonce p)

/-- the record, if the round has proof-of-work bits -/
def grOf (D : GrData W) (C P : Type) : (b : ℕ) → Option (GrW (GChal b C) (GPlain W b P))
  | 0 => none
  | b + 1 => some (GrW.ofBits D b C P)

/-- the record for the shared query: in a shared round with proof-of-work bits -/
def gr0Of (D : GrData W) (C P : Type) :
    (k : Kind) → (b : ℕ) → Option (GrW (GChal b C) (GPlain W (k.b0 b) P))
  | _, 0 => none
  | .sh, b + 1 => some (GrW.ofBits D b C P)
  | .lo, _ + 1 => none

/-- the record for a slot's query: in a local round with proof-of-work bits -/
def grJOf (D : GrData W) (C P : Type) :
    (k : Kind) → (b : ℕ) → Option (GrW (GChal b C) (GPlain W (k.bJ b) P))
  | _, 0 => none
  | .sh, _ + 1 => none
  | .lo, b + 1 => some (GrW.ofBits D b C P)

/-! ## The wire records -/

/-- The proof-of-work bits: the first b bits of a block. (Bits beyond λ, which do not occur when b ≤
λ, are zero.) -/
def testBits (lam b : ℕ) (d : Dig lam) : Fin b → Bool := fun i =>
  if h : i.val < lam then d ⟨i.val, h⟩ else false

/-- How K + 1 blocks give the challenge of a round with b proof-of-work bits. -/
def chalGrind {C : Type} (ch : (Fin K → Dig lam) → C) :
    (b : ℕ) → (Fin (K + 1) → Dig lam) → GChal b C
  | 0 => fun u => ch (firstBlocks lam (K + 1) K u)
  | b + 1 => fun u => (ch fun i => u i.succ, testBits lam (b + 1) (u 0))

/-- One round of Batch. -/
def WireRB.grind {r : Round} {a : RAnn r} (w : WireRB lam K r a) (D : GrData W) (b : ℕ) :
    WireRB lam (K + 1) (r.grind W b) (a.grind W b) where
  pt := w.pt.grind b
  depth0 := w.depth0
  depthJ := w.depthJ
  has0 := w.has0
  hasJ := w.hasJ
  place := w.place
  posAt0 := w.posAt0
  posAtJ := w.posAtJ
  chal := chalGrind w.chal b
  pr0 := w.pr0
  prJ := w.prJ
  gr0 := gr0Of D r.Chal a.P0 a.kind b
  grJ := grJOf D r.Chal a.Pj a.kind b

/-- One round of Test or Link: a local round in which only the slot sends: the annotation is
RAnn.allLocal both for the old round and for the new one. -/
def WireRB.grindLocal {r : Round} (w : WireRB lam K r (RAnn.allLocal r)) (D : GrData W) (b : ℕ) :
    WireRB lam (K + 1) (r.grind W b) (RAnn.allLocal (r.grind W b)) where
  pt := w.pt.grind b
  depth0 := w.depth0
  depthJ := w.depthJ
  has0 := w.has0
  hasJ := w.hasJ
  place := w.place
  posAt0 := w.posAt0
  posAtJ := w.posAtJ
  chal := chalGrind w.chal b
  pr0 := w.pr0
  prJ := w.prJ
  gr0 := none
  grJ := grOf D r.Chal r.Plain b

/-- all rounds of Batch -/
def RoundsQueryLayout.grind :
    {s : Shape} → {A : RoundSplits s} → RoundsQueryLayout lam K s A → GrData W → (g : GBits s) →
    RoundsQueryLayout lam (K + 1) (s.grind W g) (A.grind W g)
  | [], _, _, _, _ => ()
  | _ :: _, (_, _), (w, ws), D, (b, g) => (w.grind D b, RoundsQueryLayout.grind ws D g)

/-- all rounds of Test or Link -/
def RoundsQueryLayout.grindLocal :
    {s : Shape} → RoundsQueryLayout lam K s (RoundSplits.allLocal s) → GrData W → (g : GBits s) →
    RoundsQueryLayout lam (K + 1) (s.grind W g) (RoundSplits.allLocal (s.grind W g))
  | [], _, _, _ => ()
  | _ :: _, (w, ws), D, (b, g) => (w.grindLocal D b, RoundsQueryLayout.grindLocal ws D g)

variable {X : Type} {E : ExtSpec}

/-- Batch: the rounds; equality of positions is decided on the old positions -/
def ProtocolQueryLayout.grind {Q : BatchInteractiveOracleProof X E} (wq : ProtocolQueryLayout lam K Q) (D : GrData W) (g : GBits Q.loc.shape) :
    ProtocolQueryLayout lam (K + 1) (Q.grind W g) where
  sh := RoundsQueryLayout.grind wq.sh D g
  ext := wq.ext
  decO := @Equiv.decidableEq _ _ (OPos.stripE (W := W) g) wq.decO
  nOpen := wq.nOpen
  maxDepth := wq.maxDepth

/-- `ProtocolQueryLayout.grind` for Test or Link -/
def ProtocolQueryLayout.grindLocal {Q : InteractiveOracleProof X E} (wq : ProtocolQueryLayout lam K (BatchInteractiveOracleProof.ofProto Q))
    (D : GrData W) (g : GBits Q.shape) :
    ProtocolQueryLayout lam (K + 1) (BatchInteractiveOracleProof.ofProto (Q.grind W g)) where
  sh := RoundsQueryLayout.grindLocal wq.sh D g
  ext := wq.ext
  decO := @Equiv.decidableEq _ _ (OPos.stripE (W := W) g) wq.decO
  nOpen := wq.nOpen
  maxDepth := wq.maxDepth

variable {I : Type} {L : BatchProtocol I X}

/-- The verifier's wire record for the record with proof-of-work bits, with the records for the
honest prover's search. -/
def QueryLayout.grind (Wr : QueryLayout lam L) (D : GrData W) (gT : GBits L.offline.shape)
    (gL : GBits L.link.shape) (gB : GBits L.onlineBatch.loc.shape) :
    QueryLayout lam (L.grind W gT gL gB) where
  K := Wr.K + 1
  T := Wr.T.grindLocal D gT
  Lk := Wr.Lk.grindLocal D gL
  B := Wr.B.grind D gB
  depth := Wr.depth
  depthReq := Wr.depthReq

/-! ## The conditions -/

theorem GrW.OK.ofBits {D : GrData W} {n : ℕ} (h : D.OK n) {b : ℕ} (hb : b + 1 ≤ n) (C P : Type) :
    (GrW.ofBits D b C P).OK where
  tst_set := fun z c => GChal.test_mk (b + 1) (GChal.old c) z
  set_tst := fun c => GChal.mk_old_test c
  set_set := fun z z' c =>
    congrArg (fun x => GChal.mk (b + 1) x z) (GChal.old_mk (b + 1) (GChal.old c) z')
  get_put := fun k _ hk => h (b + 1) k hb hk

theorem grOf_ok {D : GrData W} {n : ℕ} (h : D.OK n) (C P : Type) :
    ∀ (b : ℕ), b ≤ n → ∀ g : GrW (GChal b C) (GPlain W b P), grOf D C P b = some g → g.OK
  | 0, _, _, e => by cases e
  | _ + 1, hb, _, e => by cases e; exact GrW.OK.ofBits h hb C P

theorem gr0Of_ok {D : GrData W} {n : ℕ} (h : D.OK n) (C P : Type) :
    ∀ (k : Kind) (b : ℕ),
      b ≤ n → ∀ g : GrW (GChal b C) (GPlain W (k.b0 b) P), gr0Of D C P k b = some g → g.OK
  | .sh, 0, _, _, e => by cases e
  | .lo, 0, _, _, e => by cases e
  | .sh, _ + 1, hb, _, e => by cases e; exact GrW.OK.ofBits h hb C P
  | .lo, _ + 1, _, _, e => by cases e

theorem grJOf_ok {D : GrData W} {n : ℕ} (h : D.OK n) (C P : Type) :
    ∀ (k : Kind) (b : ℕ),
      b ≤ n → ∀ g : GrW (GChal b C) (GPlain W (k.bJ b) P), grJOf D C P k b = some g → g.OK
  | .sh, 0, _, _, e => by cases e
  | .lo, 0, _, _, e => by cases e
  | .sh, _ + 1, _, _, e => by cases e
  | .lo, _ + 1, hb, _, e => by cases e; exact GrW.OK.ofBits h hb C P

theorem map_testBits_unif {b : ℕ} (h : b ≤ lam) :
    (unif (Dig lam)).map (testBits lam b) = unif (Fin b → Bool) :=
  map_firstBlocks_unif Bool false b lam h

/-- K + 1 blocks are block 0 and the K others. -/
def blocksHeadTail (B : Type) (K : ℕ) : (Fin (K + 1) → B) ≃ B × (Fin K → B) where
  toFun u := (u 0, fun i => u i.succ)
  invFun p := Fin.cons p.1 p.2
  left_inv u := Fin.cons_self_tail u
  right_inv _ := rfl

/-- If C is not empty, b ≤ λ and K uniform blocks give a uniform old challenge, then K + 1 uniform
blocks give a uniform old challenge and uniform proof-of-work bits, independent of each other. -/
theorem map_chalGrind_unif {C : Type} [Fintype C] [Nonempty C] {ch : (Fin K → Dig lam) → C}
    (hc : (unif (Fin K → Dig lam)).map ch = unif C) :
    ∀ {b : ℕ}, b ≤ lam → (unif (Fin (K + 1) → Dig lam)).map (chalGrind ch b) = unif (GChal b C)
  | 0, _ => by
      show (unif (Fin (K + 1) → Dig lam)).map (ch ∘ firstBlocks lam (K + 1) K) = unif C
      rw [← PMF.map_comp,
        show (unif (Fin (K + 1) → Dig lam)).map (firstBlocks lam (K + 1) K) = unif (Fin K → Dig lam)
          from map_firstBlocks_unif (Dig lam) (fun _ => false) K (K + 1) (Nat.le_succ K), hc]
  | b + 1, h => by
      have h1 : (unif (Dig lam × (Fin K → Dig lam))).map
            (fun p => (testBits lam (b + 1) p.1, ch p.2)) =
          unif ((Fin (b + 1) → Bool) × C) :=
        map_unif_prodMap (testBits lam (b + 1)) ch (map_testBits_unif h) hc
      show (unif (Fin (K + 1) → Dig lam)).map (fun u =>
          ((ch fun i => u i.succ, testBits lam (b + 1) (u 0)) : C × (Fin (b + 1) → Bool))) =
        unif (C × (Fin (b + 1) → Bool))
      rw [← map_unif_equiv (Equiv.prodComm (Fin (b + 1) → Bool) C), ← h1,
        ← map_unif_equiv (blocksHeadTail (Dig lam) K), PMF.map_comp, PMF.map_comp]
      rfl

theorem WireRB.OKG.grind {r : Round} {a : RAnn r} {w : WireRB lam K r a} (h : w.OKG) {D : GrData W}
    {n : ℕ} (hD : D.OK n) (hn : n ≤ lam) {b : ℕ} (hb : b ≤ n) : (w.grind D b).OKG where
  place_lt0 := h.place_lt0
  place_ltJ := h.place_ltJ
  posAt0_place := h.posAt0_place
  posAtJ_place := h.posAtJ_place
  place_posAt0 := h.place_posAt0
  place_posAtJ := h.place_posAtJ
  no0 := h.no0
  noJ := h.noJ
  chal_unif := map_chalGrind_unif h.chal_unif (hb.trans hn)
  gr0_ok := gr0Of_ok hD r.Chal a.P0 a.kind b hb
  grJ_ok := grJOf_ok hD r.Chal a.Pj a.kind b hb

theorem WireRB.OKG.grindLocal {r : Round} {w : WireRB lam K r (RAnn.allLocal r)} (h : w.OKG)
    {D : GrData W} {n : ℕ} (hD : D.OK n) (hn : n ≤ lam) {b : ℕ} (hb : b ≤ n) :
    (w.grindLocal D b).OKG where
  place_lt0 := h.place_lt0
  place_ltJ := h.place_ltJ
  posAt0_place := h.posAt0_place
  posAtJ_place := h.posAtJ_place
  place_posAt0 := h.place_posAt0
  place_posAtJ := h.place_posAtJ
  no0 := h.no0
  noJ := h.noJ
  chal_unif := map_chalGrind_unif h.chal_unif (hb.trans hn)
  gr0_ok := fun _ e => by cases e
  grJ_ok := grOf_ok hD r.Chal r.Plain b hb

theorem RoundsQueryLayout.OKG.grind {D : GrData W} {n : ℕ} (hD : D.OK n) (hn : n ≤ lam) :
    ∀ {s : Shape} {A : RoundSplits s} {ws : RoundsQueryLayout lam K s A} {g : GBits s},
      RoundsQueryLayout.OKG s A ws → g.AllLe n → RoundsQueryLayout.OKG (s.grind W g) (A.grind W g) (RoundsQueryLayout.grind ws D g)
  | [], _, _, _, _, _ => trivial
  | _ :: _, (_, _), (_, _), (_, _), h, hg => ⟨h.1.grind hD hn hg.1, RoundsQueryLayout.OKG.grind hD hn h.2 hg.2⟩

theorem RoundsQueryLayout.OKG.grindLocal {D : GrData W} {n : ℕ} (hD : D.OK n) (hn : n ≤ lam) :
    ∀ {s : Shape} {ws : RoundsQueryLayout lam K s (RoundSplits.allLocal s)} {g : GBits s},
      RoundsQueryLayout.OKG s (RoundSplits.allLocal s) ws → g.AllLe n →
      RoundsQueryLayout.OKG (s.grind W g) (RoundSplits.allLocal (s.grind W g)) (RoundsQueryLayout.grindLocal ws D g)
  | [], _, _, _, _ => trivial
  | _ :: _, (_, _), (_, _), h, hg =>
    ⟨h.1.grindLocal hD hn hg.1, RoundsQueryLayout.OKG.grindLocal hD hn h.2 hg.2⟩

theorem RoundsQueryLayout.DepthLe.grind {d : ℕ} (D : GrData W) :
    ∀ {s : Shape} {A : RoundSplits s} {ws : RoundsQueryLayout lam K s A} (g : GBits s),
      RoundsQueryLayout.DepthLe d s A ws → RoundsQueryLayout.DepthLe d (s.grind W g) (A.grind W g) (RoundsQueryLayout.grind ws D g)
  | [], _, _, _, _ => trivial
  | _ :: _, (_, _), (_, _), (_, g), h => ⟨h.1, RoundsQueryLayout.DepthLe.grind D g h.2⟩

theorem RoundsQueryLayout.DepthLe.grindLocal {d : ℕ} (D : GrData W) :
    ∀ {s : Shape} {ws : RoundsQueryLayout lam K s (RoundSplits.allLocal s)} (g : GBits s),
      RoundsQueryLayout.DepthLe d s (RoundSplits.allLocal s) ws →
      RoundsQueryLayout.DepthLe d (s.grind W g) (RoundSplits.allLocal (s.grind W g)) (RoundsQueryLayout.grindLocal ws D g)
  | [], _, _, _ => trivial
  | _ :: _, (_, _), (_, g), h => ⟨h.1, RoundsQueryLayout.DepthLe.grindLocal D g h.2⟩

theorem ProtocolQueryLayout.OKG.grind {Q : BatchInteractiveOracleProof X E} {wq : ProtocolQueryLayout lam K Q} (h : wq.OKG) {D : GrData W}
    {n : ℕ} (hD : D.OK n) (hn : n ≤ lam) {g : GBits Q.loc.shape} (hg : g.AllLe n) :
    (wq.grind D g).OKG where
  sh := h.sh.grind hD hn hg
  ext := h.ext
  opens := fun x ρ pl =>
    (congrArg (· + _) (InteractiveOracleProof.card_reads_grind g x ρ pl)).le.trans (h.opens x _ _)
  depth := h.depth.grind D g

theorem ProtocolQueryLayout.OKG.grindLocal {Q : InteractiveOracleProof X E}
    {wq : ProtocolQueryLayout lam K (BatchInteractiveOracleProof.ofProto Q)} (h : wq.OKG) {D : GrData W} {n : ℕ}
    (hD : D.OK n) (hn : n ≤ lam) {g : GBits Q.shape} (hg : g.AllLe n) :
    (wq.grindLocal D g).OKG where
  sh := h.sh.grindLocal hD hn hg
  ext := h.ext
  opens := fun x ρ pl =>
    (congrArg (· + _) (InteractiveOracleProof.card_reads_grind g x ρ pl)).le.trans (h.opens x _ _)
  depth := h.depth.grindLocal D g

/-- The wire record for the record with proof-of-work bits is well-formed (`QueryLayout.OKG`), for nonces
W with a fixed element, if the old one is, no round has more than n ≤ λ such bits, and the numbers
tried with at most n such bits are decoded to themselves. -/
theorem QueryLayout.OKG.grind {Wr : QueryLayout lam L} (h : Wr.OKG) {D : GrData W} {n : ℕ} (hD : D.OK n)
    (hn : n ≤ lam) {gT : GBits L.offline.shape} {gL : GBits L.link.shape} {gB : GBits L.onlineBatch.loc.shape}
    (hT : gT.AllLe n) (hL : gL.AllLe n) (hB : gB.AllLe n) : (Wr.grind D gT gL gB).OKG where
  T := h.T.grindLocal hD hn hT
  Lk := h.Lk.grindLocal hD hn hL
  B := h.B.grind hD hn hB
  fits := h.fits
  slots := h.slots
  extDepth := h.extDepth
  depthT := h.depthT
  depthL := h.depthL
  depthB := h.depthB
  extT := h.extT
  extB := h.extB
  extL := h.extL

/-! ## The wire record's proof-of-work checks are `Rho.pass` -/

theorem GrW.ok_ofBits (D : GrData W) (b : ℕ) (C P : Type) (c : GChal (b + 1) C) :
    (GrW.ofBits D b C P).ok c = GChal.pass c :=
  decide_eq_decide.2 funext_iff

theorem GChal.pass_zero_bits {C : Type} (c : GChal 0 C) : GChal.pass c = true :=
  (GChal.pass_iff c).2 fun i => i.elim0

theorem WireRB.pass_grind {r : Round} {a : RAnn r} (w : WireRB lam K r a) (D : GrData W)
    (b : ℕ) (c : GChal b r.Chal) :
    (w.grind D b).pass c = GChal.pass c := by
  obtain ⟨k, M0, Mj, sp, P0, Pj, pl0, plj, pl, own⟩ := a
  cases k <;> cases b
  · exact (GChal.pass_zero_bits c).symm
  · exact GrW.ok_ofBits D _ r.Chal P0 c
  · exact (GChal.pass_zero_bits c).symm
  · exact GrW.ok_ofBits D _ r.Chal Pj c

theorem WireRB.zero_grind {r : Round} {a : RAnn r} (w : WireRB lam K r a) (D : GrData W)
    (b : ℕ) (c : GChal b r.Chal) :
    (w.grind D b).zero c = GChal.zero b (GChal.old c) := by
  obtain ⟨k, M0, Mj, sp, P0, Pj, pl0, plj, pl, own⟩ := a
  cases k <;> cases b <;> rfl

theorem WireRB.pass_grindLocal {r : Round} (w : WireRB lam K r (RAnn.allLocal r)) (D : GrData W) :
    ∀ (b : ℕ) (c : GChal b r.Chal), (w.grindLocal D b).pass c = GChal.pass c
  | 0, c => (GChal.pass_zero_bits c).symm
  | b + 1, c => GrW.ok_ofBits D b r.Chal r.Plain c

theorem WireRB.zero_grindLocal {r : Round} (w : WireRB lam K r (RAnn.allLocal r)) (D : GrData W) :
    ∀ (b : ℕ) (c : GChal b r.Chal), (w.grindLocal D b).zero c = GChal.zero b (GChal.old c)
  | 0, _ => rfl
  | _ + 1, _ => rfl

/-- What the wire record calls "all tests of a local transcript are passed" (`RoundsQueryLayout.pass`: all
proof-of-work bits in a slot's transcript are 0) is `Rho.pass` of the record of protocols. -/
theorem RoundsQueryLayout.pass_grind (D : GrData W) :
    ∀ {s : Shape} {A : RoundSplits s} (ws : RoundsQueryLayout lam K s A) (g : GBits s) (ρ : Rho (s.grind W g)),
      RoundsQueryLayout.pass (s.grind W g) (A.grind W g) (RoundsQueryLayout.grind ws D g) ρ = Rho.pass g ρ
  | [], _, _, _, _ => rfl
  | _ :: _, (_, _), (w, ws), (b, g), (c, ρ) =>
    congrArg₂ (· && ·) (w.pass_grind D b c) (RoundsQueryLayout.pass_grind D ws g ρ)

/-- `RoundsQueryLayout.zero` (all proof-of-work bits set to 0) is: strip, then fill. -/
theorem RoundsQueryLayout.zero_grind (D : GrData W) :
    ∀ {s : Shape} {A : RoundSplits s} (ws : RoundsQueryLayout lam K s A) (g : GBits s) (ρ : Rho (s.grind W g)),
      RoundsQueryLayout.zero (s.grind W g) (A.grind W g) (RoundsQueryLayout.grind ws D g) ρ = Rho.fill g (Rho.strip g ρ)
  | [], _, _, _, _ => rfl
  | _ :: _, (_, _), (w, ws), (b, g), (c, ρ) =>
    Prod.ext (w.zero_grind D b c) (RoundsQueryLayout.zero_grind D ws g ρ)

theorem RoundsQueryLayout.pass_grindLocal (D : GrData W) :
    ∀ {s : Shape} (ws : RoundsQueryLayout lam K s (RoundSplits.allLocal s)) (g : GBits s) (ρ : Rho (s.grind W g)),
      RoundsQueryLayout.pass (s.grind W g) (RoundSplits.allLocal (s.grind W g)) (RoundsQueryLayout.grindLocal ws D g) ρ =
        Rho.pass g ρ
  | [], _, _, _ => rfl
  | _ :: _, (w, ws), (b, g), (c, ρ) =>
    congrArg₂ (· && ·) (w.pass_grindLocal D b c) (RoundsQueryLayout.pass_grindLocal D ws g ρ)

theorem RoundsQueryLayout.zero_grindLocal (D : GrData W) :
    ∀ {s : Shape} (ws : RoundsQueryLayout lam K s (RoundSplits.allLocal s)) (g : GBits s) (ρ : Rho (s.grind W g)),
      RoundsQueryLayout.zero (s.grind W g) (RoundSplits.allLocal (s.grind W g)) (RoundsQueryLayout.grindLocal ws D g) ρ =
        Rho.fill g (Rho.strip g ρ)
  | [], _, _, _ => rfl
  | _ :: _, (w, ws), (b, g), (c, ρ) =>
    Prod.ext (w.zero_grindLocal D b c) (RoundsQueryLayout.zero_grindLocal D ws g ρ)

/-! ## The prover's other data -/

variable {Wt : Type}

/-- Batch: whether a ρ is in the abort set (`Honest.withheld`) is decided at its stripped value -/
def WirePB.grind {Q : BatchInteractiveOracleProof X E} {H : BatchHonestProver Q Wt} (wp : WirePB Q H)
    (g : GBits Q.loc.shape) (ν : GNon W Q.loc.shape) :
    WirePB (Q.grind W g) (H.grind g ν) where
  coin0 := wp.coin0
  coin := wp.coin
  decW := fun w x ρ =>
    @decidable_of_iff _ _ (BatchGrind.mem_one_withheld_grind H g ν w x ρ).symm
      (wp.decW w x (Rho.strip g ρ))

theorem mem_ofHonest_withheld_grind {Q : InteractiveOracleProof X E} (H : Honest Q Wt) (g : GBits Q.shape)
    (ν : GNon W Q.shape) (w : Wt) (x : X) (ρ : Rho (Q.shape.grind W g)) :
    Rho.strip g ρ ∈ (BatchHonestProver.ofHonest H).one.withheld w x ↔
    ρ ∈ (BatchHonestProver.ofHonest (H.grind g ν)).one.withheld w x := by
  rw [BatchOne.ofHonest_withheld, BatchOne.ofHonest_withheld]
  rfl

/-- `WirePB.grind` for Test or Link -/
def WirePB.grindLocal {Q : InteractiveOracleProof X E} {H : Honest Q Wt}
    (wp : WirePB (BatchInteractiveOracleProof.ofProto Q) (BatchHonestProver.ofHonest H))
    (g : GBits Q.shape) (ν : GNon W Q.shape) :
    WirePB (BatchInteractiveOracleProof.ofProto (Q.grind W g)) (BatchHonestProver.ofHonest (H.grind g ν)) where
  coin0 := wp.coin0
  coin := wp.coin
  decW := fun w x ρ =>
    @decidable_of_iff _ _ (mem_ofHonest_withheld_grind H g ν w x ρ) (wp.decW w x (Rho.strip g ρ))

/-- The prover's other data for the record with proof-of-work bits. -/
def WireBP.grind (WP : WireBP L) (gT : GBits L.offline.shape)
    (gL : GBits L.link.shape) (gB : GBits L.onlineBatch.loc.shape) :
    WireBP (L.grind W gT gL gB) where
  T := WP.T.grindLocal gT _
  Lk := WP.Lk.grindLocal gL _
  B := WP.B.grind gB _
  ri := WP.ri
  perm := WP.perm

theorem WireBP.OK.grind {WP : WireBP L} (h : WP.OK) (gT : GBits L.offline.shape)
    (gL : GBits L.link.shape) (gB : GBits L.onlineBatch.loc.shape) :
    (WP.grind (W := W) gT gL gB).OK :=
  ⟨⟨h.T.coin0, h.T.coin⟩, ⟨h.Lk.coin0, h.Lk.coin⟩, ⟨h.B.coin0, h.B.coin⟩, h.ri, h.perm⟩

/-! ## Numbers of opened positions -/

/-- The same bounds on the numbers of opened positions hold. -/
theorem BatchProtocol.Opens.grind {no : OpenNums} (h : L.Opens no) (gT : GBits L.offline.shape)
    (gL : GBits L.link.shape) (gB : GBits L.onlineBatch.loc.shape) : (L.grind W gT gL gB).Opens no :=
  ⟨fun x ρ pl => (congrArg (· + _) (InteractiveOracleProof.card_reads_grind gT x ρ pl)).le.trans (h.opT x _ _),
   fun x ρ pl => (congrArg (· + _) (InteractiveOracleProof.card_reads_grind gL x ρ pl)).le.trans (h.opL x _ _),
   fun x ρ pl => (congrArg (· + _) (InteractiveOracleProof.card_reads_grind gB x ρ pl)).le.trans (h.opB x _ _)⟩

end Iop
