-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/FrontRoad/CoinsEnough.lean: one number, sampled first, holds all random choices of the
committer of the schemes frontArgK and frontId, at every index, if the public reading samples
nothing and the number's range is a multiple of coinsRange (h d) for every d.
Terms of this folder: Johnson/FrontRoad/Spec.lean.

What this file has.
coinsSuffice_frontK: let T be a family of inputs whose public reading samples nothing, and let h
give an honest side (the structure HonestSide) for every value d of the reading. If range is a
multiple of coinsRange (h d) for every d, then range is enough for the committer of frontArgK
(Johnson/FrontRoad/FrontK.lean) at every index, in the sense of the library's predicate
ZKCP.OComp.CoinsSuffice (ZKCP/CoinsFirst.lean): wherever the committer samples from 0, …, n, the
range that is left is a multiple of n + 1. It holds for every honest side: nothing is asked of its
provers.

  coinsRange h   the product of the sizes of the lists from which the committer commitW
      (Johnson/WholeKey/Defs.lean) samples: four lists for the first table, and four for each of the
      h.M + 1 copies (copyRange h).
  Enough c range   the library's predicate CoinsSuffice, written for algorithms over any family of
      oracles (Rom.OComp).
  Enough.of_dvd, enough_of_noCoin, Enough.bind, Enough.bind_noCoin, Enough.noCoin_bind,
  enough_sample, Enough.overOne, coinsSuffice_ofRom   its rules: a multiple of a range that is
      enough is enough; an algorithm that samples nothing needs nothing; sequential composition; one
      sample; the step from typed oracles to one hash function; the step to the form of
      ZKCP/Defs.lean.
  enough_coinsCopy, enough_coinsCopies, enough_coinsC, enough_commitW   the committer's coins, read
      off its definition. coinsRange_pos: the range is not 0.
  not_enough_sample, not_enough_commitW   two negative tests: a range that is no multiple of n + 1
      is not enough for a sample from 0, …, n; range 1 is not enough for commitW as soon as its
      first list has two entries.
  coinsSuffice_of_drawsNoCoin, coinsSuffice_bind_noCoin   two rules in the form of ZKCP/Defs.lean.
  drawsNoCoin_keyDigest   the query for the commitment ID samples nothing.

How it fits. The library's step Arg.coinsFirst (ZKCP/CoinsFirstArg.lean) turns a scheme into one
whose committer samples one number first and whose prover's key is the index with that number. It
keeps completeness and index privacy if one range is enough for the committer at every index. This
file proves that premise, under the two conditions of the title. Johnson/FrontRoad/Slot.lean uses
it. Not one of the release's goal statements.

Limits. A statement on where an algorithm samples: nothing on soundness, completeness or hiding. The
number holds every random choice of a run of the committer, so its range is far larger than that of
a seed that a program would keep (see ZKCP/CoinsFirst.lean on this). Range 0 meets Enough for every
algorithm and means nothing (ZKCP/CoinsFirst.lean, at CoinsSuffice). A multiple above 0 for all d
need not exist (Johnson/FrontRoad/Slot.lean, Limits).
-/
import Johnson.FrontRoad.FrontK
import Johnson.WholeKey.Complete
import ZKCP.CoinsFirst
import ZKCP.WithCoinsBind
import Rom.NoCoinExits

set_option autoImplicit false

noncomputable section

namespace OnBytes.FrontRoad
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom
open OnBytes.Prover OnBytes.WholeKey OnBytes.PublicAt VerifiableInference
open VerifiableInference.OnPublicFiles ZKCP.PublicRead
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

/-! ## For algorithms over any family of oracles -/

section General
variable {S : OSpec} {α β : Type}

/-- A number sampled from a range of this size holds enough random choices for the algorithm:
wherever it samples from 0, …, n, the range that is left is a multiple of n + 1, and the quotient is
the range that is left afterwards. -/
def Enough : Rom.OComp S α → ℕ → Prop
  | .pure _, _ => True
  | .query _ _ k, range => ∀ r, Enough (k r) range
  | .sample n k, range => (n + 1) ∣ range ∧ ∀ r, Enough (k r) (range / (n + 1))

/-- A multiple of a range that is enough is enough. -/
theorem Enough.of_dvd : ∀ (c : Rom.OComp S α) (range range' : ℕ), Enough c range →
    range ∣ range' → Enough c range'
  | .pure _, _, _, _, _ => trivial
  | .query _ _ k, range, range', h, hd => fun r => Enough.of_dvd (k r) range range' (h r) hd
  | .sample n k, range, range', h, hd =>
      ⟨Nat.dvd_trans h.1 hd, fun r => Enough.of_dvd (k r) _ _ (h.2 r) (by
        obtain ⟨u, rfl⟩ := h.1
        obtain ⟨v, rfl⟩ := hd
        rw [Nat.mul_assoc, Nat.mul_div_cancel_left _ n.succ_pos,
          Nat.mul_div_cancel_left _ n.succ_pos]
        exact Nat.dvd_mul_right u v)⟩

/-- An algorithm that samples nothing needs nothing. -/
theorem enough_of_noCoin : ∀ (c : Rom.OComp S α) (range : ℕ), c.NoCoin → Enough c range
  | .pure _, _, _ => trivial
  | .query _ _ k, range, h => fun r => enough_of_noCoin (k r) range (h r)
  | .sample _ _, _, h => h.elim

/-- Sequential composition: the product of two ranges. -/
theorem Enough.bind : ∀ (c : Rom.OComp S α) (g : α → Rom.OComp S β) (r₁ r₂ : ℕ), Enough c r₁ →
    (∀ a, Enough (g a) r₂) → Enough (c.bind g) (r₁ * r₂)
  | .pure a, g, r₁, r₂, _, hg => Enough.of_dvd (g a) r₂ _ (hg a) (Nat.dvd_mul_left r₂ r₁)
  | .query _ _ k, g, r₁, r₂, h, hg => fun r => Enough.bind (k r) g r₁ r₂ (h r) hg
  | .sample n k, g, r₁, r₂, h, hg =>
      ⟨Dvd.dvd.mul_right h.1 r₂, fun r => by
        have e : r₁ * r₂ / (n + 1) = r₁ / (n + 1) * r₂ := by
          obtain ⟨u, hu⟩ := h.1
          rw [hu, Nat.mul_assoc, Nat.mul_div_cancel_left _ n.succ_pos,
            Nat.mul_div_cancel_left _ n.succ_pos]
        show Enough ((k r).bind g) (r₁ * r₂ / (n + 1))
        rw [e]
        exact Enough.bind (k r) g _ r₂ (h.2 r) hg⟩

/-- Sequential composition with a second part that samples nothing. -/
theorem Enough.bind_noCoin : ∀ (c : Rom.OComp S α) (g : α → Rom.OComp S β) (range : ℕ),
    Enough c range → (∀ a, (g a).NoCoin) → Enough (c.bind g) range
  | .pure a, g, range, _, hg => enough_of_noCoin (g a) range (hg a)
  | .query _ _ k, g, range, h, hg => fun r => Enough.bind_noCoin (k r) g range (h r) hg
  | .sample _ k, g, _, h, hg => ⟨h.1, fun r => Enough.bind_noCoin (k r) g _ (h.2 r) hg⟩

/-- Sequential composition with a first part that samples nothing. -/
theorem Enough.noCoin_bind : ∀ (c : Rom.OComp S α) (g : α → Rom.OComp S β) (range : ℕ),
    c.NoCoin → (∀ a, Enough (g a) range) → Enough (c.bind g) range
  | .pure a, _, _, _, hg => hg a
  | .query _ _ k, g, range, h, hg => fun r => Enough.noCoin_bind (k r) g range (h r) hg
  | .sample _ _, _, _, h, _ => h.elim

/-- One sample from 0, …, n in front. -/
theorem enough_sample {n : ℕ} {k : Fin (n + 1) → Rom.OComp S α} {range : ℕ}
    (h : ∀ r, Enough (k r) range) : Enough (.sample n k) ((n + 1) * range) :=
  ⟨Nat.dvd_mul_right _ _, fun r => by
    show Enough (k r) ((n + 1) * range / (n + 1))
    rw [Nat.mul_div_cancel_left _ n.succ_pos]
    exact h r⟩

/-- The step from typed oracles to one hash function adds queries and no sample. -/
theorem Enough.overOne {lam : ℕ} (m : OracleCoding S lam) : ∀ (c : Rom.OComp S α) (range : ℕ),
    Enough c range → Enough (c.overOne m) range
  | .pure _, _, _ => trivial
  | .sample _ k, _, h => ⟨h.1, fun r => Enough.overOne m (k r) _ (h.2 r)⟩
  | .query _ _ k, range, h =>
      Enough.noCoin_bind _ _ range (noCoin_askAll _ _) fun _ => Enough.overOne m (k _) range (h _)

/-- In the form of ZKCP/Defs.lean it is the library's predicate. -/
theorem coinsSuffice_ofRom {lam : ℕ} : ∀ (c : Rom.OComp (rom lam) α) (range : ℕ),
    Enough c range → (ofRom c).CoinsSuffice range
  | .pure _, _, _ => trivial
  | .query _ _ k, range, h => fun r => coinsSuffice_ofRom (k r) range (h r)
  | .sample _ k, _, h => ⟨h.1, fun r => coinsSuffice_ofRom (k r) _ (h.2 r)⟩

/-- In the form of ZKCP/Defs.lean: an algorithm that samples nothing needs nothing. -/
theorem coinsSuffice_of_drawsNoCoin {lam : ℕ} : ∀ (c : ZKCP.OComp lam α) (range : ℕ),
    c.DrawsNoCoin → c.CoinsSuffice range
  | .pure _, _, _ => trivial
  | .query _ k, range, h => fun r => coinsSuffice_of_drawsNoCoin (k r) range (h r)
  | .sample _ _, _, h => h.elim

/-- In the form of ZKCP/Defs.lean: a second part that samples nothing. -/
theorem coinsSuffice_bind_noCoin {lam : ℕ} : ∀ (c : ZKCP.OComp lam α)
    (g : α → ZKCP.OComp lam β) (range : ℕ), c.CoinsSuffice range → (∀ a, (g a).DrawsNoCoin) →
    (c.bind g).CoinsSuffice range
  | .pure a, g, range, _, hg => coinsSuffice_of_drawsNoCoin (g a) range (hg a)
  | .query _ k, g, range, h, hg => fun r => coinsSuffice_bind_noCoin (k r) g range (h r) hg
  | .sample _ k, g, _, h, hg => ⟨h.1, fun r => coinsSuffice_bind_noCoin (k r) g _ (h.2 r) hg⟩

/-- The query for the digest of a key's code samples nothing. -/
theorem drawsNoCoin_keyDigest {lam : ℕ} {IVK : Type} (enc : IVK → Option ZKCP.Str) (key : IVK) :
    (ZKCP.keyDigest (lam := lam) enc key).DrawsNoCoin := by
  unfold ZKCP.keyDigest
  cases enc key with
  | none => trivial
  | some _ => exact fun _ => trivial

end General

/-! ## The committer's coins -/

section Committer
variable {I X : Type} {lam : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
  {aL : RoundSplits L.link.shape} (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL)
  (cA : L.OutOfDomainAnswer → List (Dig lam)) (h : HonestSide lam L Bd aT aL)

/-- The product of the sizes of the four lists from which the coins for one copy are sampled. -/
def copyRange : ℕ := (h.ri.n + 1) * ((h.sl.n + 1) * ((h.kL.n + 1) * ((h.coL.n + 1) * 1)))

/-- The product of the sizes of all lists from which the committer samples. -/
def coinsRange : ℕ :=
  (h.ri.n + 1) * ((h.sl.n + 1) * ((h.kT.n + 1) * ((h.coT.n + 1) * copyRange h ^ (h.M + 1))))

theorem enough_coinsCopy : Enough (coinsCopy W h) (copyRange h) :=
  enough_sample fun _ => enough_sample fun _ => enough_sample fun _ => enough_sample fun _ =>
    trivial

theorem enough_coinsCopies : ∀ n : ℕ, Enough (coinsCopies W h n) (copyRange h ^ n)
  | 0 => trivial
  | n + 1 =>
    Enough.of_dvd _ _ _
      (Enough.bind (coinsCopy W h) _ (copyRange h) (copyRange h ^ n) (enough_coinsCopy W h) fun _ =>
        Enough.bind_noCoin (coinsCopies W h n) _ _ (enough_coinsCopies n) fun _ => trivial)
      (dvd_of_eq (pow_succ' (copyRange h) n).symm)

theorem enough_coinsC : Enough (coinsC W h) (coinsRange h) :=
  enough_sample fun _ => enough_sample fun _ => enough_sample fun _ => enough_sample fun _ =>
    Enough.bind_noCoin (coinsCopies W h (h.M + 1)) _ _ (enough_coinsCopies W h (h.M + 1)) fun _ =>
      trivial

/-- The range is not 0. -/
theorem coinsRange_pos : 0 < coinsRange h :=
  Nat.mul_pos (Nat.succ_pos _) (Nat.mul_pos (Nat.succ_pos _) (Nat.mul_pos (Nat.succ_pos _)
    (Nat.mul_pos (Nat.succ_pos _) (Nat.pow_pos (Nat.mul_pos (Nat.succ_pos _)
      (Nat.mul_pos (Nat.succ_pos _) (Nat.mul_pos (Nat.succ_pos _)
        (Nat.mul_pos (Nat.succ_pos _) Nat.one_pos))))))))

/-- A negative test: a range that is no multiple of n + 1 is not enough for a sample from 0, …, n.
-/
theorem not_enough_sample {S' : OSpec} {α : Type} {n : ℕ} {k : Fin (n + 1) → Rom.OComp S' α}
    {range : ℕ} (hn : ¬ (n + 1) ∣ range) : ¬ Enough (.sample n k) range := fun e => hn e.1

/-- **A negative test: range 1 is not enough for the committer commitW** as soon as the list of the
index encoder's randomness has two entries. Range 1 is the bound 0, at which every sample is 0. -/
theorem not_enough_commitW (i : I) (h2 : 0 < h.ri.n) : ¬ Enough (commitW W S cA h i) 1 := fun e =>
  have e' : (h.ri.n + 1) ∣ 1 ∧ _ := e
  absurd (Nat.le_of_dvd Nat.one_pos e'.1) (by omega)

/-- **coinsRange h is enough for the committer commitW**, at every index. -/
theorem enough_commitW (i : I) : Enough (commitW W S cA h i) (coinsRange h) :=
  Enough.bind_noCoin (coinsC W h) _ _ (enough_coinsC W h) fun d => noCoin_commitAt W S cA h i d

end Committer

/-! ## The committer of frontArgK -/

variable {R : InnerCompilerInput} (T : LayoutsByPublicReading R) (h : T.D → HonestSide 256 R.protocol R.LeafBody R.offlineRoundSplits R.linkRoundSplits)
  {J K' P' : Type} (idx : J → R.Index) (x₀ : R.Instance)
  (κ : ZKCP.Digest 256 → FullKey 256 R.protocol R.offlineRoundSplits R.linkRoundSplits → K')
  (ϖ : FullKey 256 R.protocol R.offlineRoundSplits R.linkRoundSplits → RequestProof 256 R.protocol → P')
  (Vf : K' → List Token × List Token → P' → ZKCP.OComp 256 Bool)

/-- The committer behind the public reading. -/
theorem enough_readTold (range : ℕ) (noCoin : T.Pub.NoCoin)
    (hr : ∀ d, coinsRange (h d) ∣ range) (i : R.Index) : Enough ((readTold T h).C i) range :=
  Enough.noCoin_bind T.Pub _ range noCoin fun d =>
    Enough.bind_noCoin _ _ range
      (Enough.bind_noCoin _ _ range
        (Enough.overOne (T.m d) _ range
          (Enough.of_dvd _ _ _ (enough_commitW R.queryLayout (T.Sd d) (T.cA d) (h d) i) (hr d)))
        fun _ => trivial)
      fun _ => trivial

/-- **One range is enough for the committer of frontArgK at every index.** -/
theorem coinsSuffice_frontK (range : ℕ) (noCoin : T.Pub.NoCoin)
    (hr : ∀ d, coinsRange (h d) ∣ range) (w : J) :
    ((frontArgK T h idx x₀ κ ϖ Vf).C w).CoinsSuffice range :=
  coinsSuffice_bind_noCoin _ _ range
    (coinsSuffice_ofRom _ range (enough_readTold T h range noCoin hr (idx w)))
    fun keys => ZKCP.OComp.DrawsNoCoin.mapO _ _ (drawsNoCoin_keyDigest _ keys.1)

end OnBytes.FrontRoad

#print axioms OnBytes.FrontRoad.Enough.of_dvd
#print axioms OnBytes.FrontRoad.Enough.bind
#print axioms OnBytes.FrontRoad.Enough.overOne
#print axioms OnBytes.FrontRoad.coinsSuffice_ofRom
#print axioms OnBytes.FrontRoad.not_enough_commitW
#print axioms OnBytes.FrontRoad.enough_commitW
#print axioms OnBytes.FrontRoad.enough_readTold
#print axioms OnBytes.FrontRoad.coinsSuffice_frontK
