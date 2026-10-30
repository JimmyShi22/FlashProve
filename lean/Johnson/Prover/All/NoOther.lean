-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/All/NoOther.lean: THE HONEST SIDE ASKS NO POINT OF THE SPARE ORACLE: committer,
prover of a whole request and verifier, behind their coins; so over one hash function
they ask no string that codes such a point.

Why. Where a description's public readings are answers of the hash function, their strings code
points of the spare oracle (so layoutsByPublicReading_spare, Johnson/Flat/Told/Dec/LayoutsAtDescriptionDataAtFiles.lean). By pub_le
(Johnson/Prover/All/Public.lean) such readings in front of an experiment cost its bound nothing, if
the experiment asks none of their strings.

Main names.
  no_askV … no_chainO, no_proveX   the compiled prover of one slot.
  no_committerTreeKeptByProver, no_seedsO, no_committerAtFixedCoins, no_allY, no_allX, no_expAt   the whole request.
  hno_expAt   over one hash function.

The verifier's: asksIn_VRA (Johnson/Top/InnerCompiledVerifierByPublicReading.lean). The walks are those of noCoin_chainO
(OnBytes/Prover/Returns.lean).

Limits. Names of oracles alone. Nothing on which strings are public anywhere.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.All.Defs
import Johnson.Prover.Law.Asks
import Johnson.Top.InnerCompiledVerifierByPublicReading

set_option autoImplicit false

namespace OnBytes.Prover
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

section One
variable {I X : Type} {lam K : ℕ} {L : BatchProtocolWithLeafBody I X}

local notation "ON₂" => TypedOracleCompiler.Compile.Batch.OracleName

theorem no_askV (o : ON₂) (q : domOf lam L o)
    (h : o ≠ TypedOracleCompiler.Compile.Batch.OracleName.other) :
    (askTypedOracle (L := L) (K := K) o q).AsksIn (NotOther lam L) := ⟨h, fun _ => trivial⟩

theorem no_leavesO : ∀ l : List (LeafIn L),
    (leavesO (lam := lam) (K := K) l).AsksIn (NotOther lam L)
  | [] => trivial
  | _ :: xs =>
    asksIn_bind (no_askV _ _ (by intro h; cases h)) fun _ =>
      asksIn_bind (no_leavesO xs) fun _ => trivial

theorem no_pairUpO : ∀ l : List (Dig lam),
    (pairUp (hashTreeNode (K := K) (L := L)) l).AsksIn (NotOther lam L)
  | [] => trivial
  | [_] => trivial
  | _ :: _ :: l =>
    asksIn_bind (no_askV _ _ (by intro h; cases h)) fun _ =>
      asksIn_bind (no_pairUpO l) fun _ => trivial

theorem no_levelsO : ∀ (d : ℕ) (l : List (Dig lam)),
    (levelsM (hashTreeNode (K := K) (L := L)) d l).AsksIn (NotOther lam L)
  | 0, _ => trivial
  | d + 1, l => asksIn_bind (no_pairUpO l) fun u => asksIn_bind (no_levelsO d u) fun _ => trivial

theorem no_treeO (d : ℕ) (inp : ℕ → LeafIn L) :
    (treeO (lam := lam) (K := K) d inp).AsksIn (NotOther lam L) :=
  asksIn_bind (no_leavesO _) fun l => asksIn_bind (no_levelsO d l) fun _ => trivial

theorem no_treesO {r : Round} (pad : Body L) (sl : ℕ → ℕ → Bits)
    (posAt : ℕ → ℕ → Option r.Pos) (emb : (p : r.Pos) → r.Sym p → Body L) (o : r.Orc) :
    ∀ (k : ℕ) (ds : List ℕ),
      (treesO (lam := lam) (K := K) pad sl posAt emb o k ds).AsksIn (NotOther lam L)
  | _, [] => trivial
  | k, d :: ds =>
    asksIn_bind (no_treeO d _) fun _ =>
      asksIn_bind (no_treesO pad sl posAt emb o (k + 1) ds) fun _ => trivial

theorem no_climbO : ∀ (path : List (Dig lam)) (j : ℕ) (c : Dig lam),
    (climbM (rnodeV (K := K) (L := L)) path j c).AsksIn (NotOther lam L)
  | [], _, _ => trivial
  | s :: ss, j, c => by
    by_cases hb : j % 2 = 0
    · simp only [climbM, if_pos hb]
      exact asksIn_bind (no_askV _ _ (by intro h; cases h)) fun u => no_climbO ss _ u
    · simp only [climbM, if_neg hb]
      exact asksIn_bind (no_askV _ _ (by intro h; cases h)) fun u => no_climbO ss _ u

/-- The chain asks no point of the spare oracle. -/
theorem no_chainO (t : Tag) (cms : List (Dig lam)) (x : Option X) (co : Coins lam L)
    (cap : ℕ → ℕ) :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A) (embS : (p : OPos s) → OSym s p → Body L)
      (embP : PlainPart s A → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ) (ph : Phase lam) (σ : Strat s Unit),
      (chainO t cms x co cap s A W embS embP i ph σ).AsksIn (NotOther lam L)
  | [], _, _, _, _, _, _, _ => trivial
  | _ :: s, (a, A), (w, W), embS, embP, i, ph, (m, k) => by
    have hfb : ∀ q : FbIn lam L t, (askTypedOracle (L := L) (K := K) (OracleName.fb t) q).AsksIn (NotOther lam L) :=
      fun q => no_askV (OracleName.fb t) q (by intro h; cases h)
    simp only [chainO]
    generalize actOf cms (x.map L.early) co.salt a.kind ph = act
    cases act with
    | none => trivial
    | some ac =>
      cases ac with
      | one h own next =>
        cases own with
        | true =>
          exact asksIn_bind (no_treesO _ _ _ _ _ _ _) fun _ =>
            asksIn_bind (asksIn_fsO _ _ _ _ (fun _ => hfb _) _)
              (asksIn_onFs _ _ fun _ =>
                asksIn_bind (no_chainO t cms x co cap s A W _ _ _ _ _) fun _ => trivial)
        | false =>
          exact asksIn_bind (no_treesO _ _ _ _ _ _ _) fun _ =>
            asksIn_bind (asksIn_fsO _ _ _ _ (fun _ => hfb _) _)
              (asksIn_onFs _ _ fun _ =>
                asksIn_bind (no_chainO t cms x co cap s A W _ _ _ _ _) fun _ => trivial)
      | join ρ =>
        exact asksIn_bind (no_treesO _ _ _ _ _ _ _) fun _ =>
          asksIn_bind (no_treesO _ _ _ _ _ _ _) fun _ =>
          asksIn_bind (no_askV _ _ (by intro h; cases h)) fun _ =>
          asksIn_bind (no_askV _ _ (by intro h; cases h)) fun _ =>
          asksIn_bind (no_climbO _ _ _) fun _ =>
            asksIn_bind (asksIn_fsO _ _ _ _ (fun _ => hfb _) _)
              (asksIn_onFs _ _ fun _ =>
                asksIn_bind (no_chainO t cms x co cap s A W _ _ _ _ _) fun _ => trivial)

theorem no_proveX (t : Tag) {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E) (wq : ProtocolQueryLayout lam K Q)
    (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L)
    (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X)
    (cms : List (Dig lam)) (x : Y) (y : E.Str) (xt : ℕ → TreeK lam L)
    (σ : Strat Q.loc.shape Unit) (co : Coins lam L) (cap : ℕ → ℕ) :
    (proveX t Q wq embS embP xin cms x y xt σ co cap).AsksIn (NotOther lam L) :=
  asksIn_bind (no_chainO t cms (xin x) co cap _ _ _ _ _ _ _ _) fun _ => trivial

end One

variable {I X : Type} {lam : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
  {aL : RoundSplits L.link.shape} {Kap : Type}

variable (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL)
  (cA : L.OutOfDomainAnswer → List (Dig lam)) (r₀ : L.Rec) (p : Params) (b₀ : Bd) (st : Strats L Kap)
  (capT capL capB : ℕ → ℕ)

theorem no_committerTreeKeptByProver (y : Fin L.wordLength → L.Symbol) (salt : ℕ → Bits) :
    (committerTreeKeptByProver W b₀ y salt).AsksIn (NotOther lam (typedOracleCarrier L Bd aT aL)) := no_treeO _ _

theorem no_seedsO (cm : Dig lam) :
    (seedsO W S cm).AsksIn (NotOther lam (typedOracleCarrier L Bd aT aL)) :=
  ⟨(fun e => by cases e), fun _ => ⟨(fun e => by cases e), fun _ => trivial⟩⟩

theorem no_committerTreeRoot (y : Fin L.wordLength → L.Symbol) (salt : ℕ → Bits) :
    (committerTreeRoot W b₀ y salt).AsksIn (NotOther lam (typedOracleCarrier L Bd aT aL)) := by
  unfold committerTreeRoot
  rw [committerLeafHashes_eq]
  exact asksIn_bind (no_leavesO _) fun l => asksIn_bind (no_levelsO _ l) fun _ => trivial

theorem no_committerAtFixedCoins (i : I) (r : L.EncodingRandomness) (salt : ℕ → Bits) :
    (committerAtFixedCoins W S b₀ i r salt).AsksIn (NotOther lam (typedOracleCarrier L Bd aT aL)) :=
  asksIn_bind (no_committerTreeRoot W b₀ _ salt) fun _ =>
    ⟨(fun e => by cases e), fun _ => ⟨(fun e => by cases e), fun _ => trivial⟩⟩

theorem no_allY (isk : I × L.EncodingRandomness × (ℕ → Bits)) (x : X) (d : Draw lam L Bd aT aL Kap) :
    (allY W S cA r₀ b₀ st capT capL capB isk x d).AsksIn (NotOther lam (typedOracleCarrier L Bd aT aL)) :=
  asksIn_bind (no_committerTreeKeptByProver W b₀ _ _) fun _ => asksIn_bind (no_seedsO W S _) fun _ =>
    asksIn_bind (no_committerTreeKeptByProver W b₀ _ _) fun _ => asksIn_bind (no_seedsO W S _) fun _ =>
      asksIn_bind (no_proveX _ _ _ _ _ _ _ _ _ _ _ _ _) fun _ =>
        asksIn_bind (no_proveX _ _ _ _ _ _ _ _ _ _ _ _ _) fun _ =>
          asksIn_bind (no_proveX _ _ _ _ _ _ _ _ _ _ _ _ _) fun _ => trivial

theorem no_allX (isk : I × L.EncodingRandomness × (ℕ → Bits)) (x : X) (d : Draw lam L Bd aT aL Kap) :
    (allX W S cA r₀ b₀ st capT capL capB isk x d).AsksIn (NotOther lam (typedOracleCarrier L Bd aT aL)) :=
  asksIn_bind (no_allY W S cA r₀ b₀ st capT capL capB isk x d) fun _ => trivial

/-- Committer, prover and verifier behind all coins ask no point of the spare oracle. -/
theorem no_expAt (i : I) (r₁ : L.EncodingRandomness) (s₁ : ℕ → Bits) (x : X) (d : Draw lam L Bd aT aL Kap)
    (π₀ : OfflineLinkOnlineProof lam L aT aL) :
    (expAt W S cA r₀ p b₀ st capT capL capB i r₁ s₁ x d π₀).AsksIn
      (NotOther lam (typedOracleCarrier L Bd aT aL)) :=
  asksIn_bind (no_committerAtFixedCoins W S b₀ i r₁ s₁) fun k =>
    asksIn_bind (no_allX W S cA r₀ b₀ st capT capL capB k.2 x d) fun _ =>
      VerifiableInference.OnPublicFiles.asksIn_VRA W S cA r₀ p _ _ _

/-- **Over one hash function they ask no string that codes a point of the spare oracle.** -/
theorem hno_expAt (m : OracleCoding (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) lam) (i : I) (r₁ : L.EncodingRandomness)
    (s₁ : ℕ → Bits) (x : X) (d : Draw lam L Bd aT aL Kap) (π₀ : OfflineLinkOnlineProof lam L aT aL) :
    ((expAt W S cA r₀ p b₀ st capT capL capB i r₁ s₁ x d π₀).overOne m).AsksIn
      fun _ s => ¬ IsOther m s :=
  asksIn_overOne m (NotOther lam (typedOracleCarrier L Bd aT aL)) _
    (no_expAt W S cA r₀ p b₀ st capT capL capB i r₁ s₁ x d π₀)

end OnBytes.Prover
