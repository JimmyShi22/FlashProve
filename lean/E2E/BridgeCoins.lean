-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/BridgeCoins.lean: THE LAWS ON ALL COINS (`OnBytes.WholeKey.CoinsFit`,
Johnson/WholeKey/Premises.lean) AT THE LETTERS OF E2E/BridgeAtRecs.lean, WITH THE ENUMERATIONS AND
THE WINDOW CHOSEN: twelve of its nineteen clauses proved, seven left as plain sentences on lengths
and run values. General in the object, the wiring, the three provers.

  `needK`, `needJ`, **`withinWin_of_le`**: the trees of a list of rounds' wires lie within every
    window that is at least as wide as these two numbers.
  `canon W p c R₀`: the letters R₀ with: each enumeration of a finite type the library's
    `Enum.ofNum`; the tables' salts and the three kinds of run's coins of the form with a public
    start and free bits (`saltsPre`, `coinsPre`, Johnson/WholeKey/CoinLaws.lean); the window as wide
    as shapes and wires need.
  **`coinsFit_canon`**: `CoinsFit W p (atRecsOf hT hL Fm (canon W p c R₀) rvB pvB startB) c`.
    PROVED: the four enumerations list each member once; the law on the salts; the three laws on a
    run's coins; the three shapes and the three wires lie within the window. LEFT, as hypotheses
    (the three on a leaf's salt are asked at every round's number, where the structure asks them
    within the window): the public start of a table's salt has the right length; the run values that
    the three provers' coins give are of the right form; at such run values a leaf's salt has the
    length that the strict format asks (thrice).

Limits. THE CHOICE IS THIS FILE's: it shows that the laws can be met at any three provers, not that
a program samples so. The enumerations are classical (no program). No verifier reads enumerations or
window. THE SEVEN SENTENCES THAT ARE LEFT BEAR NO WEIGHT IN `PremW`: `okV`, the starts and `pre₀`
are the caller's letters: with every run value of the right form and constant starts of the right
length all seven can be met wherever `c.ℓ` is at most the strict format's length of a leaf's salt
(not typed here). THE TRUE STARTS ARE THE FORMAT's: `PremW` never asks that. c IS FREE, AND THE
ERROR OF THE STATEMENT OF INDEX PRIVACY READS `c.ℓ`, the number of free bits of a leaf's salt: where
ℓ is 0 the clauses hold (the salts are constant) and that error's term on the hash function is at
least 1: the statement then says nothing. Nothing on hiding, soundness or acceptance.


-/
import E2E.BridgeAtRecs

set_option autoImplicit false

noncomputable section

namespace AtPublicFiles.Bridge
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom Prob
open OnBytes.Prover OnBytes.WholeKey
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

/-! ## The window -/

section Window
variable {lam K : ℕ}

/-- The largest number of trees of a component in these rounds. -/
def needK : (s : Shape) → (A : RoundSplits s) → RoundsQueryLayout lam K s A → ℕ
  | [], _, _ => 0
  | _ :: s, (_, A), (w, W) => max (max w.depth0.length w.depthJ.length) (needK s A W)

/-- The largest number of leaves of a tree in a list of depths. -/
def leavesOf (ds : List ℕ) : ℕ := ds.foldr (fun d m => max (2 ^ d) m) 0

theorem le_leavesOf : ∀ (ds : List ℕ), ∀ d ∈ ds, 2 ^ d ≤ leavesOf ds
  | [], _, h => by cases h
  | e :: ds, d, h => by
      rcases List.mem_cons.1 h with rfl | h
      · exact le_max_left _ _
      · exact le_trans (le_leavesOf ds d h) (le_max_right _ _)

/-- The largest number of leaves of a tree in these rounds. -/
def needJ : (s : Shape) → (A : RoundSplits s) → RoundsQueryLayout lam K s A → ℕ
  | [], _, _ => 0
  | _ :: s, (_, A), (w, W) => max (max (leavesOf w.depth0) (leavesOf w.depthJ)) (needJ s A W)

/-- **All trees lie within every window that is at least so wide.** -/
theorem withinWin_of_le (nK nJ : ℕ) : ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A),
    needK s A W ≤ nK → needJ s A W ≤ nJ → WithinWin nK nJ s A W
  | [], _, _, _, _ => trivial
  | _ :: s, (_, A), (_, W), hK, hJ =>
      ⟨⟨le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hK,
          le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hK,
          fun d hd => le_trans (le_trans (le_trans (le_leavesOf _ d hd) (le_max_left _ _))
            (le_max_left _ _)) hJ,
          fun d hd => le_trans (le_trans (le_trans (le_leavesOf _ d hd) (le_max_right _ _))
            (le_max_left _ _)) hJ⟩,
        withinWin_of_le nK nJ s A W (le_trans (le_max_right _ _) hK)
          (le_trans (le_max_right _ _) hJ)⟩

end Window

variable {I X : Type} {L : HolographicProtocol I X} {lam : ℕ} {Bd : Type} {aT : RoundSplits L.offline.shape}
  {aL : RoundSplits L.link.shape}
  {hT : Honest L.offline (I × L.EncodingRandomness × L.OutOfDomainSeed)}
  {hL : Honest L.link (I × (L.EncodingRandomness × L.OutOfDomainSeed) × (L.EncodingRandomness × L.OutOfDomainSeed))}
  (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (p : Params) (c : CoinNums Bd)

/-- The enumeration of a finite, non-empty type. -/
def pickAll (β : Type) [Fintype β] [Nonempty β] : Enum β := Enum.ofNum β (Fintype.equivFin β)

theorem pickAll_ok (β : Type) [Fintype β] [Nonempty β] : (pickAll β).OK :=
  Enum.ofNum_ok β (Fintype.equivFin β)

/-- The window's three numbers. -/
def winR : ℕ := max (max L.offline.shape.length L.link.shape.length) L.onlineBatch.loc.shape.length

def winK : ℕ :=
  max (max (needK L.offline.shape aT (wTC W).sh) (needK L.link.shape aL (wLC W).sh))
    (needK L.onlineBatch.loc.shape L.onlineBatch.ann (wBC W).sh)

def winJ : ℕ :=
  max (max (needJ L.offline.shape aT (wTC W).sh) (needJ L.link.shape aL (wLC W).sh))
    (needJ L.onlineBatch.loc.shape L.onlineBatch.ann (wBC W).sh)

/-- **The letters R₀ with enumerations and window chosen.** -/
def canon (R₀ : RestOf lam Bd aT aL hT hL) : RestOf lam Bd aT aL hT hL :=
  { R₀ with
    nR := winR (L := L)
    nK := winK W
    nJ := winJ W
    ri := pickAll L.EncodingRandomness
    sl := saltsPre c.pre₀ (2 ^ W.depth) c.ℓ (pickAll _)
    kT := pickAll hT.Coin
    kL := pickAll hL.Coin
    coT := coinsPre (winR (L := L)) (winK W) (winJ W) p.sFS c.ℓ c.ℓr W.depthReqT c.padT c.slotT
      R₀.fill (pickAll _)
    coL := coinsPre (winR (L := L)) (winK W) (winJ W) p.sFS c.ℓ c.ℓr W.depthReqL c.padL c.slotL
      R₀.fill (pickAll _)
    coB := coinsPre (winR (L := L)) (winK W) (winJ W) p.sFS c.ℓ c.ℓr W.depthReq c.padB c.slotB
      R₀.fill (pickAll _) }

variable (Fm : Family L.onlineBatch.loc (I × L.EncodingRandomness × L.OutOfDomainSeed)) (R₀ : RestOf lam Bd aT aL hT hL)
  (rvB : Fm.Coin → R₀.RV) (pvB : Plains L.onlineBatch.loc.shape → R₀.RV)
  (startB : R₀.RV → ℕ → Bool → Bits → Bits)

/-- **The laws on all coins, at the chosen letters.** -/
theorem coinsFit_canon (hlen : c.pre₀.length + c.ℓ = p.sMT)
    (okT : ∀ κ, R₀.okV (R₀.rvT κ)) (okL : ∀ κ, R₀.okV (R₀.rvL κ)) (okB : ∀ κ, R₀.okV (rvB κ))
    (lenT : ∀ v i b s, R₀.okV v → s.length = p.sFS → (R₀.startT v i b s).length + c.ℓ = p.sMT)
    (lenL : ∀ v i b s, R₀.okV v → s.length = p.sFS → (R₀.startL v i b s).length + c.ℓ = p.sMT)
    (lenB : ∀ v i b s, R₀.okV v → s.length = p.sFS → (startB v i b s).length + c.ℓ = p.sMT) :
    CoinsFit W p (atRecsOf hT hL Fm (canon W p c R₀) rvB pvB startB) c where
  ri := pickAll_ok _
  kT := pickAll_ok _
  kL := pickAll_ok _
  kB := coinEnum_ok Fm
  sl := saltsLaw_saltsPre c.pre₀ (2 ^ W.depth) c.ℓ (pickAll _) (pickAll_ok _)
  len₀ := hlen
  okT := okT
  okL := okL
  okB := okB
  lenT := fun v i b s hv _ hs => lenT v i b s hv hs
  lenL := fun v i b s hv _ hs => lenL v i b s hv hs
  lenB := fun v i b s hv _ hs => lenB v i b s hv hs
  coT := runLaw_coinsPre _ _ _ _ _ _ _ _ _ _ (pickAll _) (pickAll_ok _)
  coL := runLaw_coinsPre _ _ _ _ _ _ _ _ _ _ (pickAll _) (pickAll_ok _)
  coB := runLaw_coinsPre _ _ _ _ _ _ _ _ _ _ (pickAll _) (pickAll_ok _)
  rounds := ⟨le_trans (le_max_left _ _) (le_max_left _ _),
    le_trans (le_max_right _ _) (le_max_left _ _), le_max_right _ _⟩
  winT := withinWin_of_le _ _ _ _ _ (le_trans (le_max_left _ _) (le_max_left _ _))
    (le_trans (le_max_left _ _) (le_max_left _ _))
  winL := withinWin_of_le _ _ _ _ _ (le_trans (le_max_right _ _) (le_max_left _ _))
    (le_trans (le_max_right _ _) (le_max_left _ _))
  winB := withinWin_of_le _ _ _ _ _ (le_max_right _ _) (le_max_right _ _)

end AtPublicFiles.Bridge

#print axioms AtPublicFiles.Bridge.le_leavesOf
#print axioms AtPublicFiles.Bridge.withinWin_of_le
#print axioms AtPublicFiles.Bridge.pickAll_ok
#print axioms AtPublicFiles.Bridge.coinsFit_canon
