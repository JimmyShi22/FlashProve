-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/All/ToyAll.lean: THE PREMISES OF THE THEOREMS ON THE PROVER OF A WHOLE REQUEST CAN BE
MET TOGETHER, AT AN OBJECT WHERE THE BOUND HAS TEETH: the small interface with records of
Johnson/TypedOracleCompiler/Joined/ToyArmsExt.lean (LRX, WRX, SRX): a word of two bits under a tree of depth 1; the
key's file and the proof's file three joined hash chains each; a link of one round with two trees; a
seed of one bit; THE KEY's INTERACTIVE VERIFIER REFUSES THE HONEST RECORD AT THE COLLISION SEED
(gT's text, there).

All premises of exp_law (Johnson/Prover/All/End.lean) and all_good (Johnson/Prover/All/Good.lean)
are proved there, for every index i and the instance (i, true), with Z₁ := the collision seeds, Z₂
and the three B's empty. So: committer, prover, verifier: the compiled verifier says no with
probability at most 1/2 (toy_law).

Main names (namespace OnBytes.Prover.ToyAll).
  wrx_okg, wiresFit, lawFit, drawFit, accAt, small   the premises, one by one.
  stX, dX, BsX   the strategies, what is drawn, the sets.
  alpha_eq    the sum of the bounds is 1/2.
  toy_law     exp_law, called.
  toy_good    all_good, called: under every g whose seed at the key's root is no collision seed the
    verifier says yes.

Limits. A toy: digests of one bit; no round has a test, so no search can run out and the three caps
are idle; the sets B are empty; the test of the copy's number accepts always, so that clause is met
idly; accAt stands at one written sample (dX) alone. It says nothing of any intended file. 1/2
is an upper bound here: that the COMPILED verifier does say no at a collision seed is not shown.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Prover.All.Good
import Johnson.TypedOracleCompiler.Joined.ToyArmsExt
import OnBytes.Prover.ToyFileAll

set_option autoImplicit false

noncomputable section

namespace OnBytes.Prover.ToyAll
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom Prob
open TypedOracleCompiler.Joined TypedOracleCompiler.Joined.Toy
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open OnBytes.Prover.ToyFileRun (σ₀)
open scoped ENNReal

/-! ## The wires, the marks, the three verifiers -/

theorem wrx_okg : WRX.OKG where
  T := ⟨V.sh_okg V_okg, we1X_ok, fun _ _ _ => Nat.zero_le _, V.sh_depthLe V_depthLe⟩
  Lk := ⟨⟨wA₁_okg, trivial⟩, we2X_ok, fun _ _ _ => Nat.zero_le _,
    ⟨⟨le_nil 1, le_one_zero⟩, trivial⟩⟩
  B := ⟨V.sh_okg V_okg, we1X_ok, fun _ _ _ => Nat.zero_le _, V.sh_depthLe V_depthLe⟩
  fits := le_rfl
  slots := rfl
  extDepth := ⟨rfl, rfl, rfl⟩
  depthT := le_rfl
  depthL := le_rfl
  depthB := le_rfl
  extT := fun _ => ⟨rfl, rfl⟩
  extB := fun _ => ⟨rfl, rfl⟩
  extL := ⟨fun _ => ⟨rfl, rfl⟩, fun _ => ⟨rfl, rfl⟩⟩
  prjE_emb := fun _ => rfl
  prjT_emb := fun _ _ => dif_pos rfl
  prjL_emb := fun _ _ => dif_pos rfl
  prjB_emb := fun _ _ => dif_pos rfl

theorem few6J : FewJ G.sh G.ann V.sh := by
  show _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ True
  exact ⟨by decide, by decide, by decide, by decide, by decide, by decide, trivial⟩

theorem few60 : Few0 G.sh G.ann V.sh := by
  show _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ True
  exact ⟨by decide, by decide, by decide, by decide, by decide, by decide, trivial⟩

theorem wiresFit : WiresFit WRX cAX where
  oka := ⟨wrx_okg, okgTX, okgLX, okgBX, ansOKX⟩
  fewT := ⟨few6J, few60⟩
  fewL := ⟨⟨by decide, trivial⟩, ⟨by decide, trivial⟩⟩
  fewB := ⟨few6J, few60⟩
  loc := ⟨isLocalTX, isLocalLkX, isLocalBX⟩
  coh := ⟨G.ann_coherent laws, BatchOne.BAnn.allLocal_coherent _, G.ann_coherent laws⟩
  fmt := ⟨G.ann_fmt laws, RoundSplits.fmt_allLocal _, G.ann_fmt laws⟩

theorem puts6 (cap : ℕ → ℕ) : PutsApart G.sh G.ann V.sh cap 0 := by
  show _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ True
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> intro g e <;> cases e

theorem lawFit (capT capL capB : ℕ → ℕ) : LawFit WRX SRX capT capL capB where
  offT := fun q _ => seedQ_other (W := WRX) (S := SRX) (by decide) q
  offL := fun q _ => seedQ_other (W := WRX) (S := SRX) (by decide) q
  offB := seedQ_off (W := WRX) (S := SRX) (seedsOff_of_depth rfl rfl)
  okT := okgTX
  okL := okgLX
  okB := okgBX
  fmt := ⟨G.ann_fmt laws, RoundSplits.fmt_allLocal _, G.ann_fmt laws⟩
  putsT := puts6 capT
  putsL := ⟨(fun g e => by cases e), trivial⟩
  putsB := puts6 capB

/-! ## Strategies, coins, sets -/

/-- the link's strategy: both bits true, the further bit false -/
def σL : Strat [rB] Unit := (((fun _ => true, false), ()), fun _ => ())

/-- The three strategies: the files' strings hold true everywhere. -/
def stX : Strats LRX Unit where
  T := fun _ _ _ _ => σ₀
  Lk := fun _ _ _ _ => σL
  B := fun _ _ _ _ _ _ => σ₀

/-- coins of a run whose request tree has depth 0 -/
def co0 : Coins 1 CX where
  salt := [true, false]
  leaf := fun i b k j => [(i + k + j + b.toNat) % 2 == 1]
  pad := .inr (.inr false)
  slot := 0
  path := []
  rsalt := [false, true, true]

/-- coins of the session: slot 1 of two -/
def co1 : Coins 1 CX := { co0 with slot := 1, path := [fun _ => true] }

def pX : Params := ⟨1, 2, 0, 0⟩

/-- what the prover draws -/
def dX : Draw 1 LRX BdX G.ann aLX Unit where
  r := ()
  s := fun j => [j % 2 == 0]
  n := 0
  κ := ()
  coT := co0
  coL := co0
  coB := co1

theorem drawFit : DrawFit WRX pX dX where
  s := fun _ _ => rfl
  T := ⟨rfl, fun _ _ _ _ => rfl, by decide, rfl⟩
  Lk := ⟨rfl, fun _ _ _ _ => rfl, by decide, rfl⟩
  B := ⟨rfl, fun _ _ _ _ => rfl, by decide, rfl⟩

/-- The sets: the collision seeds at the key; nothing else. -/
def BsX : Bads LRX where
  Z₁ := {s | coll0 s}
  Z₂ := ∅
  T := fun _ => ∅
  Lk := fun _ _ => ∅
  B := fun _ => ∅

theorem str_true (τ : Tr G.sh) (h : Puts G.sh G.ann V.sh (σ₀.run τ.rho).1 τ) :
    str₁ τ = fun _ => true := congrArg Prod.fst h.2.2.2.1

/-- **The accept laws**, at every index i and the instance (i, true). -/
theorem accAt (i : Bool) : AccAt WRX SRX stX i () (i, true) dX BsX where
  T := fun e₁ h1 τ _ hp _ => by
    have hc : e₁ 0 0 = false := by simpa [BsX, coll0] using h1
    show (gT (e₁, i) (fun _ => i) && str₁ τ _ && str₁ τ _) = true
    rw [str_true τ hp]
    simp [gT, hc]
  Lk := fun e₁ e₂ h1 _ τ _ hp _ => by
    have hc : e₁ 0 0 = false := by simpa [BsX, coll0] using h1
    have hs : τ.1.1 = (fun _ => true, false) := hp.1
    show (decide (linkLgX ((e₁, i), (e₂, i)) (fun _ => i, fun _ => i)) && τ.1.1.1 _) = true
    rw [hs]
    have hl : linkLgX ((e₁, i), (e₂, i)) (fun _ => i, fun _ => i) := by
      by_cases h2 : coll0 e₂
      · exact Or.inr (Or.inl h2)
      · have h2' : e₂ 0 0 = false := by simpa [coll0] using h2
        refine Or.inr (Or.inr ?_)
        simp [decX, gT, hc, h2']
    simp [hl]
  B := fun e₂ _ τ _ hp _ => by
    show (gB ((i, true), (e₂, i)) (fun _ => i) && str₁ τ _ && str₁ τ _) = true
    rw [str_true τ hp]
    simp [gB]
  num := fun _ _ _ => rfl

theorem small : SetsSmall WRX SRX BsX (1 / 2) 0 0 0 0 where
  z₁ := hSdX fun _ => false
  z₂ := by simp [BsX, pr]
  T := fun _ => by simp [BsX, pr]
  Lk := fun _ _ => by simp [BsX, pr]
  B := fun _ => by simp [BsX, pr]

theorem cap6 (cap : ℕ → ℕ) : capFail G.sh G.ann V.sh cap 0 = 0 := by
  show (0 : ℝ≥0∞) + (0 + (0 + (0 + (0 + (0 + 0))))) = 0
  simp

/-- The sum of the bounds is 1/2. -/
theorem alpha_eq (capT capL capB : ℕ → ℕ) :
    alphaAll WRX capT capL capB (1 / 2) 0 0 0 0 = 1 / 2 := by
  unfold alphaAll
  rw [show capFail LRX.offline.shape G.ann (wTC WRX).sh capT 0 = 0 from cap6 capT,
    show capFail LRX.onlineBatch.loc.shape LRX.onlineBatch.ann (wBC WRX).sh capB 0 = 0 from cap6 capB,
    show capFail LRX.link.shape aLX (wLC WRX).sh capL 0 = 0 from by
      show (0 : ℝ≥0∞) + 0 = 0
      simp]
  simp

/-! ## The theorems, called -/

/-- **exp_law, called**: committer, prover, verifier: the compiled verifier says no with probability
at most 1/2. -/
theorem toy_law (i : Bool) (r₀ : LRX.Rec) (capT capL capB : ℕ → ℕ) (π₀ : OfflineLinkOnlineProof 1 LRX G.ann aLX) :
    PrFrom (Table.empty _)
      (expAt WRX SRX cAX r₀ pX (.inr (.inr false)) stX capT capL capB i () (fun j => [j % 2 == 1])
        (i, true) dX π₀) {b | b = false} ≤ 1 / 2 := by
  rw [← alpha_eq capT capL capB]
  exact exp_law WRX SRX cAX r₀ pX _ stX capT capL capB (freshAll_empty WRX SRX)
    (lawFit capT capL capB) wiresFit i () _ (i, true) dX π₀ (fun _ _ => rfl) drawFit BsX (accAt i)
    small

theorem noTestL : ∀ j, hasTest [rB] aLX (wLC WRX).sh j = false
  | 0 => rfl
  | _ + 1 => rfl

/-- Where the seed at the key's root is no collision seed, what the runs yield lies outside the
event. -/
theorem toy_not_ev (g : Fam (typedOracleFamily 1 WRX.K CX)) (i : Bool) (r₀ : LRX.Rec) (capT capL capB : ℕ → ℕ)
    (s₁ : ℕ → Bits)
    (hs : ¬ coll0 (seedOfRoot WRX SRX g
      ((committerTreeKeptByProver WRX (.inr (.inr false)) (LRX.encodeIndex i ()) s₁).det g).root)) :
    (allY WRX SRX cAX r₀ (.inr (.inr false)) stX capT capL capB (i, (), s₁) (i, true) dX).det g ∉
      EvY BsX := by
  have hS := (allY_seeds WRX SRX cAX r₀ (.inr (.inr false)) stX capT capL capB g (i, (), s₁)
    (i, true) dX).1
  obtain ⟨rT, rL, rB⟩ := allY_ranOut WRX SRX cAX r₀ (.inr (.inr false)) stX capT capL capB g
    wiresFit (i, (), s₁) (i, true) dX
  generalize (allY WRX SRX cAX r₀ (.inr (.inr false)) stX capT capL capB (i, (), s₁) (i, true)
    dX).det g = Y at hS rT rL rB
  rintro (h | h | h | h | h)
  · exact hs (hS ▸ h)
  · exact h
  · rcases h with ⟨j, e⟩ | ⟨_, _, _, hb⟩
    · exact absurd ((ToyFileRun.noTest j).symm.trans (rT j e)) (by decide)
    · exact hb
  · rcases h with ⟨j, e⟩ | ⟨_, _, _, hb⟩
    · exact absurd ((noTestL j).symm.trans (rL j e)) (by decide)
    · exact hb
  · rcases h with ⟨j, e⟩ | ⟨_, _, _, hb⟩
    · exact absurd ((ToyFileRun.noTest j).symm.trans (rB j e)) (by decide)
    · exact hb

/-- **all_good, called**: under every g whose seed at the key's root is no collision seed the prover
returns a proof and the compiled verifier says yes to it at the committer's own key. -/
theorem toy_good (g : Fam (typedOracleFamily 1 WRX.K CX)) (i : Bool) (r₀ : LRX.Rec) (capT capL capB : ℕ → ℕ)
    (hs : ¬ coll0 (seedOfRoot WRX SRX g
      ((committerTreeKeptByProver WRX (.inr (.inr false)) (LRX.encodeIndex i ()) fun j => [j % 2 == 1]).det g).root)) :
    ∃ π z, (allX WRX SRX cAX r₀ (.inr (.inr false)) stX capT capL capB
        (i, (), fun j => [j % 2 == 1]) (i, true) dX).det g = .ok (π, z) ∧
      (verifyAtKeyRoot WRX SRX cAX r₀ pX
        ((committerAtFixedCoins WRX SRX (.inr (.inr false)) i () fun j => [j % 2 == 1]).det g).1 (i, true)
        π).det g = true := by
  obtain ⟨π, e₁, e₂, τT, τL, τB, hx, -, -, -, -, -, hy⟩ :=
    all_good WRX SRX cAX r₀ pX (.inr (.inr false)) stX capT capL capB g wiresFit i ()
      (fun j => [j % 2 == 1]) (i, true) dX (fun _ _ => rfl) drawFit BsX (accAt i)
      (toy_not_ev g i r₀ capT capL capB _ hs)
  exact ⟨π, _, hx, hy⟩

end OnBytes.Prover.ToyAll
