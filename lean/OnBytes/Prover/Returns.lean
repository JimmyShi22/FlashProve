-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Prover/Returns.lean: WHEN the compiled prover's chain (OnBytes/Prover/Defs.lean) yields a
value, under fixed oracle functions; and that it has no coins.

Main names:
  `chain_format`   at a formatted annotation the outcome is never "no format"
  `chain_ranOut`   a search runs out only in a round that has a test
  `chain_mono`     what smaller caps yield, larger caps yield (round by round)
  `noCoin_chainO`  the chain has no coins (with the like for its parts)
With `search_none_iff` (OnBytes/Prover/Step.lean): at a formatted annotation the chain yields a
value unless, in some round number i with a test, every nonce from 0 to cap i fails.

Limits: nothing on probability: how likely it is that a search runs out is not said.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.Prover.Chain

set_option autoImplicit false

noncomputable section

namespace OnBytes.Prover
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch Rom TypedOracleCompiler.Joined
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {I X : Type} {lam K : ℕ} {L : BatchProtocolWithLeafBody I X}

/-! ## Outcomes -/

theorem Res.map_eq_noFormat {α β : Type} {f : α → β} {r : Res α} (h : r.map f = .noFormat) :
    r = .noFormat := by
  cases r with
  | ok a => cases h
  | noFormat => rfl
  | ranOut i => cases h

theorem Res.map_eq_ranOut {α β : Type} {f : α → β} {r : Res α} {j : ℕ} (h : r.map f = .ranOut j) :
    r = .ranOut j := by
  cases r with
  | ok a => cases h
  | noFormat => cases h
  | ranOut i => exact congrArg Res.ranOut (Res.ranOut.inj h)

theorem onFsF_eq_noFormat {P β : Type} {i : ℕ} {k : P × FsAns lam K → Res β}
    {o : Option (P × FsAns lam K)} (h : onFsF i k o = .noFormat) :
    ∃ p, o = some p ∧ k p = .noFormat := by
  cases o with
  | none => cases h
  | some p => exact ⟨p, rfl, h⟩

theorem onFsF_eq_ranOut {P β : Type} {i j : ℕ} {k : P × FsAns lam K → Res β}
    {o : Option (P × FsAns lam K)} (h : onFsF i k o = .ranOut j) :
    (o = none ∧ j = i) ∨ ∃ p, o = some p ∧ k p = .ranOut j := by
  cases o with
  | none => exact Or.inl ⟨rfl, (Res.ranOut.inj h).symm⟩
  | some p => exact Or.inr ⟨p, rfl, h⟩

section
variable (g : Fam (typedOracleFamily lam K L)) (t : Tag) (cms : List (Dig lam)) (x : Option X)
  (co : Coins lam L)

/-- **At a formatted annotation the outcome is never "no format".** -/
theorem chain_format (cap : ℕ → ℕ) : ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A)
    (embS : (p : OPos s) → OSym s p → Body L) (embP : PlainPart s A → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ)
    (ph : Phase lam) (σ : Strat s Unit), RoundSplits.FmtFrom s A (fph ph) →
    (chainO t cms x co cap s A W embS embP i ph σ).det g ≠ .noFormat
  | [], _, _, _, _, _, _, _, _, h => by cases h
  | _ :: s, (a, A), (w, W), embS, embP, i, ph, (m, k), hF, hz => by
    cases e : actOf cms (x.map L.early) co.salt a.kind ph with
    | none =>
      obtain ⟨hk, hp | hp⟩ := act_none e <;> simp only [RoundSplits.FmtFrom, hk, hp] at hF
    | some ac =>
      cases ac with
      | one h own next =>
        cases own with
        | true =>
          rw [det_own g t cms x co cap w W embS embP i ph m k e] at hz
          obtain ⟨q, -, hq⟩ := onFsF_eq_noFormat hz
          obtain ⟨hk, hn, -⟩ := act_own e
          simp only [RoundSplits.FmtFrom, hk] at hF
          exact chain_format cap s A W _ _ (i + 1) _ _ (by rw [hn]; exact hF.2)
            (Res.map_eq_noFormat hq)
        | false =>
          rw [det_shared g t cms x co cap w W embS embP i ph m k e] at hz
          obtain ⟨q, -, hq⟩ := onFsF_eq_noFormat hz
          obtain ⟨hk, hp, hn, -, -⟩ := act_shared e
          simp only [RoundSplits.FmtFrom, hk, hp] at hF
          exact chain_format cap s A W _ _ (i + 1) _ _ (by rw [hn]; exact hF.2)
            (Res.map_eq_noFormat hq)
      | join ρ =>
        rw [det_join g t cms x co cap w W embS embP i ph m k e] at hz
        obtain ⟨q, -, hq⟩ := onFsF_eq_noFormat hz
        obtain ⟨hk, rfl⟩ := act_join e
        simp only [RoundSplits.FmtFrom, hk, fph] at hF
        exact chain_format cap s A W _ _ (i + 1) (.shr _ _) _ hF (Res.map_eq_noFormat hq)

theorem hasTest_succ {r : Round} {s : Shape} {a : RAnn r} {A : RoundSplits s} {w : WireRB lam K r a}
    {W : RoundsQueryLayout lam K s A} {i j : ℕ} (h : i + 1 ≤ j ∧ hasTest s A W (j - (i + 1)) = true) :
    i ≤ j ∧ hasTest (r :: s) (a, A) (w, W) (j - i) = true := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨by omega, ?_⟩
  rw [show j - i = (j - (i + 1)) + 1 by omega]
  exact h2

/-- **A search runs out only in a round that has a test.** -/
theorem chain_ranOut (cap : ℕ → ℕ) : ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A)
    (embS : (p : OPos s) → OSym s p → Body L) (embP : PlainPart s A → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ)
    (ph : Phase lam) (σ : Strat s Unit) (j : ℕ),
    (chainO t cms x co cap s A W embS embP i ph σ).det g = .ranOut j →
    i ≤ j ∧ hasTest s A W (j - i) = true
  | [], _, _, _, _, _, _, _, _, h => by cases h
  | _ :: s, (a, A), (w, W), embS, embP, i, ph, (m, k), j, hz => by
    cases e : actOf cms (x.map L.early) co.salt a.kind ph with
    | none =>
      rw [det_noFormat g t cms x co cap w W embS embP i ph m k e] at hz
      cases hz
    | some ac =>
      cases ac with
      | one h own next =>
        cases own with
        | true =>
          rw [det_own g t cms x co cap w W embS embP i ph m k e] at hz
          rcases onFsF_eq_ranOut hz with ⟨ho, rfl⟩ | ⟨q, -, hq⟩
          · refine ⟨le_refl _, ?_⟩
            rw [Nat.sub_self]
            simp only [hasTest, (act_own e).1]
            exact fs_none g _ _ _ _ _ ho
          · exact hasTest_succ (chain_ranOut cap s A W _ _ (i + 1) _ _ j (Res.map_eq_ranOut hq))
        | false =>
          rw [det_shared g t cms x co cap w W embS embP i ph m k e] at hz
          rcases onFsF_eq_ranOut hz with ⟨ho, rfl⟩ | ⟨q, -, hq⟩
          · refine ⟨le_refl _, ?_⟩
            rw [Nat.sub_self]
            simp only [hasTest, (act_shared e).1]
            exact fs_none g _ _ _ _ _ ho
          · exact hasTest_succ (chain_ranOut cap s A W _ _ (i + 1) _ _ j (Res.map_eq_ranOut hq))
      | join ρ =>
        rw [det_join g t cms x co cap w W embS embP i ph m k e] at hz
        rcases onFsF_eq_ranOut hz with ⟨ho, rfl⟩ | ⟨q, -, hq⟩
        · refine ⟨le_refl _, ?_⟩
          rw [Nat.sub_self]
          simp only [hasTest, (act_join e).1]
          exact fs_none g _ _ _ _ _ ho
        · exact hasTest_succ (chain_ranOut cap s A W _ _ (i + 1) _ _ j (Res.map_eq_ranOut hq))

/-- **What smaller caps yield, larger caps yield** (cap ≤ cap': in every round). -/
theorem chain_mono {cap cap' : ℕ → ℕ} (hle : cap ≤ cap') : ∀ (s : Shape) (A : RoundSplits s)
    (W : RoundsQueryLayout lam K s A) (embS : (p : OPos s) → OSym s p → Body L)
    (embP : PlainPart s A → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ) (ph : Phase lam) (σ : Strat s Unit)
    (z : OutP lam L s), (chainO t cms x co cap s A W embS embP i ph σ).det g = .ok z →
    (chainO t cms x co cap' s A W embS embP i ph σ).det g = .ok z
  | [], _, _, _, _, _, _, _, _, h => h
  | _ :: s, (a, A), (w, W), embS, embP, i, ph, (m, k), z, hz => by
    cases e : actOf cms (x.map L.early) co.salt a.kind ph with
    | none =>
      rw [det_noFormat g t cms x co cap w W embS embP i ph m k e] at hz
      cases hz
    | some ac =>
      cases ac with
      | one h own next =>
        cases own with
        | true =>
          rw [det_own g t cms x co cap w W embS embP i ph m k e] at hz
          obtain ⟨q, hq, hq'⟩ := onFsF_eq_ok hz
          obtain ⟨z', hz', rfl⟩ := Res.map_eq_ok hq'
          rw [det_own g t cms x co cap' w W embS embP i ph m k e, fs_mono g _ _ _ _ _ (hle i) hq]
          show (rest g t cms x co cap' W embS embP i k _ _).map _ = _
          rw [show rest g t cms x co cap' W embS embP i k (next (List.ofFn q.2.2)) (w.chal q.2.1) =
            .ok z' from chain_mono hle s A W _ _ (i + 1) _ _ z' hz']
          rfl
        | false =>
          rw [det_shared g t cms x co cap w W embS embP i ph m k e] at hz
          obtain ⟨q, hq, hq'⟩ := onFsF_eq_ok hz
          obtain ⟨z', hz', rfl⟩ := Res.map_eq_ok hq'
          rw [det_shared g t cms x co cap' w W embS embP i ph m k e, fs_mono g _ _ _ _ _ (hle i) hq]
          show (rest g t cms x co cap' W embS embP i k _ _).map _ = _
          rw [show rest g t cms x co cap' W embS embP i k (next (List.ofFn q.2.2)) (w.chal q.2.1) =
            .ok z' from chain_mono hle s A W _ _ (i + 1) _ _ z' hz']
          rfl
      | join ρ =>
        rw [det_join g t cms x co cap w W embS embP i ph m k e] at hz
        obtain ⟨q, hq, hq'⟩ := onFsF_eq_ok hz
        obtain ⟨z', hz', rfl⟩ := Res.map_eq_ok hq'
        rw [det_join g t cms x co cap' w W embS embP i ph m k e, fs_mono g _ _ _ _ _ (hle i) hq]
        show (rest g t cms x co cap' W embS embP i k _ _).map _ = _
        rw [show rest g t cms x co cap' W embS embP i k
            (.shr (List.ofFn q.2.2) (slotV g t co w embS embP i m ρ)) (w.chal q.2.1) =
          .ok z' from chain_mono hle s A W _ _ (i + 1) _ _ z' hz']
        rfl

end

/-! ## No coins -/

theorem noCoin_pairUpO : ∀ l : List (Dig lam), (pairUp (hashTreeNode (K := K) (L := L)) l).NoCoin
  | [] => trivial
  | [_] => trivial
  | _ :: _ :: l =>
    OComp.NoCoin.bind (noCoin_askV _ _) fun _ =>
      OComp.NoCoin.bind (noCoin_pairUpO l) fun _ => trivial

theorem noCoin_levelsO : ∀ (d : ℕ) (l : List (Dig lam)),
    (levelsM (hashTreeNode (K := K) (L := L)) d l).NoCoin
  | 0, _ => trivial
  | d + 1, l =>
    OComp.NoCoin.bind (noCoin_pairUpO l) fun u =>
      OComp.NoCoin.bind (noCoin_levelsO d u) fun _ => trivial

theorem noCoin_treeO (d : ℕ) (inp : ℕ → LeafIn L) : (treeO (lam := lam) (K := K) d inp).NoCoin :=
  OComp.NoCoin.bind (noCoin_leavesO _) fun l =>
    OComp.NoCoin.bind (noCoin_levelsO d l) fun _ => trivial

theorem noCoin_treesO {r : Round} (pad : Body L) (sl : ℕ → ℕ → Bits)
    (posAt : ℕ → ℕ → Option r.Pos) (emb : (p : r.Pos) → r.Sym p → Body L) (o : r.Orc) :
    ∀ (k : ℕ) (ds : List ℕ), (treesO (lam := lam) (K := K) pad sl posAt emb o k ds).NoCoin
  | _, [] => trivial
  | k, d :: ds =>
    OComp.NoCoin.bind (noCoin_treeO d _) fun _ =>
      OComp.NoCoin.bind (noCoin_treesO pad sl posAt emb o (k + 1) ds) fun _ => trivial

theorem noCoin_climbO : ∀ (path : List (Dig lam)) (j : ℕ) (c : Dig lam),
    (climbM (rnodeV (K := K) (L := L)) path j c).NoCoin
  | [], _, _ => trivial
  | s :: ss, j, c => by
    by_cases hb : j % 2 = 0
    · simp only [climbM, if_pos hb]
      exact OComp.NoCoin.bind (noCoin_askV _ _) fun u => noCoin_climbO ss _ u
    · simp only [climbM, if_neg hb]
      exact OComp.NoCoin.bind (noCoin_askV _ _) fun u => noCoin_climbO ss _ u

theorem noCoin_searchO {C P : Type} (gr : GrW C P) (chal : (Fin K → Dig lam) → C)
    (ask : P → TypedOracleComputation lam K L (FsAns lam K)) (hask : ∀ β, (ask β).NoCoin) (α : P) :
    ∀ fuel n : ℕ, (searchO gr chal ask α fuel n).NoCoin
  | 0, _ => trivial
  | fuel + 1, n =>
    OComp.NoCoin.bind (hask _) fun a => by
      by_cases hk : gr.ok (chal a.1) = true
      · rw [if_pos hk]
        trivial
      · rw [if_neg hk]
        exact noCoin_searchO gr chal ask hask α fuel (n + 1)

theorem noCoin_fsO {C P : Type} (gr : Option (GrW C P)) (cap : ℕ) (chal : (Fin K → Dig lam) → C)
    (ask : P → TypedOracleComputation lam K L (FsAns lam K)) (hask : ∀ β, (ask β).NoCoin) (α : P) :
    (fsO gr cap chal ask α).NoCoin := by
  cases gr with
  | none => exact OComp.NoCoin.bind (hask _) fun _ => trivial
  | some q => exact noCoin_searchO q chal ask hask α _ _

theorem noCoin_onFs {P β : Type} (i : ℕ) (k : P × FsAns lam K → TypedOracleComputation lam K L (Res β))
    (hk : ∀ p, (k p).NoCoin) : ∀ o, (onFs i k o).NoCoin
  | none => trivial
  | some p => hk p

/-- **The chain has no coins.** -/
theorem noCoin_chainO (t : Tag) (cms : List (Dig lam)) (x : Option X) (co : Coins lam L)
    (cap : ℕ → ℕ) :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A) (embS : (p : OPos s) → OSym s p → Body L)
      (embP : PlainPart s A → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ) (ph : Phase lam) (σ : Strat s Unit),
      (chainO t cms x co cap s A W embS embP i ph σ).NoCoin
  | [], _, _, _, _, _, _, _ => trivial
  | _ :: s, (a, A), (w, W), embS, embP, i, ph, (m, k) => by
    simp only [chainO]
    generalize actOf cms (x.map L.early) co.salt a.kind ph = act
    cases act with
    | none => trivial
    | some ac =>
      cases ac with
      | one h own next =>
        cases own with
        | true =>
          exact OComp.NoCoin.bind (noCoin_treesO _ _ _ _ _ _ _) fun _ =>
            OComp.NoCoin.bind (noCoin_fsO _ _ _ _ (fun _ => noCoin_askV _ _) _)
              (noCoin_onFs _ _ fun _ =>
                OComp.NoCoin.bind (noCoin_chainO t cms x co cap s A W _ _ _ _ _) fun _ => trivial)
        | false =>
          exact OComp.NoCoin.bind (noCoin_treesO _ _ _ _ _ _ _) fun _ =>
            OComp.NoCoin.bind (noCoin_fsO _ _ _ _ (fun _ => noCoin_askV _ _) _)
              (noCoin_onFs _ _ fun _ =>
                OComp.NoCoin.bind (noCoin_chainO t cms x co cap s A W _ _ _ _ _) fun _ => trivial)
      | join ρ =>
        exact OComp.NoCoin.bind (noCoin_treesO _ _ _ _ _ _ _) fun _ =>
          OComp.NoCoin.bind (noCoin_treesO _ _ _ _ _ _ _) fun _ =>
          OComp.NoCoin.bind (noCoin_askV _ _) fun _ =>
          OComp.NoCoin.bind (noCoin_askV _ _) fun _ =>
          OComp.NoCoin.bind (noCoin_climbO _ _ _) fun _ =>
            OComp.NoCoin.bind (noCoin_fsO _ _ _ _ (fun _ => noCoin_askV _ _) _)
              (noCoin_onFs _ _ fun _ =>
                OComp.NoCoin.bind (noCoin_chainO t cms x co cap s A W _ _ _ _ _) fun _ => trivial)

end OnBytes.Prover
