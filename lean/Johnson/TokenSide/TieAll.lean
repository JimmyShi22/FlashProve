-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/TokenSide/TieAll.lean: THE CHAIN OF THE TOKEN SIDE DOES WHAT THE COMPILED PROVER's CHAIN
DOES: ChainTie (Johnson/TokenSide/TieChain.lean) for every list of rounds. One theorem with its
proof.

A lemma of one step of a proof. This file states no goal of the release.

  chain_tie   by recursion on the rounds; in each round by the case of the token side's act: one
              Fiat-Shamir query on the slot's component (chain_own), on the shared one
              (chain_shared), the joining round (chain_join), or no format: then both sides stop.
  act_none    the case split of the two sides agrees where a round has no format.

Limits. All is said of the ERASED program (plainOf, Johnson/TokenSide/Erased.lean): tokens are
strings in a store, and the names fbw t k are written back to fb t. Nothing here speaks of these
names, or of the two modes of deferred programming (Rom/Defer.lean): they are the matter of
Johnson/HopSide/, Johnson/GhostSide/ and Compile/DeferRun/.
Terms: lean/GLOSSARY.md.

-/
import Johnson.TokenSide.TieOwn
import Johnson.TokenSide.TieShared
import Johnson.TokenSide.TieJoin

set_option autoImplicit false

noncomputable section

namespace OnBytes.TokenSide
open _root_.Compile hiding ON
open TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch Rom Prob OnBytes.Prover
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {I X : Type} {lam K : ℕ} {L : BatchProtocolWithLeafBody I X}
variable {Ω : Type} {μ : PMF Ω} {ℓ : ℕ} {Z : ℕ → Bool → ℕ → ℕ → Prop}

theorem act_none {cms : List (Dig lam)} {x : Option X} {salt : Tok} {kd : Kind} {ph : PhT}
    (h : actT cms x salt kd ph = none) (sv : Bits) (val : Tok → Bits) :
    actOf cms x sv kd (ph.val lam val) = none := by
  cases kd <;> cases ph <;> first | rfl | simp [actT] at h

/-- **The chain of the token side does what the compiled prover's chain does.** -/
theorem chain_tie (ll : LeafLens Ω μ ℓ Z) (t : Tag) (cms : List (Dig lam)) (x : Option X)
    (pre : ℕ → Bool → Bits → Bits) (salt : Tok) (cd : CoinsD lam L) (cap : ℕ → ℕ) :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A), ChainTie ll t cms x pre salt cd cap s A W
  | [], _, _ => fun _ _ _ _ _ vs _ _ _ =>
      .done ⟨List.prefix_rfl, fun z hz => by
        cases hz
        exact ⟨trivial, fun u hu => by cases hu⟩⟩ fun _ => rfl
  | r :: s, (a, A), (w, W) => fun embS embP i ph σ vs hs hph hc => by
    obtain ⟨m, k⟩ := σ
    have IH := chain_tie ll t cms x pre salt cd cap s A W
    cases h : actT cms (x.map L.early) salt a.kind ph with
    | none =>
      have eT : chainT t cms x ℓ pre salt cd cap (r :: s) (a, A) (w, W) embS embP i ph (m, k) =
          .pure .noFormat := by rw [chainT, h]
      have eO : ∀ ω, chainO t cms x (coOf ll (vs.getD salt []) cd pre ω) cap (r :: s) (a, A) (w, W)
          embS embP i (ph.val lam fun u => vs.getD u []) (m, k) = .pure .noFormat := by
        intro ω
        rw [chainO]
        show (match actOf cms (x.map L.early) (vs.getD salt []) a.kind
          (ph.val lam fun u => vs.getD u []) with
          | some (.one h true next) => _
          | some (.one h false next) => _
          | some (.join ρ) => _
          | none => _) = _
        rw [act_none h]
      rw [eT]
      exact .done ⟨List.prefix_rfl, fun z hz => by cases hz⟩ fun ω => by rw [eO]; rfl
    | some act =>
      cases act with
      | join tk =>
        exact chain_join ll t cms x pre salt cd cap a A w W IH embS embP i ph m k vs hs hph hc h
      | one tk us hd inj own next =>
        cases own with
        | true =>
          exact chain_own ll t cms x pre salt cd cap a A w W IH embS embP i ph m k vs hs hph hc h
        | false =>
          exact chain_shared ll t cms x pre salt cd cap a A w W IH embS embP i ph m k vs hs hph hc h

end OnBytes.TokenSide

#print axioms OnBytes.TokenSide.chain_tie
