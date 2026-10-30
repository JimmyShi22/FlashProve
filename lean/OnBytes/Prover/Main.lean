-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Prover/Main.lean: THE COMPILED PROVER's STRING IS ACCEPTED: under whatever oracle functions,
the proof string that the compiled prover of one slot returns (OnBytes/Prover/Defs.lean) gets the
yes of the compiled verifier of the second form (verifyOneProtocol, OnBytes/TypedOracleCompiler/Compile/Batch/Verifier.lean),
if the interactive verifier accepts the transcript that was hashed.

Main names:
  `proveX_ok_iff`   string and transcript are functions of the chain's value
  `yes_of_prove`    (T1) for all oracle functions g: whatever string the prover returns under g: all
                    tests are passed; the transcript beside it is the strategy's own run at these
                    verifier messages but for nonces; the string's plain parts are the transcript's;
                    and if the interactive verifier accepts THAT transcript at the true external
                    strings, verifyOneProtocol says yes to the string under g
  `noCoin_proveX`   (T2) the prover has no coins of its own
  `proveX_returns`, `proveX_mono`   (T3) at a formatted annotation it returns a string, or the
                    search of a round that has a test has run out; larger caps keep what smaller
                    caps have yielded

What is asked in T1, and who can pay. The laws of the wire record, that the decision is local, that
the annotation is coherent and formatted: as the theorems on soundness ask them. At most maxRt trees
a component. The coins' lengths (Coins.Fit). The outer trees kept rightly under g, with the roots
cms (ExtAt): owed by whoever writes the committer. That the interactive verifier accepts: owed by
the accept laws of the protocol's steps: T1 asks it at one transcript, at which all tests are
passed.

Limits. NO PROBABILITY: nothing says how likely it is that a search runs out, nor that the
interactive verifier accepts at verifier messages drawn from the oracles: no completeness error
follows from this file alone. The strategy is a letter: at a strategy that no program computes the
theorem holds and describes no program. A typed proof string: nothing on bytes. One slot. Tied to no
program.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.Prover.Returns
import OnBytes.Prover.Opened
import OnBytes.Prover.Walks
import OnBytes.Prover.Accept
import OnBytes.Prover.Yes

set_option autoImplicit false

noncomputable section

namespace OnBytes.Prover
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch Rom TypedOracleCompiler.Joined
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {I X : Type} {lam K : ℕ} {L : BatchProtocolWithLeafBody I X}

section
variable (sMT sFS : ℕ) (t : Tag) {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E)
  (wq : ProtocolQueryLayout lam K Q) (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L)
  (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X)
  (embE : E.Sym → Body L) (depthReq : ℕ) (cms : List (Dig lam)) (x : Y) (y : E.Str)
  (xt : ℕ → TreeK lam L) (σ : Strat Q.loc.shape Unit) (co : Coins lam L) (cap : ℕ → ℕ)

theorem det_proveX (g : Fam (typedOracleFamily lam K L)) :
    (proveX t Q wq embS embP xin cms x y xt σ co cap).det g =
      ((chainO t cms (xin x) co cap Q.loc.shape Q.ann wq.sh embS embP 0 .first σ).det g).map
        fun z => (finish Q wq x y xt co z, trK Q.loc.shape z.2.1 z.1) := by
  unfold proveX
  rw [OComp.det_bind]
  rfl

/-- String and transcript are functions of the chain's value. -/
theorem proveX_ok_iff (g : Fam (typedOracleFamily lam K L)) (π : OneProtocolProof lam Q) (τ : Tr Q.loc.shape) :
    (proveX t Q wq embS embP xin cms x y xt σ co cap).det g = .ok (π, τ) ↔
      ∃ z,
        (chainO t cms (xin x) co cap Q.loc.shape Q.ann wq.sh embS embP 0 .first σ).det g = .ok z ∧
        π = finish Q wq x y xt co z ∧ τ = trK Q.loc.shape z.2.1 z.1 := by
  rw [det_proveX]
  constructor
  · intro h
    obtain ⟨z, hz, he⟩ := Res.map_eq_ok h
    obtain ⟨h1, h2⟩ := Prod.mk.inj he
    exact ⟨z, hz, h1.symm, h2.symm⟩
  · rintro ⟨z, hz, rfl, rfl⟩
    rw [hz]
    rfl

/-- **(T1) The compiled prover's string is accepted.** -/
theorem yes_of_prove (g : Fam (typedOracleFamily lam K L)) (hw : wq.OKG) (hJ : FewJ Q.loc.shape Q.ann wq.sh)
    (h0 : Few0 Q.loc.shape Q.ann wq.sh) (hloc : Q.loc.IsLocal) (hC : Q.ann.Coherent)
    (hF : Q.ann.Fmt) (hDe : wq.ext.depth ≤ wq.maxDepth) (hfit : co.Fit sMT sFS depthReq)
    (hx : ExtAt g sMT wq.ext embE cms y xt) (π : OneProtocolProof lam Q) (τ : Tr Q.loc.shape)
    (hp : (proveX t Q wq embS embP xin cms x y xt σ co cap).det g = .ok (π, τ)) :
    RoundsQueryLayout.pass Q.loc.shape Q.ann wq.sh τ.rho = true ∧
      Puts Q.loc.shape Q.ann wq.sh (σ.run τ.rho).1 τ ∧
      π.plains = τ.plains ∧
      (Q.loc.accept x y τ = true →
        (verifyOneProtocol sMT sFS t Q wq embS embP xin embE depthReq cms x π).det g = true) := by
  obtain ⟨z, hz, rfl, rfl⟩ := (proveX_ok_iff t Q wq embS embP xin cms x y xt σ co cap g π τ).1 hp
  obtain ⟨R, hc⟩ := chain_at g sMT t cms (xin x) co cap hfit.leaf Q.loc.shape Q.ann wq.sh embS
    embP 0 .first σ z hz hF hJ h0 (z.2.2.2.getD fun _ => false) (fun r hr => by rw [hr]; rfl)
  rw [rho_trK]
  refine ⟨hc.pass, hc.puts, rfl, fun hacc => ?_⟩
  have heff := (mkTr_at g sMT Q.loc.shape Q.ann wq.sh embS z.2.1 R z.1 (fun _ =>
    true) hc.rounds hC hw.sh).1
  have hrd : rdS Q wq x (trK Q.loc.shape z.2.1 z.1).plains z.1 R =
      (haveI := wq.decO
       fun p => decide (p ∈ Q.loc.reads x z.1 (trK Q.loc.shape z.2.1 z.1).plains)) := by
    unfold rdS
    rw [heff]
  refine yes_of_parts sMT sFS t Q wq embS embP xin embE depthReq cms x g
    (finish Q wq x y xt co z) z.1 R z.2.2.1 hc.chain hw hfit.salt (le_of_eq hc.count.symm) hfit.slot
    ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro c hcs
    have hq := chain_req g t cms (xin x) co cap Q.loc.shape Q.ann wq.sh embS embP 0
      .first σ z c hz rfl hcs
    refine ⟨?_, ?_⟩
    · show (if z.2.2.1.slotVal.isSome then co.path else []).length = depthReq
      rw [hcs]
      exact hfit.path
    · show climbF (TypedOracleCompiler.Run.rnodeF g)
        (if z.2.2.1.slotVal.isSome then co.path else []) co.slot
        (g OracleName.rleaf (List.ofFn c ++ (if z.2.2.1.slotVal.isSome then co.rsalt else []) : Bits)) =
          z.2.2.2.getD fun _ => false
      rw [hcs, hq]
      rfl
  · intro hn
    refine ⟨?_, ?_⟩
    · show (if z.2.2.1.slotVal.isSome then co.path else []) = []
      rw [hn]
      rfl
    · show (if z.2.2.1.slotVal.isSome then co.rsalt else []) = []
      rw [hn]
      rfl
  · show Opened sMT Q.loc.shape Q.ann wq.sh R
      (rdS Q wq x (trK Q.loc.shape z.2.1 z.1).plains z.1 R) (opensK Q.loc.shape Q.ann wq.sh z.2.1 _)
    rw [hrd]
    exact opened_at g sMT Q.loc.shape Q.ann wq.sh embS z.2.1 R _ hc.rounds hw.sh
  · exact openedE_at g sMT wq.maxDepth E wq.ext embE cms y xt _ hx hDe
  · show ∀ Fs, forestsB Q.loc.shape Q.ann wq.sh embS R
      (rdS Q wq x (trK Q.loc.shape z.2.1 z.1).plains z.1 R)
      (opensK Q.loc.shape Q.ann wq.sh z.2.1 _) = some Fs → _
    rw [hrd]
    exact walks_at g sMT Q.loc.shape Q.ann wq.sh embS z.2.1 R _ hc.rounds hw.sh
  · exact walksE_at g sMT E wq.ext embE cms y xt _ hx
  · have := accept_at sMT Q wq embS x y xt g z.2.1 R z.1 hc.rounds hC hw hloc hacc
    rw [hrd] at this
    exact this

/-- **(T2) The prover has no coins of its own.** -/
theorem noCoin_proveX : (proveX t Q wq embS embP xin cms x y xt σ co cap).NoCoin :=
  OComp.NoCoin.bind (noCoin_chainO t cms (xin x) co cap _ _ _ _ _ _ _ _) fun _ => trivial

/-- **(T3) When the prover returns.** At a formatted annotation it returns a string, or the search
of a round that has a test has run out. -/
theorem proveX_returns (g : Fam (typedOracleFamily lam K L)) (hF : Q.ann.Fmt) :
    (∃ z, (proveX t Q wq embS embP xin cms x y xt σ co cap).det g = .ok z) ∨
      ∃ j, (proveX t Q wq embS embP xin cms x y xt σ co cap).det g = .ranOut j ∧
        hasTest Q.loc.shape Q.ann wq.sh j = true := by
  rw [det_proveX]
  cases h : (chainO t cms (xin x) co cap Q.loc.shape Q.ann wq.sh embS embP 0 .first σ).det g with
  | ok z => exact Or.inl ⟨_, rfl⟩
  | noFormat => exact absurd h (chain_format g t cms (xin x) co cap _ _ _ _ _ 0 .first σ hF)
  | ranOut j =>
    exact Or.inr ⟨j, rfl, (chain_ranOut g t cms (xin x) co cap _ _ _ _ _ 0 .first σ j h).2⟩

/-- Larger caps keep what smaller caps have yielded (cap ≤ cap': in every round). -/
theorem proveX_mono (g : Fam (typedOracleFamily lam K L)) (cap' : ℕ → ℕ) (z : OneProtocolProof lam Q × Tr Q.loc.shape)
    (h : (proveX t Q wq embS embP xin cms x y xt σ co cap).det g = .ok z) (hle : cap ≤ cap') :
    (proveX t Q wq embS embP xin cms x y xt σ co cap').det g = .ok z := by
  rw [det_proveX] at h ⊢
  obtain ⟨u, hu, rfl⟩ := Res.map_eq_ok h
  rw [chain_mono g t cms (xin x) co hle _ _ _ _ _ 0 .first σ u hu]
  rfl

end

end OnBytes.Prover
