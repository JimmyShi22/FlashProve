-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/OfflineFirstFamilyAtTerm.lean: THE VALUE OF THE JOIN'S LETTER U₁. `TheLots` (E2E/OfflineJoin.lean) takes the first chain's family
of threads as a letter; the laws on the test on the ranges speak at the first chain's own thread `Th`
(E2E/FirstHSeat.lean). Here the family that is `Th` at the offline prover's own senders and the index's reader is
named, typed as the join types its letter, and what a member of `ThreadsP` says at it is projected.

  `firstFamilyAt Q`     the family: at an input (w₀, rc, seed) and an instance x: `Th` at the description's three parts, the
                        offline prover's senders, the index's reader, Q, w₀, rc, x. Q: the filling's letter, free
  `firstFamilyAt_eq`    by unfolding
  `thr_of_first`        where a member of `ThreadsP` has as its first family of invariants the pair of a thread's sentence and
                        a letter, its invariant at a border gives the thread's sentence there. General
  `thr_at_term`         the same at `firstFamilyAt Q`: the sentence of `Th`
  `firstPublic_at_term` `FirstPublic` at these senders and this reader, in scope (E2E/LotFirstPublicAtValue.lean)

Definitions, unfoldings and one call. No thread is shown to stand at any border. Nothing on any property.
-/
import E2E.OfflineJoin
import E2E.LotFirstPublicAtValue
import Johnson.Desc.ProofFile.Honest.Law.OwedParts

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtPublicFiles.OfflineRows
open ProofFile.Honest
open VerifiableInference.Desc (FileDescription)
open VerifiableInference.Desc.Key (Xi)
open AtPublicFiles.KeyBook (KeyPub keyBook)
open AtPublicFiles.KeyStandWalked (offlineValue)
open AtPublicFiles.FirstH (Th LaterFill FirstPublic)
open AtPublicFiles.AtFiles (KeySourced FullSizeMatrix protocolAtFiles)
open AtPublicFiles.AtFiles.HonestTerm (OfflineDescription matrixReader FirstFamily)
open VerifierAndGoals (PublicFiles InScope)

/-- **Where the first family of invariants is a thread's sentence together with a letter, the invariant gives the
sentence.** -/
theorem thr_of_first {W₀ Rc Xi' Ky Tr X₀ X : Type} {Bk : ProverCoinCounts} {F : FileDescription Xi'}
    {H : Prover W₀ Rc Xi' Ky Tr X₀ X} {w₀ : W₀} {rc : Rc} {x : Xi'} {k : Coins Bk}
    {R : Ready W₀ Rc Xi' Ky Tr X₀ X} (T : ThreadsP F Bk H w₀ rc x k R)
    {U : Thread Bk F.S₁ F.Cl (Local W₀ Rc Xi' Tr) (Local W₀ Rc Xi' Tr) X Xi'}
    {S : Nat → Coins Bk → Mid (Local W₀ Rc Xi' Tr) X → Prop} (h : T.I₁ = ThrS U S) (b : Nat)
    (k' : Coins Bk) (s : F.S₁) (m : Mid (Local W₀ Rc Xi' Tr) X) (E : Env)
    (hI : T.I₁ b k' s m E) : Thr U b k' s m E := by
  rw [h] at hI
  exact hI.1

variable {Z : PublicFiles} (d : OfflineDescription) {K₀ : KeyPub}

/-- **The first chain's own thread as the join's family.** -/
abbrev firstFamilyAt (Q : LaterFill (keyBook K₀) FullSizeMatrix (protocolAtFiles Z).EncodingRandomness) : FirstFamily Z d (keyBook K₀) :=
  fun w x => Th d.source d.numbers d.later (offlineValue (files := Z) d) matrixReader Q w.1 w.2.1 x

/-- By unfolding. -/
theorem firstFamilyAt_eq (Q : LaterFill (keyBook K₀) FullSizeMatrix (protocolAtFiles Z).EncodingRandomness) (w₀ : FullSizeMatrix) (rc : (protocolAtFiles Z).EncodingRandomness)
    (e : (protocolAtFiles Z).OutOfDomainSeed) (x : Xi) :
    firstFamilyAt d Q (w₀, rc, e) x =
      Th d.source d.numbers d.later (offlineValue (files := Z) d) matrixReader Q w₀ rc x := rfl

/-- **At that family the invariant gives the sentence of `Th`.** -/
theorem thr_at_term (Q : LaterFill (keyBook K₀) FullSizeMatrix (protocolAtFiles Z).EncodingRandomness)
    {H : Prover FullSizeMatrix (protocolAtFiles Z).EncodingRandomness Xi OnBytes.TableKey Unit Unit Unit} {w₀ : FullSizeMatrix} {rc : (protocolAtFiles Z).EncodingRandomness} {x : Xi}
    {k : Coins (keyBook K₀)} {R : Ready FullSizeMatrix (protocolAtFiles Z).EncodingRandomness Xi OnBytes.TableKey Unit Unit Unit}
    (T : ThreadsP (AtPublicFiles.AtFiles.keyFileDescription d.source d.numbers d.later) (keyBook K₀) H w₀ rc x k R)
    {S : Nat → Coins (keyBook K₀) → Mid (Local FullSizeMatrix (protocolAtFiles Z).EncodingRandomness Xi Unit) Unit → Prop} (e : (protocolAtFiles Z).OutOfDomainSeed)
    (h : T.I₁ = ThrS (firstFamilyAt d Q (w₀, rc, e) x) S) (b : Nat) (k' : Coins (keyBook K₀))
    (s : (AtPublicFiles.AtFiles.keyFileDescription d.source d.numbers d.later).S₁)
    (m : Mid (Local FullSizeMatrix (protocolAtFiles Z).EncodingRandomness Xi Unit) Unit) (E : Env) (hI : T.I₁ b k' s m E) :
    Thr (Th d.source d.numbers d.later (offlineValue (files := Z) d) matrixReader Q w₀ rc x) b k' s m
      E :=
  thr_of_first T h b k' s m E hI

/-- **`FirstPublic` at the offline prover's senders and the index's reader**, in scope. -/
theorem firstPublic_at_term (hs : KeySourced Z d.source d.numbers d.later)
    (scope : InScope Z = true) :
    FirstPublic (Pl := d.later) d.source d.numbers (offlineValue (files := Z) d) matrixReader :=
  AtPublicFiles.FirstH.Lots.firstPublic_atValue hs scope

end AtPublicFiles.OfflineRows

#print axioms AtPublicFiles.OfflineRows.thr_of_first
#print axioms AtPublicFiles.OfflineRows.firstFamilyAt_eq
#print axioms AtPublicFiles.OfflineRows.thr_at_term
#print axioms AtPublicFiles.OfflineRows.firstPublic_at_term
