-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/Law/LaysT.lean: THE KIND K1's MEMBER AT THE READS OF THE HEAD's
SEGMENT LAYS THE CLAUSE "t is there" OF A THREAD's LETTER rides: LaysAt and LaysAtS
(Johnson/Desc/ProofFile/Honest/Thread/Riders.lean,
Johnson/Desc/ProofFile/Honest/Thread/SharesS.lean) at riderHead lo hi (fun o => o.t.isSome = true),
general in the thread T, in Said and in lo and hi. Statements and proofs, over
Johnson/Desc/ProofFile/Honest/K1/Law/ReadsHead.lean.

  k1_lays_t: where the thread's member number b is the lot's sub-protocol at the reads of a link
    that is neither of kind 0 nor of kind 1, seated alone (IM.LaidAlone, Johnson/IMR/SeatForm.lean):
    LaysAt T b (riderHead lo hi …). FROM THE MEMBER's ACCEPTING STEP ALONE: neither the thread in
    front nor the test on the challenges is spent.
  k1_laysS_t: the same from the pair of the thread and what is said: by laysAtS_of.

Not shown here. The premise "member": which sub-protocol stands at the thread's number b: it is the
thread's maker's (for files in scope the first chain's flat list has that member at number 342: by
IM.k1_reads_of (Johnson/IMR/K1Scope.lean), IM.hear_at_flat (Johnson/IMR/FlatIx.lean) and
IM.flatIx_scope (Johnson/IMR/FlatScope.lean), as the proof of k1_reads_342
(Johnson/Desc/ProofFile/Honest/K1/Law/ReadsHead.lean) joins them; no statement of its own says it).
That the member accepts anywhere. Which lo and hi are laid. Nothing on soundness, on completeness or
on any other property.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.K1.Law.ReadsHead
import Johnson.Desc.ProofFile.Honest.Thread.SharesS
import Johnson.Desc.ProofFile.Honest.Thread.Riders

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Place)
open VerifiableInference.Desc.First (S)
open OnBytes.Model.Stages (LinkH)

variable {V W X Pb : Type} {Bk : ProverCoinCounts} (T : Thread Bk S ProofFile.Cl V W X Pb)

/-- **THE MEMBER LAYS THE CLAUSE "t is there"**, from its accepting step alone. -/
theorem k1_lays_t (b lo hi : Nat) {Z : ProofFile.Pub} {G : ProofFile.Ground} {l : Nat} {Xl : LinkH} {pr : Nat}
    {reads : Option (List Nat)}
    (member : ∀ blk, T.bs[b]? = some blk → ∃ same name a,
      IM.LaidAlone same blk (IM.k1Reads Z G l Xl pr reads).retype name a)
    (hb : G.built[l]? = some Xl) (h0 : Xl.kind ≠ 0) (h1 : Xl.kind ≠ 1) :
    LaysAt T b (riderHead lo hi fun o => o.t.isSome = true) := by
  intro blk hblk k s m E ds y cols s' _ _ hS
  obtain ⟨same, name, a, hla⟩ := member blk hblk
  obtain ⟨-, -, -, d⟩ := VerifiableInference.Desc.step_inv T.ft _ s s' _ cols _ hS.2
  have d' : (IM.k1Reads Z G l Xl pr reads).decide s _ _ = .ok s' := (IM.alone_noMark hla d).1
  exact k1_reads_head_t hb h0 h1 d'

/-- The same from the pair of the thread and what is said. -/
theorem k1_laysS_t (Said : Nat → Coins Bk → Mid W X → Prop) (b lo hi : Nat) {Z : ProofFile.Pub}
    {G : ProofFile.Ground} {l : Nat} {Xl : LinkH} {pr : Nat} {reads : Option (List Nat)}
    (member : ∀ blk, T.bs[b]? = some blk → ∃ same name a,
      IM.LaidAlone same blk (IM.k1Reads Z G l Xl pr reads).retype name a)
    (hb : G.built[l]? = some Xl) (h0 : Xl.kind ≠ 0) (h1 : Xl.kind ≠ 1) :
    LaysAtS T Said b (riderHead lo hi fun o => o.t.isSome = true) :=
  laysAtS_of T Said (k1_lays_t T b lo hi member hb h0 h1)

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.k1_lays_t
#print axioms ProofFile.Honest.K1.k1_laysS_t
