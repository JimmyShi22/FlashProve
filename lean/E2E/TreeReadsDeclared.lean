-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/TreeReadsDeclared.lean: the property `FileWithin` (E2E/TreeReads.lean) said of the DECLARED
ROUNDS of an IOP as written in Lean (`FileDescription.roundsDeclaredByBlocks`, Johnson/Desc/Block.lean; below: a
description), where the other files of this group say it of the rounds' data that are made of them;
and so at the proof file's description from which `VerifierAndGoals.verify` is compiled. Definitions,
statements and proofs.

Why. Whoever follows a run of a description's sub-protocols reads the declared rounds: each names a
tree that it opens by its source: the chain's own n-th tree, or the k-th tree of an earlier chain
(`Fmt.TreeSource`). The rounds' data name a tree by one number over the file. The library ties the two
(`numAt`, Johnson/Desc/BlockSlot.lean; `opensOfData`, Johnson/Desc/BlockSlotOpens.lean;
`roundsOfData`, Johnson/Desc/Sound/DataRounds.lean; `counts_of_data`,
Johnson/Desc/Sound/TakenBelowOfData.lean). Here these are put together for the counts.

What is defined.
  `treeNo F ch n`: the number over the file of the n-th tree that the chain number ch (from 0)
    sends.
  `declPairs`, `declOpens F`: what the declared rounds of F open, each tree by that number. THE
    FIRST CHAIN'S LAST DECLARED ROUND, in which the transcript's final digest is taken, IS LEFT OUT,
    as in the rounds' data.
What is shown.
  `numAt_own`, `numAt_taken`: a source's number is `treeNo` of its sender and its number there.
  **`opens_of_data`**: where `F.data file = .ok D`: `opensOf D = declOpens F`.
  `seal_poss`, **`readsOn_first_whole`**: there the round that is left out samples no position; so
    the first chain's declared rounds, taken whole, read every tree as often as `declOpens F` says.
  **`declared_atFiles`**: in scope, with the gate open, for every public part Zp that `P5J.LaidAt`
    ties to the object: `FileWithin (declOpens F) slots … 98 proofSlack` at F := the proof file's
    description made of Zp (`F0T`), with the table and the number of requests of
    E2E/TreeReadsAtFiles.lean.

For whoever counts what a run asks of a tree. If the positions that ONE request's run asks of the
n-th tree of the chain ch lie in the union, over the declared rounds that open it, of these rounds'
sampled positions, and no round's list is longer than its entry says, then they are at most
`(declOpens F).inBatch 1 (treeNo F ch n)`. By `inBatch_mono` that is at most `inBatch` at the sizes'
number of requests, which `Within.le` bounds by r of each row beneath. That first half is not shown
here.

What still lies between.
- THE UNION OVER THE REQUESTS OF A BATCH. One request's run reads a tree of the second chain at its
  own share alone (Omega's tree: 51 + 55 of the 3571). That all requests of a batch together stay
  within r is shown here for the verifier over the rounds' data (`Within.slots_points`,
  E2E/TreeReads.lean), not for runs of a description's sub-protocols.
- `treeNo` is not shown to be injective: a number n beyond what a chain sends runs into the next
  chain's numbers. For an upper bound that is not needed.

Limits.
- The key file's description is not treated.
- All limits of E2E/TreeReadsAtFiles.lean stand. Nothing on hiding follows from this file alone.

The statement under `Spec` may be read as part of a goal. It counts as none.


-/
import E2E.TreeReadsAtFiles
import Johnson.Desc.Sound.DataRounds
import Johnson.Desc.Sound.TakenBelowOfData

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AtPublicFiles.TreeReads
open VerifiableInference.Desc
open OnBytes OnBytes.Maker

/-! ## 1. General in the description -/

section
variable {Xi : Type}

/-- The number over the file of the n-th tree that the chain number ch, from 0, sends. -/
def treeNo (F : FileDescription Xi) (ch n : ℕ) : ℕ := numAt F.t₁ F.t₂ ch (.own n)

theorem numAt_own (F : FileDescription Xi) (chain n : ℕ) :
    numAt F.t₁ F.t₂ chain (.own n) = treeNo F chain n := rfl

theorem numAt_taken (F : FileDescription Xi) (chain ch k : ℕ) :
    numAt F.t₁ F.t₂ chain (.taken ch k) = treeNo F ch k := rfl

/-- Declared rounds as pairs: how many positions each samples; the numbers of the trees that it
opens. -/
def declPairs (t₁ t₂ chain : ℕ) (l : List Fmt.DeclaredRound) : Pairs :=
  l.map fun r => (r.entry.poss, r.opens.map fun o => numAt t₁ t₂ chain o.2)

/-- **What a description's declared rounds open.** -/
def declOpens (F : FileDescription Xi) : Opens :=
  ⟨declPairs F.t₁ F.t₂ 0 F.roundsDeclaredByBlocks.1.dropLast, declPairs F.t₁ F.t₂ 1 F.roundsDeclaredByBlocks.2.1,
    declPairs F.t₁ F.t₂ 2 F.roundsDeclaredByBlocks.2.2, F.t₁, F.t₂⟩

theorem pairs_of (F : FileDescription Xi) (chain : ℕ) : ∀ {ds : List RDT} {l : List Fmt.DeclaredRound},
    List.Forall₂ RoundAsG ds l → List.Forall₂ (RoundOpens F chain) ds l →
      pairsT ds = declPairs F.t₁ F.t₂ chain l
  | _, _, .nil, _ => rfl
  | d :: ds, r :: l, .cons h t, .cons h' t' => by
      show (d.entry.poss, d.opens) :: pairsT ds =
        (r.entry.poss, r.opens.map fun o => numAt F.t₁ F.t₂ chain o.2) ::
          declPairs F.t₁ F.t₂ chain l
      rw [pairs_of F chain t t', h.1, h'.2]

/-- **The rounds' data open what the declared rounds open.** -/
theorem opens_of_data {F : FileDescription Xi} {file : String} {D : WholeD} (h : F.data file = .ok D) :
    opensOf D = declOpens F := by
  obtain ⟨a₁, a₂, a₃⟩ := roundsOfData F file D h
  obtain ⟨b₁, b₂, b₃⟩ := opensOfData Xi F file D h
  obtain ⟨c₁, c₂⟩ := counts_of_data h
  unfold opensOf declOpens
  rw [pairs_of F 0 a₁ b₁, pairs_of F 1 a₂ b₂, pairs_of F 2 a₃ b₃, c₁, c₂]

theorem last_rel {α β : Type} {P : α → β → Prop} : ∀ {l : List α} {m : List β},
    List.Forall₂ P l m → ∀ a, l.getLast? = some a → ∃ b, m.getLast? = some b ∧ P a b
  | _, _, .nil, _, h => by cases h
  | [a], [b], .cons h .nil, a', e => by
      obtain rfl : a = a' := by simpa using e
      exact ⟨b, rfl, h⟩
  | _ :: a₂ :: l, _ :: b₂ :: m, .cons _ t, a', e => by
      rw [List.getLast?_cons_cons] at e
      obtain ⟨b, hb, hp⟩ := last_rel t a' e
      exact ⟨b, by rw [List.getLast?_cons_cons]; exact hb, hp⟩

/-- A last round that samples no position does not count. -/
theorem readsOn_dropLast (j : ℕ) : ∀ (ps : Pairs), (∀ p, ps.getLast? = some p → p.1 = 0) →
    readsOn ps j = readsOn ps.dropLast j
  | [], _ => rfl
  | [p], h => by
      rw [readsOn_cons, h p rfl]
      simp [readsOn]
  | p :: q :: ps, h => by
      have ih := readsOn_dropLast j (q :: ps) fun x hx =>
        h x (by rw [List.getLast?_cons_cons]; exact hx)
      rw [List.dropLast_cons₂, readsOn_cons p (q :: ps), readsOn_cons p (q :: ps).dropLast, ih]

/-- The first chain's last declared round samples no position. -/
theorem seal_poss {F : FileDescription Xi} {file : String} {D : WholeD} (h : F.data file = .ok D)
    (r : Fmt.DeclaredRound) (hr : F.roundsDeclaredByBlocks.1.getLast? = some r) : r.entry.poss = 0 := by
  obtain ⟨⟨R₁, R₂, R₃⟩, hR, hk, -⟩ := data_ok h
  obtain ⟨w₁, -, -⟩ := writtenOf_ok hR
  obtain ⟨x, hx, y, hy, rfl⟩ := last_rel w₁ r hr
  have hf : Three.Whole.fits R₁ R₂ R₃ 2 = true := (okAt_parts hk).fits
  unfold Three.Whole.fits at hf
  simp only [Bool.and_eq_true] at hf
  have h5 := List.all_eq_true.1 hf.1.2 R₁ (by simp)
  have hx' : R₁.getLast? = some (y, r.stored) := hx
  rw [hx'] at h5
  simp only [Bool.and_eq_true, beq_iff_eq] at h5
  rw [← (round_ok hy).1]
  exact h5.1.2

/-- **So the first chain's declared rounds, taken WHOLE, read a tree as often as without the last.**
-/
theorem readsOn_first_whole {F : FileDescription Xi} {file : String} {D : WholeD}
    (h : F.data file = .ok D) (j : ℕ) :
    readsOn (declPairs F.t₁ F.t₂ 0 F.roundsDeclaredByBlocks.1) j = readsOn (declOpens F).first j := by
  show _ = readsOn (declPairs F.t₁ F.t₂ 0 F.roundsDeclaredByBlocks.1.dropLast) j
  unfold declPairs
  rw [List.map_dropLast]
  refine readsOn_dropLast j _ fun p hp => ?_
  rw [List.getLast?_map] at hp
  obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.1 hp
  exact seal_poss h r hr

end

/-! ## 2. At the proof file's description -/

open VerifierAndGoals (PublicFiles InScope asDescriptionFiles)
open FlashProve (dataAtFiles)
open FlashProve (protocolDataWellFormed flashProveData theProofData theProofRun)
open OnBytes.Slice (frS frZ)
open P5J

/-- The statement of `declared_atFiles`. -/
def Spec.declared_atFiles : Prop :=
  ∀ (Z : PublicFiles), InScope Z = true → protocolDataWellFormed (asDescriptionFiles Z) = true →
    ∀ (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : Chain TS ProofFile.Cl),
      LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL (theProofData (asDescriptionFiles Z)) (theProofRun (asDescriptionFiles Z))
        Zp Np cF →
      FileWithin (declOpens (F0T OnBytes.secondHashFunction Zp Np cF)) Zp.p.chains.made.sized.lines.slots
        (tableProof ((dataAtFiles flashProveData Z).DP.at frS.P.T.a) Zp.p.chains.made.sized.proof
          Zp.p.chains.made.sized.set.samples) 98 proofSlack

/-- **The declared rounds of the proof file's description**: in scope, with the gate open: their
reads of every tree lie within the encoding randomness of every row beneath it, in a batch of as
many requests as the sizes say: 64. -/
theorem declared_atFiles : Spec.declared_atFiles := fun Z scope live Zp Np cF L => by
  have h := (three_of_laid Z scope live _ _ Zp Np cF L).2.1
  have e : opensOf ((dataAtFiles flashProveData Z).DP.at frS.P.T.a) =
      declOpens (F0T OnBytes.secondHashFunction Zp Np cF) := by
    rw [opensOf_at, FlashProve.dp_built_live Z live, opens_of_data L.data]
  rw [e] at h
  exact h

end AtPublicFiles.TreeReads

#print axioms AtPublicFiles.TreeReads.numAt_own
#print axioms AtPublicFiles.TreeReads.numAt_taken
#print axioms AtPublicFiles.TreeReads.pairs_of
#print axioms AtPublicFiles.TreeReads.opens_of_data
#print axioms AtPublicFiles.TreeReads.seal_poss
#print axioms AtPublicFiles.TreeReads.readsOn_dropLast
#print axioms AtPublicFiles.TreeReads.readsOn_first_whole
#print axioms AtPublicFiles.TreeReads.declared_atFiles
