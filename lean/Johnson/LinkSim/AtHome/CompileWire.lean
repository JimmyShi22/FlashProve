-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LinkSim/AtHome/CompileWire.lean: three facts on the link's compilation data, for all lists
of rounds, and its numbers at the library's full-size parameter set (dsFull).
Terms of this folder: Johnson/LinkSim/Spec.lean.

What this file has (namespace OnBytes.LinkSim.AtHome). The link proof's compilation data is the
term wqW C ds a xs dec K chal (Johnson/RunOne/StrictLinkW.lean). Its list of rounds has a first
round with no Merkle tree and no proof-of-work check, then one round for each entry of the list ds
(wireS, wiresSL, OnBytes/TypedOracleCompiler/Run/PlanQS.lean). The first four results hold for every choice C of
challenge types, every list ds and all other parameters.
  noncesBack_wqW    in every round of the link with a proof-of-work check, the number k that is
                    written as the nonce into the plain part is read back unchanged. This holds for
                    every bound on proof-of-work attempts and from every round number; grBack_Dn
                    proves it for every k, with no bound at all.
  withinWin_wqW     if every round of ds has at most nK Merkle trees and every tree at most nJ
                    leaves, then the link's compilation data lies within the window nK, nJ.
  reads_linkW       for a fixed instance and fixed verifier messages, the positions of the
                    prover's own oracle messages that the link's verifier reads are the same for
                    all messages sent in the clear. It holds by definition.
  readsFree_wqW     so ReadsFree holds: two transcripts that differ only in their nonces have the
                    same positions read. This is the narrower form that PremW asks.
At the library's full-size parameter set (dsFull, its list of rounds; OnBytes/Flat/LinkSibAt.lean),
for all other parameters:
  fr_deep, fr_leaves   no Merkle tree is deeper than 24 (checked by evaluation in Lean's kernel),
                    so none has more than 2 ^ 24 leaves.
  withinWin_full    so the window holds at dsFull whenever 1 ≤ nK and 2 ^ 24 ≤ nJ (at most one
                    tree per round: fr_one, Johnson/Prover/Link/ChainTrees.lean).
  length_full       the link at dsFull has 42 rounds. That the link has one round more than ds
                    has members is proved elsewhere (length_linkW,
                    Johnson/Flat/Dec/CountAtFrame.lean), and so is the number at the explicit link
                    (sibF_len, Johnson/Flat/ArmSibCount.lean). Both are called.

How it fits. Through Johnson/LinkSim/AtHome/CompileHome.lean these lemmas serve, under
Johnson/LinkSim/, link_all_met (Johnson/LinkSim/AtHome/CompileFiller.lean) alone; premW_withLaid
(Johnson/LinkSim/AtHome/CompileFit.lean) copies these clauses from its premise and does not use
them. Four clauses of PremW (Johnson/WholeKey/Premises.lean) concern only the link's compilation
data and public numbers: freeL (ReadsFree), backL (NoncesBack at the bound a.capL), the link's part
of coins.rounds (at most a.nR rounds) and coins.winL (WithinWin a.nK a.nJ). This file gives what
they need for wqW: readsFree_wqW, noncesBack_wqW, withinWin_wqW with the numbers at dsFull, and
length_full for the number of rounds; CompileHome.lean carries them to the link's compilation data
at homeR b Z. They are not the only clauses of that kind: the link's parts of wires, fmt and
coherent are proved by a call in CompileHome.lean.

Limits.
  These are facts about wqW for arbitrary parameters. That the link's compilation data at
      homeR b Z is wqW at dsFull is not stated as a theorem; Johnson/LinkSim/AtHome/CompileHome.lean
      applies these lemmas there, and Lean accepts that by unfolding the definitions.
  In Lean a nonce is a natural number; in a file it has eight bytes. So "for every bound" holds of
      the Lean model: a number from 2 ^ 64 on cannot be written into a file, and whoever goes to
      bytes must bound the attempts (Johnson/Prover/Law/PutsAt.lean says so of its own statement).
  Nothing says that a proof-of-work search succeeds.
  The window's numbers are sufficient; that they are needed is not proved.

Sources. The inductions follow putsFree_wiresSL and putsFree_wqW (Johnson/Prover/At/FitAt.lean);
grBack_Dn follows grApart_Dn (Johnson/Prover/Law/PutsAt.lean); fr_deep follows fr_one
(Johnson/Prover/Link/ChainTrees.lean), and is proved, as that is, under a raised limit of
elaboration: the kernel checks the term by evaluation.
Terms: lean/GLOSSARY.md.

-/
import Johnson.WholeKey.Premises
import Johnson.Prover.At.FitAt
import Johnson.Prover.Link.ChainTrees
import Johnson.Flat.Dec.CountAtFrame

set_option autoImplicit false

noncomputable section

namespace OnBytes.LinkSim.AtHome
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch OnBytes.WholeKey
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run.PQ (CK XO View Dn)
open TypedOracleCompiler.Run.PQ (RD wiresSL)
open OnBytes.Flat (linkSkeletonOfRoundData dsFull)
open Johnson.RunOne.StrictW (wqW)
open Johnson.Prover.Link (fr_one)

/-! ## Reading back a nonce -/

/-- **A proof-of-work check made by grOf at Dn reads back every number that it has written**:
get (put k α) = k for all k and α. -/
theorem grBack_Dn {C P : Type} : ∀ (b : ℕ) (g : GrW (GChal b C) (GPlain ℕ b P)),
    (grOf Dn C P b).map TypedOracleCompiler.Tagged.ofGr = some g → ∀ k α, g.get (g.put k α) = k
  | 0, _, h => by cases h
  | b + 1, g, h => by
    obtain rfl : TypedOracleCompiler.Tagged.ofGr (_root_.Iop.GrW.ofBits Dn b C P) = g := Option.some.inj h
    intro k α
    rfl

section
variable (C : CK) (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k)

/-! ## The rounds after the first -/

/-- NoncesBack for the rounds after the first, by induction on ds. -/
theorem noncesBack_wiresSL : ∀ (ds : List RD) (cap : ℕ → ℕ) (i : ℕ),
    NoncesBack _ _ (wiresSL C K chal ds) cap i
  | [], _, _ => trivial
  | _ :: ds, cap, i =>
    ⟨fun g hg k α _ => grBack_Dn _ g hg k α, noncesBack_wiresSL ds cap (i + 1)⟩

/-- WithinWin for the rounds after the first, by induction on ds. -/
theorem withinWin_wiresSL (nK nJ : ℕ) : ∀ ds : List RD, (∀ d ∈ ds, d.trees.length ≤ nK) →
    (∀ d ∈ ds, ∀ s ∈ d.trees, 2 ^ s.a ≤ nJ) → WithinWin nK nJ _ _ (wiresSL C K chal ds)
  | [], _, _ => trivial
  | d :: ds, h1, h2 =>
    ⟨⟨Nat.zero_le _, by
        show (d.trees.map (·.a)).length ≤ nK
        rw [List.length_map]
        exact h1 d List.mem_cons_self, fun _ h => (by cases h), fun e he => by
        obtain ⟨s, hs, rfl⟩ := List.mem_map.1 (show e ∈ d.trees.map (·.a) from he)
        exact h2 d List.mem_cons_self s hs⟩,
      withinWin_wiresSL nK nJ ds (fun d' h => h1 d' (List.mem_cons_of_mem _ h))
        fun d' h => h2 d' (List.mem_cons_of_mem _ h)⟩

/-! ## The link's compilation data -/

variable (ds : List RD) (a : ℕ) (xs : List XO) {Y : Type} (dec : Y → View → Bool)

/-- **Every number is read back from the plain part into which it was written**: for every bound
on proof-of-work attempts, from every round number. -/
theorem noncesBack_wqW (cap : ℕ → ℕ) (i : ℕ) :
    NoncesBack _ _ (wqW C ds a xs dec K chal).sh cap i :=
  ⟨(fun _ hg => by cases hg), noncesBack_wiresSL C K chal ds cap (i + 1)⟩

/-- **All trees lie within the window**, if each round has at most nK trees and each tree at most nJ
leaves. -/
theorem withinWin_wqW (nK nJ : ℕ) (h1 : ∀ d ∈ ds, d.trees.length ≤ nK)
    (h2 : ∀ d ∈ ds, ∀ s ∈ d.trees, 2 ^ s.a ≤ nJ) :
    WithinWin nK nJ _ _ (wqW C ds a xs dec K chal).sh :=
  ⟨⟨Nat.zero_le _, Nat.zero_le _, fun _ h => (by cases h), fun _ h => (by cases h)⟩,
    withinWin_wiresSL C K chal nK nJ ds h1 h2⟩

/-- **The positions of its own oracle messages that the link's verifier reads do not depend on what
the prover sends in the clear**: at one instance and one list of verifier messages they are the same
for all clear messages. -/
theorem reads_linkW (x : Y) (ρ : Rho (linkSkeletonOfRoundData C ds a xs dec).up.loc.shape)
    (π π' : Plains (linkSkeletonOfRoundData C ds a xs dec).up.loc.shape) :
    (linkSkeletonOfRoundData C ds a xs dec).up.loc.reads x ρ π = (linkSkeletonOfRoundData C ds a xs dec).up.loc.reads x ρ π' := rfl

/-- So ReadsFree holds: at two transcripts that differ only in their nonces the verifier reads the
same positions. -/
theorem readsFree_wqW : ReadsFree (linkSkeletonOfRoundData C ds a xs dec).up (wqW C ds a xs dec K chal).sh :=
  fun x τ τ' _ => reads_linkW C ds a xs dec x τ.rho τ'.plains τ.plains

end

/-! ## The numbers at the full-size parameter set (dsFull) -/

set_option maxRecDepth 100000 in
/-- At dsFull no tree is deeper than 24. -/
theorem fr_deep : ∀ d ∈ dsFull, ∀ s ∈ d.trees, s.a ≤ 24 := fun d hd s hs =>
  of_decide_eq_true (List.all_eq_true.1 (List.all_eq_true.1
    (show (dsFull.all fun d => d.trees.all fun s => decide (s.a ≤ 24)) = true by decide +kernel)
    d hd) s hs)

/-- So none has more than 2 ^ 24 leaves. -/
theorem fr_leaves : ∀ d ∈ dsFull, ∀ s ∈ d.trees, 2 ^ s.a ≤ 2 ^ 24 := fun d hd s hs =>
  Nat.pow_le_pow_right (by decide) (fr_deep d hd s hs)

section
variable (C : CK) (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k) (a : ℕ) (xs : List XO)
  {Y : Type} (dec : Y → View → Bool)

/-- **At dsFull all trees lie within the window** whenever 1 ≤ nK and 2 ^ 24 ≤ nJ. -/
theorem withinWin_full (nK nJ : ℕ) (hK : 1 ≤ nK) (hJ : 2 ^ 24 ≤ nJ) :
    WithinWin nK nJ _ _ (wqW C dsFull a xs dec K chal).sh :=
  withinWin_wqW C K chal dsFull a xs dec nK nJ (fun d hd => (fr_one d hd).trans hK)
    fun d hd s hs => (fr_leaves d hd s hs).trans hJ

set_option maxRecDepth 100000 in
/-- The link at dsFull has 42 rounds, for all other parameters. -/
theorem length_full : (linkSkeletonOfRoundData C dsFull a xs dec).up.loc.shape.length = 42 := by
  have h1 : dsFull.length + 1 = 42 :=
    (VerifiableInference.OnPublicFiles.length_linkW _ _ _ _ _).symm.trans
      TypedOracleCompiler.Compile.Batch.Cms.sibF_len
  exact (VerifiableInference.OnPublicFiles.length_linkW C dsFull a xs dec).trans h1

end

end OnBytes.LinkSim.AtHome

#print axioms OnBytes.LinkSim.AtHome.grBack_Dn
#print axioms OnBytes.LinkSim.AtHome.noncesBack_wqW
#print axioms OnBytes.LinkSim.AtHome.withinWin_wqW
#print axioms OnBytes.LinkSim.AtHome.reads_linkW
#print axioms OnBytes.LinkSim.AtHome.readsFree_wqW
#print axioms OnBytes.LinkSim.AtHome.fr_deep
#print axioms OnBytes.LinkSim.AtHome.withinWin_full
#print axioms OnBytes.LinkSim.AtHome.length_full
