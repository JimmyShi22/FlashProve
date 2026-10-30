-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Thread/FirstAt.lean: the first chain's parameters at the library's own
terms. `Letters` (Honest/Thread/First.lean) is filled under the one hypothesis that ties the table's
parameters to the proof file's description (`P5J.AtMgA`, Johnson/P5J/MgAtAll.lean), at
`OnBytes.secondHashFunction`. That is the hash that the format page calls the earlier hash
(docs/format/FORMAT.md, R15.3). The format uses two hash functions: its hash H, and this one, for
the digests in the statement's item `request` and in computing the public part. One definition;
no theorem is stated.

What is supplied. `links`, `ps`, `N`: those of `P5J.At` (Johnson/P5J/LettersAt.lean). `bs`: the flat
list of the hypothesis's own chain. `first`: `ProofFile.startS Zp`. `MgP`: the library's constant
`mgAtAll h`. `Mg w`: the same term `mgAll … mgBase` with two fields of its data replaced: `decT`:
the constant "the cells that the `Script` gives for the input"; `cr1`: a parameter for the exact
carry.

What stays a parameter: the book, the prover's sides, the `Script`, the stored table's columns,
`ans`, `test`, the exact carry, three numbers, `valid`, `rides`, `keeps`.

Limits.
  * Only at the full size and at `secondHashFunction` is the written list of places tied to the chain's flat
    list (`At.places_paid`, Johnson/P5J/PlacesPaid.lean).
  * No lemma that the library states at `mgAtAll h` speaks of `Mg w`: its data differ at two fields.
    The field lemmas `mgAll_…` (Johnson/Desc/Sound/MgAll.lean) are general in the data and do.
  * This file does not prove that the hypothesis `AtMgA` can be met (the library's
    `head_exists_at_name` gives a term of it, at `D` := `dpZ Z` and `r` := `theProofRun (asDescriptionFiles Z)`
    alone, under four hypotheses on the public files), or that the invariant holds at any run.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.First
import Johnson.P5J.MgAtAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Chain Strs Wit)
open VerifiableInference.Desc.Sound (mgAll mgBase MsgT)
open OnBytes.Maker (WholeD)
open P5J (AtMgA mgAtAll CellsM TS)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- The type of witnesses at the full size. -/
abbrev WtF : Type := Wit (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT

/-- **The first chain's parameters at the library's own terms.** -/
noncomputable def lettersAt (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts}
    {W₀ Rc Tr X : Type}
    (hs : List (Placed (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X))
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (stored : Local W₀ Rc ProofFile.Inst Tr → Nat → Nat → Option (List UInt64))
    (ans : Nat → Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ : Nat)
    (valid : Local W₀ Rc ProofFile.Inst Tr → Prop) (rides : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
    (keeps : Nat → TS → TS → Prop) :
    Letters Bk ProofFile.Cl W₀ Rc ProofFile.Inst Tr X ProofFile.InstPub (CellsM OnBytes.Flat.numsFull) P5J.At.Tok
      MsgT :=
  { links := P5J.At.links, ps := P5J.At.ps, N := P5J.At.N Zp cF
    Mg := fun w => mgAll { h.𝔇 with decT := fun _ _ => some (Q.cells w), cr1 := carryX } mgBase
    MgP := mgAtAll h
    ans := ans, test := test, bs := cF.blocksInOrder, hs := hs, Q := Q, stored := stored
    pubOf := fun ξ => ξ.pub, first := ProofFile.startS Zp
    item := item, n₁ := n₁, n₂ := n₂, valid := valid, rides := rides, keeps := keeps }

end ProofFile.Honest.FirstThread
