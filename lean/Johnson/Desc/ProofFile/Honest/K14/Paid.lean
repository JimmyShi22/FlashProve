-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K14/Paid.lean: kind K14, the kind's own four sub-protocols that have a
round. WHAT IS PROVED: Plays T b, which is what a chain's thread asks of the prover's side at the
member number b (Honest/Thread/Pays.lean), HOLDS WHEREVER AtQuiet, AtSplit OR AtLoc HOLDS AT b:
three structures, defined here, on whatever stands at the number b of the thread's list and on the
thread's halves; general in the thread's fields. Where nothing stands at the number b (a list that
is too short) the three structures and Plays are all met vacuously. Statements with their proofs,
over Debts.lean of this folder and the general lemmas of Honest/K13/DebtsKit.lean and
Honest/K14/Kit.lean.

  AtQuiet T b A weights   whatever stands at the number b of the thread's list declares one round
                  that cuts no item, opens no tree and reads no committed table, states no oracle
                  message, and the quiet half stands at its place among the thread's halves
  AtLoc T b A weights     the like, but that the round may read committed tables; and at every valid
                  input the thread's committed tables have a column of the declared width at every
                  position below the table's length
  AtSplit T b A weights   as AtQuiet, but that the round cuts one element, and the half of "SPLIT"
                  stands at the place
  quiet_Plays, split_Plays   **Plays T b**, from AtQuiet | AtSplit alone: no premise on the thread's
                  sentence in front
  loc_Plays       **Plays T b**, from AtLoc: of the thread's sentence in front it uses that the
                  committed tables at hand are the thread's, and that the input is valid

What is not claimed. That AtQuiet, AtLoc or AtSplit hold at the shared chain's thread of the IOP as
written in Lean (from facts on a thread's two lists, under premises of their own:
Honest/K14/PaidAt.lean, Honest/K14/PaidFlat.lean). The other sentences that a thread asks at a
member. Nothing on soundness or on hiding.
-/
import Johnson.Desc.ProofFile.Honest.K14.Debts

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open VerifiableInference.Desc (Block Place OpenedColumn)
open ProofFile.Honest.K13 (fresh_none)

variable {Bk : ProverCoinCounts} {S Cl W₀ Rc Ky X Pb : Type}

variable (T : Thread Bk S Cl Empty (Common W₀ Rc Ky) X Pb)

/-- **What stands at the number b has one round in which nothing is sent or read**, and the quiet
half stands at its place. -/
structure AtQuiet (b : Nat) (A : Data) (weights : W₀ → Weights) : Prop where
  member : ∀ blk, T.bs[b]? = some blk → ∃ d, blk.rounds = [d] ∧ blk.oracles = [[]] ∧
    d.items = [] ∧ d.opens = [] ∧ d.stored = []
  half : ∀ blk, T.bs[b]? = some blk → (T.hs.find? fun h => h.place == blk.place) =
    some { place := blk.place, parts := [liftK14 A weights quietPart] }

/-- **What stands at the number b has one round in which nothing is sent and committed tables may be
read** (the round's list of them may be empty); at every valid input each of them has a column of
the declared width at every position below its length; and the quiet half stands at its place. -/
structure AtLoc (b : Nat) (A : Data) (weights : W₀ → Weights) : Prop where
  member : ∀ blk, T.bs[b]? = some blk → ∃ d, blk.rounds = [d] ∧ blk.oracles = [[]] ∧
    d.items = [] ∧ d.opens = [] ∧
    ∀ w, T.valid w → ∀ s ∈ d.stored, ∀ p < 2 ^ s.sh.a,
      ∃ u, T.stored w s.item p = some u ∧ u.length = s.sh.W
  half : ∀ blk, T.bs[b]? = some blk → (T.hs.find? fun h => h.place == blk.place) =
    some { place := blk.place, parts := [liftK14 A weights quietPart] }

/-- **What stands at the number b has one round in which one element is sent and nothing is read**,
and the half of "SPLIT" stands at its place. -/
structure AtSplit (b : Nat) (A : Data) (weights : W₀ → Weights) : Prop where
  member : ∀ blk, T.bs[b]? = some blk → ∃ d, blk.rounds = [d] ∧ blk.oracles = [[]] ∧
    d.items = [.e] ∧ d.opens = [] ∧ d.stored = []
  half : ∀ blk, T.bs[b]? = some blk → (T.hs.find? fun h => h.place == blk.place) =
    some { place := blk.place, parts := [liftK14 A weights (splitPart A)] }

variable {T} {b : Nat} {A : Data} {weights : W₀ → Weights}

/-- **"LIN point", "LIN zeta": it plays, where AtQuiet holds at b**: at all coins, with no premise
on the thread's sentence in front. -/
theorem quiet_Plays (h : AtQuiet T b A weights) : Plays T b := by
  intro blk hb k s m E ds l _ hd _ hl
  obtain ⟨d, hr, ho, hi, hop, hst⟩ := h.member blk hb
  obtain ⟨x, -, hp, hc⟩ :=
    quiet_moved A weights blk d hr ho hi hop hst (h.half blk hb) hl m ds hd
  refine ⟨_, [], ⟨⟨l, hl, hp⟩, hc _ _ _ _⟩, ?_⟩
  rw [fresh_none T hb (by rw [ho]; rfl)]
  intro σ hσ
  cases hσ

/-- **"SPLIT": it plays, where AtSplit holds at b**: at all coins, with no premise on the thread's
sentence in front. -/
theorem split_Plays (h : AtSplit T b A weights) : Plays T b := by
  intro blk hb k s m E ds l _ hd _ hl
  obtain ⟨d, hr, ho, hi, hop, hst⟩ := h.member blk hb
  obtain ⟨x, c, -, -, hp, hc⟩ :=
    split_moved A weights blk d hr ho hi hop hst (h.half blk hb) hl m ds hd
  refine ⟨_, [], ⟨⟨l, hl, hp⟩, hc _ _ _ _⟩, ?_⟩
  rw [fresh_none T hb (by rw [ho]; rfl)]
  intro σ hσ
  cases hσ

/-- **"LOC": it plays, where AtLoc holds at b**: at all coins; the columns are laid off the thread's
committed tables. -/
theorem loc_Plays (h : AtLoc T b A weights) : Plays T b := by
  intro blk hb k s m E ds l hT hd _ hl
  obtain ⟨d, hr, ho, hi, hop, hcol⟩ := h.member blk hb
  obtain ⟨x, -, hp, hc⟩ := loc_moved A weights blk d hr ho hi hop (h.half blk hb) hl m ds hd
  obtain ⟨cols, hcols⟩ := hc T.chain T.ft (E.add [playedBy blk [] [] x]).stored
    (E.add [playedBy blk [] [] x]).tree fun s' hs' p hp' => by
      obtain ⟨u, hu, hw⟩ := hcol m.st.input hT.2.2.2.2.2.2 s' hs' p hp'
      exact ⟨u, (hT.1.1 s'.item p).trans hu, hw⟩
  refine ⟨_, cols, ⟨⟨l, hl, hp⟩, hcols⟩, ?_⟩
  rw [fresh_none T hb (by rw [ho]; rfl)]
  intro σ hσ
  cases hσ

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.quiet_Plays
#print axioms ProofFile.Honest.K14.split_Plays
#print axioms ProofFile.Honest.K14.loc_Plays
