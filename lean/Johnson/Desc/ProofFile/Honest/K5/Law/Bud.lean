-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/Bud.lean: the letter bud of Good (Honest/Side.lean) at the row
of an attention segment's own rounds (kind K5): which positions of the row's tables may be read: THE
ROW SENDS NO TABLE, AND THE LETTER SAYS: NONE IS READ, AT ANY ROUND. One definition, and statements
with their proofs. No coin, no distribution, no run occurs.

  k5Bud          the letter: a count with code: every round's list of lists of positions is empty
  asksFrom_none  the frame's own function for the positions read (asksFrom,
                 Honest/Law/Rule/Session.lean) lays nothing at rounds without a root
  no_oracle      no round of a member of K5's side has an oracle message
  bud_at         **the letter holds of what that function lays at a member's own rounds**, whatever
                 is read of any tree, from whatever tree's number on, at whatever challenges
  k5Lettered, side_row   the row at a place with the letters of Good
  k5_bud₁        the clause in the letters in which the rule's premise on bud asks it of a row of
                 the first chain

bud_at, no_oracle and k5_bud₁ are CONDITIONAL: on K5Block (Honest/K5/Law/RowIs.lean); the side's row
is K5's.
The letter leans on no stop and reads no challenge. NOTHING HANGS ON IT: what a part shows reads the
positions at the part's tables alone (shownOf, Honest/Side.lean), and no part of the row sends one.

Limits. Lists alone. That the letter is the one that any rule asks is not said here.
No property is claimed. Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.RowIs
import Johnson.Desc.ProofFile.Honest.Law.Rule.Session
import Johnson.Desc.ProofFile.Honest.Rule

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K5
open VerifiableInference.Desc (Block Oracle FileDescription)
open VerifiableInference.Desc.First.Att

/-- **The positions read: none, at any round.** A count with code. It is a definition. -/
def k5Bud : Nat → List Fmt.Drawn → List (List (List Nat)) → Prop :=
  fun _ _ asks => asks.all (·.isEmpty) = true

/-- At rounds without a root the frame's function for the positions lays nothing. -/
theorem asksFrom_none (tree : Nat → List Nat) : ∀ (ns : List Nat) (n : Nat), (∀ r ∈ ns, r = 0) →
    (asksFrom tree ns n).all (·.isEmpty) = true
  | [], _, _ => rfl
  | r :: rs, n, h => by
    obtain rfl : r = 0 := h r List.mem_cons_self
    show (((List.range 0).map fun i => tree (n + i)).isEmpty &&
      (asksFrom tree rs (n + 0)).all (·.isEmpty)) = true
    rw [asksFrom_none tree rs _ fun x hx => h x (List.mem_cons_of_mem _ hx)]
    rfl

variable {W₀ Rc Xi Tr X Pb S Cl : Type}
  {σ : Side S Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb} {cells : Tr → Cells} {Z : Seat5}
  {p : P.Par}

/-- No round of a member has an oracle message. CONDITIONAL: see the head. -/
theorem no_oracle (hB : K5Block σ.block Z p) (hr : σ.row = k5Pairs cells Z)
    {u : Member (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb} (hu : u ∈ σ.members) :
    ∀ r ∈ u.rounds, r.2 = [] := by
  obtain ⟨j, s, -, rfl⟩ := member_at hr hu
  intro r hr'
  have h1 : r ∈ σ.block.rounds.zip σ.block.oracles :=
    List.mem_of_mem_drop (List.mem_of_mem_take hr')
  have h2 : r.2 ∈ σ.block.oracles := (List.of_mem_zip (a := r.1) (b := r.2) h1).2
  rw [hB.oracles] at h2
  obtain ⟨_, _, e⟩ := List.mem_map.1 h2
  exact e.symm

/-- **The letter holds of what the frame's function lays at a member's own rounds.** CONDITIONAL:
see the head. -/
theorem bud_at (hB : K5Block σ.block Z p) (hr : σ.row = k5Pairs cells Z)
    {u : Member (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb} (hu : u ∈ σ.members)
    (tree : Nat → List Nat) (n : Nat) (ds : List Fmt.Drawn) :
    k5Bud u.number ds (asksFrom tree (u.rounds.map (·.2.length)) n) := by
  refine asksFrom_none tree _ n fun r hr' => ?_
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hr'
  rw [no_oracle hB hr hu x hx]
  rfl

/-! ## The row with its letters, and the clause as the rule asks it -/

/-- **K5's row at a place, with the letters of Good** (Lettered, Honest/Rule.lean): A := B := the
empty sentence; On := True; bud := k5Bud. It is a definition. -/
def k5Lettered (Bk : ProverCoinCounts) (S Cl : Type) (cells : Tr → Cells) (Z : Seat5) :
    Lettered Bk S Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb :=
  { place := Z.place, row := k5Pairs cells Z, A := fun _ _ _ _ => False
    B := fun _ _ _ _ => False, On := fun _ _ _ _ => True, bud := k5Bud }

/-- The side of that row has that row. -/
theorem side_row {Bk : ProverCoinCounts} {bs : List (Block S Cl)} {fs : List (Fall S)}
    (h : (k5Lettered (W₀ := W₀) (Rc := Rc) (Xi := Xi) (X := X) (Pb := Pb) Bk S Cl cells Z).side bs
      fs = some σ) : σ.row = k5Pairs cells Z := by
  unfold Lettered.side Side.seated at h
  obtain ⟨b, -, rfl⟩ := Option.map_eq_some_iff.1 h
  rfl

/-- **The row's clause on the positions read**, in the letters of the first chain's clause of the
rule's premise on bud (BudDebts.bud₁, Honest/Law/OwedRule.lean, which is not imported): AT EVERY
NUMBER n OF ROUNDS IN FRONT, EVERY NUMBER N OF TREES IN FRONT AND EVERY LIST OF CHALLENGES, due or
not: so that clause's own n, N and its premises on them are not spent. CONDITIONAL: the member of
the description at the place meets K5Block. -/
theorem k5_bud₁ {F : FileDescription Xi} {Bk : ProverCoinCounts}
    {τ : Side F.S₁ F.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi}
    (h : (k5Lettered Bk F.S₁ F.Cl cells Z).side F.first.blocksInOrder = some τ)
    (hB : K5Block τ.block Z p) : ∀ u ∈ τ.members, ∀ (n N : Nat) (ρ : Draws),
    (k5Lettered (W₀ := W₀) (Rc := Rc) (Xi := Xi) (X := X) (Pb := Xi) Bk F.S₁ F.Cl cells Z).bud
      u.number ((ρ.first.drop n).take u.rounds.length)
      (asksFrom (treeAsks F ρ 0) (u.rounds.map (·.2.length)) N) :=
  fun u hu n N ρ =>
    bud_at hB (side_row h) hu (treeAsks F ρ 0) N ((ρ.first.drop n).take u.rounds.length)

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.asksFrom_none
#print axioms ProofFile.Honest.K5.no_oracle
#print axioms ProofFile.Honest.K5.bud_at
#print axioms ProofFile.Honest.K5.side_row
#print axioms ProofFile.Honest.K5.k5_bud₁
