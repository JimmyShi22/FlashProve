-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K8/QuietForm.lean: THE SMALLNESS TEST: ITS ROW IS A QUIET ROW WITH A
SECOND STOP, AND SO THE FRAME's `Good` (Johnson/Desc/ProofFile/Honest/Side.lean) HOLDS AT ITS SIDE
IN THE THREE FIELDS THAT ARE A KIND's: fits, exact, fresh. Statements, each a definition of a
proposition, and their proofs. WHAT FOLLOWS FROM `Good` IS NOT SAID HERE: its two fields exact and
fresh say that two laws on lists of shown rounds are equal, in the frame's letters, and no more.
None is one of the library's goals.
One empty round is simulated by a term that yields, for that round, no item and no column. This is
not to be quoted as "the range check is simulated exactly": what the range check can tell goes
through the second stop. The block in `small_good` has a single round; every item that this round
declares is a root, and no oracle message goes with it. The fields exact and fresh of `Good` ask
their equations only where the part's stop does not answer "hid" at the challenges drawn: where it
does, neither field speaks.

  `smallStop cells P`   the row's second stop, of the chain's input: `smallHid`
                       (Honest/K8/Part.lean) at what the part is handed of that input
  `Spec.small_parts`, `small_parts`   AN EQUATION OF TERMS: WHERE THE SEAT's TEST ON PUBLIC DATA
                       PASSES (`smallFits`), the half's row is one part, and that part is `quietStop
                       (smallStop cells P) (windowShare P.1)`
                       (Johnson/Desc/ProofFile/Honest/K9/QuietMember.lean): the frame's quiet part
                       of one round with that second stop and its stated number. The lifted move's
                       one test reads how many names the half was handed, and nothing of the input
  `Spec.small_good`, `small_good`   at the kind's side (`smallSide`, Honest/K8/Side.lean) over a
                       block with one round that cuts no item but roots and one empty list of oracle
                       messages, under `smallFits` and one premise on the book (no entry lets
                       anybody spend a coin of this part): `Good pre φ σ Bk ord chain firstTree A'
                       B' On bud` at A' := B' := False, On := True, bud := True. exact and fresh:
                       the two general laws of that file, called; fits: by the texts; plays and acc:
                       from False: they are no kind's
General in the list pre, the face, the book (but for that premise), ord, chain, firstTree, the list
of blocks and the falls.
Limits. THE LISTS AT WHICH THE SECOND STOP IS THE FIRST TO SPEAK ARE LEFT OUT OF exact AND fresh BY
THESE FIELDS' OWN PREMISE: nothing is said there. Where `smallFits` fails for the names the move is
at fault at every state, and exact is false wherever its premises can be met at all (by reading; no
lemma says it). The second clause of `smallFits` (the numbers of rows) is spent by neither
statement. The premises at any description or book are not shown. A member of `small_good`:
Honest/K8/QuietFormToy.lean.
Nothing is claimed on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K8.Side
import Johnson.Desc.ProofFile.Honest.K9.QuietMember

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K8
open VerifiableInference.Desc (Place Block)
open VerifiableInference.Desc.First.K8 (Par)
open ProofFile.Honest.K9 (quietStop quietAt quiet_exact_at quiet_fresh_at)

variable {W₀ Rc Xi Tr X Pb S Cl : Type}

/-- The row's second stop, of the chain's input. -/
def smallStop (cells : Tr → Cells) (P : Par × List (Nat × String × Nat)) (v : Local W₀ Rc Xi Tr) :
    List Fmt.Drawn → List Fmt.Drawn → Option String :=
  smallHid P.1 (askOfInput cells P.2 v)

namespace Spec

/-- States: where the seat's test passes, the half's row is the quiet part with the kind's second
stop. -/
def small_parts : Prop :=
  ∀ (W₀ Rc Xi Tr X : Type) (cells : Tr → Cells) (P : Par × List (Nat × String × Nat)),
    smallFits P = true →
    (smallHalf (W₀ := W₀) (Rc := Rc) (Xi := Xi) (X := X) cells P).parts =
      [quietStop (smallStop cells P) (windowShare P.1)]

/-- States: `Good` at the kind's side, in the three fields that are a kind's. pre is tied to no
description; at each pre this says no more than quiet_exact_at and quiet_fresh_at beneath. -/
def small_good : Prop :=
  ∀ (W₀ Rc Xi Tr X Pb S Cl : Type) (bs : List (Block S Cl)) (cells : Tr → Cells)
    (P : Par × List (Nat × String × Nat)) (fs : List (Fall S))
    (σ : Side S Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb)
    (pre : List (Nat × Nat × List Fmt.DeclaredRound))
    (φ : Face (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) Pb) (Bk : ProverCoinCounts) (ord : List Place)
    (chain firstTree : Nat) (d₀ : Fmt.DeclaredRound),
    smallSide bs cells P fs = some σ → smallFits P = true → σ.block.rounds = [d₀] →
    d₀.items.filter (· != .root) = [] → σ.block.oracles = [[]] →
    (∀ q, Bk.spentBy ⟨σ.block.place, 0⟩ q = []) →
    Good pre φ σ Bk ord chain firstTree (fun _ _ _ _ => False) (fun _ _ _ _ => False)
      (fun _ _ _ _ => True) (fun _ _ _ => True)

end Spec

theorem small_parts : Spec.small_parts := by
  intro W₀ Rc Xi Tr X cells P h
  have hn : (P.2.length == P.1.ks.length) = true := (Bool.and_eq_true_iff.1 h).1
  show [(smallPart P.1).lift (askOfInput cells P.2) (askOfInput cells P.2) (fun _ => ())
    fun x _ => x] = _
  simp only [Part.lift, smallPart, quietStop, quietPart, List.map_cons, List.map_nil, Move.lift,
    State.narrow, askOfInput, hn, if_true, List.replicate]
  rfl

theorem small_good : Spec.small_good := by
  intro W₀ Rc Xi Tr X Pb S Cl bs cells P fs σ pre φ Bk ord chain firstTree d₀ hσ hn hr hi ho hown
  obtain ⟨blk, hb, rfl⟩ := Option.map_eq_some_iff.1 hσ
  have hp : blk.place = smallPlace P.1 := by simpa using List.find?_some hb
  have hrow : smallRow (W₀ := W₀) (Rc := Rc) (Xi := Xi) (X := X) (Pb := Pb) cells P =
      [(quietStop (smallStop cells P) (windowShare P.1), quietSim ⟨smallPlace P.1, 0⟩)] := by
    unfold smallRow smallSims
    rw [small_parts W₀ Rc Xi Tr X cells P hn]
    rfl
  simp only at hr ho hown
  have hmem : (⟨blk, smallRow cells P, fallOf fs (smallPlace P.1)⟩ :
      Side S Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb).members =
        [quietAt 0 d₀ (smallStop cells P) (windowShare P.1) ⟨smallPlace P.1, 0⟩] := by
    unfold Side.members
    simp only [hrow, hr, ho]
    rfl
  refine ⟨?_, fun _ _ _ _ _ h => h.elim, fun _ _ _ _ _ h => h.elim, ?_, ?_⟩
  · unfold Side.fits Side.half
    simp [hrow, hr, ho, hp, quietSim, quietStop, quietPart, Placed.rounds]
  · intro u hu ca m front ds asks _ _ _ hd _ _ hs
    rw [hmem, List.mem_singleton] at hu
    subst hu
    exact quiet_exact_at _ φ 0 d₀ hi _ _ _ ca m front ds asks hd hs
  · intro u hu q sp ca m ds asks _ _ _
    rw [hmem, List.mem_singleton] at hu
    subst hu
    exact quiet_fresh_at _ φ Bk ord 0 d₀ _ _ _ q (hown q) sp ca m ds asks

end ProofFile.Honest.K8

#print axioms ProofFile.Honest.K8.small_parts
#print axioms ProofFile.Honest.K8.small_good
#print axioms ProofFile.Honest.K8.smallStop
#print axioms ProofFile.Honest.K8.Spec.small_parts
#print axioms ProofFile.Honest.K8.Spec.small_good
