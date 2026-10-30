-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K14/AcceptedAll.lean: kind K14: FitsAt (Honest/Thread/Shape.lean) AND
ACCEPTED (Honest/Thread/Pays.lean) AT THE MEMBERS 1 TO 8 OF THE THREAD OF THIS KIND's LETTERS
(Honest/K14/Thread2.lean: letters2), AT EVERY Others WHOSE HALVES ARE AS HalvesIn AND SendsIn SAY;
for Accepted under Plan2 besides, and at the member 3 under two premises on valid inputs' keys; for
FitsAt where blocks Q returns the eight (Eight Q), which is less than Plan2. The proofs are calls:
eight_Fits (Honest/K14/PaidAll.lean) and accepted_at (Honest/K14/AcceptedAt.lean).

  HalvesIn Q O A weights   the facts on the letter O.hs that the kind's own six members spend: the
                  halves stand at different places; the kind's own halves (Honest/K14/Parts.lean:
                  proverSidesOfSharedRounds: four where the shape splits, else three) are among them; A has Q's shape
  SendsIn Q O A weights rand   the two sendings' halves are among them too: A SENTENCE OF ITS OWN:
                  atEight2 does not take it. fits2 and accepted_all DO, AT EVERY b: each is one
                  theorem for all eight members
  atEight2        AtEight at the thread, at b0 := 1, from Eight Q and HalvesIn
  chainAt2        ChainAt at the thread: by how the letters are laid
  fits2           **FitsAt at the members 1 to 8**, from Eight Q, HalvesIn and SendsIn
  accepted_all    **Accepted at the members 1 to 8, at every fall**, under all the premises below

WHAT STAYS A PREMISE: Plan2 (public; it holds at the two typed shapes, at every list bp that is not
empty: Honest/K14/Thread2Member.lean: plan2_key, plan2_real) · HalvesIn and SendsIn (public data of
whoever lays the halves) · at the member 3 alone: a valid input's key has sizes that fit, and no
seed of it has the factor 0.

What is not claimed. That the thread's sentence in front holds at any stand. Nothing on soundness or
on hiding.
-/
import Johnson.Desc.ProofFile.Honest.K14.AcceptedAt
import Johnson.Desc.ProofFile.Honest.K14.PaidFlat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open VerifiableInference.Desc (Block Place)
open VerifiableInference.Desc.Own (keyFits)
open Desc.K14 (P14 St)
open Desc.K14.Honest (Eight flatOf_carried)

variable {Bk : ProverCoinCounts} {W₀ Rc X₀ P₁ Wt : Type} {Q : P14} {sentU : Array OnBytes.OracleNotice}
  {layO : OnBytes.TreeLay}

/-- **The facts on the letter O.hs**: the halves stand at different places, and the kind's own
halves are among them; and that A has Q's shape. -/
structure HalvesIn (Q : P14) (O : Others Bk W₀ Rc X₀ P₁ Wt) (A : Data) (weights : W₀ → Weights) :
    Prop where
  shape : A.S = Q.S
  apart : (O.hs.map (·.place)).Nodup
  own : ∀ h ∈ (proverSidesOfSharedRounds A weights :
    List (Placed Empty (Common W₀ Rc OnBytes.TableKey) X₀)), h ∈ O.hs

/-- **The two sendings' halves are among the halves.** -/
def SendsIn (Q : P14) (O : Others Bk W₀ Rc X₀ P₁ Wt) (A : Data) (weights : W₀ → Weights)
    (rand : Rc → TableRand) : Prop :=
  ∀ g ∈ (proverSidesOfSharedSendings ⟨Q, A.atPoint⟩ weights rand :
    List (Placed Empty (Common W₀ Rc OnBytes.TableKey) X₀)), g ∈ O.hs

variable {O : Others Bk W₀ Rc X₀ P₁ Wt} {A : Data} {weights : W₀ → Weights} {rand : Rc → TableRand}

/-- AtEight at the thread of this kind's letters, at b0 := 1, from HalvesIn, where blocks Q returns
the eight (B : Eight Q). -/
theorem atEight2 (B : Eight Q) (sentU : Array OnBytes.OracleNotice) (Cl : Type)
    (H : HalvesIn Q O A weights) :
    AtEight (letters2 Q sentU O Cl).thread 1 Q A weights :=
  atEight_of_flat (letters2 Q sentU O Cl).thread Q A weights B.b1 B.b2 B.b3 B.b4 B.b5 B.b6 B.b7
    B.b8 B.made O.c (flatOf_carried O.c Q B.b1 B.b2 B.b3 B.b4 B.b5 B.b6 B.b7 B.b8 O.tests O.last
      B.made) H.shape H.apart H.own

/-- ChainAt at the thread of this kind's letters. -/
theorem chainAt2 (Q : P14) (sentU : Array OnBytes.OracleNotice) (O : Others Bk W₀ Rc X₀ P₁ Wt)
    (Cl : Type) : ChainAt (letters2 Q sentU O Cl).thread Q O.c fun w => w.key :=
  ⟨fun B => flatOf_carried O.c Q B.b1 B.b2 B.b3 B.b4 B.b5 B.b6 B.b7 B.b8 O.tests O.last B.made,
    fun _ _ _ _ h => h⟩

/-- **FitsAt at the members 1 to 8**, from HalvesIn and SendsIn, where blocks Q returns the eight
(B : Eight Q). -/
theorem fits2 (B : Eight Q) (sentU : Array OnBytes.OracleNotice) (Cl : Type)
    (H : HalvesIn Q O A weights) (Hs : SendsIn Q O A weights rand) :
    FitsAt (letters2 Q sentU O Cl).thread 1 ∧ FitsAt (letters2 Q sentU O Cl).thread 2 ∧
      FitsAt (letters2 Q sentU O Cl).thread 3 ∧ FitsAt (letters2 Q sentU O Cl).thread 4 ∧
      FitsAt (letters2 Q sentU O Cl).thread 5 ∧ FitsAt (letters2 Q sentU O Cl).thread 6 ∧
      FitsAt (letters2 Q sentU O Cl).thread 7 ∧ FitsAt (letters2 Q sentU O Cl).thread 8 :=
  eight_Fits (b0 := 1) (atEight2 B sentU Cl H) Hs

/-- **Accepted at the members 1 to 8, at every fall**, under Plan2, HalvesIn and SendsIn; at the
member 3 besides: every valid input's key has sizes that fit (hkey), and no seed of it has the
factor 0 (hseeds). -/
theorem accepted_all (hQ : Plan2 Q sentU layO) (Cl : Type) (H : HalvesIn Q O A weights)
    (Hs : SendsIn Q O A weights rand)
    (fall : Nat → St → List Fmt.Drawn → Option String) (b : Nat) (h1 : 1 ≤ b) (h8 : b ≤ 8)
    (hkey : b = 3 → ∀ w, O.valid w → keyFits w.key Q.par.S.fold.index = true)
    (hseeds : b = 3 → ∀ w, O.valid w → noZeroFactor w.key = true) :
    Accepted (letters2 Q sentU O Cl).thread fall b := by
  obtain ⟨B⟩ := hQ.eight
  exact accepted_at hQ (chainAt2 Q sentU O Cl) (atEight2 B sentU Cl H) Hs fall b h1 h8 hkey hseeds

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.atEight2
#print axioms ProofFile.Honest.K14.chainAt2
#print axioms ProofFile.Honest.K14.fits2
#print axioms ProofFile.Honest.K14.accepted_all
