--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/IMR/RowsAtPaid.lean: OUR 101 NUMBERS, BY NUMBER (rows_at), WITH TWO OF
ITS NAMED PREMISES PAID BY TERMS THAT LIE; and the count of these numbers. Theorems, proved; two of
them evaluations by the kernel.



  rows_at_plan   rows_at at N := N₀.withTold placesW (toldOf c.blocksInOrder), N₀ free: the book's test at
    every reached state is book_reached_planOk, under the tests on the plan
    (F.planOk). PREMISES THAT STAY: the scope's three · F.planOk · hFk · alike · MadeOwed at Fk.
  rows_at_base   the same at the base that answers "false" everywhere: there "alike" is rfl.
    PREMISES THAT STAY: the scope's three · F.planOk · hFk · MadeOwed at Fk.
  rows_at_mgBase   the same with that base written as the closed meaning's public tests (mgBase.pub,
    Johnson/Desc/Sound/MgBase.lean), at any type W of witnesses: one function, by unfolding.
  makers_count, makers_by_kind   of the written list's 358 numbers (places_len)
    101 bear one of the six kinds: K3 50, K4 12, K5 12, K6 1, K8 25, K11 1.

OBJECT: c.blocksInOrder[k]. USER: K8Owed, RowsAtRch, MadeOwedDigits. LETTERS: N₀, D, z, p, Fk (and base at
rows_at_plan): free: D is tied to nothing: N₀ stands beside D.N, linksW beside D.links, z beside p.

WHO CAN PAY F.planOk: an accepting run of the file's decision holds it (the landed
planOk_of_runEnd, Johnson/Desc/PlanPasses.lean: F.runEnd x v₁ v₂ v₃ = .ok e → F.planOk = true).

What is not claimed. MadeOwed at any sub-protocol. That any state is reached, or that any step
accepts. Anything at the other 257 numbers. No soundness.
-/
import Johnson.IMR.RowsAt
import Johnson.IMR.BookPaidR
import Johnson.Desc.Sound.MgBase

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace IM

open VerifiableInference.Desc (Block Chain FileDescription KindName)
open VerifiableInference.Desc.Sound (mgBase)
open VerifiableInference.Desc.First (S Numbers Pub PubData)
open ProofFile (Cl)

variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base₀ : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **OUR 101, BY NUMBER, UNDER THE TESTS ON THE PLAN.** -/
theorem rows_at_plan {Q : Type} {D : PubData} {base : Pub → Q × S → Bool} {z : Q}
    {p : ProofFile.InstPub} {Fk : ℕ → S → Prop} (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base₀ c A B) (hF : F.planOk = true)
    (N₀ : Numbers) (alike : ∀ q s s', base q (z, s') = base q (z, s)) {k : ℕ} {b : Block S Cl}
    (hb : c.blocksInOrder[k]? = some b) (hq : quietMaker b.place.kind = true)
    (hFk : ∀ s, Fk k s → RF 0 c.blocksInOrder (ProofFile.startS Z) p k s)
    (M : MadeOwed Fk (N₀.withTold placesW (Meaning.Carry.toldOf c.blocksInOrder)) linksW placesW D base z
      0 k b b.place) :
    HandsR Fk (N₀.withTold placesW (Meaning.Carry.toldOf c.blocksInOrder)) linksW placesW
      (LPFK9.HandsAt.EW D base z) 0 k b :=
  rows_at hS hR O (book_reached_planOk hS hR O N₀ hF p) alike hb hq hFk M

/-- **… AND AT THE BASE THAT ANSWERS "FALSE".** -/
theorem rows_at_base {Q : Type} {D : PubData} {z : Q} {p : ProofFile.InstPub} {Fk : ℕ → S → Prop}
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base₀ c A B) (hF : F.planOk = true)
    (N₀ : Numbers) {k : ℕ} {b : Block S Cl}
    (hb : c.blocksInOrder[k]? = some b) (hq : quietMaker b.place.kind = true)
    (hFk : ∀ s, Fk k s → RF 0 c.blocksInOrder (ProofFile.startS Z) p k s)
    (M : MadeOwed Fk (N₀.withTold placesW (Meaning.Carry.toldOf c.blocksInOrder)) linksW placesW D
      (fun _ _ => false) z 0 k b b.place) :
    HandsR Fk (N₀.withTold placesW (Meaning.Carry.toldOf c.blocksInOrder)) linksW placesW
      (LPFK9.HandsAt.EW D (fun _ _ => false) z) 0 k b :=
  rows_at_plan hS hR O hF N₀ (fun _ _ _ => rfl) hb hq hFk M

/-- … written at the closed meaning's public tests. -/
theorem rows_at_mgBase {Q W : Type} {D : PubData} {z : Q} {p : ProofFile.InstPub} {Fk : ℕ → S → Prop}
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base₀ c A B) (hF : F.planOk = true)
    (N₀ : Numbers) {k : ℕ} {b : Block S Cl}
    (hb : c.blocksInOrder[k]? = some b) (hq : quietMaker b.place.kind = true)
    (hFk : ∀ s, Fk k s → RF 0 c.blocksInOrder (ProofFile.startS Z) p k s)
    (M : MadeOwed Fk (N₀.withTold placesW (Meaning.Carry.toldOf c.blocksInOrder)) linksW placesW D
      (mgBase (P := Q) (W := W)).pub z 0 k b b.place) :
    HandsR Fk (N₀.withTold placesW (Meaning.Carry.toldOf c.blocksInOrder)) linksW placesW
      (LPFK9.HandsAt.EW D (mgBase (P := Q) (W := W)).pub z) 0 k b :=
  rows_at_base hS hR O hF N₀ hb hq hFk M

/-- **Of the written list's numbers, 101 bear one of the six kinds.** -/
theorem makers_count :
    ((List.range 358).filter fun k => (kindW k).any quietMaker).length = 101 := by
  decide +kernel

/-- … kind by kind. -/
theorem makers_by_kind :
    [KindName.K3, .K4, .K5, .K6, .K8, .K11].map (fun K =>
      ((List.range 358).filter fun k => kindW k == some K).length) = [50, 12, 12, 1, 25, 1] := by
  decide +kernel

end IM

#print axioms IM.rows_at_plan
#print axioms IM.rows_at_base
#print axioms IM.rows_at_mgBase
#print axioms IM.makers_count
#print axioms IM.makers_by_kind
