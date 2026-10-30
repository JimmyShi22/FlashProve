-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/Law/K12Law15.lean: THE CLAIM's HALF OF A PROXIMITY TEST's ROW OF THE KEY FILE's TABLES, ITS «law»: THE ITEMS THAT THE ROW CLOSES HOLD AT THE WITNESS WITH THE CANDIDATE's TABLE LAID: THE TWO GENERAL LAYERS. Statements with proofs; each is calls of other files' lemmas. IT MOVES THE WEIGHT INTO NAMED PREMISES; IT PAYS NONE.
OBJECT. The premise «law» of back_15 (Johnson/RunOne/Law/KeyRide15.lean): for each item of the row's ins ([grows, pin 1] at row 1.15): it holds at the verifier's state in front of the test and the witness layAt at_ [1] (fun _ => m) w.
USER. The join at the tables' files' filling (to come).
LETTERS. The tables' (F · G · at_ · K · R · X); the composition's over the proximity test's law (cs · mem · rd · m).
  pin_laid: a member of the word's list that meets the sample, laid as message k, IS pinned there. GENERAL IN ALL LETTERS. By msgOf_layAt (Johnson/Desc/Key/KeyLay.lean).
  grows_laid: AT M := Fill.Tab: where all rows that the test takes in say their claims of the tuple's words, and the group has the one member o: the item "grows" holds at the witness with the tuple's table laid as message 1. ONE CALL of grows_of_allSay (GrowsOfAllSay.lean); its premise on the words by hval_of_links (K12Hval.lean), with reads_layAt.
ONE TABLE FOR BOTH ITEMS: ofU … (m x₁).
PREMISES ON THE TABLES' FILES' LETTERS: ArrOk · ReadsPinned · LayIdem at [1] · R.same reads alike · hread.
Limits. As empty as its premises. Nothing on soundness, nothing on hiding.

-/
import Johnson.RunOne.Law.K12Hval
import Johnson.RunOne.Law.GrowsOfAllSay
import Johnson.Desc.Key.KeyLay

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Johnson.RunOne.Law.K12Law15
open VerifiableInference.Desc VerifiableInference.Desc.Sound VerifiableInference.Desc.Key VerifiableInference.Desc.Key.Fill
open Cb Johnson.Pack OnBytes OnBytes.Maker OnBytes.Slice
open OnBytes.Model (Reading)
open OnBytes.Means (AllSay OpenKinds InOrder)
open H2K.Pin (tabP)

/-- **A member that is laid is pinned.** -/
theorem pin_laid {A Cells M Smp Rec XI : Type} (F : FileDescription XI) (G : VerifiableInference.Desc.Reading A Cells M Smp Rec) (at_ : Where)
    (k : ℕ) (μ : M) (a : A) (y : Strs) (w : Wit Cells Unit M) (ha : ArrOk G at_ [k]) (hi : LayIdem G)
    (o : VerifiableInference.Desc.Oracle) (z : Smp) (ho : F.oracleAt (at_ k).1 = some o)
    (hz : G.smp a (at_ k).1 (at_ k).2 = some z) (hM : Member F G o (at_ k).1 (at_ k).2 y z μ) :
    PIN F G (at_ k).1 (at_ k).2 a y (layAt at_ [k] (fun _ => μ) w) := by
  refine ⟨o, z, ho, hz, ?_⟩
  rw [msgOf_layAt G at_ [k] (fun _ => μ) w ha hi
    (fun k₁ h₁ k₂ h₂ _ => (List.mem_singleton.1 h₁).trans (List.mem_singleton.1 h₂).symm) k (List.mem_singleton.2 rfl)]
  exact hM

/-- **The item "grows" at the witness with the tuple's table laid.** -/
theorem grows_laid {P St Cells A' Smp Rec : Type} (cs : Codes) (K : KPlan) (R : KRead Cells Fill.Tab) (X : KReaders St)
    (near : ℕ → P × St → Strs → Prop)
    (forms worth other : ℕ → String → P × St → Strs → Wit Cells Unit Fill.Tab → Prop)
    (G : VerifiableInference.Desc.Reading A' Cells Fill.Tab Smp Rec) (at_ : Where) (a : P × St) (y : Strs) (w : Wit Cells Unit Fill.Tab)
    (g : ℕ) (G0 : Group) (o : ℕ) (x : OnBytes.Oracle)
    (hg : X.grpB a.2 = some g) (hG : (X.st a.2).groups[g]? = some G0) (ho : K.orc 1 = some o)
    (hx : (X.st a.2).oracles[o]? = some x) (hne : G0.rows.size ≠ 0) (hone : G0.members.toList = [o])
    (hsame : R.same = fun a b => readE a = readE b) (hI : InOrder (X.st a.2)) (hK : OpenKinds (X.st a.2))
    (mem : ℕ → Option Mem) (rd : (x : Mem) → ((sigOf cs x.1.l).om x.2).Msg → Part → ℕ → GE)
    (hrd : ∀ x m part i, rd x m part i = tabP cs (x.1.l.get x.2).1 m part i)
    (m : (x : Mem) → ((sigOf cs x.1.l).om x.2).Msg) (x₁ : Mem) (hmem : mem o = some x₁) (hnum : K.num o = some 1)
    (h : AllSay Reading.gl (begun (X.st a.2) g G0) (runRows (X.st a.2) G0).toList (_root_.Desc.K14.Law.wordsT cs mem rd m))
    (ha : ArrOk G at_ [1]) (hr : ReadsPinned G at_ R [1]) (hi : LayIdem G)
    (hread : ∀ part i, readE (R.val (ofU cs (x₁.1.l.get x₁.2).1 (x₁.1.l.get x₁.2).2 (m x₁)) part i) =
      ofU cs (x₁.1.l.get x₁.2).1 (x₁.1.l.get x₁.2).2 (m x₁) part i) :
    (meaning₁ K R X near forms worth other).grows a y
      (layAt at_ [1] (fun _ => ofU cs (x₁.1.l.get x₁.2).1 (x₁.1.l.get x₁.2).2 (m x₁)) w) := by
  refine GrowsOfAllSay.grows_of_allSay K R X near forms worth other a y _ g G0 o x hg hG ho hx hne
    (by rw [hone]; exact List.mem_singleton.2 rfl) hsame hI hK _ h ?_
  intro o' ho' pt i _
  rw [hone] at ho'
  obtain rfl : o' = o := List.mem_singleton.1 ho'
  exact K12Hval.hval_of_links cs K R mem rd hrd m _ o' 1 x₁ hmem hnum
    (reads_layAt G at_ R [1] _ w ha hr hi
      (fun k₁ h₁ k₂ h₂ _ => (List.mem_singleton.1 h₁).trans (List.mem_singleton.1 h₂).symm) 1 (List.mem_singleton.2 rfl))
    hread pt i

end Johnson.RunOne.Law.K12Law15

#print axioms Johnson.RunOne.Law.K12Law15.pin_laid
#print axioms Johnson.RunOne.Law.K12Law15.grows_laid
