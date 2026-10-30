--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Kinds/Law/K6ItemsBack.lean: THREE OF THE ITEMS THAT THE TABLE's ROW OPENS BEHIND THE
SUB-PROTOCOL AT THE OUTPUT HEAD, AT THE COMPOSED MEANING OF ALL HOUSES "mgAll D Mg"
(Johnson/Desc/Sound/MgAll.lean): formsT 24 4 "own" · formsT 24 4 "join" · formsT 24 4
"weights": FROM THIS HOUSE's ELDER RELATION K6Out (Law/RowPins.lean) AT THE COMPONENTS THAT THE LAW
READS OFF THE WITNESS (compCut). THE WAY BACK OF Law/K6AtMgAll.lean's formsSay_mgAll AND
Law/K6OpenedCut.lean's opened_cut. STATED AND PROVED: unfoldings over Law/K6OpenedBack.lean: no new
mathematics.
WHAT IT CANNOT GIVE, FIRST. · TWO OF THE FIVE ITEMS THAT opened_cut NAMES: formsT 24 3 "planes" and
constr 24 "small": K6Out does not read them: they want honest facts of their own · A WITNESS: it
stands at every w: that some w has compCut ... w = the cells and the mask row of an honest run is
another statement · RecordDue and the four public tests at an honest state · an example. SO IT SHOWS
NO ITEM TRUE ANYWHERE: it carries "K6Out holds at these components" to version 9's words. Nothing on
soundness or on hiding.
  weights_idle     at a list of sorts whose number 24 is the head's, the table's name (4, "weights")
                   stands for no run.
  formsBack_mgAll  formsSay_mgAll's three fields, the other way: the forms' sentences give the
                   items.
  **opened_back**  under MgFitsK6 · the sort of segment 24 · K6States · RecordDue at a.2 · the
                   plan's test · one test on N · K9.formsInT at the four names: K6Out Wp a.2
                   (compCut ... w) gives the three items at (a, y, w).

-/
import Johnson.Desc.Kinds.Law.K6AtMgAll
import Johnson.Desc.Kinds.Law.K6OpenedBack

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.Desc.Kinds.Head.Law.AtTable

open OnBytes
open OnBytes.Maker OnBytes.Flat Johnson.Pack
open OnBytes.Params (ReqLayout ReqShape)
open VerifiableInference.OnPublicFiles.Flat (GE)
open VerifiableInference.Desc.First (S ModelPart Numbers Meaning)
open VerifiableInference.Desc.Sound (Mem MsgT Frame SeatsNamed GroupsSeated MgData mgAll namedOnce)

variable {Xi P Tok : Type} {rows cols nR : ℕ} {Wp : OnBytes.Model.Verify.Public}
  {D : MgData Xi P Tok rows cols nR Wp}
  (Mg : Meaning P (Wit (Fin rows → Fin cols → GE) Tok MsgT)) {lay6 : ReqLayout}
  {num : ℕ → ℕ → ℕ} {n rb : ℕ} {tokV : Tok → Fin Inst.Model.ppref.V}
  {req : P × P5J.TS → P5J.TReq}
  {dec : P × P5J.TS → Strs → Option (Fin rows → Fin cols → GE)}
  {hN : SeatsNamed D.arr D.N (Meaning.sizesOf Wp) (seatLay Wp lay6 num)} {hG : GroupsSeated D.ms
      D.N} {tab : ℕ → ℕ}
  {tokH : P × P5J.TS → Fin Inst.Model.ppref.V}

/-- At the head's sort the table's name (4, "weights") stands for no run. -/
theorem weights_idle (hs : D.links[24]? = some .head) : D.runs 24 4 "weights" = [] := by
  show Sound.runsAt D.links 24 4 "weights" = []
  unfold Sound.runsAt
  rw [hs]
  decide

/-- **The forms' sentences give the three items, at the composed meaning.** -/
theorem formsBack_mgAll (F : MgFitsK6 D lay6 num n rb tokV req dec hN hG tab tokH)
    (hs : D.links[24]? = some .head) (a : P × S) (y : Strs)
    (w : Wit (Fin rows → Fin cols → GE) Tok MsgT)
    (hf : ∀ r, K6Name r →
      Sound.formsTQ (D.Rd 24) D.St (D.N.sent 24 0) 3 r a.2 (Sound.seatTab D.cs D.arr D.ms w))
    (hWt : WeightAt Wp a.2 (compCut D.cs D.arr D.ms D.N (Meaning.sizesOf Wp) (seatLay Wp lay6 num)
        Wp (plAt n rb) w).1.toCells (compCut D.cs D.arr D.ms D.N (Meaning.sizesOf Wp) (seatLay Wp
            lay6 num) Wp (plAt n rb) w).2) :
    (mgAll D Mg).formsT 24 4 "own" a y w ∧ (mgAll D Mg).formsT 24 4 "join" a y w ∧
      (mgAll D Mg).formsT 24 4 "weights" a y w := by
  rw [Sound.mgAll_formsT]
  refine ⟨⟨fun p hp => ?_, fun h => absurd h (by decide)⟩,
    ⟨fun p hp => ?_, fun h => absurd h (by decide)⟩, ⟨fun p hp => ?_, fun _ => ?_⟩⟩
  · rw [F.own] at hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl
    · exact hf "norm" (Or.inl rfl)
    · exact hf "policy" (Or.inr (Or.inl rfl))
    · exact hf "logits" (Or.inr (Or.inr (Or.inl rfl)))
  · rw [F.join] at hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    obtain rfl := hp
    exact hf "join" (Or.inr (Or.inr (Or.inr rfl)))
  · rw [weights_idle hs] at hp
    exact absurd hp (List.not_mem_nil)
  · rw [F.wt]
    exact fun _ _ => hWt

/-- **FROM K6Out AT compCut TO THE THREE ITEMS AT VERSION 9.** -/
theorem opened_back (F : MgFitsK6 D lay6 num n rb tokV req dec hN hG tab tokH)
    (hs : D.links[24]? = some .head) (P8 : K8.ReadsQuiet.PH) (l piece : ℕ)
    (states : ℕ → List (K9.RunOf S))
    (KS : K6States Wp.hS (readsOf Wp) (parOf Wp.hS (workOf Wp)) l piece states 3)
    (a : P × S) (y : Strs) (w : Wit (Fin rows → Fin cols → GE) Tok MsgT) (aK : K9.Part)
    (cU : ℕ × String)
    (R : RecordDue D.arr D.N Wp lay6 num n rb P8 D.St states (D.Rd 24) a.2 aK cU)
    (hok : (parOf Wp.hS (workOf Wp)).ok = true) (h1 : namedOnce D.arr D.N 24 n = true)
    (hIn : ∀ r, K6Name r → K9.formsInT (D.Rd 24) (D.N.sent 24 0) 3 r a.2 = true)
    (hO : K6Out Wp a.2 (compCut D.cs D.arr D.ms D.N (Meaning.sizesOf Wp) (seatLay Wp lay6 num) Wp
      (plAt n rb) w)) :
    (mgAll D Mg).formsT 24 4 "own" a y w ∧ (mgAll D Mg).formsT 24 4 "join" a y w ∧
      (mgAll D Mg).formsT 24 4 "weights" a y w := by
  obtain ⟨hWt, hf⟩ := Came.forms_of_k6Out_cut D.cs D.arr D.ms D.N Wp lay6 num n rb P8 l piece states
    KS (D.Rd 24) D.St a.2 aK cU w R hok h1 hIn hO
  exact formsBack_mgAll Mg F hs a y w hf hWt

end VerifiableInference.Desc.Kinds.Head.Law.AtTable

#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.weights_idle
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.formsBack_mgAll
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.opened_back
