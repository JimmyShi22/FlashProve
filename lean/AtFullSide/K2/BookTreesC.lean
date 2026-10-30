-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K2/BookTreesC.lean: a helper of AtFullSide/K2/BookTrees.lean: THE SENDERS THAT A CODE
SWITCH READS, AT THE WRITTEN LISTS: one public test, put to Lean's kernel once, and its tie to the
senders' plans under the head `P5J.AtMg` and the opening.

  `senderFits codes sent b`   the test on one sender: its number is 2 or more; the trees that its
                    plan lays have room among the oracle messages that sub-protocol number b states
                    (`treesTold toldFull`); tree by tree the written list of shapes (`LFull`) has the
                    plan's shape at the place (trees stated in front of b) + τ
  `sendersWritten`   the 76 senders at the written values: the opening · 50 later senders · the
                    25 switches of `placesW`
  `senders_fit`      the test says yes at all of them: by the kernel
  `senders_fit_fails`  a control: it says no where the opening's plan is asked at number 5
  `sender_fits_at_head`  under the head and the opening the test says yes at each sender's own plan
-/
import Johnson.Desc.ProofFile.Honest.K2.SeatedL
import Johnson.Desc.ProofFile.Honest.K2.Law.PlacesWritten
import Johnson.Desc.ProofFile.Honest.K2.Law.SwitchNo
import Johnson.Desc.K1.Law.LaterOne
import Johnson.Desc.K1.Law.PlanOwn
import Johnson.Desc.K1.Law.QFull
import Johnson.HB.LLHARD.LaidWritten
import Johnson.HB.LLHARD.PlanInScope
import Johnson.Goal.Skeleton.PinsOfLaid

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.K2
open OnBytes
open VerifiableInference.Desc (Block Chain)
open VerifiableInference.Desc.K1 (Par firstPar parLater parL noL gpOf qFull gpFull laterFull
  LikeFull firstPar_full parLater_full)
open VerifiableInference.Desc.K13.Law (LFull)
open VerifiableInference.Desc.First (treesTold)
open VerifiableInference.Desc.First.K2Ties (toldFull)
open VerifiableInference.Desc.Own (treesMade)
open OnBytes.Maker (WholeD)
open P5J (AtMg F0T TS)
open _root_.Desc.K14.Law (secondAt seatZ)
open ProofFile.Honest.K2 (SwitchPlace switchPar switchPlaces)
open ProofFile.Honest.K2.Law (switchNo placesW places_at_head)

/-- **The test on one sender.** codes, sent: its plan's codes and messages. b: its number in the
first chain. -/
def senderFits (codes : Codes) (sent : Array OracleNotice) (b : Nat) : Bool :=
  decide (2 ≤ b) &&
    decide (treesTold toldFull b + ((treesMade codes sent).getD {}).shapes.size ≤
      treesTold toldFull (b + 1)) &&
    (List.range ((treesMade codes sent).getD {}).shapes.size).all fun τ =>
      LFull.shapes[treesTold toldFull b + τ]? == some (((treesMade codes sent).getD {}).shapes.getD τ {})

/-- What the test says. -/
theorem senderFits_says {codes : Codes} {sent : Array OracleNotice} {b : Nat}
    (h : senderFits codes sent b = true) :
    2 ≤ b ∧ treesTold toldFull b + ((treesMade codes sent).getD {}).shapes.size ≤
        treesTold toldFull (b + 1) ∧
      ∀ τ, τ < ((treesMade codes sent).getD {}).shapes.size →
        LFull.shapes[treesTold toldFull b + τ]? =
          some (((treesMade codes sent).getD {}).shapes.getD τ {}) := by
  unfold senderFits at h
  rw [Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq,
    List.all_eq_true] at h
  exact ⟨h.1.1, h.1.2, fun τ hτ => eq_of_beq (h.2 τ (List.mem_range.2 hτ))⟩

/-- **The senders at the written values.** -/
def sendersWritten : List (Par × Nat) :=
  (firstPar qFull gpFull, 2) ::
    ((List.range 25).flatMap fun l => [false, true].map fun d => (laterFull l d, noL l d)) ++
    placesW.map fun p => (switchPar p, switchNo p)

set_option maxRecDepth 1000000 in
/-- **The test says yes at all of them.** -/
theorem senders_fit : (sendersWritten.all fun x => senderFits x.1.codes x.1.sent x.2) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- **The test can fail**: the opening's plan at number 5, which is a later sender's. -/
theorem senders_fit_fails :
    senderFits (firstPar qFull gpFull).codes (firstPar qFull gpFull).sent 5 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- The list is not empty: 76 senders. -/
theorem senders_count : sendersWritten.length = 76 := by decide +kernel

theorem fits_of_mem {x : Par × Nat} (hx : x ∈ sendersWritten) :
    senderFits x.1.codes x.1.sent x.2 = true :=
  List.all_eq_true.1 senders_fit x hx

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {Bs : ProofFile.PureBase} {base : List (Block TS ProofFile.Cl)}

/-- **Under the head and the opening the test says yes at each sender's own plan.** The premise on
P and b is the body of `SenderAt` (AtFullSide/K2/BookTrees.lean). -/
theorem sender_fits_at_head (h : AtMg OnBytes.secondHashFunction Z D r Zp Np cF)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    {P : Par} {b : Nat}
    (hP : (P = firstPar Bs.G₀.first (gpOf Zp) ∧ b = 2) ∨
      (∃ l d, l < 25 ∧ P = parL Zp Bs.G₀ l d ∧ b = noL l d) ∨
      ∃ p₀ ∈ switchPlaces Zp Bs.G₀, P = switchPar p₀ ∧ b = switchNo p₀) :
    senderFits P.codes P.sent b = true := by
  have hF : LikeFull Bs.G₀.first := by
    rw [O.first]
    exact VerifiableInference.Desc.K13.Law.likeFull_in_scope h.scope h.laid.pub
      (P5J.pins_of_laid h.scope h.laid).1
  rcases hP with ⟨rfl, rfl⟩ | ⟨l, d, hl, rfl, rfl⟩ | ⟨p₀, hp₀, rfl, rfl⟩
  · rw [firstPar_full hF]
    exact fits_of_mem (x := (firstPar qFull gpFull, 2)) List.mem_cons_self
  · have hm : (laterFull l d, noL l d) ∈ sendersWritten :=
      List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_flatMap.2
        ⟨l, List.mem_range.2 hl, List.mem_map.2 ⟨d, by cases d <;> simp, rfl⟩⟩))
    have e := fits_of_mem hm
    cases d with
    | true =>
      show senderFits (parLater Bs.G₀.first (gpOf Zp) l (IM.k1Ix l true + 1) 2).codes
        (parLater Bs.G₀.first (gpOf Zp) l (IM.k1Ix l true + 1) 2).sent (noL l true) = true
      rw [parLater_full hF]
      exact e
    | false =>
      show senderFits (parLater Bs.G₀.first (gpOf Zp) l (IM.k1Ix l false + 1) 1).codes
        (parLater Bs.G₀.first (gpOf Zp) l (IM.k1Ix l false + 1) 1).sent (noL l false) = true
      rw [parLater_full hF]
      exact e
  · rw [places_at_head h O] at hp₀
    exact fits_of_mem (x := (switchPar p₀, switchNo p₀)) (List.mem_cons_of_mem _
      (List.mem_append_right _ (List.mem_map.2 ⟨p₀, hp₀, rfl⟩)))

end AtFullSide.K2

#print axioms AtFullSide.K2.senderFits_says
#print axioms AtFullSide.K2.senders_fit
#print axioms AtFullSide.K2.senders_fit_fails
#print axioms AtFullSide.K2.senders_count
#print axioms AtFullSide.K2.sender_fits_at_head
