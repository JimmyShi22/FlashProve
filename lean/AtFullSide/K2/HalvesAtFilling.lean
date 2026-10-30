-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K2/HalvesAtFilling.lean: the kind "the code switch" (K2): among the first chain's sides of
the filling onlineProverPartsInUse, those of this kind's places are the sides of this kind's lot, in the
lot's order: no other lot lays a side of the kind. No premise.
Statements with their proofs, calls; one definition.

  switchFillLot        the lot as the filling lays it
  filter_kind_flatMap  general: the sides of a kind in a list of lots whose sides stand at the lots'
                       kinds, each lot with its kind, are the sides of the lots of that kind
  first_kind_base      at the filling

By: FirstFill.widerKinds, closeLotAt_kinds, proxLotAt_kinds, wLotAt_halves, widerFillAtCPUOWM_lots.

Limits. The first chain alone. Of sides; nothing on what a side plays.
-/
import Johnson.Desc.ProofFile.Honest.K1.Law.WSideAtFill
import Johnson.Desc.ProofFile.Honest.Thread.FirstFillAll
import Johnson.Desc.ProofFile.Honest.AtPureWiderK12Places

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K2
open ProofFile.Honest ProofFile.Honest.K2 ProofFile.Honest.FirstFill
open VerifiableInference.Desc (KindName)

variable {W₀ : Type}

/-- **The kind's lot as the filling lays it.** -/
def switchFillLot (I : WiderIn W₀) (S : OnBytes.HonestTrace.Sz) :
    HLot (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit :=
  HLot.byPub I.weights fun wt => HLot.byRows (widerRows S) fun D =>
    switchLot D fun w : Local W₀ IndexCommitterCoins ProofFile.Inst Cells => ⟨w.trace, wt w.w₀, w.rc⟩

section
variable {V W X : Type}

/-- No side of a list at a place of another kind's name passes the test. -/
theorem filter_kind_none {l : List (Placed V W X)} {k : KindName} (hk : k ≠ .K2)
    (h : ∀ x ∈ l, x.place.kind = k) : l.filter (fun x => x.place.kind == .K2) = [] := by
  refine List.filter_eq_nil_iff.2 fun x hx => ?_
  rw [h x hx]
  simpa using hk

/-- Every side of a list at places of the kind's name passes the test. -/
theorem filter_kind_all {l : List (Placed V W X)} (h : ∀ x ∈ l, x.place.kind = .K2) :
    l.filter (fun x => x.place.kind == .K2) = l :=
  List.filter_eq_self.2 fun x hx => by rw [h x hx]; rfl

/-- **The sides of the kind in a list of lots**, each lot with its kind. -/
theorem filter_kind_flatMap (Z : ProofFile.Pub) (G : ProofFile.Ground) :
    ∀ ps : List (HLot V W X × KindName), (∀ r ∈ ps, ∀ x ∈ r.1.halves Z G, x.place.kind = r.2) →
      ((ps.map (·.1)).flatMap fun L => L.halves Z G).filter (fun x => x.place.kind == .K2) =
        (ps.filter (·.2 == .K2)).flatMap fun r => r.1.halves Z G
  | [], _ => rfl
  | r :: ps, h => by
    have ih := filter_kind_flatMap Z G ps fun q hq => h q (List.mem_cons_of_mem _ hq)
    have hr := h r (List.mem_cons_self ..)
    rw [List.map_cons, List.flatMap_cons, List.filter_append, ih]
    cases e : r.2 with
    | K2 =>
      rw [e] at hr
      rw [filter_kind_all hr, List.filter_cons_of_pos (by rw [e]; rfl), List.flatMap_cons]
    | K1 | K3 | K4 | K5 | K6 | K7 | K8 | K9 | K10 | K11 | K12 | K13 | K14 | K15 | frame =>
      rw [e] at hr
      rw [filter_kind_none (by decide) hr, List.filter_cons_of_neg (by rw [e]; decide),
        List.nil_append]

end

/-- **At the filling**: the sides of the kind are the kind's lot's. No premise. -/
theorem first_kind_base (I : WiderIn W₀) (o : ProofFile.SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz)
    (O : OnlineProverArguments) (Z : ProofFile.Pub) (G : ProofFile.Ground) :
    (firstOf Z G (onlineProverPartsInUse I o S O).lots).filter (fun x => x.place.kind == .K2) =
      (switchFillLot I S).halves Z G := by
  have hten := filter_kind_flatMap Z G (widerPairs I o S O) (widerKinds I o S O Z G).all
  have hone : ((widerPairs I o S O).filter (·.2 == .K2)) = [(switchFillLot I S, .K2)] := rfl
  rw [hone, ← widerFillAt_lots] at hten
  have hw : ∀ x ∈ (wLotAt (X := Unit) I o O).halves Z G, x.place.kind = .K1 := by
    intro x hx
    rw [wLotAt_halves] at hx
    cases hm : OnBytes.linMessageW Z.first.lin with
    | none =>
      rw [hm] at hx
      cases hx
    | some msg =>
      rw [hm] at hx
      obtain rfl := List.mem_singleton.1 hx
      rfl
  rw [widerFillAtCPUOWM_lots]
  unfold firstOf
  simp only [List.flatMap_append, List.filter_append, List.flatMap_cons, List.flatMap_nil,
    List.append_nil]
  rw [hten, filter_kind_none (by decide) (closeLotAt_kinds I S Z G),
    filter_kind_none (by decide) (proxLotAt_kinds I S Z G), filter_kind_none (by decide) hw]
  simp

end AtFullSide.K2

#print axioms AtFullSide.K2.filter_kind_flatMap
#print axioms AtFullSide.K2.first_kind_base
