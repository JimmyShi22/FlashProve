-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LinkSim/AtText/SeamCounts.lean: for all parameters, how many positions of each of the two
tables the link's verifier reads, and that its decision is local.
Terms: Johnson/LinkSim/Spec.lean; for the prover's algorithm, Johnson/LinkSim/AtText/Defs.lean.

What this file proves. The link's protocol linkProtocolOfRoundData (OnBytes/Flat/LinkSib.lean) is taken in general
form: its rounds' description ds, the tables' depth a, its list xs of openings of the two tables and
its decision function dec are all variables. Spec.linkCounts, proved as linkCounts, says this.
Suppose every tree that a round of ds opens has a number below 2^16. Then, at every instance and
verifier message, the verifier reads at most cntOf false xs positions of the first table and at most
cntOf true xs positions of the copy (cntOf, Run/PlanQXDoor.lean). Each count is the sum of the
counts that xs has for that table. The verifier is also local: its decision depends on the oracles
only at the positions that it reads (IsLocal, Iop/InteractiveOracleProof.lean).

How it fits. The premises of index privacy ask of the link's protocol, besides a simulator, among
other things these two counts and locality (LinkBeside, Johnson/LinkSim/Spec.lean). SeamAtFull2.lean
evaluates the counts at the full-size parameters, where both are 62. linkCounts goes on through
SeamAtFull2.lean's fr_linkCounts to home_beside (Johnson/LinkSim/AtHome/HomeTies.lean), which
link_all_met (Johnson/LinkSim/AtHome/CompileFiller.lean) uses.

The other names (namespace OnBytes.LinkSim.Seam).
  sideXL_len, xSide_len, side_card   one table's count, by induction over the rounds.

Sources. The three lemmas on one table's count repeat the library's own of the same names
(Run/PlanQXDoorProofs.lean), which are stated for the first form of the rounds' data; here they are
stated for the form with several trees a round (OnBytes/TypedOracleCompiler/Run/PlanQX.lean). The lemmas that do not
name the rounds' data are called, not stated again.

Limits.
- The counts are upper bounds: challenges that repeat a position lower the number read.

Notes. LinkBeside itself is about a protocol structure. It is proved of one in SeamAtFull2.lean, and
of homeR b Z's own protocol structure, at 62 and 62, in Johnson/LinkSim/AtHome/HomeTies.lean.
Terms: lean/GLOSSARY.md.

-/
import Johnson.LinkSim.Spec
import OnBytes.Flat.LinkSib
import Run.PlanQXDoorProofs
import OnBytes.TypedOracleCompiler.Run.PlanQXLawsProofs

set_option autoImplicit false

noncomputable section

namespace OnBytes.LinkSim.Seam
open OnBytes.LinkSim
open OnBytes.Flat (linkProtocolOfRoundData linkW_local)
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run.PQ (CK View XO SgX storedKey xsAt xPos cntOf keepS keepS_own sideA_len xsAt_side
  filterMap_len_le xPos_side)
open TypedOracleCompiler.Run.PQ (RD SOf drawnSL wantedX wantedXL xWanted)

/-- From round i on, one table's number of wanted positions is at most the sum of the counts that
the openings from round i on have for it. -/
theorem sideXL_len (a : ℕ) (all : List RD) (xs : List XO) (b : Bool) :
    ∀ (i : ℕ) (ds : List RD) (Ds : List Fmt.Drawn), (∀ d ∈ ds, ∀ n ∈ d.opens, n < 2 ^ 16) →
      ((wantedXL a all xs i ds Ds).filterMap (keepS b)).length ≤
        (((xs.filter fun o => o.which == b).filter fun o => decide (i ≤ o.round)).map
          (·.count)).sum
  | _, [], _, _ => by simp [wantedXL]
  | _, _ :: _, [], _ => by simp [wantedXL]
  | i, d :: ds, D :: Ds, h => by
      have ih := sideXL_len a all xs b (i + 1) ds Ds fun e he => h e (List.mem_cons_of_mem _ he)
      rw [wantedXL, List.filterMap_append, List.filterMap_append, List.length_append,
        List.length_append, _root_.Run.PQ.sum_split i (xs.filter fun o => o.which == b),
        ← xsAt_side]
      refine le_trans
        (Nat.add_le_add
          (Nat.add_le_add (sideA_len a D b _)
            (Nat.le_of_eq
              (congrArg List.length (List.filterMap_eq_nil_iff.2 fun kx hkx => keepS_own b kx ?_))))
          ih) (by simp)
      obtain ⟨n, hn, hm⟩ := List.mem_flatMap.1 hkx
      split at hm
      · cases hm
      · obtain ⟨x, _, rfl⟩ := List.mem_map.1 hm
        exact h d List.mem_cons_self n hn

/-- One table's number of wanted positions is at most cntOf b xs. -/
theorem xSide_len (a : ℕ) (ds : List RD) (xs : List XO) (Ds : List Fmt.Drawn) (b : Bool)
    (h : ∀ d ∈ ds, ∀ n ∈ d.opens, n < 2 ^ 16) :
    ((xWanted a ds xs Ds).filter fun wx => wx.1 == b).length ≤ cntOf b xs := by
  have h1 := sideXL_len a ds xs b 0 ds Ds h
  rw [List.filter_eq_self.2 (fun o _ => decide_eq_true (Nat.zero_le _))] at h1
  have e : ((xWanted a ds xs Ds).filter fun wx => wx.1 == b) =
      (wantedX a ds xs Ds).filterMap (keepS b) :=
    List.filter_filterMap
  rw [e]
  exact h1

/-- One table's number of distinct positions read is at most cntOf b xs. -/
theorem side_card (ds : List RD) (a : ℕ) (xs : List XO) (Ds : List Fmt.Drawn) (b : Bool)
    (hown : ∀ d ∈ ds, ∀ n ∈ d.opens, n < 2 ^ 16) :
    ((((xWanted a ds xs Ds).filterMap (xPos (2 ^ a))).toFinset).filter fun p =>
        (p.isRight == b) = true).card ≤ cntOf b xs := by
  rw [← List.toFinset_filter]
  refine le_trans (List.toFinset_card_le _) ?_
  rw [List.filter_filterMap]
  refine le_trans (filterMap_len_le _ (fun wx => wx.1 == b) (fun wx hs => ?_) _)
    (xSide_len a ds xs Ds b hown)
  cases hp : xPos (2 ^ a) wx with
  | none => rw [hp] at hs; cases hs
  | some p =>
      rw [hp] at hs
      have e := xPos_side _ wx p hp
      cases hb : (p.isRight == b) with
      | true =>
          show (wx.1 == b) = true
          rw [← e]
          exact hb
      | false => simp [Option.filter, hb] at hs

/-- Statement only; proved as linkCounts below. **How many positions of each table the link's
verifier reads, and locality**: where every tree that a round opens has a number below 2^16, at most
cntOf false xs of the first table and cntOf true xs of the copy. -/
def Spec.linkCounts : Prop :=
  ∀ (K : CK) (ds : List RD) (a : ℕ) (xs : List XO) (Xi : Type) (dec : Xi → View → Bool),
    (∀ d ∈ ds, ∀ n ∈ d.opens, n < 2 ^ 16) →
    (∀ x ρ, (((linkProtocolOfRoundData K ds a xs dec).extReads x ρ).filter fun p => p.isLeft).card ≤
      cntOf false xs) ∧
    (∀ x ρ, (((linkProtocolOfRoundData K ds a xs dec).extReads x ρ).filter fun p => p.isRight).card ≤
      cntOf true xs) ∧
    (linkProtocolOfRoundData K ds a xs dec).IsLocal

/-- Proof of Spec.linkCounts. -/
theorem linkCounts : Spec.linkCounts := by
  intro K ds a xs Xi dec hown
  refine ⟨fun _ ρ => ?_, fun _ ρ => ?_, linkW_local K ds a xs dec⟩
  · have := side_card ds a xs (drawnSL K ds ρ.2) false hown
    refine le_trans
      (Nat.le_of_eq (congrArg Finset.card (Finset.filter_congr fun p _ => ?_))) this
    cases p <;> simp
  · have := side_card ds a xs (drawnSL K ds ρ.2) true hown
    refine le_trans
      (Nat.le_of_eq (congrArg Finset.card (Finset.filter_congr fun p _ => ?_))) this
    cases p <;> simp

end OnBytes.LinkSim.Seam

#print axioms OnBytes.LinkSim.Seam.side_card
#print axioms OnBytes.LinkSim.Seam.linkCounts
