-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K9/FallDebtAttList.lean: K9's FALL AS THE LIST OF FALLS LAYS IT (Honest/K9/FallTies.lean),
IN THE COVER's FORM, AT THE BATCHING OF AN ATTENTION SEGMENT, UNDER THE LIBRARY's HEAD: WHAT IS ASKED OF A STAND IS
THREE CLAUSES OF TWO OTHER HOUSES, AND THAT IT IS REACHED BY THE WRAPPED BLOCKS. Statements and proofs; no prover is in
this file, and no goal is stated.
  **`k9_fallDebt_att_list`**, **`k9_fallDebt_att_list_blocks`**   from the head, g < 12, K9's seat at 2 g + 1 (at the
      number 7), the segment's plan a, the two lookups' places, the stretch's one typed round d, and a letter Q on the
      stands: Q fr s' gives `HeldLive a.own (Forest.elems a.fs) s'` · the lookups' `Clause pC
      s'.lookHeard?` · their `Clause pD (s'.tl?.bind (·.heard))` · s' is reached by the chain's wrapped blocks
      (`cF.blocksInOrder.map Sound.below`) in front of the batching, from the letter start: `FallDebt` of `quietFall p
      w.2.2.filled (w.2.1 - 1) notGood` at the seated batching block: n, top and the bound ARE THE LIST's OWN:
      FallTies.lean's `k9_fallDebt_list`, `k9_fallDebt_list_blocks` at l := 2 g + 1
HOW. `goodW` by `goodW_att_clauses_all` (Honest/K9/GoodAttEight.lean) · "reached by the chain's own blocks", which
FallTies.lean asks, by the library's `reach_raw` (Johnson/Top/H0/Walk/Reach.lean) · the ledger's planned number of
claims, which Honest/K9/FallDebtAttClauses.lean asks as a fourth thing, is no premise here: `planned_at_front` pays it
inside `k9_fallDebt_list`.
A FORM, NOT A DEBT PAID: all that FallTies.lean's head says of its two holds of these, but that `goodW` is no premise
here. notGood · d · ft · Q · start · u ARE LETTERS. At a Q that never holds they hold idly. SINCE THIS FILE the words
"outside this file the nine are called by no line; Honest/K9/AllTogether.lean alone imports it" (FallTies.lean's head)
and "called by no line but one another's" (Honest/K9/GoodAttEight.lean's) are overtaken: this file calls two of the nine
and `goodW_att_clauses_all`; Honest/K9/FallDebtAttClauses.lean calls `lookLive_of_clauses_all`. These files are not
turned.
WHAT IS NOT CLAIMED. The four at any stand of any Q; that K5's hearing begins at the slot `Forest.elems a.fs`; that a
state is reached. No number is evaluated. No member: called by no line. Nothing on any property.
GROUND: beneath this file, beside the sealed library, lie 290 files, this one among them: reading copies, all but ours.
-/
import Johnson.Desc.ProofFile.Honest.K9.FallTies
import Johnson.Desc.ProofFile.Honest.K9.GoodAttEight
import Johnson.Top.H0.Walk.Reach

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model
open OnBytes.Maker (RDT)
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open Johnson.Desc.First.Walk.Tied (Reach)
open ProofFile.Honest (Odds Fall FallDebt)
open Iop
open H2K5.Honest (HeldLive)
open VerifiableInference.Desc.First.Look (placeAt)
open ProofFile.Honest.K3.Good.Live (Clause)
open scoped ENNReal

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : First.Look.Place}

/-- **K9's fall at an attention segment's batching, AT THE LIST's OWN NUMBERS, at typed challenges**: from two houses'
three clauses at the stand, and that it is reached by the wrapped blocks. -/
theorem k9_fallDebt_att_list (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {g : ℕ} (hg : g < 12)
    {Lk : Link S ProofFile.Cl} {p : Desc.K9.Where} {w : Desc.K9.SegSort × ℕ × Desc.K9.TWhere}
    (Sd : SeatedFree cF Zp (2 * g + 1) 7 Lk p w) (u : HTailF2) {a : OnBytes.Attention.Plan}
    (ha : (P5J.At.X Zp).A[g]? = some a) {pC pD : First.Look.P}
    (hC : placeAt (P5J.At.X Zp) (2 * g + 1) false = some pC) (hD : placeAt (P5J.At.X Zp) (2 * g + 1) true = some pD)
    (d : RDT) (he : d.entry = Desc.K9.entry p) (h5 : d.kind ≠ .seeds) (h6 : d.kind ≠ .sealed) (notGood : Odds)
    (ft : ℕ) (Q : List Fmt.Drawn → S → Prop) {Q' : Type} (start : Q' → S)
    (hQ : ∀ fr s', Q fr s' → HeldLive a.own (Forest.elems a.fs) s' ∧ Clause pC s'.lookHeard? ∧
      Clause pD (s'.tl?.bind (·.heard)) ∧
      ∃ z, Reach 0 (cF.blocksInOrder.map Sound.below) start (14 * (2 * g + 1) + 9) (z, s')) :
    FallDebt (_root_.Run.ck .two) (quietFall p w.2.2.filled (w.2.1 - 1) notGood) ft
      (Lk.batch (claimsInBy Lk.each Lk.hear Lk.order)) (cF.blocksInOrder.drop (14 * (2 * g + 1) + 9 + 1)) [d] [] Q
      (((w.2.2.filled * (w.2.1 - 1) : ℕ) : ℝ≥0∞) / ((sizeOfE : ℕ) : ℝ≥0∞)) := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have n24 : ¬ 2 * g + 1 = 24 := by omega
  have Sd' : SeatedFree cF Zp (2 * g + 1) (if 2 * g + 1 = 24 then 9 else 7) Lk p w := by
    rw [if_neg n24]
    exact Sd
  have K := k9_fallDebt_list h.scope h.reads O (l := 2 * g + 1) (by omega) Sd' d he h5 h6 notGood ft Q start
    (fun fr s' q => by
      obtain ⟨hI, JC, JD, z, hr⟩ := hQ fr s' q
      refine ⟨goodW_att_clauses_all h hg Sd u ha hC hD s' hI JC JD, z, ?_⟩
      rw [if_neg n24]
      exact Johnson.Desc.First.Walk.Tied.reach_raw hr)
  rw [if_neg n24] at K
  exact K

/-- **At strings of hash blocks.** -/
theorem k9_fallDebt_att_list_blocks (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {g : ℕ} (hg : g < 12)
    {Lk : Link S ProofFile.Cl} {p : Desc.K9.Where} {w : Desc.K9.SegSort × ℕ × Desc.K9.TWhere}
    (Sd : SeatedFree cF Zp (2 * g + 1) 7 Lk p w) (u : HTailF2) {a : OnBytes.Attention.Plan}
    (ha : (P5J.At.X Zp).A[g]? = some a) {pC pD : First.Look.P}
    (hC : placeAt (P5J.At.X Zp) (2 * g + 1) false = some pC) (hD : placeAt (P5J.At.X Zp) (2 * g + 1) true = some pD)
    (d : RDT) (he : d.entry = Desc.K9.entry p) (h5 : d.kind ≠ .seeds) (h6 : d.kind ≠ .sealed) (notGood : Odds)
    (ft : ℕ) (Q : List Fmt.Drawn → S → Prop) {Q' : Type} (start : Q' → S)
    (hQ : ∀ fr s', Q fr s' → HeldLive a.own (Forest.elems a.fs) s' ∧ Clause pC s'.lookHeard? ∧
      Clause pD (s'.tl?.bind (·.heard)) ∧
      ∃ z, Reach 0 (cF.blocksInOrder.map Sound.below) start (14 * (2 * g + 1) + 9) (z, s')) :
    FallDebt (_root_.Run.ckP .two) (quietFall p w.2.2.filled (w.2.1 - 1) notGood) ft
      (Lk.batch (claimsInBy Lk.each Lk.hear Lk.order)) (cF.blocksInOrder.drop (14 * (2 * g + 1) + 9 + 1)) [d] [] Q
      (kapSl 128 ^ 3 * ((w.2.2.filled * (w.2.1 - 1) : ℕ) : ℝ≥0∞) / ((sizeOfE : ℕ) : ℝ≥0∞)) := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have n24 : ¬ 2 * g + 1 = 24 := by omega
  have Sd' : SeatedFree cF Zp (2 * g + 1) (if 2 * g + 1 = 24 then 9 else 7) Lk p w := by
    rw [if_neg n24]
    exact Sd
  have K := k9_fallDebt_list_blocks h.scope h.reads O (l := 2 * g + 1) (by omega) Sd' d he h5 h6 notGood ft Q start
    (fun fr s' q => by
      obtain ⟨hI, JC, JD, z, hr⟩ := hQ fr s' q
      refine ⟨goodW_att_clauses_all h hg Sd u ha hC hD s' hI JC JD, z, ?_⟩
      rw [if_neg n24]
      exact Johnson.Desc.First.Walk.Tied.reach_raw hr)
  rw [if_neg n24] at K
  exact K

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.k9_fallDebt_att_list
#print axioms ProofFile.Honest.K9.k9_fallDebt_att_list_blocks
