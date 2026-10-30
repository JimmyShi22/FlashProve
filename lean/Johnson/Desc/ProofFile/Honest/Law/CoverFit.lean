-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/CoverFit.lean: TWO SORTS OF MARKS THAT THE FRAME ITSELF LAYS, AND
WHAT PAYS THEM. (1) THE FIT. `state_in_thread` (Honest/Law/CoverThread.lean; not in the sealed
library) asks that the challenges in front are such as the rounds in front can draw (`drawsFit`). A
debt is asked at every list fr, and of what `debt_join` (Honest/Law/CoverJoin.lean) has in hand at Q
:= `silentQ` nothing says so (found by another author of this folder). So one mark more a member:
`fitMarks`: it speaks where the member's own challenges are not such as its rounds can draw. The
silence then gives the fit (`fit_of_silent`); under a kit whose typed challenges always fit, the
mark never speaks at a typed message (`fitMark_debt`: any number). (2) THE STOPS' MARKS
(`stopMarks`, Honest/Law/CoverStops.lean): a member's stop mark is paid from its parts' own
sentences (`StopDebt`, Honest/Law/SharesParts.lean): `stopDebt_any`: the two sorts' sentences give
«the part stops, by either stop»; `stopMark_debt`: `MarkDebt` at the sum of the member's gates'
numbers.

WHAT THIS IS. A definition that fills a letter of the cover (no owner is asked to meet it), lemmas
on lists, and conditional lemmas on the library's own measure. None of the library's goals.

  0  `mark_silent`, `markOf_none_of`
  1  `fitMarks`, `fit_of_quiet`, `fit_of_silent`, `fitMark_debt`
  2  `stopDebt_any`, `stopMark_debt`

Limits. That a kit's typed challenges always fit a member's rounds is a premise (at `Run.ckP .two`:
Honest/Law/KitTwo.lean, DueData.lean). THE STOPS' NUMBERS ARE COUNTED TWICE where the withheld set's
measure is added beside the falls' number. This file proves nothing about soundness, completeness,
hiding or any other property of the protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.CoverPay
import Johnson.Desc.ProofFile.Honest.Law.SharesParts
import Johnson.Desc.ProofFile.Honest.Law.SharesStops

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open Prob
open scoped ENNReal
open VerifiableInference.Desc
open OnBytes.Maker (RDT uLT drawnT)
open _root_.Run.PQ (CK)

variable {S Cl V W Y : Type}

/-! ## 0 One mark of a list -/

/-- Where the marks at a place are silent, each mark of the list that stands there is. -/
theorem mark_silent {ms : List Mark} {mk : Mark} (hmem : mk ∈ ms) {fr own : List Fmt.Drawn}
    (h : (markOf ms mk.place fr own).isSome = false) : mk.test fr own = none := by
  cases ht : mk.test fr own with
  | none => rfl
  | some _ =>
    exfalso
    unfold markOf at h
    have hf : mk ∈ ms.filter fun m => m.place == mk.place :=
      List.mem_filter.2 ⟨hmem, beq_self_eq_true mk.place⟩
    rw [(findSome_isSome (fun m : Mark => m.test fr own) _).2 ⟨mk, hf, by rw [ht]; rfl⟩] at h
    cases h

/-- And the other way round. -/
theorem markOf_none_of (ms : List Mark) (a : Place) (fr own : List Fmt.Drawn)
    (h : ∀ mk ∈ ms, mk.place = a → mk.test fr own = none) : markOf ms a fr own = none := by
  cases hc : markOf ms a fr own with
  | none => rfl
  | some _ =>
    exfalso
    obtain ⟨mk, hmk, ht⟩ := markOf_mem (ms := ms) (a := a) (fr := fr) (own := own)
      (by rw [hc]; rfl)
    obtain ⟨h1, h2⟩ := List.mem_filter.1 hmk
    rw [h mk h1 (eq_of_beq h2)] at ht
    cases ht

/-! ## 1 The fit -/

/-- **One mark a member: its own challenges are not such as its rounds can draw.** -/
def fitMarks (bs : List (Block S Cl)) : List Mark :=
  bs.map fun b => ⟨b.place,
    fun _ own => if drawsFit b.rounds own then none else some "its rounds cannot draw these",
    ⟨0, 1⟩⟩

/-- all: the list of which the fit's marks are made; A: members of it; r: A's own challenges. -/
theorem fit_of_quiet (all : List (Block S Cl)) (ms : List Mark)
    (hsub : ∀ mk ∈ fitMarks all, mk ∈ ms) : ∀ (A : List (Block S Cl)) (f r : List Fmt.Drawn),
    (∀ c ∈ A, c ∈ all) → r.length = (A.flatMap (·.rounds)).length →
    marksQuiet ms A f r = true → drawsFit (A.flatMap (·.rounds)) r = true
  | [], _, r, _, hl, _ => by
    obtain rfl := List.eq_nil_of_length_eq_zero hl
    rfl
  | c :: A, f, r, hA, hl, h => by
    have h' : ((markOf ms c.place f (r.take c.rounds.length)).isNone &&
      marksQuiet ms A (f ++ r.take c.rounds.length) (r.drop c.rounds.length)) = true := h
    rw [Bool.and_eq_true] at h'
    obtain ⟨h1, h2⟩ := h'
    rw [List.flatMap_cons, List.length_append] at hl
    have s1 := mark_silent (mk := ⟨c.place,
        fun _ own => if drawsFit c.rounds own then none else some "its rounds cannot draw these",
        ⟨0, 1⟩⟩) (hsub _ (List.mem_map.2 ⟨c, hA c List.mem_cons_self, rfl⟩)) (fr := f)
      (own := r.take c.rounds.length) (by
        cases hm : markOf ms c.place f (r.take c.rounds.length) with
        | none => rfl
        | some _ =>
          rw [hm] at h1
          cases h1)
    have s1' : (if drawsFit c.rounds (r.take c.rounds.length) then (none : Option String)
      else some "its rounds cannot draw these") = none := s1
    have s2 : drawsFit c.rounds (r.take c.rounds.length) = true := by
      cases hd : drawsFit c.rounds (r.take c.rounds.length) with
      | true => rfl
      | false =>
        rw [hd] at s1'
        cases s1'
    have s3 := fit_of_quiet all ms hsub A (f ++ r.take c.rounds.length) (r.drop c.rounds.length)
      (fun d hd => hA d (List.mem_cons_of_mem _ hd)) (by rw [List.length_drop]; omega) h2
    rw [List.flatMap_cons, drawsFit_append, s2, s3]
    rfl

/-- **The silence gives the fit.** -/
theorem fit_of_silent (bs : List (Block S Cl)) (ms : List Mark)
    (hsub : ∀ mk ∈ fitMarks bs, mk ∈ ms) (skip j : Nat) (fr : List Fmt.Drawn)
    (hn : (fr.drop skip).length = ((bs.take j).flatMap (·.rounds)).length)
    (h : silentQ ms skip bs j fr) :
    drawsFit ((bs.take j).flatMap (·.rounds)) (fr.drop skip) = true :=
  fit_of_quiet bs ms hsub (bs.take j) (fr.take skip) (fr.drop skip)
    (fun _ hc => List.mem_of_mem_take hc) hn h

/-- **Under a kit whose typed challenges always fit the member's rounds, the fit's mark owes
nothing.** -/
theorem fitMark_debt (C : CK) (b : Block S Cl) (dsb : List RDT)
    (hk : ∀ ρ : Iop.Rho (uLT C dsb), drawsFit b.rounds (drawnT C dsb ρ) = true)
    (P : List Fmt.Drawn → Prop) (q : ℝ≥0∞) :
    MarkDebt C ⟨b.place,
      fun _ own => if drawsFit b.rounds own then none else some "its rounds cannot draw these",
      ⟨0, 1⟩⟩ dsb P q := by
  intro fr _
  refine zero_of_not C dsb _ (fun ρ hρ => ?_) q
  have hρ' : (if drawsFit b.rounds (drawnT C dsb ρ) then (none : Option String)
    else some "its rounds cannot draw these").isSome = true := hρ
  rw [hk ρ] at hρ'
  cases hρ'

/-! ## 2 The stops' marks -/

/-- **The two sorts' sentences give «the part stops, by either stop».** -/
theorem stopDebt_any (C : CK) (v : Option V) (p : Part V W Y) (dsp : List RDT) (q₁ q₂ : ℝ≥0∞)
    (h₁ : StopDebt C (·.isSome) none p dsp q₁)
    (h₂ : StopDebt C (· == some Why.hid) v p dsp q₂) :
    StopDebt C (·.isSome) v p dsp (q₁ + q₂) := by
  intro fr
  refine le_trans (pr_mono _ ?_) (le_trans (pr_union_le _ _ _) (add_le_add (h₁ fr) (h₂ fr)))
  intro ρ hρ
  have hρ' : (p.stopAt v fr (drawnT C dsp ρ)).isSome = true := hρ
  rcases (stopRel_part p v fr (drawnT C dsp ρ)).iff.1 hρ' with g | g
  · exact Or.inl g
  · refine Or.inr ?_
    show (p.stopAt v fr (drawnT C dsp ρ) == some Why.hid) = true
    rw [g]
    rfl

/-- **A member's stop mark is paid from its parts' sentences.** val: each part's number for «it
stops, by either stop». -/
theorem stopMark_debt (C : CK) (v : Option V) (hs : List (Placed V W Y)) (skip : Nat)
    (loc₀ : List Fmt.Drawn → List Fmt.Drawn) (sh : Place → Odds) (val : Part V W Y → ℝ≥0∞)
    (b : Block S Cl) (dsb : List RDT) (hlen : dsb.length = b.rounds.length)
    (hf : HalvesFit hs [b]) (hh : ChainHeld (·.isSome) v val hs C [b] dsb)
    (P : List Fmt.Drawn → Prop) :
    MarkDebt C ⟨b.place, fun fr own =>
        (chainStopAt v [b] hs (loc₀ (fr.take skip) ++ fr.drop skip) own).map
          fun _ => "a part stops", sh b.place⟩ dsb P
      ((chainGates (·.isSome) v val hs [b] dsb).map (·.p)).sum := by
  intro fr _
  refine le_trans (pr_mono _ ?_) (chain_stops_le (·.isSome) v val hs isSome_or' rfl C [b] dsb
    (by rw [List.flatMap_cons, List.flatMap_nil, List.append_nil]; exact hlen) hf hh
    (loc₀ (fr.take skip) ++ fr.drop skip))
  intro ρ hρ
  have hρ' : ((chainStopAt v [b] hs (loc₀ (fr.take skip) ++ fr.drop skip)
    (drawnT C dsb ρ)).map fun _ => "a part stops").isSome = true := hρ
  show (chainStopAt v [b] hs (loc₀ (fr.take skip) ++ fr.drop skip) (drawnT C dsb ρ)).isSome = true
  cases hc : chainStopAt v [b] hs (loc₀ (fr.take skip) ++ fr.drop skip) (drawnT C dsb ρ) with
  | none =>
    rw [hc] at hρ'
    cases hρ'
  | some _ => rfl

end ProofFile.Honest

#print axioms ProofFile.Honest.mark_silent
#print axioms ProofFile.Honest.markOf_none_of
#print axioms ProofFile.Honest.fit_of_quiet
#print axioms ProofFile.Honest.fit_of_silent
#print axioms ProofFile.Honest.fitMark_debt
#print axioms ProofFile.Honest.stopDebt_any
#print axioms ProofFile.Honest.stopMark_debt
