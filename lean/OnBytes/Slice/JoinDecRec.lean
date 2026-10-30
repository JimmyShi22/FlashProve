-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/JoinDecRec.lean: the join of three checkers at the three languages of one decoder with
a record.

THIS IS WHAT WOULD BE CLAIMED; NOTHING IS SHOWN. An implication: no part that meets its hypotheses
with a bound below 1 is written.

This file puts the three languages of `DecR` (OnBytes/Slice/DecoderRec.lean) into the join,
over `join_id_run3`
(OnBytes/Slice/JoinOut3.lean), which names no decoder.

Main definitions: `goodDecR` (with a record the string decodes, its matrix is in range, the claim
holds); `good3R` (what the three languages give before the records are tied).
Main theorems: `goodDecR_of_good3R` (with the two ties, by `DecR.path`); `join_id_decR_run`.

What is particular here. The decoder takes a record. From each checker's value the
records that it speaks of are read: one for the key's, two for the entry's (the first table's and
the copy's), one for the proof's. `hYes` has two clauses for them: the entry's first record is the
key's; the proof's is the entry's second. The bound has `join_id`'s six terms.

What is not claimed. The three parts, the verifier, the sample map, the way out, the matrix and the
claims are variables. NO PART FOR A TABLE WITH A RECORD EXISTS: the entry's part of
OnBytes/Slice/PartEntryTables.lean has a checker that refuses such a table. The public strings' sets
are free here: whoever shows `hYes` needs that no string of a seed's calls lies in them, since the
verifier runs on the pinned oracle and the checkers on g. All limits in the heads of JoinRun.lean,
JoinOut3.lean and DecoderRec.lean hold here too.

-/
import OnBytes.Slice.DecoderRec
import OnBytes.Slice.JoinOut3

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Rom Prob Compile Compile.Batch MeasureTheory
open OnBytes.Tie (IdKey idCode firstId)
open scoped ENNReal

variable {β δ Xi : Type} {D : DecR}

/-- Of an instance, a record and a raw string: with the record the string decodes, its matrix is in
range, and the claim of the instance holds of that matrix. -/
def goodDecR (A : D.Claims Xi) (x : Xi) (rec : D.Rec) (y : Raw Run.PQ.SgX) : Prop :=
  ∃ u, D.dcdRaw y rec = some u ∧ A.inRange (A.mat u) ∧ A.Rel (A.mat u) x

/-- What the three parts' languages give together, before the records are tied: each part's at the
records that are read off ITS OWN checker's value. -/
def good3R {OK OE OF : Type} (A : D.Claims Xi) (w : DecR.Way D) (recK : OK → D.Rec)
    (recE₀ recE₁ : OE → D.Rec) (recF : OF → D.Rec) (xOf : OF → Xi) (oK : OK) (oE : OE) (oF : OF)
    (y₀ : Raw Run.PQ.SgX) : Prop :=
  ∃ y₁, DecR.LangK A w (recK oK) y₀ ∧ DecR.LangE w (recE₀ oE) (recE₁ oE) y₀ y₁ ∧
    DecR.LangP A w (xOf oF) (recF oF) y₁

/-- With the two ties of records `good3R` gives `goodDecR` at the first table's record. -/
theorem goodDecR_of_good3R {OK OE OF : Type} (A : D.Claims Xi) (w : DecR.Way D) (recK : OK → D.Rec)
    (recE₀ recE₁ : OE → D.Rec) (recF : OF → D.Rec) (xOf : OF → Xi) (oK : OK) (oE : OE) (oF : OF)
    (y₀ : Raw Run.PQ.SgX) (h0 : recE₀ oE = recK oK) (h1 : recF oF = recE₁ oE)
    (h : good3R A w recK recE₀ recE₁ recF xOf oK oE oF y₀) :
    goodDecR A (xOf oF) (recK oK) y₀ := by
  obtain ⟨y₁, hK, hE, hP⟩ := h
  rw [h0] at hE
  rw [h1] at hP
  exact DecR.path A w hK hE hP

/-- **THIS IS WHAT WOULD BE CLAIMED; NOTHING IS SHOWN. The join for stored tables with a record**,
for an experiment in which a verifier is run.
The decoder takes a record; w is the way out of the entry's and the
proof's languages (either candidate of OnBytes/Slice/DecoderRec.lean); from each checker's value the
records that it speaks of are read (`recK`; `recE₀`, `recE₁`; `recF`); `hYes` has TWO TIES: the
entry's first record is the key's, and the proof's is the entry's second (the copy's own); its last
clause has `goodDecR` at the key's record. The three parts, the
verifier, the decoder's sample map, the matrix and the claims are variables. -/
theorem join_id_decR_run (w : DecR.Way D) (S₀ : Finset (List Bool))
    (S₁ : Tab → Finset (List Bool))
    (C : OComp (rom 256) β) (dig : β → ZKCP.Digest 256) (P : β → OComp (rom 256) δ)
    (key : Tab → Tab → δ → IdKey) (tC tP : ℕ) (hC : C.QueryBound tC)
    (hP : ∀ b, (P b).QueryBound tP)
    (K E F : Tab → Tab → PartO 256 ((β × Trace (rom 256)) × δ) Run.PQ.SgX)
    (hK : ∀ T₀ T₁, (K T₀ T₁).OK) (hE : ∀ T₀ T₁, (E T₀ T₁).OK) (hF : ∀ T₀ T₁, (F T₀ T₁).OK)
    (bS : ℕ → ℕ → ℝ≥0∞) (hS : ∀ T₀ T₁, (K T₀ T₁).Stable bS)
    (hKE : ∀ T₀ T₁, SameRaw (K T₀ T₁) (E T₀ T₁)) (hEF : ∀ T₀ T₁, SameRaw (E T₀ T₁) (F T₀ T₁))
    (A : Tab → Tab → D.Claims Xi) (xOf : ∀ T₀ T₁, (F T₀ T₁).Out → Xi)
    (recK : ∀ T₀ T₁, (K T₀ T₁).Out → D.Rec) (recE₀ recE₁ : ∀ T₀ T₁, (E T₀ T₁).Out → D.Rec)
    (recF : ∀ T₀ T₁, (F T₀ T₁).Out → D.Rec)
    (hLK : ∀ T₀ T₁ oK Y, (K T₀ T₁).Lang oK [Y] → DecR.LangK (A T₀ T₁) w (recK T₀ T₁ oK) Y)
    (hLE : ∀ T₀ T₁ oE Y₀ Y₁, (E T₀ T₁).Lang oE [Y₀, Y₁] →
      DecR.LangE w (recE₀ T₀ T₁ oE) (recE₁ T₀ T₁ oE) Y₀ Y₁)
    (hLF : ∀ T₀ T₁ oF Y, (F T₀ T₁).Lang oF [Y] →
      DecR.LangP (A T₀ T₁) w (xOf T₀ T₁ oF) (recF T₀ T₁ oF) Y)
    (X' : Tab → Tab → Fam (rom 256) → Set (((β × Trace (rom 256)) × δ) × Trace (rom 256)))
    (bX' : ℝ≥0∞)
    (hX' : ∀ T₀ T₁, Rom.Pr (twoExp (pinOn (S₁ T₀) T₁ (pinOn S₀ T₀ C))
      fun b => pinOn (S₁ T₀) T₁ (pinOn S₀ T₀ (P b))).withTrace (X' T₀ T₁) ≤ bX')
    (hid : ∀ k s, idCode k = some s → s ∉ S₀ ∧ ∀ T₀, s ∉ S₁ T₀)
    (V : β × δ → OComp (rom 256) Bool) (hV : ∀ x, (V x).NoCoin)
    (Fine : ((β × Trace (rom 256)) × δ) × Trace (rom 256) → Prop)
    (FineT : Tab → Tab → ((β × Trace (rom 256)) × δ) × Trace (rom 256) → Prop)
    (hFine : ∀ T₀ T₁ w, FineT T₀ T₁ w → Fine w)
    (hoff₀ : ∀ w, ¬ Fine w → ¬ Fine (offBoth S₀ w))
    (hoff₁ : ∀ T₀ w, ¬ Fine w → ¬ Fine (offBoth (S₁ T₀) w))
    (hYes : ∀ T₀ T₁ g w,
      (V (w.1.1.1, w.1.2)).det (over S₀ T₀ (over (S₁ T₀) T₁ g)) = true → w ∉ X' T₀ T₁ g →
      (∃ s, idCode (key T₀ T₁ w.1.2) = some s ∧
        over S₀ T₀ (over (S₁ T₀) T₁ g) () s = dig w.1.1.1) ∧ ∃ oK oE oF cm',
        ((K T₀ T₁).chk w.1).det g = some oK ∧ ((E T₀ T₁).chk w.1).det g = some oE ∧
        ((F T₀ T₁).chk w.1).det g = some oF ∧
        (K T₀ T₁).roots oK = [Run.bytesToDig (key T₀ T₁ w.1.2).2.2.root] ∧
        (E T₀ T₁).roots oE = [Run.bytesToDig (key T₀ T₁ w.1.2).2.2.root, cm'] ∧
        (F T₀ T₁).roots oF = [cm'] ∧
        recE₀ T₀ T₁ oE = recK T₀ T₁ oK ∧ recF T₀ T₁ oF = recE₁ T₀ T₁ oE ∧
        (firstId (dig w.1.1.1) w.1.1.2 = some (key T₀ T₁ w.1.2) → NoClash w.2 →
          (∃ τ, w.2 = w.1.1.2 ++ τ) →
          goodDecR (A T₀ T₁) (xOf T₀ T₁ oF) (recK T₀ T₁ oK)
            ((K T₀ T₁).raw w.1.1.2 (Run.bytesToDig (key T₀ T₁ w.1.2).2.2.root)) →
          FineT T₀ T₁ w))
    (B : ℝ≥0∞)
    (hB : ∀ T₀ T₁, (K T₀ T₁).bound (tC + tP) + ((E T₀ T₁).bound (tC + tP) +
      ((F T₀ T₁).bound (tC + tP) +
        (bS tC tP + ((((tC + tP + 2) ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256 + bX')))) ≤ B) :
    Rom.Pr (twoExp (twoExp C P) fun x => V (x.1.1, x.2))
      (fun _ => {z | z.2 = true ∧ ¬ Fine z.1}) ≤ B :=
  join_id_run3 S₀ S₁ C dig P key tC tP hC hP K E F hK hE hF bS hS hKE hEF
    (fun T₀ T₁ => good3R (A T₀ T₁) w (recK T₀ T₁) (recE₀ T₀ T₁) (recE₁ T₀ T₁) (recF T₀ T₁)
      (xOf T₀ T₁))
    (fun T₀ T₁ oK oE oF Y₀ Y₁ lK lE lF =>
      ⟨Y₁, hLK T₀ T₁ oK Y₀ lK, hLE T₀ T₁ oE Y₀ Y₁ lE, hLF T₀ T₁ oF Y₁ lF⟩)
    X' bX' hX' hid V hV Fine FineT hFine hoff₀ hoff₁
    (fun T₀ T₁ g w' hy hx => by
      obtain ⟨hI, oK, oE, oF, cm', cK, cE, cF, rK, rE, rF, t0, t1, hG⟩ := hYes T₀ T₁ g w' hy hx
      exact ⟨hI, oK, oE, oF, cm', cK, cE, cF, rK, rE, rF, fun hf hc hs hg =>
        hG hf hc hs (goodDecR_of_good3R _ w _ _ _ _ _ oK oE oF _ t0 t1 hg)⟩)
    B hB

end OnBytes.Slice
