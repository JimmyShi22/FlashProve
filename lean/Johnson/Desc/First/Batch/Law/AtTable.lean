-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Batch/Law/AtTable.lean
(kind K9's soundness lemma): THEOREMS: K9's ROW AT THE LETTERS
OF THE TABLE OF JOINTS: the fields forms and total (formsQ, totalQ:
the form of the four fields), in place of the row's own relations.
  goodIn_mono   a good piece stays good if the relation in front is weakened and the relation behind
                is strengthened, each inside its promise.
  tabAt own rd s   THE ROW's LETTER tabOf AT THE TABLE's ONE ACCESSOR: the tables that tabQ reads at
                the record's own statement and book.
  data_at       at these tables the row's data (dataAt) are dataQ.
  total_iff     **totalQ own s rd IS "a part is there, and the ledger's one sum is 0 at these
                data"**.
  zero_of_runs  where every coefficient of the runs' terms in a row is 0, so is every coefficient of
                each run's terms, at some number.
  forms_of_front   **THE FRONT OF K9's LAW GIVES forms OF A RUN OF PLAIN CLAIMS**: from "every
                coefficient of the moves' terms is 0", for a run of the steps whose terms are
                numbered values, the values being the worth of the reader's forms in formsQ's
                world of own rows, and the public test formsIn: formsQ.
  relT          the relations at the three boundaries in the table's letters: forms of the listed
                runs and the open rows; total and the open rows; the open rows.
  k9_row_table  **THE ROW AT THESE RELATIONS**, from the row at its own (k9_row_steps's conclusion).
HYPOTHESES NEW HERE: hpart (behind the first piece a part is there) - hitems: each listed run is a
run of the steps, plain, with a reader whose forms' worth are its values, and the public test says
yes: at every state of the promise in front.
Not claimed: hitems for any run; totalB; formsT; that the accessor's tables are the same along the
pieces (htabb, htab of the row: for the one equation's block a trial has shown it: TableTabs.lean).

-/
import Johnson.Desc.Sound.FormsQ
import Johnson.Desc.First.Batch.Law.RowSteps
import Johnson.Desc.First.Batch.Law.PlainRuns

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K9L
open OnBytes OnBytes.Model OnBytes.Maker OnBytes.Flat KObj
open VerifiableInference.Desc.K9 (atS Where)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound
open _root_.Run (ckP)
open _root_.Run.PQ (CK)
open _root_.Iop (Doomed)

/-- A good piece stays good between a weaker relation in front and a stronger one behind. -/
theorem goodIn_mono {T Cl W : Type} {C : CK} {F : Frame} (p : Piece C F T Cl W)
    (on on' : T × F.E.Str → Prop) (R R' R₂ R₂' : T × F.E.Str → W → Prop)
    (h : p.GoodIn on on' R R') (hf : ∀ a w, on a → R a w → R₂ a w)
    (hb : ∀ b w, on' b → R₂' b w → R' b w) : p.GoodIn on on' R₂ R₂' := by
  intro a ha
  refine Doomed.mono _ _ (fun τ hτ b hout => ?_) (h a ha)
  obtain ⟨h1, h2⟩ := hτ b hout
  exact ⟨h1, fun w hw => hf a _ ha (h2 w (hb b w h1 hw))⟩

/-- The row's letter tabOf at the table's one accessor. -/
noncomputable def tabAt (own : List (ℕ × ℕ)) (rd : ℕ × ℕ → MsgQ) (s : S) :
    ℕ → OnBytes.Part → ℕ → GQ :=
  match atS.get? s with
  | some a => tabQ own a.d.st a.d.book rd
  | none => fun _ _ _ => 0

/-- At these tables the row's data are dataQ (Johnson/Desc/Sound/FormsQ.lean). -/
theorem data_at (own : List (ℕ × ℕ)) (rd : ℕ × ℕ → MsgQ) (s : S) (a : K9.Part)
    (ha : atS.get? s = some a) : dataAt atS s (tabAt own rd s) = dataQ own a rd := by
  simp only [dataAt, tabAt, ha]
  rfl

/-- **totalQ (Johnson/Desc/Sound/FormsQ.lean), in the row's words.** -/
theorem total_iff (own : List (ℕ × ℕ)) (rd : ℕ × ℕ → MsgQ) (s : S) :
    totalQ own s rd ↔ (atS.get? s).isSome = true ∧
      oneK atS Reading.gl s s (dataAt atS s (tabAt own rd s)) = 0 := by
  constructor
  · rintro ⟨a, ha, h⟩
    refine ⟨by simp [ha], ?_⟩
    rw [data_at own rd s a ha]
    simp only [oneK, ha]
    exact h
  · rintro ⟨hs, h⟩
    obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp hs
    rw [data_at own rd s a ha] at h
    simp only [oneK, ha] at h
    exact ⟨a, ha, h⟩

section
variable {T P K : Type}

/-- Every coefficient of numbered terms is 0 just if every value is. -/
theorem numbered_zero [Zero K] : ∀ (l : List K) (n : ℕ),
    (∀ x ∈ numbered n l, x.2 = 0) ↔ ∀ v ∈ l, v = 0
  | [], _ => by simp [numbered]
  | v :: l, n => by
    simp only [numbered, List.mem_cons, forall_eq_or_imp, numbered_zero l (n + 1)]

/-- From the runs' terms in a row to each run's. -/
theorem zero_of_runs [Zero K] (p : P) (y : Bound K) : ∀ (rl : List (TermedRun T P K)) (n : ℕ),
    (∀ x ∈ termsOf p y (rl.map asMove) n, x.2 = 0) →
    ∀ r ∈ rl, ∃ m, ∀ x ∈ r.tm m p y, x.2 = 0
  | [], _, _, r, hr => nomatch hr
  | r0 :: l, n, h, r, hr => by
    have e : termsOf p y ((r0 :: l).map asMove) n =
        r0.tm n p y ++ termsOf p y (l.map asMove) (n + r0.len p) := rfl
    rw [e] at h
    rcases List.mem_cons.1 hr with rfl | hr
    · exact ⟨n, fun x hx => h x (List.mem_append_left _ hx)⟩
    · exact zero_of_runs p y l _ (fun x hx => h x (List.mem_append_right _ hx)) r hr

end

variable {α : Type}

/-- **The front of K9's law gives forms of a run of plain claims.** -/
theorem forms_of_front (Rd : K9.Readers) (own : List (ℕ × ℕ)) (piece : ℕ) (run : String) (s : S)
    (rd : ℕ × ℕ → MsgQ) (a : K9.Part) (R : K9.Read) (q : α × Option Pub9)
    (l : List (Step S (α × Option Pub9) GQ)) (r : TermedRun S (α × Option Pub9) GQ)
    (vals : α × Option Pub9 → Bound GQ → List GQ) (hr : r ∈ runsOf l)
    (hplain : ∀ n y, r.tm n q y = numbered n (vals q y)) (ha : atS.get? s = some a)
    (hR : Rd.forms piece run s = some R) (hin : K9.formsIn Rd own piece run s = true)
    (hvals : vals q (dataQ own a rd) =
      R.forms.map fun f => f.value Reading.gl (worldOwn a R.late (dataQ own a rd)))
    (h0 : ∀ x ∈ termsOf q (dataQ own a rd) (movesOf l) 0, x.2 = 0) :
    formsQ Rd own piece run s rd := by
  rw [terms_steps] at h0
  obtain ⟨m, hm⟩ := zero_of_runs q (dataQ own a rd) (runsOf l) 0 h0 r hr
  rw [hplain] at hm
  have hz := (numbered_zero _ m).1 hm
  rw [hvals] at hz
  have hseg := K9.segAt_of_atS s a ha
  unfold K9.formsIn at hin
  rw [hseg, hR] at hin
  obtain ⟨h1, h2⟩ := Eq.mp (Bool.and_eq_true _ _) hin
  exact ⟨a, R, hseg, hR, h1, fun f hf => ⟨List.all_eq_true.1 h2 f hf,
    hz _ (List.mem_map.2 ⟨f, hf, rfl⟩)⟩⟩

variable {W Cl : Type} {F : Frame}

/-- The relations at the three boundaries, in the table's letters. items: the listed runs: the
piece's number in its segment, the run's name. -/
def relT (Rd : K9.Readers) (own : List (ℕ × ℕ)) (rdW : W → ℕ × ℕ → MsgQ)
    (items : List (ℕ × String)) (N : ℕ) (ctx : S × F.E.Str → W → Prop) (j : ℕ) :
    ℕ → S × F.E.Str → W → Prop := fun i a w =>
  if i = j then
    (∀ e ∈ items, formsQ Rd own e.1 e.2 a.1 (rdW w)) ∧
      GroupHoldsAt atS Reading.gl N a.1 (tabAt own (rdW w) a.1)
  else if i = j + 1 then
    (totalQ own a.1 (rdW w) ∧ GroupHoldsAt atS Reading.gl N a.1 (tabAt own (rdW w) a.1)) ∧ ctx a w
  else GroupHoldsAt atS Reading.gl N a.1 (tabAt own (rdW w) a.1) ∧ ctx a w

/-- **The row at the table's letters.** -/
theorem k9_row_table (φ : S → α) (Ok : α × Option Pub9 → Prop) (Fu : S → Prop)
    (Rd : K9.Readers) (own : List (ℕ × ℕ)) (rdW : W → ℕ × ℕ → MsgQ) (items : List (ℕ × String))
    (l : List (Step S (α × Option Pub9) GQ)) (N j : ℕ) (pb pe : Piece (ckP .two) F S Cl W)
    (on0 : S × F.E.Str → Prop) (ctx : S × F.E.Str → W → Prop)
    (hrow : EachGoodIn (onPost on0 pb j)
      (relM Reading.gl atS (O9 φ Ok Fu) (movesOf l) N (fun a w => tabAt own (rdW w) a.1) ctx j) j
      [pb, pe])
    (hpart : ∀ a, onPost on0 pb j (j + 1) a → (atS.get? a.1).isSome = true)
    (hitems : ∀ a w, on0 a → ∀ e ∈ items, ∃ (b : K9.Part) (R : K9.Read)
      (r : TermedRun S (α × Option Pub9) GQ) (vals : α × Option Pub9 → Bound GQ → List GQ),
      atS.get? a.1 = some b ∧ r ∈ runsOf l ∧
      (∀ n y, r.tm n (fixed9 φ a.1) y = numbered n (vals (fixed9 φ a.1) y)) ∧
      Rd.forms e.1 e.2 a.1 = some R ∧ K9.formsIn Rd own e.1 e.2 a.1 = true ∧
      vals (fixed9 φ a.1) (dataQ own b (rdW w)) =
        R.forms.map fun f => f.value Reading.gl (worldOwn b R.late (dataQ own b (rdW w)))) :
    EachGoodIn (onPost on0 pb j) (relT Rd own rdW items N ctx j) j [pb, pe] := by
  obtain ⟨g1, g2, _⟩ := hrow
  have m0 : ∀ a w, relM Reading.gl atS (O9 φ Ok Fu) (movesOf l) N
      (fun a w => tabAt own (rdW w) a.1) ctx j j a w =
      ((∃ y, boundAt atS (fun a w => tabAt own (rdW w) a.1) ctx a w y ∧
        ∀ x ∈ termsOf ((O9 (K := GQ) φ Ok Fu).fixed a.1) y (movesOf l) 0, x.2 = 0) ∧
        GroupHoldsAt atS Reading.gl N a.1 (tabAt own (rdW w) a.1)) := fun a w => by
    simp [relM]
  have m1 : ∀ a w, relM Reading.gl atS (O9 φ Ok Fu) (movesOf l) N
      (fun a w => tabAt own (rdW w) a.1) ctx j (j + 1) a w =
      ((oneK atS Reading.gl a.1 a.1 (dataAt atS a.1 (tabAt own (rdW w) a.1)) = 0 ∧
        GroupHoldsAt atS Reading.gl N a.1 (tabAt own (rdW w) a.1)) ∧ ctx a w) := fun a w => by
    simp [relM]
  have m2 : ∀ a w, relM Reading.gl atS (O9 φ Ok Fu) (movesOf l) N
      (fun a w => tabAt own (rdW w) a.1) ctx j (j + 1 + 1) a w =
      (GroupHoldsAt atS Reading.gl N a.1 (tabAt own (rdW w) a.1) ∧ ctx a w) := fun a w => by
    unfold relM
    rw [if_neg (by omega), if_neg (by omega)]
  have t0 : ∀ a w, relT Rd own rdW items N ctx j j a w =
      ((∀ e ∈ items, formsQ Rd own e.1 e.2 a.1 (rdW w)) ∧
        GroupHoldsAt atS Reading.gl N a.1 (tabAt own (rdW w) a.1)) := fun a w => by
    simp [relT]
  have t1 : ∀ a w, relT Rd own rdW items N ctx j (j + 1) a w =
      ((totalQ own a.1 (rdW w) ∧ GroupHoldsAt atS Reading.gl N a.1 (tabAt own (rdW w) a.1)) ∧
        ctx a w) := fun a w => by
    simp [relT]
  have t2 : ∀ a w, relT Rd own rdW items N ctx j (j + 1 + 1) a w =
      (GroupHoldsAt atS Reading.gl N a.1 (tabAt own (rdW w) a.1) ∧ ctx a w) := fun a w => by
    unfold relT
    rw [if_neg (by omega), if_neg (by omega)]
  have o0 : ∀ a, onPost on0 pb j j a → on0 a := fun a h => by
    simpa [onPost] using h
  refine ⟨goodIn_mono pb _ _ _ _ _ _ g1 (fun a w ha h => ?_) (fun b w _ h => ?_),
    goodIn_mono pe _ _ _ _ _ _ g2 (fun a w ha h => ?_) (fun b w _ h => ?_), trivial⟩
  · rw [m0] at h
    rw [t0]
    obtain ⟨⟨y, ⟨_, hy⟩, hz⟩, hG⟩ := h
    refine ⟨fun e he => ?_, hG⟩
    obtain ⟨b, R, r, vals, hb, hr, hp, hR, hin, hv⟩ := hitems a w (o0 a ha) e he
    have ey : y = dataQ own b (rdW w) := hy.trans (data_at own (rdW w) a.1 b hb)
    rw [ey] at hz
    exact forms_of_front Rd own e.1 e.2 a.1 (rdW w) b R (fixed9 φ a.1) l r vals hr hp hb hR hin hv
      hz
  · rw [t1] at h
    rw [m1]
    exact ⟨⟨((total_iff own (rdW w) b.1).1 h.1.1).2, h.1.2⟩, h.2⟩
  · rw [m1] at h
    rw [t1]
    exact ⟨⟨(total_iff own (rdW w) a.1).2 ⟨hpart a ha, h.1.1⟩, h.1.2⟩, h.2⟩
  · rw [t2] at h
    rw [m2]
    exact h

end VerifiableInference.Desc.K9L

#print axioms VerifiableInference.Desc.K9L.goodIn_mono
#print axioms VerifiableInference.Desc.K9L.total_iff
#print axioms VerifiableInference.Desc.K9L.forms_of_front
#print axioms VerifiableInference.Desc.K9L.k9_row_table
