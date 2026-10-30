-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Law/TupleVals.lean: the converse of a proximity test's batching, counted in the
typed values of the round "BAT", at the law's own word `yOf`: one tuple for all rows, or, whatever
the round's message shows, at few typed values does the batching return a row that has a witness
within the radius. Statements and proofs.

There is no game here, no test of work, and no `row.kept = #[]` in the counted set. The letters are
those of `proximityTestKind guardedProximityTestParts p`.
What it is for: the law of the proximity test in the plain form leaves one count open, `BatVals`
(Johnson/Desc/K12/Coin/Vals.lean): for all `m`, `cnt {v | ∃ row w, bat x.1.st
x.1.g dB.entry (noDigest (rvOf dB m v)) = .ok (row, Ly, begun …) ∧ RIn (rad …) (stmG row, yOf π a
row₀ D hok rd (W0 …)) w ∧ ¬ N …} ≤ v₀`. The second arm of `bat_vals_yOf` is that set without `¬ N`,
at `en := dB.entry`, `k := dB.kind`, `gs :=` the message's values as shown, `V := W0 F no D.book
x.2`, `e := rad (sgOf a)`. So at `N :=` "there are `row₀`, `hok` with `TupleAt …`" and `v₀ := lstJ e
* (rows - 1)` that count follows by cases; this is not stated in this file.
What it asks that the plain form's promise does not name: `StageJ e` (the facts on codes at the
radius); `combineAt` at the statement behind the beginning (a test with code); the layout's four
numbers; the round's draws.
Main names:
  `theta_vals`: the one element that the batching hears on a round shown at the typed values `v`,
    read in the field, is `gOne _ v`.
  `cnt_vals_one`: at a round that draws one element and nothing else: `cnt (P (gOne _ v))` over its
    typed values is at most `cnt P`.
  `vals_of_draws`: `Good`, `Made`, the group, the round's draws are one element and nothing else,
    and `cnt (BadDraws … y) ≤ n`: then for all `gs`, `cnt {v | ∃ rowB w, bat … = .ok (rowB, L, t.st)
    ∧ RIn e (stmG rowB, y) w} ≤ n`. It holds at any word `y`, whatever stands in the other arm: so
    each of `tuple_or_few`, `tuple_words_or_few` and `tuple_on_or_few`, whose second arm is that one
    count, is carried to typed values by it.
  `tuple_or_few_vals`: the eleven premises of `tuple_or_few`, and the round's draws are one element
    and nothing else: then `TupleAt … e`, or for all `gs` the count above, at the law's word, is at
    most `lstJ e * (rows - 1)`.
  `bat_vals_yOf`: the same at a record `t` in front of the block and what it fixes (the group `G0`
    under `t.g`, its layout `Ly`, `D := gpOf`'s value behind the batching's beginning) and at `yOf p
    a row₀ D hok rd V`, `V` any written oracles by the book's places.
  `bat_vals_yOf_rows`: the same with `lstJ e * (en.rows - 1)`, the plan's number: every counted
    value holds the batching's return, and the batching asks that the entry count the batched rows
    (`bat_rows`, Johnson/Desc/K12/Law/BatRows.lean).
  `tupleAt_indep`: `TupleAt` there depends neither on the row that the record names nor on the proof
    that names it.
Limits: `TupleAt` is not "one witness at which every row, carried to the group's tables, holds": the
bridge row by row is not stated anywhere. Which arm holds no program can choose. No level of
security follows. No soundness is claimed, and nothing is said on hiding.
No sorry, no axiom of ours; each theorem has its premises; what each rests on is printed at the
file's end.

-/
import Johnson.Desc.K12.Law.TupleAt
import Johnson.Desc.K12.Law.BatNoKept
import Johnson.Desc.K12.Law.BatRows
import Johnson.Desc.K12.Law.FibreOf
import Johnson.Desc.K12.Law.K12Lemma

set_option autoImplicit false
namespace H2K.Pin
open Cb Cb.Ood Iop Prob OnBytes OnBytes.Slice OnBytes.Slice.ProxRun Johnson.Pack
open OnBytes.Means H2K.ClaimSays
open VerifiableInference.Desc VerifiableInference.Desc.K12
open _root_.Run
open H2K.First (Seat1 Plain gpL gpG gpP gpOf good_of_ok made_of oM oZ skM skZ Good Made entered)
open H2K.Pub (sgOf)
open H2K.JointK (yOf WO)
open H2K.Fibre (gOne_inj)

theorem theta_vals (en : Fmt.Entry) (k : Fmt.Kind) (gs : List Fmt.ItemValue)
    (v : Vals .two (Fmt.dsOf en k)) (x : E)
    (h : (noDigest ⟨gs, drawnOf .two en k v⟩).drawn.elems.map E.ofTriple = [x]) :
    readE x = gOne _ v := by
  have h0 : (Fmt.collect (outAll .two _ v)).elems.map E.ofTriple = [x] := h
  have h1 := collect_elems _ v
  cases hl : (Fmt.collect (outAll .two _ v)).elems with
  | nil =>
    rw [hl] at h0
    cases h0
  | cons t r =>
    rw [hl] at h0 h1
    obtain ⟨hx, _⟩ := List.cons.inj h0
    unfold gOne
    rw [← h1, ← hx, readE_ofTriple]
    rfl

theorem cnt_vals_one (ds : List Fmt.Draw) (h1 : ds = [.elem, .trits 0]) (P : GE → Prop) :
    cnt (fun v : Vals .two ds => P (gOne ds v)) ≤ cnt P := by
  haveI : Finite (Vals .two ds) := finite_Vals .two _
  haveI : Fintype (Vals .two ds) := Fintype.ofFinite _
  haveI : Fintype GE := Fintype.ofFinite _
  have h2 : cnt (fun v => P (gOne ds v)) ≤ cnt P * 1 :=
    cnt_comp_le _ (fun c => cnt_le_one fun a b ha hb => gOne_inj _ h1 (ha.trans hb.symm)) P
  rw [Nat.mul_one] at h2
  exact h2

/-- From the count of drawn elements to the count of typed values, whatever stands in the other
arm: a bound on BadDraws (Johnson/Desc/K12/Law/BatJoint.lean) at any word y bounds, whatever the
round's message
shows, the typed values at which the batching returns a row that has a witness within e of y. -/
theorem vals_of_draws {F : ℕ} {a : Fmt.M1.Stage} {row : GroupRow} {D : Plain} {p : P12} {t : T12}
    {L : GroupLayout} (h : Good F a row D) (hm : Made p t a L D) (S : Statement) (g : Nat)
    (G : Group) (hG : S.groups[g]? = some G) (y : (sgOf a).cIn.Word) (e : ℕ)
    (en : Fmt.Entry) (k : Fmt.Kind) (h1 : Fmt.dsOf en k = [.elem, .trits 0]) (eB : Fmt.Entry)
    (n : ℕ) (h2 : cnt (BadDraws (sgOf a) e t.st g L (runRows S G) y) ≤ n) (gs : List Fmt.ItemValue) :
    cnt (fun v : Vals .two (Fmt.dsOf en k) => ∃ (rowB : GroupRow) (w : (sgOf a).cIn.N.Wit),
      First.Close.bat S g eB (noDigest ⟨gs, drawnOf .two en k v⟩) = .ok (rowB, L, t.st) ∧
      (sgOf a).RIn e (stmG (sgOf a) rowB, y) w) ≤ n := by
  refine le_trans (cnt_mono ?_) ((cnt_vals_one _ h1 _).trans h2)
  rintro v ⟨rowB, w, hb, hw⟩
  obtain ⟨G2, x, hG2, _, _, hx, hc⟩ := bat_ok _ _ _ _ _ _ _ hb
  obtain rfl : G2 = G := Option.some.inj (hG2.symm.trans hG)
  exact ⟨x, rowB, theta_vals en k gs v x hx, hc, bat_noKept h hm _ _ _ _ _ _ hb, w, hw⟩

theorem tuple_or_few_vals {F : ℕ} {a : Fmt.M1.Stage} {row : GroupRow} {D : Plain} {p : P12}
    {t : T12} {L : GroupLayout} (h : Good F a row D) (hm : Made p t a L D) (S : Statement) (g : Nat)
    (G : Group) (hG : S.groups[g]? = some G) (hLf : S.layout g = some L) (hst : t.st = begun S g G)
    (rd : ℕ → ℕ) (dM : Fin D.mems.length → PQ.RD) (dF : PQ.RD) (os : ∀ i, (wRound (dM i)).Orc)
    (e : ℕ) (hJ : (sgOf a).StageJ e) (ht : combineAt t.st g ⟨L, runRows S G⟩ = true)
    (hk : L.k = (sgOf a).h + (sgOf a).g) (hh : L.h = (sgOf a).h)
    (hl : 2 ^ L.logEll = (sgOf a).C.l) (hz : 2 ^ L.logEllZk = (sgOf a).Z.l)
    (en : Fmt.Entry) (k : Fmt.Kind) (h1 : Fmt.dsOf en k = [.elem, .trits 0]) (eB : Fmt.Entry) :
    TupleAt h t L S G rd dM dF os e ∨
      ∀ gs : List Fmt.ItemValue,
        cnt (fun v : Vals .two (Fmt.dsOf en k) => ∃ (rowB : GroupRow) (w : (sgOf a).cIn.N.Wit),
          First.Close.bat S g eB (noDigest ⟨gs, drawnOf .two en k v⟩) = .ok (rowB, L, t.st) ∧
          (sgOf a).RIn e (stmG (sgOf a) rowB,
            (gpG h rd).word fun i =>
              ((gpG h rd).mb i).ofOrc ((gpP h rd dM dF).lay i) (dM i) (os i)) w) ≤
          (sgOf a).lstJ e * ((runRows S G).size - 1) := by
  rcases tuple_at_or_few h hm S g G hG hLf hst rd dM dF os e hJ ht hk hh hl hz with h2 | h2
  · exact Or.inl h2
  · exact Or.inr (vals_of_draws h hm S g G hG _ e en k h1 eB _ h2)

theorem bat_vals_yOf (p : P12) (t : T12) (a : Fmt.M1.Stage) (G0 : Group) (Ly : GroupLayout)
    (D : Plain) (row₀ : GroupRow) (hok : H2K.First.ok (gpL p a row₀ D) = true)
    (hG : t.st.groups[t.g]? = some G0) (hLy : t.st.layout t.g = some Ly)
    (hD : gpOf p { t with st := begun t.st t.g G0, pass := .claim row₀ Ly } a Ly = some D)
    (rd : ℕ → ℕ) (V : ℕ → WO) (e : ℕ) (hJ : (sgOf a).StageJ e)
    (ht : combineAt (begun t.st t.g G0) t.g ⟨Ly, runRows t.st G0⟩ = true)
    (hk : Ly.k = (sgOf a).h + (sgOf a).g) (hh : Ly.h = (sgOf a).h)
    (hl : 2 ^ Ly.logEll = (sgOf a).C.l) (hz : 2 ^ Ly.logEllZk = (sgOf a).Z.l)
    (en : Fmt.Entry) (k : Fmt.Kind) (h1 : Fmt.dsOf en k = [.elem, .trits 0]) :
    TupleAt (good_of_ok p a row₀ D hok)
        { t with st := begun t.st t.g G0, pass := .claim row₀ Ly } Ly t.st G0 rd
        (fun i => (V (D.mems.get i).t).1) (V D.fresh.t).1 (fun i => (V (D.mems.get i).t).2) e ∨
      ∀ gs : List Fmt.ItemValue,
        cnt (fun v : Vals .two (Fmt.dsOf en k) => ∃ (row : GroupRow) (w : (sgOf a).cIn.N.Wit),
          First.Close.bat t.st t.g en (noDigest ⟨gs, drawnOf .two en k v⟩) =
            .ok (row, Ly, begun t.st t.g G0) ∧
          (sgOf a).RIn e (stmG (sgOf a) row, yOf p a row₀ D hok rd V) w) ≤
          (sgOf a).lstJ e * ((runRows t.st G0).size - 1) :=
  tuple_or_few_vals (good_of_ok p a row₀ D hok) (made_of _ _ _ _ _ hD) t.st t.g G0 hG hLy rfl rd
    (fun i => (V (D.mems.get i).t).1) (V D.fresh.t).1 (fun i => (V (D.mems.get i).t).2) e hJ ht
    hk hh hl hz en k h1 en

/-- The same with the number of rows read off the plan: the entry's own count. Every counted
value
holds the batching's return, and the batching asks that the entry count the batched rows. -/
theorem bat_vals_yOf_rows (p : P12) (t : T12) (a : Fmt.M1.Stage) (G0 : Group) (Ly : GroupLayout)
    (D : Plain) (row₀ : GroupRow) (hok : H2K.First.ok (gpL p a row₀ D) = true)
    (hG : t.st.groups[t.g]? = some G0) (hLy : t.st.layout t.g = some Ly)
    (hD : gpOf p { t with st := begun t.st t.g G0, pass := .claim row₀ Ly } a Ly = some D)
    (rd : ℕ → ℕ) (V : ℕ → WO) (e : ℕ) (hJ : (sgOf a).StageJ e)
    (ht : combineAt (begun t.st t.g G0) t.g ⟨Ly, runRows t.st G0⟩ = true)
    (hk : Ly.k = (sgOf a).h + (sgOf a).g) (hh : Ly.h = (sgOf a).h)
    (hl : 2 ^ Ly.logEll = (sgOf a).C.l) (hz : 2 ^ Ly.logEllZk = (sgOf a).Z.l)
    (en : Fmt.Entry) (k : Fmt.Kind) (h1 : Fmt.dsOf en k = [.elem, .trits 0]) :
    TupleAt (good_of_ok p a row₀ D hok)
        { t with st := begun t.st t.g G0, pass := .claim row₀ Ly } Ly t.st G0 rd
        (fun i => (V (D.mems.get i).t).1) (V D.fresh.t).1 (fun i => (V (D.mems.get i).t).2) e ∨
      ∀ gs : List Fmt.ItemValue,
        cnt (fun v : Vals .two (Fmt.dsOf en k) => ∃ (row : GroupRow) (w : (sgOf a).cIn.N.Wit),
          First.Close.bat t.st t.g en (noDigest ⟨gs, drawnOf .two en k v⟩) =
            .ok (row, Ly, begun t.st t.g G0) ∧
          (sgOf a).RIn e (stmG (sgOf a) row, yOf p a row₀ D hok rd V) w) ≤
          (sgOf a).lstJ e * (en.rows - 1) := by
  rcases bat_vals_yOf p t a G0 Ly D row₀ hok hG hLy hD rd V e hJ ht hk hh hl hz en k h1 with h2 | h2
  · exact Or.inl h2
  · refine Or.inr fun gs => ?_
    by_cases hne : ∃ v : Vals .two (Fmt.dsOf en k), ∃ (row : GroupRow) (w : (sgOf a).cIn.N.Wit),
        First.Close.bat t.st t.g en (noDigest ⟨gs, drawnOf .two en k v⟩) =
          .ok (row, Ly, begun t.st t.g G0) ∧
        (sgOf a).RIn e (stmG (sgOf a) row, yOf p a row₀ D hok rd V) w
    · obtain ⟨v, row, _, hb, _⟩ := hne
      rw [bat_rows _ _ _ _ _ _ _ hb G0 hG]
      exact h2 gs
    · rw [cnt_false fun v hv => hne ⟨v, hv⟩]
      exact Nat.zero_le _

/-- TupleAt at the record behind the batching's beginning hangs neither on the row that the record
names nor on the proof that names it. -/
theorem tupleAt_indep (p : P12) (t : T12) (a : Fmt.M1.Stage) (G0 : Group) (Ly : GroupLayout)
    (D : Plain) (r₁ r₂ : GroupRow) (h₁ : H2K.First.ok (gpL p a r₁ D) = true)
    (h₂ : H2K.First.ok (gpL p a r₂ D) = true) (rd : ℕ → ℕ) (V : ℕ → WO) (e : ℕ) :
    TupleAt (good_of_ok p a r₁ D h₁)
        { t with st := begun t.st t.g G0, pass := .claim r₁ Ly } Ly t.st G0 rd
        (fun i => (V (D.mems.get i).t).1) (V D.fresh.t).1 (fun i => (V (D.mems.get i).t).2) e =
      TupleAt (good_of_ok p a r₂ D h₂)
        { t with st := begun t.st t.g G0, pass := .claim r₂ Ly } Ly t.st G0 rd
        (fun i => (V (D.mems.get i).t).1) (V D.fresh.t).1 (fun i => (V (D.mems.get i).t).2) e :=
  rfl

end H2K.Pin

#print axioms H2K.Pin.theta_vals
#print axioms H2K.Pin.cnt_vals_one
#print axioms H2K.Pin.vals_of_draws
#print axioms H2K.Pin.tuple_or_few_vals
#print axioms H2K.Pin.bat_vals_yOf
#print axioms H2K.Pin.bat_vals_yOf_rows
#print axioms H2K.Pin.tupleAt_indep
