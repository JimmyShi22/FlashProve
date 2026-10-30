-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Law/TupleValsOn.lean: the converse of a proximity test's batching in typed values,
with the first arm of `tuple_on_or_few` in the other arm: one tuple of candidates, one message for
each member, of whose words all the batched rows hold, or few typed values. Definitions, statements
and proofs.

It stands beside `bat_vals_yOf_rows` (Johnson/Desc/K12/Law/TupleVals.lean).
Main names:
  `OnAt`: the first arm of `tuple_on_or_few` (Johnson/Desc/K12/Law/TupleOn.lean) under a name: its
    text, but that `t.st` is set as `S'`, the statement behind the beginning.
  `vals_rows_of_draws`: a bound `c₀ * (the batched rows - 1)` on `BadDraws` at any word gives, for
    all `gs`, that the count in typed values is at most `c₀ * (en.rows - 1)`: the plan's number.
  `bat_vals_on`: the premises of `bat_vals_yOf_rows`, radii `e0s` for the members, `siteL`'s yes at
    every member, at every member a message with `sampleL`'s yes, and `e < (e0s j + 1) * 2 ^ (C.a -
    the member's a)`: then `OnAt …`, or for all `gs`, `cnt {v | ∃ row w, bat … = .ok (row, Ly, begun
    …) ∧ RIn e (stmG row, yOf p a row₀ D hok rd V) w} ≤ lstJ e * (en.rows - 1)`.
Limits: All the limits of Johnson/Desc/K12/Law/TupleOn.lean and Johnson/Desc/K12/Law/TupleVals.lean
stand. `e0s` is bounded from below alone: whoever uses the statement must pick the smallest that the
bound allows. A group with an unsampled member meets the third premise nowhere. No soundness is
claimed, and nothing is said on hiding.
No sorry, no axiom of ours; each theorem has its premises; what each rests on is printed at the
file's end.

-/
import Johnson.Desc.K12.Law.TupleVals
import Johnson.Desc.K12.Law.TupleOn

set_option autoImplicit false
namespace H2K.Pin
open Cb Cb.Ood Iop Prob OnBytes OnBytes.Slice OnBytes.Slice.ProxRun Johnson.Pack
open OnBytes.Means H2K.ClaimSays
open VerifiableInference.Desc VerifiableInference.Desc.K12
open _root_.Run
open H2K.First (Seat1 Plain gpL gpG gpP gpOf good_of_ok made_of oM oZ skM skZ Good Made entered)
open H2K.Pub (sgOf)
open H2K.JointK (yOf WO)

/-- tuple_on_or_few's first arm: its text, but that «t.st» is set as S', the statement behind the
beginning. -/
def OnAt (S' S : Statement) (G : Group) (D : Plain) (e0s : Fin D.mems.length → ℕ)
    (dM : Fin D.mems.length → PQ.RD) (os : ∀ i, (wRound (dM i)).Orc) : Prop :=
  (∃ c : ∀ j : Fin D.mems.length, (portCode D.st.codes (D.mems.get j).sh).J → GE,
      AllSay rdE S' (runRows S G).toList (wordsOnW S' (tabT D c)) ∧
      ∀ (j : Fin D.mems.length) (x : OnBytes.Oracle),
        D.st.oracles[(D.mems.get j).id]? = some x →
        ∀ (seed : SampleSeed) (row0 : Row) (tt : E) (β : GEˣ),
        Send.form D.st.codes (D.mems.get j).sh (D.mems.get j).id seed 0 = some row0 →
        x.sampleRows.toList = [{ row0 with target := tt }] →
        bitsZ D.st.codes (D.mems.get j).sh ≤ seed.z.length → (β : GE) = readE seed.beta →
        (portOmZ D.st.codes (D.mems.get j).sh (e0s j)).Cand
          (strOf D.st.codes (D.mems.get j).sh (e0s j) (layOf (D.mems.get j)) (dM j) (os j))
          ((readP (bitsZ D.st.codes (D.mems.get j).sh) seed.z, β), fun _ => readE tt) (c j))

theorem vals_rows_of_draws {F : ℕ} {a : Fmt.M1.Stage} {row : GroupRow} {D : Plain} {p : P12}
    {t : T12} {L : GroupLayout} (h : Good F a row D) (hm : Made p t a L D) (S : Statement) (g : Nat)
    (G : Group) (hG : S.groups[g]? = some G) (y : (sgOf a).cIn.Word) (e : ℕ)
    (en : Fmt.Entry) (k : Fmt.Kind) (h1 : Fmt.dsOf en k = [.elem, .trits 0]) (c₀ : ℕ)
    (h2 : cnt (BadDraws (sgOf a) e t.st g L (runRows S G) y) ≤ c₀ * ((runRows S G).size - 1))
    (gs : List Fmt.ItemValue) :
    cnt (fun v : Vals .two (Fmt.dsOf en k) => ∃ (rowB : GroupRow) (w : (sgOf a).cIn.N.Wit),
      First.Close.bat S g en (noDigest ⟨gs, drawnOf .two en k v⟩) = .ok (rowB, L, t.st) ∧
      (sgOf a).RIn e (stmG (sgOf a) rowB, y) w) ≤ c₀ * (en.rows - 1) := by
  by_cases hne : ∃ v : Vals .two (Fmt.dsOf en k), ∃ (rowB : GroupRow) (w : (sgOf a).cIn.N.Wit),
      First.Close.bat S g en (noDigest ⟨gs, drawnOf .two en k v⟩) = .ok (rowB, L, t.st) ∧
      (sgOf a).RIn e (stmG (sgOf a) rowB, y) w
  · obtain ⟨v, rowB, _, hb, _⟩ := hne
    rw [bat_rows _ _ _ _ _ _ _ hb G hG]
    exact vals_of_draws h hm S g G hG y e en k h1 en _ h2 gs
  · rw [cnt_false fun v hv => hne ⟨v, hv⟩]
    exact Nat.zero_le _

theorem bat_vals_on (p : P12) (t : T12) (a : Fmt.M1.Stage) (G0 : Group) (Ly : GroupLayout)
    (D : Plain) (row₀ : GroupRow) (hok : H2K.First.ok (gpL p a row₀ D) = true)
    (hG : t.st.groups[t.g]? = some G0) (hLy : t.st.layout t.g = some Ly)
    (hD : gpOf p { t with st := begun t.st t.g G0, pass := .claim row₀ Ly } a Ly = some D)
    (rd : ℕ → ℕ) (V : ℕ → WO) (e : ℕ) (hJ : (sgOf a).StageJ e)
    (ht : combineAt (begun t.st t.g G0) t.g ⟨Ly, runRows t.st G0⟩ = true)
    (hk : Ly.k = (sgOf a).h + (sgOf a).g) (hh : Ly.h = (sgOf a).h)
    (hl : 2 ^ Ly.logEll = (sgOf a).C.l) (hz : 2 ^ Ly.logEllZk = (sgOf a).Z.l)
    (en : Fmt.Entry) (k : Fmt.Kind) (h1 : Fmt.dsOf en k = [.elem, .trits 0])
    (e0s : Fin D.mems.length → ℕ)
    (hS : ∀ j : Fin D.mems.length, ok (siteL D.st.codes a (D.mems.get j)) = true)
    (hQ : ∀ j : Fin D.mems.length, ∃ x, D.st.oracles[(D.mems.get j).id]? = some x ∧
      ok (sampleL D.st.codes (D.mems.get j) x) = true)
    (hfit : ∀ j : Fin D.mems.length,
      e < (e0s j + 1) * 2 ^ ((sgOf a).C.a - aOf D.st.codes (D.mems.get j).sh)) :
    OnAt (begun t.st t.g G0) t.st G0 D e0s (fun i => (V (D.mems.get i).t).1)
        (fun i => (V (D.mems.get i).t).2) ∨
      ∀ gs : List Fmt.ItemValue,
        cnt (fun v : Vals .two (Fmt.dsOf en k) => ∃ (row : GroupRow) (w : (sgOf a).cIn.N.Wit),
          First.Close.bat t.st t.g en (noDigest ⟨gs, drawnOf .two en k v⟩) =
            .ok (row, Ly, begun t.st t.g G0) ∧
          (sgOf a).RIn e (stmG (sgOf a) row, yOf p a row₀ D hok rd V) w) ≤
          (sgOf a).lstJ e * (en.rows - 1) := by
  rcases tuple_on_or_few (good_of_ok p a row₀ D hok) (made_of _ _ _ _ _ hD) t.st t.g G0 hG hLy rfl
    rd (fun i => (V (D.mems.get i).t).1) (V D.fresh.t).1 (fun i => (V (D.mems.get i).t).2) e hJ ht
    hk hh hl hz e0s hS hQ hfit with h2 | h2
  · exact Or.inl h2
  · exact Or.inr (vals_rows_of_draws (good_of_ok p a row₀ D hok) (made_of _ _ _ _ _ hD) t.st t.g G0
      hG _ e en k h1 _ h2)

end H2K.Pin

#print axioms H2K.Pin.vals_rows_of_draws
#print axioms H2K.Pin.bat_vals_on
