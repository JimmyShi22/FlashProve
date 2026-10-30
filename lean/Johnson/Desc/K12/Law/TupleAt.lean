-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Law/TupleAt.lean: the first arm of `tuple_or_few`
(Johnson/Desc/K12/Law/TupleRoad.lean) under a name. A definition and one statement.

Main names:
  `TupleAt`: the text of that first arm: one witness `w` within `e` positions of the law's word, of
    whose own words all the batched rows hold, and whose parts are candidates at each sampled
    member. It has a name so that the count in typed values (Johnson/Desc/K12/Law/TupleVals.lean)
    can state it.
  `tuple_at_or_few`: `tuple_or_few` at that name.
Limits: `TupleAt` is not "one witness at which every row, carried to the group's tables, holds". All
the limits of Johnson/Desc/K12/Law/TupleRoad.lean stand. No soundness is claimed, and nothing is
said on hiding.

-/
import Johnson.Desc.K12.Law.TupleRoad

set_option autoImplicit false
namespace H2K.Pin
open Cb Cb.Ood Iop Prob OnBytes OnBytes.Slice OnBytes.Slice.ProxRun Johnson.Pack
open OnBytes.Means H2K.ClaimSays
open VerifiableInference.Desc VerifiableInference.Desc.K12
open _root_.Run
open H2K.First (Seat1 Plain gpL gpG gpP good_of_ok oM oZ skM skZ Good Made entered)
open H2K.Pub (sgOf)

/-- tuple_or_few's first arm, its text to the letter. -/
def TupleAt {F : ℕ} {a : Fmt.M1.Stage} {row : GroupRow} {D : Plain} (h : Good F a row D) (t : T12)
    (L : GroupLayout) (S : Statement) (G : Group) (rd : ℕ → ℕ) (dM : Fin D.mems.length → PQ.RD)
    (dF : PQ.RD) (os : ∀ i, (wRound (dM i)).Orc) (e : ℕ) : Prop :=
    (∃ w : (sgOf a).cIn.N.Wit,
      offCnt (Ex := (sgOf a).cIn.ext)
        ((gpG h rd).word fun i => ((gpG h rd).mb i).ofOrc ((gpP h rd dM dF).lay i) (dM i) (os i))
        ((sgOf a).cIn.N.enc w.1 w.2) ≤ e ∧
      AllSay rdE t.st (runRows S G).toList (H2K.ClaimSays.wordsOf t.st L (tabOf (sgOf a) w.1)) ∧
      ∀ (j : Fin D.mems.length) (e0 : ℕ)
        (hs : ok (siteL D.st.codes a (D.mems.get j)) = true) (x : OnBytes.Oracle),
        D.st.oracles[(D.mems.get j).id]? = some x →
        ok (sampleL D.st.codes (D.mems.get j) x) = true →
        e < (e0 + 1) * 2 ^ ((sgOf a).C.a - aOf D.st.codes (D.mems.get j).sh) →
        ∀ (seed : SampleSeed) (row0 : Row) (tt : E) (β : GEˣ),
        Send.form D.st.codes (D.mems.get j).sh (D.mems.get j).id seed 0 = some row0 →
        x.sampleRows.toList = [{ row0 with target := tt }] →
        bitsZ D.st.codes (D.mems.get j).sh ≤ seed.z.length → (β : GE) = readE seed.beta →
        (portOmZ D.st.codes (D.mems.get j).sh e0).Cand
          (strOf D.st.codes (D.mems.get j).sh e0 (layOf (D.mems.get j)) (dM j) (os j))
          ((readP (bitsZ D.st.codes (D.mems.get j).sh) seed.z, β), fun _ => readE tt)
          (fun q => w.1
            ((siteOf D.st.codes a (D.mems.get j) e0 (oM D.L j.val) (oZ D.L j.val) hs).atJ q)))

theorem tuple_at_or_few {F : ℕ} {a : Fmt.M1.Stage} {row : GroupRow} {D : Plain} {p : P12} {t : T12}
    {L : GroupLayout} (h : Good F a row D) (hm : Made p t a L D) (S : Statement) (g : Nat) (G :
        Group)
    (hG : S.groups[g]? = some G) (hLf : S.layout g = some L) (hst : t.st = begun S g G)
    (rd : ℕ → ℕ) (dM : Fin D.mems.length → PQ.RD) (dF : PQ.RD) (os : ∀ i, (wRound (dM i)).Orc)
    (e : ℕ) (hJ : (sgOf a).StageJ e) (ht : combineAt t.st g ⟨L, runRows S G⟩ = true)
    (hk : L.k = (sgOf a).h + (sgOf a).g) (hh : L.h = (sgOf a).h)
    (hl : 2 ^ L.logEll = (sgOf a).C.l) (hz : 2 ^ L.logEllZk = (sgOf a).Z.l) :
    TupleAt h t L S G rd dM dF os e ∨
      cnt (BadDraws (sgOf a) e t.st g L (runRows S G)
        ((gpG h rd).word fun i =>
          ((gpG h rd).mb i).ofOrc ((gpP h rd dM dF).lay i) (dM i) (os i))) ≤
        (sgOf a).lstJ e * ((runRows S G).size - 1) :=
  tuple_or_few h hm S g G hG hLf hst rd dM dF os e hJ ht hk hh hl hz

end H2K.Pin

#print axioms H2K.Pin.tuple_at_or_few
