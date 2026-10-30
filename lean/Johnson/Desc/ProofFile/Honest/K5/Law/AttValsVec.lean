-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/AttValsVec.lean: WHERE THE MAKER OF THE VECTOR OF READS AT AN
ATTENTION SEGMENT (`attVals`, Johnson/HonestTrace/U3Rows.lean) RETURNS, AND ITS VECTOR IS RETURNED
AT A LIST OF CHALLENGES, THERE ARE POINTS p AND TABLES t SUCH THAT: THE HONEST SIDE's `ptsOf`
RETURNS p; THE VERIFIER's `tablesP` RETURNS t AT p; AND THE VECTOR IS, ENTRY BY ENTRY, `u3Of` AT t's
TABLES (Johnson/Desc/K5/Honest/U3.lean). By unfolding the maker's text. No definition; two theorems,
and two helpers of the file's own.

Main names:
  `attVals_vec`: hV: `attVals Z G sps seg g` returns V. Then there are the group's plan A and the
    segment's first places k5, k3 of the kinds K5 and K3, each fixed by an equation; V.n = A.nW; and
    at every list heard at which V.vec returns v: p and t as above, OUTSIDE «for all cells»: one p
    and one t serve all cells C and all entries j.
  `attVals_is_u3Att`: the same with p and t folded away: at all cells C, `u3Att` at the same letters
    returns v C. A corollary.

The letters at which the three functions stand, as the maker's text has them: the honest side's
public data ⟨A.S, A.own⟩; the matrices' sizes `sizesOf A.mats`; the length A.nW; the cells `ofInt
(cellsAtOf C (matsOwn G.W seg) a r c)`; what the lookup hands in, `lookOf A.S.cf.lmb fo`; the
challenges ⟨fo.zk, heard.drop k5.2⟩; fo := `k4LookOf A.fs k3.2 heard`.

What it is for. A law on what lies in the array "U3" at an attention segment can speak of `u3Of` and
of the tables that `tablesP` returns, on which laws stand (Johnson/Desc/K5/Honest/Law/U3Law.lean;
Johnson/Desc/First/Att/Claims/ReadsOfIs.lean), in the place of the maker's text. A caller that must
name the tables takes the first theorem.

How. `attVals` is one «do» in `Except`: where it returns, each step has returned (`ok_of_bind`,
`some_of_have`: the two helpers); V is the written record; the same at V.vec. The second: `u3Att`'s
text.

Limits. ONE WAY: from the maker's returns. THAT `attVals` RETURNS AT ANY PUBLIC DATA, OR ITS VECTOR
AT ANY LIST OF CHALLENGES, IS NOT SAID HERE. The converse is not said: between a return of `u3Att`
and the maker's stand four public tests of the maker's own. V.front does not stand in the ends. The
ends hold at every j: at an entry that no table covers `u3Of` is 0, by its own text. THE CELLS C ARE
BOUND AND READ IN BOTH ENDS, AT ALL CELLS: the last clause of `attVals_vec` is the last line of the
maker's own text, and its proof is `rfl`. Nothing is said of a seat, a message, a Script, or of what
is committed or sent. Both hold of nothing where hV fails.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.HonestTrace.U3Rows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K5
open OnBytes OnBytes.Model
open ProofFile (Pub Ground Spot spotsOf)
open ProofFile.Honest (MsgAddr RowData RowDataOf ArrayVals Cells drawsFit msgFits layFits)
open ProofFile.Honest.K8 (cellsAtOf)
open ProofFile.Honest.K3 (matsOwn tlOf linkG linkA)
open ProofFile.Honest.K4 (k4LookOf k4LookRounds)
open ProofFile.Honest.K6 (headHeardWholeAt headParAt headInFront)
open OnBytes.Desc.First.K4.Honest (K4Pub K4In ptsOf namedPts)
open OnBytes.Model.Layer (Lay TableAsk layTables tableAsks funsOf)
open VerifiableInference.Desc (KindName)
open VerifiableInference.Desc.K8 (ReadsQuiet.tables)
open VerifiableInference.Desc.First.K8.Honest (CellsAt)
open OnBytes.HonestTrace.U3 (attVals SegVals placeIn sizesOf have_)

/-- Where a step and what follows it return, the step has returned. -/
private theorem ok_of_bind {α β : Type} {x : Except String α} {f : α → Except String β} {b : β}
    (h : (x >>= f) = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

/-- Where `have_` returns a value, the value was there. -/
private theorem some_of_have {α : Type} {n : String} {o : Option α} {a : α}
    (h : have_ n o = .ok a) : o = some a := by
  cases o with
  | none => cases h
  | some x => exact congrArg some (Except.ok.inj h)

/-- **THE MAKER's VECTOR AT AN ATTENTION SEGMENT IS `u3Of` AT THE TABLES THAT `tablesP` RETURNS AT
THE POINTS THAT `ptsOf` RETURNS.** hV: the maker returns V. One p and one t serve all cells and all
entries. -/
theorem attVals_vec {Z : Pub} {G : Ground} {sps : List Spot} {seg g : ℕ} {V : SegVals}
    (hV : attVals Z G sps seg g = .ok V) :
    ∃ A k5 k3, G.W.A[g]? = some A ∧ placeIn Z sps seg .K5 = .ok k5 ∧
      placeIn Z sps seg .K3 = .ok k3 ∧ V.n = A.nW ∧
      ∀ (heard : List Fmt.Drawn) (v : Cells → ℕ → E), V.vec heard = .ok v →
        ∃ p t,
          H2K5.Honest.ptsOf ⟨A.S, A.own⟩
            ⟨(k4LookOf A.fs k3.2 heard).zk, heard.drop k5.2⟩ = some p ∧
          VerifiableInference.Desc.First.Att.P.tablesP (⟨A.S, A.own⟩ : H2K5.Honest.Pub5).g
            (sizesOf A.mats) A.nW
            (VerifiableInference.Desc.First.Att.P.lookOf A.S.cf.lmb (k4LookOf A.fs k3.2 heard))
            p = some t ∧
          ∀ (C : Cells) (j : ℕ), v C j =
            H2K5.Honest.u3Of (sizesOf A.mats)
              (fun a r c => ofInt (cellsAtOf C (matsOwn G.W seg) a r c)) t.funs j := by
  unfold attVals at hV
  obtain ⟨A, hA, hV⟩ := ok_of_bind hV
  obtain ⟨k5, h5, hV⟩ := ok_of_bind hV
  obtain ⟨k3, h3, hV⟩ := ok_of_bind hV
  dsimp only at hV
  obtain ⟨_, _, hV⟩ := ok_of_bind hV
  obtain ⟨_, _, hV⟩ := ok_of_bind hV
  obtain ⟨_, _, hV⟩ := ok_of_bind hV
  have eV := Except.ok.inj hV
  subst eV
  refine ⟨A, k5, k3, some_of_have hA, h5, h3, rfl, ?_⟩
  intro heard v hv
  dsimp only at hv
  obtain ⟨t, ht, hv⟩ := ok_of_bind hv
  obtain ⟨_, _, hv⟩ := ok_of_bind hv
  have ev := Except.ok.inj hv
  subst ev
  obtain ⟨p, hp, htp⟩ := Option.bind_eq_some_iff.1 (some_of_have ht)
  exact ⟨p, t, hp, htp, fun _ _ => rfl⟩

/-- **The same with the points and the tables folded away: the maker's vector is what `u3Att`
returns.** hV: the maker returns V. -/
theorem attVals_is_u3Att {Z : Pub} {G : Ground} {sps : List Spot} {seg g : ℕ} {V : SegVals}
    (hV : attVals Z G sps seg g = .ok V) :
    ∃ A k5 k3, G.W.A[g]? = some A ∧ placeIn Z sps seg .K5 = .ok k5 ∧
      placeIn Z sps seg .K3 = .ok k3 ∧ V.n = A.nW ∧
      ∀ (heard : List Fmt.Drawn) (v : Cells → ℕ → E), V.vec heard = .ok v → ∀ C : Cells,
        H2K5.Honest.u3Att ⟨A.S, A.own⟩ (sizesOf A.mats) A.nW
          (fun a r c => ofInt (cellsAtOf C (matsOwn G.W seg) a r c))
          (VerifiableInference.Desc.First.Att.P.lookOf A.S.cf.lmb (k4LookOf A.fs k3.2 heard))
          ⟨(k4LookOf A.fs k3.2 heard).zk, heard.drop k5.2⟩ = some (v C) := by
  obtain ⟨A, k5, k3, hA, h5, h3, hn, H⟩ := attVals_vec hV
  refine ⟨A, k5, k3, hA, h5, h3, hn, fun heard v hv C => ?_⟩
  obtain ⟨p, t, hp, htp, hC⟩ := H heard v hv
  unfold H2K5.Honest.u3Att
  exact Option.bind_eq_some_iff.2
    ⟨p, hp, Option.map_eq_some_iff.2 ⟨t, htp, funext fun j => (hC C j).symm⟩⟩

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.attVals_vec
#print axioms ProofFile.Honest.K5.attVals_is_u3Att
#print axioms ProofFile.Honest.K5.ok_of_bind
#print axioms ProofFile.Honest.K5.some_of_have
