-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Law/LocKept.lean: WHAT "LOC" LEAVES AS IT WAS, and (loc_x)'s equation cut in its
two sides: for whoever carries the law of "LOC" (Johnson/Desc/K14/Law/RowsCore.lean: loc_core) to a
table of joints that is said in the program's own arithmetic.

  LocKept d d'      the small record, the oracle messages and the codes are as they were; G_u's list
                    of constraints has grown at its end alone; "in order" is kept.
  kept_of_loc       **a yes of "LOC" gives it.**
  foldeqSymbol_val  the program's fold of a column (OnBytes/Iop/Foldeq.lean: foldeqSymbol) reads as
                    the sum of weight times entry: the right side of (loc_x)'s equation.
  codeVal           the left side: row x of the code's generator matrix on the message and on the
                    random tail.
  locAt_iff         (loc_x)'s equation at a location is "codeVal = what foldeqSymbol reads as".
What is not claimed. Nothing on a draw. Nothing on what a constraint means beyond LocAt's own text.
No soundness of a verifier.

-/
import Johnson.Desc.K14.Law.RowsCore
import Johnson.Desc.K14.Law.StoredCols
import Johnson.Desc.Means.Page

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain
open OnBytes.Means (Words)
open VerifiableInference.Desc.Ground (addRowP addRowsP addRowsFrom)

/-- What "LOC" leaves as it was. -/
structure LocKept (d d' : St) : Prop where
  loc : d'.loc = d.loc
  oracles : d'.st.oracles = d.st.oracles
  codes : d'.st.codes = d.st.codes
  rows : ∃ rows, rowsOn d' d.loc.gU = rowsOn d d.loc.gU ++ rows
  order : Means.InOrder d.st → Means.InOrder d'.st

/-- The adding of rows turns neither a message nor the codes. -/
theorem addRowsFrom_same {L : Type} (g : Nat) : ∀ (l : List Row) (d d' : DState L),
    addRowsFrom g l d = some d' → d'.st.oracles = d.st.oracles ∧ d'.st.codes = d.st.codes
  | [], d, d', h => by
    obtain rfl := Option.some.inj h
    exact ⟨rfl, rfl⟩
  | row :: l, d, d', h => by
    unfold addRowsFrom at h
    obtain ⟨d1, h1, h2⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨a, b⟩ := addRowsFrom_same g l d1 d' h2
    unfold addRowP at h1
    split at h1
    · obtain rfl := Option.some.inj h1
      exact ⟨a, b⟩
    · cases h1

/-- **A yes of "LOC".** -/
theorem kept_of_loc (p : Par) (d d' : St) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) (h : loc p d rs gs = some d') : LocKept d d' := by
  obtain ⟨r, cols, rfl, rfl⟩ := loc_one p d d' rs gs h
  obtain ⟨l, rows, _, _, hU, _⟩ := laysLocW p d d' r cols h
  unfold loc at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨rows', _, ha⟩ := h
  have hs : d'.st.oracles = d.st.oracles ∧ d'.st.codes = d.st.codes := by
    unfold addRowsP at ha
    split at ha
    · exact addRowsFrom_same _ _ _ _ ha
    · cases ha
  exact ⟨l, hs.1, hs.2, ⟨rows, hU⟩, fun hI => Means.addRowsP_keeps ha hI⟩

variable {K : Type} [Field K] (ρ : OnBytes.Model.Reading K)

/-- The loop of the program's fold of a column. -/
theorem foldl_maddS (col : Array F) (w : Array E) : ∀ (l : List Nat) (a : E),
    ρ.val (l.foldl (fun s r => maddS s (col.getD r 0) (w.getD r zeroE)) a) = ρ.val a +
      (l.map fun r => ρ.val (w.getD r zeroE) * ρ.val (ofF (col.getD r 0))).sum
  | [], a => by simp
  | r :: l, a => by
    rw [List.foldl_cons, foldl_maddS col w l, maddS_val]
    simp only [List.map_cons, List.sum_cons]
    ring

/-- **The program's fold of a column reads as the sum of weight times entry.** -/
theorem foldeqSymbol_val (w : Array E) (col : Array F) :
    ρ.val (foldeqSymbol w col) =
      ∑ r ∈ Finset.range w.size, ρ.val (w.getD r zeroE) * ρ.val (ofF (col.getD r 0)) := by
  unfold foldeqSymbol
  rw [foldl_maddS, ρ.zero, zero_add, list_range_sum]

/-- Row x of the code's generator matrix, on the message and on the random tail. -/
def codeVal (S : FoldeqShape) (x : Nat) (u : Nat → K) : K :=
  let c := S.index.code
  let g := generatorAt c x
  let f := g.f.map fun a => ρ.val (ofF a)
  ρ.val (ofF g.messageScale) * (∑ j ∈ Finset.range c.ell, bitsK (f.take c.logEll) j * u j) +
    ρ.val (ofF g.tailScale) *
      (∑ j ∈ Finset.range c.r, bitsK (f.take c.logR) j * u (S.tailFirst + j))

/-- **(loc_x)'s equation, cut in its two sides.** -/
theorem locAt_iff (p : Par) (d : St) (m : Words K) (tab : Nat → List UInt64) (x : Nat) :
    LocAt ρ p d m tab x ↔
      codeVal ρ p.S.fold x (fun k => m d.loc.oU.oracle .main (d.loc.oU.lay.index k)) =
        ρ.val (foldeqSymbol (foldeqWeights (d.loc.psiSh.drop p.S.kLo)) (tab x).toArray) := by
  rw [foldeqSymbol_val]
  exact Iff.rfl

end Desc.K14.Law
