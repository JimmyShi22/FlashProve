-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Law/RunSound.lean: the two counts of the linear claim's shared rounds, along a run:
from the places' own yes to the two proximity tests, with no premise on the statement's tables.

  fold_sound_run   the places up to the joinings have said yes (SharedFront); the words of o_omega
                   and o_u are fixed. If omega_col is not col_psi_lo(u) at a row of M, then at no
                   more than kRow |K| ^ (kRow - 1) points z_fd can the run go on ("LIN zeta" draws
                   elements that read as z_fd; "SPLIT" says yes; the state reaches the two tests)
                   so that all constraints on the two groups hold of words that agree with the fixed
                   ones on these two messages.
  loc_sound_run    the places up to "(rec_gamma)" have led to a state; the words of o_u and the
                   table's columns are fixed. The lists of c locations at which a run can go on to
                   the tests so that all constraints hold of words that agree with the fixed ones on
                   o_u are no more than g ^ c, g the number of locations at which LocAt holds.
The words of every other message, and of messages that are sent later, may hang on what is drawn.

What is not claimed. What lies between a receiving and the kind's note behind it is a premise inside
SharedRun and SharedFront (it goes onward and leaves the small record). That the state behind
"SPLIT" reaches each test's state stands inside the counted event (Reaches). That the constraints
hold of words is the proximity tests' law's to give. Nothing on how z_fd and the locations are
drawn, on the number g, on the columns handed being the table's, or on (rec_gamma). No soundness of
a verifier.

-/
import Johnson.Desc.K14.Law.Run

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain
open OnBytes.Model (Reading)
open OnBytes.Means (Words)
open VerifiableInference.Desc (Grows)
open VerifiableInference.Desc.Ground

variable {K : Type} [Field K] (ρ : Reading K)

/-- Two assignments of words agree on the main table of a message. -/
def AgreeOn (o : Nat) (m m' : Words K) : Prop := ∀ i, m' o .main i = m o .main i

/-- **The places up to the joinings have said yes.** -/
structure SharedFront (p : Par) (d0 d2 d3 d6 : St) (r4 : Fmt.RoundView)
    (cols : List (Nat × List UInt64)) : Prop where
  twoCodes : p.S.sharedSplitNeeded = true
  run : ∃ (d1 a1 a2 d4 b1 b2 d5 : St) (rs1 rs3 rs6 : List Fmt.RoundView)
    (ftU ftO : Nat) (sentU : Array OracleNotice) (idsU idsO : Array Nat),
    linPoint p d0 rs1 = some d1 ∧
    withU p.S = some sentU ∧ recvP ftU d1 sentU = some (idsU, a1) ∧
    Onward a1 a2 ∧ a2.loc = a1.loc ∧ behindU p a2 idsU = some d2 ∧
    laysRec p d2 rs3 = some d3 ∧ loc p d3 [r4] [cols] = some d4 ∧
    recvP ftO d4 (withOmega p.S) = some (idsO, b1) ∧
    Onward b1 b2 ∧ b2.loc = b1.loc ∧ behindOmega p b2 idsO = some d5 ∧
    joins p d5 rs6 = some d6

/-- The front with the two last places is a run. -/
theorem SharedFront.toRun {p : Par} {d0 d2 d3 d6 : St} {r4 : Fmt.RoundView}
    {cols : List (Nat × List UInt64)} (h : SharedFront p d0 d2 d3 d6 r4 cols) (d7 d8 : St)
    (r7 r8 : Fmt.RoundView) (h7 : linZeta d6 [r7] = some d7) (h8 : split p d7 [r8] = some d8) :
    SharedRun p d0 d2 d3 d7 d8 r4 cols := by
  obtain ⟨hS, d1, a1, a2, d4, b1, b2, d5, rs1, rs3, rs6, ftU, ftO, sentU, idsU, idsO,
    h1, hU, rU, cU, cUl, h2, h3, h4, rO, cO, cOl, h5, h6⟩ := h
  exact ⟨hS, d1, a1, a2, d4, b1, b2, d5, d6, rs1, rs3, rs6, r7, r8, ftU, ftO, sentU, idsU, idsO,
    h1, hU, rU, cU, cUl, h2, h3, h4, rO, cO, cOl, h5, h6, h7, h8⟩

open Classical in
/-- **The law of (fold), along a run.** -/
theorem fold_sound_run [Fintype K] (p : Par) (d0 d2 d3 d6 : St) (r4 : Fmt.RoundView)
    (cols : List (Nat × List UInt64)) (hF : SharedFront p d0 d2 d3 d6 r4 cols) (m : Words K)
    (hgap : ∃ j < p.S.matrixRows, omegaOf d6.loc (linLayOmega d6.st.codes p.S) m j ≠
      ∑ t ∈ Finset.range (2 ^ p.S.kLo),
        eqK ((d6.loc.psiSh.take p.S.kLo).map ρ.val) t * uOf d6.loc m (t + 2 ^ p.S.kLo * j)) :
    (Finset.univ.filter fun z : Fin p.S.kRow → K =>
      ∃ (r7 r8 : Fmt.RoundView) (d7 d8 eU eO : St) (m' : Words K),
        (drawn r7).map ρ.val = List.ofFn z ∧ linZeta d6 [r7] = some d7 ∧
        split p d7 [r8] = some d8 ∧
        Reaches d8 eU d6.loc.gU ∧ Reaches d8 eO d6.loc.gOmega ∧
        AgreeOn d6.loc.oOmega m m' ∧ AgreeOn d6.loc.oU.oracle m m' ∧
        Means.AllSay ρ eU.st (rowsOn eU d6.loc.gU) m' ∧
        Means.AllSay ρ eO.st (rowsOn eO d6.loc.gOmega) m').card ≤
      p.S.kRow * Fintype.card K ^ (p.S.kRow - 1) := by
  refine le_trans (Finset.card_le_card ?_) (foldCatches p.S
    ((d6.loc.psiSh.take p.S.kLo).map ρ.val) (omegaOf d6.loc (linLayOmega d6.st.codes p.S) m)
    (uOf d6.loc m) (le_two_pow_ceilLog2 _) hgap)
  intro z hz
  rw [Finset.mem_filter] at hz ⊢
  obtain ⟨_, r7, r8, d7, d8, eU, eO, m', hzs, h7, h8, hU, hO, aO, aU, sU, sO⟩ := hz
  refine ⟨Finset.mem_univ _, ?_⟩
  have l8 := (onward_split p d7 d8 r8 hF.twoCodes h8).2
  have e7 := linZeta_inv d6 d7 r7 h7
  have hg : d8.loc.gU = d6.loc.gU ∧ d8.loc.gOmega = d6.loc.gOmega := by
    rw [l8, e7]; exact ⟨rfl, rfl⟩
  have h := (shared_means ρ p d0 d2 d3 d7 d8 eU eO r4 cols (hF.toRun d7 d8 r7 r8 h7 h8)
    (by rw [hg.1]; exact hU) (by rw [hg.2]; exact hO) m'
    (by rw [hg.1]; exact sU) (by rw [hg.2]; exact sO)).2.2
  subst e7
  have eO : omegaOf d6.loc (linLayOmega d6.st.codes p.S) m' =
      omegaOf d6.loc (linLayOmega d6.st.codes p.S) m := funext fun j => aO _
  have eU : uOf d6.loc m' = uOf d6.loc m := funext fun k => aU _
  rw [← hzs, ← eO, ← eU]
  exact h

open Classical in
/-- **The law of (loc_x), along a run.** -/
theorem loc_sound_run (p : Par) (d0 d2 d3 : St) (m : Words K) (tab : Nat → List UInt64)
    (c : Nat) :
    (Finset.univ.filter fun Q : Fin c → Fin (2 ^ p.S.fold.index.code.logN) =>
      ∃ (r4 : Fmt.RoundView) (cols : List (Nat × List UInt64)) (d7 d8 eU eO : St) (m' : Words K),
        r4.drawn.poss = List.ofFn (fun i => (Q i).val) ∧
        (∀ x col, cols.lookup x = some col → col = tab x) ∧
        SharedRun p d0 d2 d3 d7 d8 r4 cols ∧
        Reaches d8 eU d8.loc.gU ∧ Reaches d8 eO d8.loc.gOmega ∧ AgreeOn d3.loc.oU.oracle m m' ∧
        Means.AllSay ρ eU.st (rowsOn eU d8.loc.gU) m' ∧
        Means.AllSay ρ eO.st (rowsOn eO d8.loc.gOmega) m').card ≤
    (Finset.univ.filter fun x : Fin (2 ^ p.S.fold.index.code.logN) =>
      LocAt ρ p d3 m tab x.val).card ^ c := by
  refine le_trans (Finset.card_le_card ?_) (le_of_eq (Fintype.card_piFinset_const _ c))
  intro Q hQ
  rw [Finset.mem_filter] at hQ
  obtain ⟨_, r4, cols, d7, d8, eU, eO, m', hr, htab, hR, hU, hO, aU, sU, sO⟩ := hQ
  rw [Fintype.mem_piFinset]
  intro i
  rw [Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_⟩
  have hx : (Q i).val ∈ locations p r4 := by
    unfold locations
    rw [hr, List.mem_map]
    exact ⟨(Q i).val, by simp [List.mem_ofFn], Nat.mod_eq_of_lt (Q i).isLt⟩
  obtain ⟨col, hcol, hEq⟩ :=
    (shared_means ρ p d0 d2 d3 d7 d8 eU eO r4 cols hR hU hO m' sU sO).2.1 _ hx
  rw [htab _ _ hcol] at hEq
  have eU : (fun k => m' d3.loc.oU.oracle .main (d3.loc.oU.lay.index k)) =
      fun k => m d3.loc.oU.oracle .main (d3.loc.oU.lay.index k) := funext fun k => aU _
  unfold LocAt
  rw [← eU]
  exact hEq

end Desc.K14.Law
