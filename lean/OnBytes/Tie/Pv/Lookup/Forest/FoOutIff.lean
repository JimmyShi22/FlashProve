-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Forest/FoOutIff.lean.
The lookup of a sub-proof: what its output claim says, in the terms of the byte-level verifier's end
values.

The typed lookup's output claim speaks of a masked claim on the joint key vector and of a list of
rows. A caller needs it in the terms in which the byte-level verifier hands its end values on.

States:
  toRow_holds: a sparse row, its places renamed and then spread over all entries, holds of a reading
    if and only if the sparse row holds of the reading after the renaming.
  forOut_iff: for every out-statement x whose list of rows is the one that the record of end values
    describes, its places renamed by ι (one clause of Fo.OutIs; of the rest of x nothing is asked),
    and every reading μ of the entries that reads the entry "none" as 0:
    the lookup's output claim holds of x and μ if and only if
      every claim on mask entries alone holds (the tie's 31, the key levels' v, the table's levels'
        d, the bits' sumcheck's),
      the row of the leaves' sumcheck holds in the byte-level verifier's form (leavesA times the
        planes at zb0),
      the value shown by the bits' sumcheck, less its mask's share, is the planes at zb1,
      the counts sum to the number of keys that are not padding (TwV.rowNum), and
      the masked claim on the joint key vector holds: and nothing else.
Premises: FoNums.ok h, 5 ≤ lm ≤ kT + 5; the renaming ι takes the place that is no cell to the entry
"none". None reads a witness.
"The byte-level verifier's form" is here the plain functions Fo.leavesAK, Fo.planesK and Fo.colsK.
That the byte-level routines compute them is not stated in this file (for leavesAK: leavesA_val,
OnBytes/Tie/Pv/Lookup/Port/FoTwins.lean). The masked claim on the keys stands on both sides as it
is.

-/
import OnBytes.Tie.Pv.Lookup.Forest.FoPlaneRows
import OnBytes.Tie.Pv.Lookup.Forest.FoOut
import OnBytes.Tie.Pv.Lookup.Forest.FoJoinAt

set_option autoImplicit false

namespace Fo
open Iop IOR Cb Cb.Tw Cb.LdLkp Cb.Lkp TwV Tw3 Tw Cb.Fo Cb.Fo.NumsEq Finset

section
variable {E : Type} [Field E] [Fintype E] {St₀ J₀ : Type} [Fintype J₀] [DecidableEq J₀]

omit [Fintype E] in
/-- A sparse row, renamed and spread, holds if and only if it holds after the renaming of the
reading. -/
theorem toRow_holds (ι : Pl → Option J₀) (r : SRow Pl E) (μ : Option J₀ → E) :
    (toRow (rowMap ι r)).Holds μ ↔ SRowHolds r fun p => μ (ι p) := by
  unfold SRowHolds valS
  show ∑ j, dense (mapL ι r.cf) j * μ j = r.tg ↔ _
  rw [dense_val]
  unfold mapL
  rw [List.map_map]
  rfl

omit [Field E] [Fintype E] [Fintype J₀] [DecidableEq J₀] in
/-- The rows in the order in which the lookup leaves them, and in the order of the run. -/
theorem mem_split {α : Type} (A B C : List α) (re bu be rn : α) (P : α → Prop) :
    (∀ r ∈ A.reverse ++ (B.reverse ++ ((C.reverse ++ [re, bu, be]) ++ [rn])), P r) ↔
      (∀ r ∈ A ++ B ++ C ++ [bu], P r) ∧ P re ∧ P be ∧ P rn := by
  simp only [List.mem_append, List.mem_reverse, List.mem_cons, List.not_mem_nil, or_false, or_imp,
      forall_and,
    forall_eq]
  tauto

/-- What the lookup's output claim says. -/
theorem forOut_iff (h : FoNums.Sh) (H : FoNums.ok h = true) (L : Lay E St₀ J₀) (lm jLK : ℕ) (h5 : 5
    ≤ lm)
    (hlm : lm ≤ h.kT + 5) (ι : Pl → Option J₀) (hι : ι .zero = none) (rs : Rounds E)
    (x : TX (St₀ × E) E (Option J₀))
    (hx : x.2.2 = (((endsOf h lm jLK rs).tieRows.reverse ++ ((endsOf h lm jLK rs).keyRows.reverse ++
        (((endsOf h lm jLK rs).tabRows.reverse ++
          [rowEnd (forN h lm jLK rs) (forTrace h lm jLK rs), (endsOf h lm jLK rs).bitU,
            rowBitE (forN h lm jLK rs) (forTrace h lm jLK rs)]) ++
          [rowNum (forN h lm jLK rs)]))).map (rowMap ι)).map toRow)
    (μ : Option J₀ → E) (hμ : μ none = 0) :
    (forA E h L).lk.out id id x μ ↔
      (∀ r ∈ (endsOf h lm jLK rs).rows, SRowHolds r fun p => μ (ι p)) ∧
      (valS (hide (forN h lm jLK rs).ledE (dgE (forN h lm jLK rs)) (endsOf h lm jLK rs).lvXs) (fun p
          => μ (ι p)) +
          (endsOf h lm jLK rs).lvEps * valS (endsOf h lm jLK rs).lvInc (fun p => μ (ι p)) +
          (endsOf h lm jLK rs).lvEps * (leavesAK h (endsOf h lm jLK rs).theta (endsOf h lm jLK
              rs).alpha (endsOf h lm jLK rs).zb0 *
            planesK h lm (endsOf h lm jLK rs).zb0 (colsK h lm (endsOf h lm jLK rs).zb0 fun p => μ (ι
                p))) =
        (endsOf h lm jLK rs).lvFin - (endsOf h lm jLK rs).lvEps) ∧
      (((forTrace h lm jLK rs).bits.v 0 - (forTrace h lm jLK rs).bits.be * μ (ι ((forN h lm jLK
          rs).ledB.sh 0))) -
          planesK h lm (endsOf h lm jLK rs).zb1 (colsK h lm (endsOf h lm jLK rs).zb1 fun p => μ (ι
              p)) = 0) ∧
      SRowHolds (rowNum (forN h lm jLK rs)) (fun p => μ (ι p)) ∧
      x.2.1.Holds (FoNums.v' h + 1) ((forA E h L).key x.1 μ) μ := by
  have h0 : (fun p => μ (ι p)) Pl.zero = 0 := by
    show μ (ι .zero) = 0
    rw [hι]
    exact hμ
  have hE := rowEnd_iff h H lm jLK h5 hlm (thetaOf h rs) (fun p => μ (ι p)) h0 (forTrace h lm jLK
      rs)
  have hB := rowBitE_iff h H lm jLK h5 hlm (thetaOf h rs) (fun p => μ (ι p)) h0 (forTrace h lm jLK
      rs)
  have hR : RowsHold x.2.2 μ ↔
      ∀ r ∈ (endsOf h lm jLK rs).tieRows.reverse ++ ((endsOf h lm jLK rs).keyRows.reverse ++
        (((endsOf h lm jLK rs).tabRows.reverse ++
          [rowEnd (forN h lm jLK rs) (forTrace h lm jLK rs), (endsOf h lm jLK rs).bitU,
            rowBitE (forN h lm jLK rs) (forTrace h lm jLK rs)]) ++
          [rowNum (forN h lm jLK rs)])), SRowHolds r fun p => μ (ι p) := by
    rw [hx]
    unfold RowsHold
    simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    exact forall_congr' fun r => imp_congr_right fun _ => toRow_holds ι r μ
  show x.2.1.Holds _ _ μ ∧ RowsHold x.2.2 μ ∧ True ↔ _
  rw [hR, mem_split]
  exact ⟨fun ⟨hk, ⟨h1, h2, h3, h4⟩, _⟩ => ⟨h1, hE.1 h2, hB.1 h3, h4, hk⟩,
    fun ⟨h1, h2, h3, h4, hk⟩ => ⟨hk, ⟨h1, hE.2 h2, hB.2 h3, h4⟩, trivial⟩⟩

end
end Fo
