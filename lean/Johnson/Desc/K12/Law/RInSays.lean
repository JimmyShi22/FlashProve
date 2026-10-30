-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Law/RInSays.lean: what the relation in front of the proximity test's chain says,
unfolded into `GroupSays`. Statements and proofs.

The library's relation before a fold (`Sg.RIn`, OnBytes/Slice/Stage.lean) at the claim `q := stmG s
row` is told in the words of `GroupSays` (Johnson/Desc/Means/Says.lean). It is the second half of
the condition under which the law of the proximity test stands.
Main names:
  `tabOf s w`: the way back: a message of the stage's tables before the fold as a group's two
    tables: the entry at the index J is the message's at (row J % 2^k, place J / 2^k); 0 beyond the
    table; no kept table.
  `msgOf_tabOf`: `msgOf s (tabOf s w) = w`.
  `rIn_iff`: under the five premises of Johnson/Desc/K12/Law/ClaimSays.lean: `s.RIn e (stmG s row,
    y) w` holds just where the witness's encoding is within e positions of y and `GroupSays rdE S L
    row (tabOf s w.1)`.
  `no_rIn_iff`: the premise of `chain_many` (OnBytes/Slice/ManySem.lean) "the claim on the word y
    has no witness at the radius e" says: no message and tail whose encoding is within e positions
    of y make tables of which the group's row says its claim.
Limits: nothing is said on y (that it is the reading of the committed trees). Nothing is said on how
the tables of `tabOf` lie to the members' own tables (`tablesOf`, `Laid`, `Padded`,
Johnson/Desc/Means/Says.lean): a witness's message fills the whole of the group's tables, also the
rows that no member has. No soundness is claimed, and nothing is said on hiding.
Lemmas of `verify-on-bytes`'s library that are called (none runs in a context of that program):
`rowNo_lt`, `testBit_rowNo` (OnBytes/Slice/Cells.lean).
No sorry, no axiom of ours; each theorem has its premises; what the main ones rest on is printed at
the file's end.

-/
import Johnson.Desc.K12.Law.ClaimSays

set_option autoImplicit false
namespace H2K.ClaimSays
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun
open Iop Prob Cb Cb.Ood _root_.Run
open OnBytes.Means

/-- One table back: k row variables, l places. -/
def tabBack (k l : ℕ) (w : (Fin k → Bool) × Fin l → GE) (J : ℕ) : GE :=
  if h : J / 2 ^ k < l then w (fun t => (J % 2 ^ k).testBit t.val, ⟨J / 2 ^ k, h⟩) else 0

theorem tabBack_at (k l : ℕ) (w : (Fin k → Bool) × Fin l → GE) (x : (Fin k → Bool) × Fin l) :
    tabBack k l w (Sz.rowNo x.1 + 2 ^ k * x.2.val) = w x := by
  have hlt := rowNo_lt x.1
  have hd : (Sz.rowNo x.1 + 2 ^ k * x.2.val) / 2 ^ k = x.2.val := by
    rw [Nat.add_mul_div_left _ _ (Nat.two_pow_pos k), Nat.div_eq_of_lt hlt, Nat.zero_add]
  have hm : (Sz.rowNo x.1 + 2 ^ k * x.2.val) % 2 ^ k = Sz.rowNo x.1 := by
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]
  unfold tabBack
  rw [dif_pos (by rw [hd]; exact x.2.isLt)]
  congr 1
  refine Prod.ext ?_ (Fin.ext hd)
  funext t
  show ((Sz.rowNo x.1 + 2 ^ k * x.2.val) % 2 ^ k).testBit t.val = x.1 t
  rw [hm, testBit_rowNo]

/-- The way back. -/
def tabOf (s : Sg) (w : s.cIn.J → GE) : Tables GE where
  main := tabBack (s.h + s.g) s.C.l fun x => w (.inl x)
  mask := tabBack s.h s.Z.l fun x => w (.inr x)
  kept := fun _ _ => 0

theorem msgOf_tabOf (s : Sg) (w : s.cIn.J → GE) : msgOf s (tabOf s w) = w := by
  funext j
  rcases j with x | x
  · exact tabBack_at (s.h + s.g) s.C.l (fun x => w (.inl x)) x
  · exact tabBack_at s.h s.Z.l (fun x => w (.inr x)) x

theorem rIn_iff (s : Sg) (S : Statement) (L : GroupLayout) (row : GroupRow) (e : ℕ)
    (y : s.cIn.Word) (w : s.cIn.N.Wit)
    (hk : L.k = s.h + s.g) (hh : L.h = s.h) (hl : 2 ^ L.logEll = s.C.l) (hz : 2 ^ L.logEllZk =
        s.Z.l)
    (h0 : row.kept = #[]) :
    s.RIn e (stmG s row, y) w ↔
      offCnt (Ex := s.cIn.ext) y (s.cIn.N.enc w.1 w.2) ≤ e ∧ GroupSays rdE S L row (tabOf s w.1) :=
          by
  rw [groupSays_iff s S L row (tabOf s w.1) hk hh hl hz h0, msgOf_tabOf]
  exact Iff.rfl

theorem no_rIn_iff (s : Sg) (S : Statement) (L : GroupLayout) (row : GroupRow) (e : ℕ)
    (y : s.cIn.Word)
    (hk : L.k = s.h + s.g) (hh : L.h = s.h) (hl : 2 ^ L.logEll = s.C.l) (hz : 2 ^ L.logEllZk =
        s.Z.l)
    (h0 : row.kept = #[]) :
    (∀ w, ¬ s.RIn e (stmG s row, y) w) ↔
      ∀ w : s.cIn.N.Wit, offCnt (Ex := s.cIn.ext) y (s.cIn.N.enc w.1 w.2) ≤ e →
        ¬ GroupSays rdE S L row (tabOf s w.1) := by
  constructor
  · intro h w h1 h2
    exact h w ((rIn_iff s S L row e y w hk hh hl hz h0).2 ⟨h1, h2⟩)
  · intro h w hw
    obtain ⟨h1, h2⟩ := (rIn_iff s S L row e y w hk hh hl hz h0).1 hw
    exact h w h1 h2

end H2K.ClaimSays

#print axioms H2K.ClaimSays.rIn_iff
#print axioms H2K.ClaimSays.no_rIn_iff
