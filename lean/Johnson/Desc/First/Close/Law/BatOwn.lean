-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Close/Law/BatOwn.lean: the defect of the row that the closing's batching returns
(`bat`, Johnson/Desc/First/Close/Closing.lean), with every premise said at the statement IN FRONT of
the batching and every row read on the oracle messages' own tables. One definition, statements and
proofs.

`bat_defect` (BatAtClosing.lean, beside this file) speaks at the statement behind the mark "the
group's test has begun", and of rows "seen through the group". Whoever lays a row knows it at the
statement in front, and on the messages' own tables. Here the two are joined.
  `placeBits_of_shape`, `begun_placeBits`: the mark turns no table's number of place bits.
  `begun_rowFits`, `begun_maskFits`, `begun_rowInGroup`, `begun_codesAgree`: the four conditions go
    over from the statement in front to the statement behind the mark.
  `ownSum ρ S N tab r`: a row's coefficients applied to the two tables of each oracle message below
    N.
  `bat_defect_own`: if `bat` says yes; every row that it batches meets `RowFits`, `MaskFits` and
    `RowInGroup` at the statement in front; and `CodesAgree` holds there: what the returned row says
    of the group's two tables, made of tab, and of the kept members' own tables, minus its target,
    is the sum under the powers of the drawn element of `ownSum` of each row minus that row's
    target.

Limits. One direction: from a yes of `bat`. The four conditions are premises, asked of every row
that is batched: the group's open rows, the members' sample rows, the generator rows. The tables are
letters: nothing says which tables a prover is bound to. Nothing on the fold behind the batching.
Nothing on soundness.

-/
import Johnson.Desc.First.Close.Law.BatAtClosing
import Johnson.Desc.First.Close.Law.LayNames

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.LayLaw
open OnBytes.Slice

variable {K : Type} [CommRing K] (ρ : Model.Reading K)

/-- Two statements with the same shapes and the same codes give a table the same place bits. -/
theorem placeBits_of_shape (S T : Statement) (o : Nat) (part : Part) (hc : T.codes = S.codes)
    (h : (T.oracles[o]?).map (·.shape) = (S.oracles[o]?).map (·.shape)) :
    T.placeBits o part = S.placeBits o part := by
  unfold Statement.placeBits
  cases h1 : T.oracles[o]? with
  | none =>
    cases h2 : S.oracles[o]? with
    | none => rfl
    | some y => rw [h1, h2] at h; cases h
  | some x =>
    cases h2 : S.oracles[o]? with
    | none => rw [h1, h2] at h; cases h
    | some y =>
      rw [h1, h2] at h
      have e : x.shape = y.shape := Option.some.inj h
      dsimp only
      rw [e, hc]

theorem begun_placeBits (S : Statement) (g : Nat) (G : Group) (o : Nat) (part : Part) :
    (begun S g G).placeBits o part = S.placeBits o part :=
  placeBits_of_shape S _ o part (closeLedgers_codes _ _) (closeLedgers_shape G.members.toList S o)

theorem begun_rowFits (S : Statement) (g : Nat) (G : Group) (r : Row) (h : RowFits S r) :
    RowFits (begun S g G) r :=
  ⟨fun t ht => by rw [begun_rowBits]; exact h.terms t ht, h.runs,
    fun f hf v hv => by rw [begun_rowBits]; exact h.forms f hf v hv⟩

theorem begun_maskFits (S : Statement) (g : Nat) (G : Group) (L : GroupLayout) (r : Row)
    (h : MaskFits S L r) : MaskFits (begun S g G) L r :=
  fun t ht hp => by rw [begun_rowBits]; exact h t ht hp

theorem begun_rowInGroup (S : Statement) (g : Nat) (G : Group) (r : Row)
    (h : RowInGroup ρ S G r) :
    RowInGroup ρ (begun S g G) { G with inRun := true, rows := #[] } r :=
  ⟨h.off, fun o part hh => h.absent o part (by rw [← begun_has S g G]; exact hh)⟩

theorem begun_codesAgree (S : Statement) (g : Nat) (G : Group) (L : GroupLayout)
    (h : CodesAgree S G L) :
    CodesAgree (begun S g G) { G with inRun := true, rows := #[] } L :=
  ⟨fun o i hi hh hk => by
      rw [begun_placeBits]
      exact h.main o i hi (by rw [← begun_has S g G]; exact hh) hk,
    fun o i hi hh => by
      rw [begun_placeBits]
      exact h.mask o i hi (by rw [← begun_has S g G]; exact hh)⟩

/-- A row's coefficients applied to the two tables of each oracle message below N. -/
def ownSum (S : Statement) (N : Nat) (tab : Nat → Part → Nat → K) (r : Row) : K :=
  ∑ o ∈ Finset.range N,
    ((∑ J ∈ Finset.range (2 ^ (S.rowBits o .main + S.placeBits o .main)),
        ρ.val (r.coefficient o .main J) * tab o .main J) +
      ∑ j ∈ Finset.range (2 ^ (S.rowBits o .mask + S.placeBits o .mask)),
        ρ.val (r.coefficient o .mask j) * tab o .mask j)

theorem begun_ownSum (S : Statement) (g : Nat) (G : Group) (N : Nat)
    (tab : Nat → Part → Nat → K) (r : Row) :
    ownSum ρ (begun S g G) N tab r = ownSum ρ S N tab r := by
  unfold ownSum
  simp only [begun_rowBits, begun_placeBits]

end OnBytes.LayLaw

namespace VerifiableInference.Desc.First.Close

open OnBytes OnBytes.Slice OnBytes.LayLaw Cb

/-- **THE DEFECT OF THE ROW THAT THE CLOSING's BATCHING RETURNS, FROM WHAT EACH ROW SAYS OF THE
ORACLE MESSAGES' OWN TABLES**, every premise at the statement in front. -/
theorem bat_defect_own {S S1 : Statement} {g : Nat} {e : Fmt.Entry} {r : Fmt.RoundView} {row : GroupRow}
    {lay : GroupLayout} (h : bat S g e r = .ok (row, lay, S1)) :
    ∃ (G : Group) (x : E), S.groups[g]? = some G ∧ r.drawn.elems = [x.triple] ∧ S1 = begun S g G ∧
      ((∀ w ∈ (runRows S G).toList, RowFits S w ∧ MaskFits S lay w ∧ RowInGroup rdE S G w) →
        CodesAgree S G lay → ∀ (N : Nat), lay.top ≤ N → ∀ tab : Nat → Part → Nat → GE,
          groupSum rdE S1 lay N tab (groupMain S1 lay N fun o => tab o .main)
              (groupMask S1 lay N fun o => tab o .mask) row - readE row.target =
            hornerSum (readE x) ((runRows S G).toList.map fun w =>
              ownSum rdE S N tab w - readE w.target)) := by
  obtain ⟨G, x, hG, hx, hc, rfl, -, hl⟩ := bat_inv_layout h
  refine ⟨G, x, hG, hx, rfl, fun hr hca N hN tab => ?_⟩
  refine (defect_at_layout rdE (begun S g G) g lay hl (runRows S G) x row hc
    (fun w hw => ⟨begun_rowFits S g G w (hr w hw).1, begun_maskFits S g G lay w (hr w hw).2.1⟩)
    N hN tab).trans ?_
  refine congrArg _ (List.map_congr_left fun w hw => ?_)
  have e1 : rowSumIn rdE (begun S g G) lay N tab w = ownSum rdE (begun S g G) N tab w :=
    rowSumIn_own rdE (begun S g G) g _ lay (begun_group S g G hG) hl w
      (begun_rowInGroup rdE S g G w (hr w hw).2.2) (begun_codesAgree S g G lay hca) N tab
  rw [e1, begun_ownSum]
  rfl

end VerifiableInference.Desc.First.Close

#print axioms VerifiableInference.Desc.First.Close.bat_defect_own
