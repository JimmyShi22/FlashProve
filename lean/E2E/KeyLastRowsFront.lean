-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
E2E/KeyLastRowsFront.lean: the rows in front of the last chain's first member hold of the chain's words, from the first chain's item
(Eval): the own group has one open row, and it is the row that the item speaks of.

  `rows_front`: at a state.
  `one_row_A0`, `one_row_of_shape`: the one row, at the written shape: a closed line.

What stays open. hh: the item, read at the first half of the witness. hsame: the letter for sameness is "the two read as one element".
Nothing on soundness, completeness, hiding or binding.
-/
import E2E.KeyLastWords
import Johnson.Desc.Key.RowHoldsSays

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace AtPublicFiles.KeyLastChain
open OnBytes OnBytes.Slice OnBytes.Means Cb
open OnBytes.Params (LinShape)
open VerifiableInference.Desc.Ground.Sh
open VerifiableInference.Desc.Third (S₃)
open VerifiableInference.Desc.Third.Law (RowsHold says_congr Names)
open VerifiableInference.Desc.Key (RowHolds rowHolds_iff_says_of_rowIn)
open AtPublicFiles.AtFiles (Sh₃ sh₃ SF)
open AtPublicFiles.AtFiles.Full (A0)

section
variable {Wt₁ : Type} (val₁ : Wt₁ → Nat → Part → Nat → GE)

/-- **The rows in front hold.** val: the reading of the first half at u. -/
theorem rows_front (s : S₃) (u : Wt₁ × Words GE) (val : Nat → Part → Nat → E)
    (hv : ∀ o pt i, val₁ u.1 o pt i = readE (val o pt i)) (G : OnBytes.Group)
    (hG : s.st.groups[s.loc.own]? = some G) (h1 : G.rows.size = 1) (r : OnBytes.Row) (hr : G.rows[0]? = some r)
    (hin : RowIn s.st G r) (hh : RowHolds (fun a b => readE a = readE b) s.st val r)
    (ho : s.st.oracles.size ≤ s.loc.omega) : RowsHold rdE s (wordsKey val₁ s u) := by
  intro G' hG' r' hr'
  obtain rfl : G = G' := Option.some.inj (hG.symm.trans hG')
  obtain rfl : r' = r := by
    have hm := Array.mem_toList_iff.1 hr'
    obtain ⟨i, hi, e⟩ := Array.mem_iff_getElem.1 hm
    have hi0 : i = 0 := by omega
    subst hi0
    have e' : G.rows[0]? = some r' := by
      rw [Array.getElem?_eq_getElem hi, e]
    exact Option.some.inj (e'.symm.trans hr)
  refine (says_congr rdE s.st r' _ _ fun o hlt pt i => ?_).2
    ((rowHolds_iff_says_of_rowIn rdE s.st G val r' hin).1 hh)
  unfold wordsKey
  rw [if_neg (by omega), hv]
  rfl

end

/-- The own group has one open row, at the written shape. -/
theorem one_row_A0 : ((A0.1.st.groups[A0.2.own]?).any fun G => G.kinds.length == 1) = true := by decide +kernel

/-- **So at a state of that shape.** -/
theorem one_row_of_shape {s : S₃} (hsh : sh₃ SF s = A0) {G : OnBytes.Group}
    (hG : s.st.groups[s.loc.own]? = some G) : G.rows.size = 1 := by
  have h := one_row_A0
  rw [← hsh] at h
  have h' : (((stSh s.st).groups[s.loc.own]?).any fun G => G.kinds.length == 1) = true := h
  rw [grp_get, hG] at h'
  have h'' : ((grpSh G).kinds.length == 1) = true := h'
  have e : (grpSh G).kinds.length = G.rows.size := by
    show (G.rows.toList.map (·.kind)).length = _
    simp
  rw [e] at h''
  exact beq_iff_eq.1 h''

end AtPublicFiles.KeyLastChain

#print axioms AtPublicFiles.KeyLastChain.rows_front
#print axioms AtPublicFiles.KeyLastChain.one_row_A0
#print axioms AtPublicFiles.KeyLastChain.one_row_of_shape
