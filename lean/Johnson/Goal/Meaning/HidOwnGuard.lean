-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Meaning/HidOwnGuard.lean: the make hidOf (Johnson/Goal/Meaning/HidOwn.lean) loses no
witness, and the eleven clauses that it leaves ask neither too much nor too little.

hidOf makes hidden values from each sub-proof's own arrays, so that the three seams of Means hold by
the make. A make could be too narrow: it could be that hidden values which meet Means are never of
this form, so that MeansOwn is met by nothing. This file shows that it is not so.

Main names:
  ownsOf w   the lists of hidden values w, as one family by sub-proof: 2 g: w.MG g; 2 g + 1: w.MA g.
  oneWord_of_means   hidden values that meet Means have OneWord at ownsOf w: it is their two seams.
  means_hidOf_of_means   if w meets Means, so does hidOf X w.tok (ownsOf w).
  meansOwn_iff_true   at public files in the goals' scope: some family own meets the eleven clauses
    exactly if the request is true under its policy (with means_iff_true,
    Johnson/Goal/Meaning/RowGuard.lean).

What is not claimed. That an honest prover's files hold these values; anything on a protocol, on
extractors or on the commitments. OneWord is shown here of hidden values that meet Means already,
where it is the seams themselves; of what two sub-proofs read in a run nothing is shown.
The program does not import this file.
-/
import Johnson.Goal.Meaning.HidOwn
import Johnson.Goal.Meaning.RowGuard

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Meaning

open Inst.Model Inst.Model.All
open OnBytes OnBytes.Road OnBytes.Road.L5 OnBytes.Road.Rows.Norms
open OnBytes.Model.Verify (publicOf layerShape)
open OnBytes.Model.Layer (Lay matIx)

/-- The lists of hidden values, as one family by sub-proof. -/
def ownsOf (w : Hid) : ℕ → Mats ℤ := fun k => if k % 2 = 0 then w.MG (k / 2) else w.MA (k / 2)

theorem ownsOf_even (w : Hid) (g : ℕ) : ownsOf w (2 * g) = w.MG g := by
  unfold ownsOf
  rw [if_pos (by omega), show 2 * g / 2 = g by omega]

theorem ownsOf_odd (w : Hid) (g : ℕ) : ownsOf w (2 * g + 1) = w.MA g := by
  unfold ownsOf
  rw [if_neg (by omega), show (2 * g + 1) / 2 = g by omega]

variable {X : Model.Verify.Public} {pp : ScalesAndPolicy} {i : Cm.Idx} {x : Instance ppref}

/-- Of hidden values that meet Means, OneWord is the two kinds of seams. -/
theorem oneWord_of_means {w : Hid} (M : Means X pp i x w) : OneWord X (ownsOf w) := by
  refine OneWord.of_all (fun g h0 hg r c => ?_) fun g hg r c => ?_
  · rw [ownsOf_even, ownsOf_even]
    exact (M.layers g hg).seam h0 r c
  · rw [ownsOf_odd, ownsOf_even]
    exact (M.attention g hg).seam r c

/-- **The make loses no witness.** -/
theorem means_hidOf_of_means {w : Hid} (M : Means X pp i x w) :
    Means X pp i x (hidOf X w.tok (ownsOf w)) := by
  refine means_hidOf_iff.mpr ⟨fun g hg => ?_, fun g hg => ?_, ?_⟩
  · rw [mgOf_seen (oneWord_of_means M) hg, ownsOf_even]
    exact ⟨(M.layers g hg).small, (M.layers g hg).norm, (M.layers g hg).hot, (M.layers g hg).emb,
      (M.layers g hg).key⟩
  · rw [maOf_of_all (fun r c => by
      rw [ownsOf_odd, ownsOf_even]
      exact (M.attention g hg).seam r c), ownsOf_odd]
    exact ⟨(M.attention g hg).small, (M.attention g hg).key, (M.attention g hg).own1,
      (M.attention g hg).own2, (M.attention g hg).ridden⟩
  · rw [mgOf_seen (oneWord_of_means M) (by norm_num : 11 < 12), ownsOf_even]
    exact SaysHead.congr M.head.seam (fun _ _ _ => rfl) M.head.plain

/-- **The eleven clauses ask neither too much nor too little.** -/
theorem meansOwn_iff_true {Z : VerifierAndGoals.PublicFiles} {lay : Option ByteArray}
    (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) (i : Cm.Idx) (x : Instance ppref) :
    (∃ own : ℕ → Mats ℤ, MeansOwn X pp i x own) ↔
      Policy.IsTrueUnder (Cm.Scales.of pp) pp.pol i x := by
  rw [← means_iff_true hZ hR h i x]
  exact ⟨fun ⟨own, O⟩ => ⟨hidOf X x.y own, means_hidOf_iff.mpr O⟩,
    fun ⟨_, M⟩ => ⟨_, means_hidOf_iff.mp (means_hidOf_of_means M)⟩⟩

end Meaning

#print axioms Meaning.ownsOf_even
#print axioms Meaning.ownsOf_odd
#print axioms Meaning.oneWord_of_means
#print axioms Meaning.means_hidOf_of_means
#print axioms Meaning.meansOwn_iff_true
