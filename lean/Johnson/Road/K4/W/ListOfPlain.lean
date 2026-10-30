-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/W/ListOfPlain.lean: CONDITIONAL.

Not shown here. THAT ANY DATA HOLD THE PACKING OF ANY LIST: hpack is a hypothesis, and it is the
content. That the list is 0 outside the sizes of the plan tl (hsup) and small at the library's shift
2 ^ 17 (hsmall): hypotheses on the list. Of tl the statement reads the number of matrices, their
rows and columns, and which array holds a matrix's symbols (`gtTree`); the radix 2 ^ 20 and the
shift are the library's constants at every tl. hpack lays one address for each matrix: at a tl that
names one array for two matrices it forces two packings to be equal. THAT THE DATA HOLD ANYTHING AT
AN ADDRESS: they read 0 where no seat is listed for the array: whether the seats are there is a
public test, shown here of no list. Of the hypotheses together, at a run's data, no example is
known. Nothing on soundness, on completeness or on any other property.
No property is claimed.
WHAT THIS FILE's IMPORTS REACH, by a program's walk from import to import: no module under
Johnson/Goal/, Johnson/D/ or ThirdParty/, and none whose name holds RecCompile. It imports nothing
of the honest side (Johnson/Desc/ProofFile/Honest/).

The hypothesis `DataIsList` (W/MatsOfList.lean) from three sentences IN PLAIN NUMBERS: no index of a
bounded type; every bound is a plain inequality on numbers: so that whoever knows what the data hold
at an address, and whoever knows the list, can each read them. General in the sizes.

  `packAt rad L a c i`   row i of the packing of column c of matrix a of the list L, at the radix
      rad: three rows of L in one integer.
  `pack_plain`   the library's `Alg.pack` of a column of L, cut at m rows, is `packAt` where L is 0
      from row m on.
  `dataIsList_of_plain`   **`DataIsList tl names Dt L`** from hsup, hsmall and hpack.
-/
import Johnson.Road.K4.W.MatsOfList

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.W
open OnBytes OnBytes.Model OnBytes.Road
open OnBytes.Road.Rows (Addr)
open OnBytes.Road.Rows.Norms (mzTot)
open Cb.Pv.Tail (baseAt_of_packs uniq_gl)
open VerifiableInference.Desc.K9L (Bound)
open VerifiableInference.Desc.First.Look (szOf)
open VerifiableInference.Desc.Sound (GQ dataByAddr)

/-- Row i of the packing of column c of matrix a of the list L, at the radix rad. -/
def packAt (rad : ℤ) (L : Mats ℤ) (a c i : ℕ) : ℤ :=
  L a (3 * i) c + rad * L a (3 * i + 1) c + rad ^ 2 * L a (3 * i + 2) c

/-- The library's packing of a column of L, cut at m rows, where L is 0 from row m on. CONDITIONAL:
on h0. -/
theorem pack_plain (rad : ℤ) (L : Mats ℤ) (a c m : ℕ) (h0 : ∀ r, m ≤ r → L a r c = 0) (i : ℕ) :
    Alg.pack rad (fun r : Fin m => L a r.val c) i = packAt rad L a c i := by
  have hl : ∀ l, Alg.lane (fun r : Fin m => L a r.val c) i l = L a (3 * i + l) c := by
    intro l
    unfold Alg.lane
    by_cases h : 3 * i + l < m
    · rw [dif_pos h]
    · rw [dif_neg h, h0 _ (Nat.le_of_not_lt h)]
  unfold Alg.pack packAt
  rw [hl 0, hl 1, hl 2]
  simp

/-- **`DataIsList` FROM THREE SENTENCES IN PLAIN NUMBERS.** hsup: L is 0 outside the plan's sizes.
hsmall: its entries are small at the library's shift. hpack: inside the sizes the data's cell at the
address of a symbol is the image of that row of L's packing at the library's radix. CONDITIONAL: on
hsup, hsmall and hpack. -/
theorem dataIsList_of_plain (tl : HTailF2) (names : Array (ℕ × String)) (Dt : Bound GQ)
    (L : Mats ℤ)
    (hsup : ∀ a r c, ¬ (a < (szOf tl).NM ∧ c < (szOf tl).k a ∧ r < (szOf tl).m a) → L a r c = 0)
    (hsmall : ∀ a r c, |L a r c| < 2 * ((szOf tl).beta : ℤ))
    (hpack : ∀ a, a < (szOf tl).NM → ∀ i, i < Alg.symRows ((szOf tl).m a) → ∀ c,
      c < (szOf tl).k a →
        dataByAddr names Dt (Addr.cell (tl.gtTree.getD a 0) i c) =
          ((packAt ((szOf tl).rad : ℤ) L a c i : ℤ) : GQ)) :
    DataIsList tl names Dt L := by
  refine ⟨fun μ c i => L μ.val i.val c.val,
    baseAt_of_packs Cb.Gl.p (uniq_gl (s := szOf tl) rfl rfl) (fun μ c i => hsmall _ _ _)
      (fun μ c i' => ?_), ?_⟩
  · show dataByAddr names Dt (Addr.cell (tl.gtTree.getD μ.val 0) i'.val c.val) = _
    rw [hpack μ.val μ.isLt i'.val i'.isLt c.val c.isLt,
      pack_plain _ L μ.val c.val _ (fun r hr => hsup _ _ _ fun q => absurd q.2.2 (Nat.not_lt.2 hr))]
  · funext σ r c
    unfold mzTot
    by_cases h : σ < (szOf tl).NM
    · rw [dif_pos h]
      by_cases hc : c < (szOf tl).k (⟨σ, h⟩ : Fin (szOf tl).NM)
      · rw [dif_pos hc]
        by_cases hr : r < (szOf tl).m (⟨σ, h⟩ : Fin (szOf tl).NM)
        · rw [dif_pos hr]
        · rw [dif_neg hr, hsup _ _ _ fun q => hr q.2.2]
      · rw [dif_neg hc, hsup _ _ _ fun q => hc q.2.1]
    · rw [dif_neg h, hsup _ _ _ fun q => h q.1]

end OnBytes.Road.K4.W

#print axioms OnBytes.Road.K4.W.pack_plain
#print axioms OnBytes.Road.K4.W.dataIsList_of_plain
