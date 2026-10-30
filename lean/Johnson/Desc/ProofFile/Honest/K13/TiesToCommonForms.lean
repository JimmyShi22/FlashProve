-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K13/TiesToCommonForms.lean: kind K13, the members' batching: THE KIND's TWO TIES
ON THE THREAD's WITNESS (`CoinsTie`, `MatTie`, ExchangeAtM3.lean of this folder) HELD AGAINST THE
FRAME's COMMON FORMS `MaskTie` AND `CellsTie` (Honest/Law/Rule/Ties.lean). Statements with their
proofs.
Main names:
  `k13Opn`, `k13Entry`: what of the state must be open (the taking of the mask entries returns), and
    the reader of the j-th mask entry.
  `coinsTie_iff`: **`CoinsTie` is `MaskTie`** at each sub-protocol that stands at the number b, at
    its place, at the second part's first spent run.
  `k13_spentOf`: that run IS all that the row's parts spend (`spentOf`, Honest/Law/Rule/Spent.lean).
  `coinsTie_iff_spent`: so `CoinsTie` is `MaskTie` at `spentOf` too.
  `coinsTie_of_book`: `CoinsTie` from `MaskTieBook`, the form without parts.
  `matN`, `cellsTie_of_matTie`: `MatTie` gives `CellsTie`, at a matrix read by two numbers.

What is not claimed. Either tie at any thread. The way back from `CellsTie` to `MatTie`: `MatTie` is
asked at every state and every list of challenges, with no thread in front. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K13.ExchangeAtM3
import Johnson.Desc.ProofFile.Honest.Law.Rule.Ties

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K13
open OnBytes
open OnBytes.Slice (GE)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Ground (takeMasksP)
open VerifiableInference.Desc.K13 (Where St)
open VerifiableInference.Desc.K13.Law (Wit ρg dOf)
open VerifiableInference.Desc.K13.Honest (maskAt)
open ProofFile.Honest.FirstThread (Letters)

variable {Bk : ProverCoinCounts} {Cl W₀ Rc Xi Tr X Pp Cells Tok M : Type}
  (L : Letters Bk Cl W₀ Rc Xi Tr X Pp Cells Tok M) (b : Nat) (weights : W₀ → Weights)
  (pile : PileOf Xi) (P : Where)
  (rd : Pp × S → VerifiableInference.Desc.Wit Cells Tok M → Wit GE P.lin.matrixRows P.lin.kCol)

/-- What of the verifier's state must be open: the taking of the kind's mask entries returns. -/
def k13Opn (s : S) : Option (List Nat × St) :=
  takeMasksP (dOf s) s.out.indexMasks (Batt.masksOf P.lin.kCol)

/-- The reader of the j-th mask entry: under the j-th slot that the verifier takes. -/
def k13Entry (t : List Nat × St) (s : S) (w : Local W₀ Rc Xi Tr)
    (v : VerifiableInference.Desc.Wit Cells Tok M) (j : Nat) : GE :=
  maskAt (rd (L.pubOf w.x, s) v) (t.1.map fun i => ⟨s.out.indexMasks, i⟩) j

/-- **`CoinsTie` is the frame's `MaskTie`**, at each sub-protocol at the number b. -/
theorem coinsTie_iff :
    CoinsTie L b weights pile P rd ↔ ∀ blk, L.thread.bs[b]? = some blk →
      MaskTie L.thread b blk.place (proverSideOfClaimCombination (Rc := Rc) (Tr := Tr) (X := X) weights pile P).parts
        (k13Opn P) (k13Entry L P rd) ρg.val (fun c => coinsE c.2.1.2.1.1)
        fun _ j => j < 2 * P.lin.kCol + 1 :=
  ⟨fun h blk hb k s m En hT t c ht hc ds j hj => (h blk hb k s m En hT c hc t ht ds j hj).symm,
    fun h blk hb k s m En hT c hc t ht ds j hj => (h blk hb k s m En hT t c ht hc ds j hj).symm⟩

/-- The second part's first spent run is all that the row's parts spend. -/
theorem k13_spentOf
    (c : RowCoins (proverSideOfClaimCombination (Rc := Rc) (Tr := Tr) (X := X) weights pile P).parts) :
    spentOf _ c = coinsE c.2.1.2.1.1 := by
  show [] ++ ((coinsE c.2.1.2.1.1 ++ []) ++ []) = _
  simp

/-- So `CoinsTie` is `MaskTie` at all that the row's parts spend. -/
theorem coinsTie_iff_spent :
    CoinsTie L b weights pile P rd ↔ ∀ blk, L.thread.bs[b]? = some blk →
      MaskTie L.thread b blk.place (proverSideOfClaimCombination (Rc := Rc) (Tr := Tr) (X := X) weights pile P).parts
        (k13Opn P) (k13Entry L P rd) ρg.val (spentOf _) fun _ j => j < 2 * P.lin.kCol + 1 := by
  rw [coinsTie_iff]
  have e : (spentOf (proverSideOfClaimCombination (Rc := Rc) (Tr := Tr) (X := X) weights pile P).parts) =
      fun c => coinsE c.2.1.2.1.1 := funext (k13_spentOf weights pile P)
  rw [e]

/-- **`CoinsTie` from the form without parts.** -/
theorem coinsTie_of_book
    (h : ∀ blk, L.thread.bs[b]? = some blk →
      MaskTieBook L.thread b blk.place 2 (k13Opn P) (k13Entry L P rd) ρg.val
        fun _ j => j < 2 * P.lin.kCol + 1) : CoinsTie L b weights pile P rd :=
  (coinsTie_iff_spent L b weights pile P rd).2 fun blk hb => maskTie_of_book (h blk hb)

/-- A matrix on rows and Boolean column points, read by two numbers: the row's number, and the
column's number by its bits; 0 beyond the rows. -/
def matN {nR k : Nat} (A : Fin nR → (Fin k → Bool) → GE) (r c : Nat) : GE :=
  if h : r < nR then A ⟨r, h⟩ fun t => c.testBit t else 0

/-- **`MatTie` gives the frame's `CellsTie`**: nothing need be open; at every row and column; the
first number (which matrix) is not read. -/
theorem cellsTie_of_matTie (h : MatTie L weights pile P rd) :
    CellsTie L.thread b (fun _ => some ())
      (fun w _ r c => matN (k13Wit P.lin.matrixRows P.lin.kCol (k13Ask weights pile w)).mat r c)
      (fun _ s w v _ r c => matN (rd (L.pubOf w.x, s) v).mat r c) fun _ _ _ => True := by
  intro k s m En hT _ _ ds _ r c _
  show matN _ r c = matN (rd (L.pubOf m.st.input.x, s)
    (L.Q.wit k m.st.input (m.st.heard ++ ds))).mat r c
  rw [h k s m.st.input _ hT.2.2.2.2.2.2]

end ProofFile.Honest.K13

#print axioms ProofFile.Honest.K13.coinsTie_iff
#print axioms ProofFile.Honest.K13.k13_spentOf
#print axioms ProofFile.Honest.K13.coinsTie_iff_spent
#print axioms ProofFile.Honest.K13.coinsTie_of_book
#print axioms ProofFile.Honest.K13.cellsTie_of_matTie
