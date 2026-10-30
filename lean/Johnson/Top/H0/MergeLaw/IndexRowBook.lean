-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/MergeLaw/IndexRowBook.lean: the two readings of the index masks are one, said of the
reader of the pending rows. One theorem with its proof, and a corollary.

`index_readings`: the mask entries that `rwBook` (Johnson/Desc/K13/Law/ReaderByBook.lean) gives at
the message that the verifier's state names as the index masks' are, at every index, the merge's
reading off the witness at the member xI (`vecBy`, Pin.lean). It is `index_words` (IndexRow.lean)
with `rwBook` unfolded; the premises are that theorem's, and its head says what each asks.
`index_readings_at`: the same with the mask table's size and the bits that number its rows as
parameters ni and RI, each tied to the verifier's state by one equation.

Limits. IndexRow.lean's. Nothing on soundness.
-/
import Johnson.Top.H0.MergeLaw.IndexRow
import Johnson.Desc.K13.Law.ReaderByBook

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.First.MergeLaw
open OnBytes (OracleShape)
open OnBytes.Slice (GE)
open OnBytes.Means (tableSize)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.K12.Door (Laid msgShapesB bookInOrderB seatsCarriedB placesBelowB)

/-- **The reader of the pending rows and the merge's law read the index masks alike, at every
index.** -/
theorem index_readings {Pp Cells Tok : Type} {nR kk : ℕ} (cs : OnBytes.Codes) (arr : ℕ → ℕ → ℕ)
    (mat : Cells → Fin nR → (Fin kk → Bool) → GE) (N : Numbers) (M : List OracleShape) (L : Laid)
    (b : S) (xI : Mem) (k : ℕ)
    (h₁ : msgShapesB M b.st = true) (h₂ : bookInOrderB 0 b.book b.roots = true)
    (h₃ : seatsCarriedB L b.book = true) (hs : b.book.place.size = b.st.oracles.size)
    (hb : placesBelowB L b.book.place.size b.book.trees.size = true)
    (ht : b.out.indexMasks < b.st.oracles.size)
    (hseat : b.book.place[b.out.indexMasks]? = some N.index) (hcs : b.st.codes = cs)
    (hsh : M[b.out.indexMasks]? = some (xI.1.l.get xI.2).1) (hx : seatOf xI = N.index)
    (hp : (xI.1.l.get xI.2).1.maskRows = 2 ^ k) (z : Pp) (w : Wit Cells Tok MsgT) (c : ℕ) :
    (K13.Law.rwBook arr mat (z, b) w).mask ⟨b.out.indexMasks, c⟩ =
      vecBy cs arr (tableSize b.st b.out.indexMasks .mask)
        (posMask (b.st.rowBits b.out.indexMasks .mask)) xI w c :=
  index_words cs arr N M L b xI k h₁ h₂ h₃ hs hb ht hseat hcs hsh hx hp w c

/-- The same with the two numbers as parameters. ni: the size of the message's mask table; RI: the
bits that number its rows. -/
theorem index_readings_at {Pp Cells Tok : Type} {nR kk : ℕ} (cs : OnBytes.Codes) (arr : ℕ → ℕ → ℕ)
    (mat : Cells → Fin nR → (Fin kk → Bool) → GE) (N : Numbers) (M : List OracleShape) (L : Laid)
    (b : S) (xI : Mem) (k ni RI : ℕ)
    (h₁ : msgShapesB M b.st = true) (h₂ : bookInOrderB 0 b.book b.roots = true)
    (h₃ : seatsCarriedB L b.book = true) (hs : b.book.place.size = b.st.oracles.size)
    (hb : placesBelowB L b.book.place.size b.book.trees.size = true)
    (ht : b.out.indexMasks < b.st.oracles.size)
    (hseat : b.book.place[b.out.indexMasks]? = some N.index) (hcs : b.st.codes = cs)
    (hsh : M[b.out.indexMasks]? = some (xI.1.l.get xI.2).1) (hx : seatOf xI = N.index)
    (hp : (xI.1.l.get xI.2).1.maskRows = 2 ^ k)
    (hni : tableSize b.st b.out.indexMasks .mask = ni)
    (hR : b.st.rowBits b.out.indexMasks .mask = RI) :
    ∀ (z : Pp) (w : Wit Cells Tok MsgT) (c : ℕ),
      (K13.Law.rwBook arr mat (z, b) w).mask ⟨b.out.indexMasks, c⟩ =
        vecBy cs arr ni (posMask RI) xI w c := by
  intro z w c
  rw [← hni, ← hR]
  exact index_readings cs arr mat N M L b xI k h₁ h₂ h₃ hs hb ht hseat hcs hsh hx hp z w c

end VerifiableInference.Desc.First.MergeLaw

#print axioms VerifiableInference.Desc.First.MergeLaw.index_readings
#print axioms VerifiableInference.Desc.First.MergeLaw.index_readings_at
