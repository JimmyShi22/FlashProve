-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Law/OmegaTie.lean: OMEGA's TWO READERS AGREE AT THE SHARED CHAIN's LAST STATE: THE
STATEMENT, AS A DEFINITION (OmegaTie), AND ITS PROOF (omegaTie): omega_at_last
(Johnson/Desc/K14/Law/LedgerLast.lean) at S := Q.par.S, with the state's number of o_omega turned
to the plan's (sharedX_twelve) and the state's codes to the plan's (codY_iff at border 12).
What is not claimed. That the three tests at border 12 are had anywhere; no member; nothing on
soundness.

-/
import Johnson.Desc.K14.Law.LedgerLast

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice Cb Johnson.Pack Desc.Plain
open OnBytes.Means (Words)
open VerifiableInference.Desc (Wit)
open VerifiableInference.Desc.K1 (shapesOf shapeAt)
open VerifiableInference.Desc.Sound
open Desc.K14.Law.Fence (sharedX sharedX_twelve)

/-- **(A3), THE STATEMENT.** Under omega_at_last's own premises at S := Q.par.S: (Dot)'s reader of
Omega off the state (omegaOf, at the words by the state's book: wordsSh, which is wordsShared by
rfl: wordsSh_is, Johnson/Desc/K14/Law/LedgerReaderAt.lean) is the ledger's fixed reader omWK
(at the plan's number, codes and layout), below matrixRows. -/
def OmegaTie {Cells Tok : Type} (arr : ℕ → ℕ → ℕ) (mem : ℕ → Option Mem) (Q : P14) : Prop :=
  ∀ (sentU : Array OracleNotice) (layU layO : TreeLay) (d : St)
    (_hO : 0 < (withOmega Q.S).size) (h0 : 0 < (shapesOf (parO Q)).length) (nO : ℕ)
    (_hnO : nO = sentU.size) (_hX : sharedX Q sentU layU layO 12 d = true)
    (_hY : codY Q 12 d = true) (_hZ : omY (shapeAt (parO Q) ⟨0, h0⟩) nO 12 d = true) (t₁ : ℕ)
    (w : Wit Cells Tok MsgT) (x : Mem) (_hm : mem nO = some x)
    (_hent : (x.1.l.get x.2).1 = shapeAt (parO Q) ⟨0, h0⟩)
    (_hten : x.1.seat x.2 =
      (t₁ + (Q.par.toGPar.firstTree + (layU.shapes.size + layO.tree.getD 0 0)),
        layO.part.getD 0 0))
    (_hin : ∀ y < Q.par.S.matrixRows, (linLayOmega d.st.codes Q.par.S).index y /
      2 ^ ceilLog2 (x.1.l.get x.2).1.mainRows < (pMain Q.codes (x.1.l.get x.2).1).ell),
    ∀ y < Q.par.S.matrixRows,
      omegaOf d.loc (linLayOmega d.st.codes Q.par.S) (wordsSh arr t₁ d.st d.book w) y =
        omWK Q.codes arr mem (rdK Q.codes) nO Q w y

/-- **(A3).** The two readers of Omega agree. -/
theorem omegaTie {Cells Tok : Type} (arr : ℕ → ℕ → ℕ) (mem : ℕ → Option Mem) (Q : P14) :
    OmegaTie (Cells := Cells) (Tok := Tok) arr mem Q := by
  intro sentU layU layO d hO h0 nO hnO hX hY hZ t₁ w x hm hent hten hin y hy
  have eO : d.loc.oOmega = nO := by
    rw [hnO]
    exact (sharedX_twelve Q sentU layU layO d hO hX).2.1
  have eC : d.st.codes = Q.codes := ((codY_iff Q 12 d).1 hY).resolve_left (by omega)
  have h := omega_at_last arr mem Q sentU layU layO d hO h0 nO hnO hX hY hZ t₁ Q.par.S w x hm hent
    hten hin y hy
  unfold omegaOf omWK
  rw [h, eO, eC]

end Desc.K14.Law
