-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/FrontClaim.lean: THE CLAIM BEHIND THE LINK's BATCHING HOLDS AT THE FOLDS. One
theorem: the library's head_claimR (OnBytes/Slice/BlkHeadRec.lean: the row that the batching
returns, read in the field, IS the sum of the link's rows under the powers of the drawn element, at
the typed statement after the five written rounds) joined with holds_of_src
(Johnson/Prover/Link/FrontSrc.lean).

  front_claim   head_claimR's own premises, to the letter · a row of the group's code has 2 ^ aP
                places · Src at that typed statement ⟹ (Slf.idf).Holds (stmG (S.sg t₀) row) μ

Not shown here. That a run meets head_claimR's premises (LinkRanR, BatRan: they come from a yes
of the link's blocks and of the batching: Johnson/Desc/K15/K15Law.lean, K12/Law/BatOk.lean). That
any written message meets Src. Nothing on soundness; nothing on what any entry of a message
discloses or does not disclose.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Link.FrontSrc
import OnBytes.Slice.BlkHeadRec

set_option autoImplicit false

namespace Johnson.Prover.Link
open OnBytes OnBytes.Slice Cb Cb.Ood Iop _root_.Run
open OnBytes.Params (LinkShape)

/-- **The claim behind the batching holds at the folds.** -/
theorem front_claim (S : Sz) (t₀ lg n : ℕ) (Λ : LinkShape) (first further : TableKey)
    (d1 d2 d3 d4 d5 dA : PQ.RD)
    (m1 : (wRound d1).Msg) (c1 : (wRound d1).Chal) (m2 : (wRound d2).Msg)
    (c2 : (wRound d2).Chal) (m3 : (wRound d3).Msg) (c3 : (wRound d3).Chal)
    (m4 : (wRound d4).Msg) (c4 : (wRound d4).Chal) (m5 : (wRound d5).Msg) (c5 : (wRound d5).Chal)
    (c c' cd : Ctx) (x : LinkRun) (D : LinkDataR) (G0 : Group) (L : GroupLayout)
    (θ : E) (row : GroupRow) (hS : LinkSizes S Λ c.st.codes)
    (hF : LinkFit S Λ (Λ.side false 1) (Λ.side true 1)) (hd : BatDraws S d1 d2 d3 d4 d5 dA)
    (hn0 : (Λ.side false 1).columns = Λ.columnsFirst)
    (hn1 : (Λ.side true 1).columns = Λ.columnsFurther)
    (hi0 : first.item = 0) (hi1 : further.item = 1) (hpads : 3 * n ≤ S.P.T.l)
    (r : (S.lkR (recZ S.P.T.l lg n)).X0)
    (hK0 : first.fits Λ.table = true → (first.seeds.all fun x => !isZeroE x.beta) = true →
      KeyHasR S.P.v lg n (Λ.side false 1).index first r.1)
    (hK1 : further.fits Λ.table = true → (further.seeds.all fun x => !isZeroE x.beta) = true →
      KeyHasR S.P.v lg n (Λ.side true 1).index further r.2)
    (y : (S.lkR (recZ S.P.T.l lg n)).E0.Str)
    (hR : LinkRanR Λ first further c c' x D) (hB : BatRan x.group c' cd G0 L θ row)
    (a1 : D.r1 = rvW d1 m1 c1) (a2 : D.r2 = rvW d2 m2 c2) (a3 : D.r3 = rvW d3 m3 c3)
    (a4 : D.r4 = rvW d4 m4 c4) (a5 : D.r5 = rvW d5 m5 c5)
    (hop : ∀ o ∈ c.ch.opened,
      (o.1 = Fmt.storedKey 0 → storedOf S.P.T.a y 0 o.2.1 = some o.2.2) ∧
      (o.1 = Fmt.storedKey 1 → storedOf S.P.T.a y 1 o.2.1 = some o.2.2))
    (hmask : ∀ i, i < S.P.Z.l → readV row.d i = 0)
    (hl2 : S.P.C.l = 2 ^ S.P.aP) (μ : (S.sg t₀).cIn.J → GE)
    (M₀ M₁ : (S.ixR (recZ S.P.T.l lg n)).Row → S.Co → GE)
    (hsrc : Src t₀ (st4R S (recZ S.P.T.l lg n) r d1 d2 d3 d4 d5 y c1 m2 c2 m3 c4 c5).1 μ M₀ M₁) :
    (Slf.idf (E := GE) (J := (S.sg t₀).cIn.J)).Holds (stmG (S.sg t₀) row) μ := by
  rw [head_claimR S t₀ lg n Λ first further d1 d2 d3 d4 d5 dA m1 c1 m2 c2 m3 c3 m4 c4 m5 c5
    c c' cd x D G0 L θ row hS hF hd hn0 hn1 hi0 hi1 hpads r hK0 hK1 y hR hB a1 a2 a3 a4 a5 hop
    hmask]
  exact holds_of_src _ t₀ _ _ _
    (isRowsR_rowsXR S (recZ S.P.T.l lg n) n (Equiv.refl (Fin n)) t₀ hl2 _)
    (covers_port n _ (Equiv.refl (Fin n)).surjective) μ M₀ M₁ hsrc (readE θ)

end Johnson.Prover.Link

#print axioms Johnson.Prover.Link.front_claim
