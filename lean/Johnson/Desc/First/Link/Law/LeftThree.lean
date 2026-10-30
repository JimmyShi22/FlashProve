-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/LeftThree.lean: THE THREE FIELDS OF `DigitsLeft`
(RestStatic.lean beside this file) THAT TIE THE EXCHANGE's READING OF THE WITNESS TO THE BATCHING's
BOUND DATA (cellsB, cellsZ, masks), AT THE DATA TO WHICH THE LAW OF A LINK BINDS y: A JOINING:
CALLED, NOT TYPED: `rest_pays_of` (Johnson/Top/H/Keep/DigitsRestPays.lean).
Theorems. A law file; no running text imports it.
  `bound_is`        boundAt atS (fun a w => tabAt own (rdW w) a.1) ctx a w y · atS.get? a.1 = some
                    pa ⊢ y = dataQ own pa (rdW w) (by data_at,
                    Johnson/Desc/First/Batch/Law/AtTable.lean).
  `LeftAsks`        what rest_pays_of asks, as one structure with a name for each: at the part pa in
                    front of the batching, the reader rd, the witness w, a link's context L and the
                    run's list of claims c.
  `left_three`      boundAt … y · a part pa is there · LeftAsks ⊢ the three fields, in
                    DigitsLeft's own text.
  `digitsLeft_of`   so DigitsLeft, from its other three fields (shape, five, points) and these.

Limits. AN IMPLICATION. LeftAsks IS SHOWN OF NO STATE HERE. Its field cells can hold only where the
oracle messages that hold the counts' and the digits' arrays are sent (DigitsRestPays.lean's limit):
meant at the batching's front. Where no part is there, y is all zeros and nothing is said. Nothing
on soundness or on hiding.
-/
import Johnson.Desc.First.Link.Law.RestStatic
import Johnson.Top.H.Keep.DigitsRestPays
import Johnson.Desc.First.Batch.Law.AtTable

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model OnBytes.DgP
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc.K9 (atS)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Look
open VerifiableInference.Desc.First.K8.Four (unknownOf)
open VerifiableInference.Desc.First.Att.P (OneReader ReadMsgOf)

section
variable {Cells Tok : Type} {F : Sound.Frame}

/-- The data to which the law of a link binds y are the table of joints' data at the part. -/
theorem bound_is (own : List (ℕ × ℕ)) (rdW : Desc.Wit Cells Tok MsgT → ℕ × ℕ → MsgQ)
    (ctx : S × F.E.Str → Desc.Wit Cells Tok MsgT → Prop) {a : S × F.E.Str}
    {w : Desc.Wit Cells Tok MsgT} {y : Bound Cb.Gl.E} {pa : K9.Part}
    (hb : boundAt atS (fun a w => tabAt own (rdW w) a.1) ctx a w y)
    (hpa : atS.get? a.1 = some pa) : y = dataQ own pa (rdW w) := by
  rw [hb.2]
  exact data_at own (rdW w) a.1 pa hpa

/-- **What `rest_pays_of` asks.** Each field in its own text. -/
structure LeftAsks (x : First.Look.Place) (tlD : HTailF2) (D : First.Look.Sent)
    (rad : OracleShape → ℕ) (seatT : Fin (digList x D rad).length → ℕ × ℕ) (arr : ℕ → ℕ → ℕ)
    (own : List (ℕ × ℕ)) (rd : ℕ × ℕ → MsgQ) (w : Desc.Wit Cells Tok MsgT) (pa : K9.Part)
    (L : LinkCtx) (c : List Claim) : Prop where
  dig : ∃ set pp, DigOK set x tlD D rad pp
  oneCells : OneReader (ReadMsgOf (cellAddr tlD) (seatOf D x.link)) D.codes (digList x D rad)
    seatT (msgsOf D.codes (digList x D rad) seatT arr w) rd
  oneMask : OneReader (ReadMsgOf (maskAddr x.arrays.ns) (seatOf D x.link)) D.codes
    (digList x D rad) seatT (msgsOf D.codes (digList x D rad) seatT arr w) rd
  cells : CellOkR x tlD D rad seatT own pa
  mask : MaskOkR x D rad seatT own pa
  maskPub : maskB D (digList x D rad) x.link x.arrays.ns = true
  arrays : L.arrayOf = pa.L.arrayOf
  first : ∀ q < 2, ∀ p ∈ piecesL tlD q, p.c0 = q * tlD.mz
  slots : ∀ k ∈ c.take 4, ∀ s ∈ k.form.slots.toList, s.1 < pa.F.ns

/-- **The three fields, at the data to which the law binds y.** -/
theorem left_three (x : First.Look.Place) (tlD : HTailF2) (D : First.Look.Sent)
    (rad : OracleShape → ℕ) (seatT : Fin (digList x D rad).length → ℕ × ℕ) (arr : ℕ → ℕ → ℕ)
    (own : List (ℕ × ℕ)) (rdW : Desc.Wit Cells Tok MsgT → ℕ × ℕ → MsgQ)
    (ctx : S × F.E.Str → Desc.Wit Cells Tok MsgT → Prop) {a : S × F.E.Str}
    {w : Desc.Wit Cells Tok MsgT} {y : Bound Cb.Gl.E} {pa : K9.Part}
    (hb : boundAt atS (fun a w => tabAt own (rdW w) a.1) ctx a w y)
    (hpa : atS.get? a.1 = some pa) {L : LinkCtx} {c : List Claim}
    (A : LeftAsks x tlD D rad seatT arr own (rdW w) w pa L c) :
    (∀ r < 32, ∀ i < tlD.bzColumns,
      digVal x D rad (msgsOf D.codes (digList x D rad) seatT arr w) (.cell tlD.ix.BZ r i) =
        some (unknownOf L y (Sum.inl (tlD.ix.BZ, r, i)))) ∧
    (∀ q < 2, ∀ p ∈ piecesL tlD q, ∀ r < p.Rp, ∀ i < p.Cp,
      digVal x D rad (msgsOf D.codes (digList x D rad) seatT arr w)
          (.cell tlD.ix.ZZ (p.r0 + r) (p.c0 + i)) =
        some (unknownOf L y (Sum.inl (tlD.ix.ZZ, p.r0 + r, p.c0 + i)))) ∧
    ∀ k ∈ c.take 4, ∀ s ∈ k.form.slots.toList,
      y.mask s.1 = digMu x D rad seatT arr w (mkOf x.arrays s.1) := by
  obtain ⟨set, pp, HD⟩ := A.dig
  rw [bound_is own rdW ctx hb hpa]
  exact rest_pays_of seatT arr own HD (rdW w) w A.oneCells A.oneMask pa A.cells A.mask A.maskPub L
    A.arrays A.first c A.slots

/-- So `DigitsLeft`, from its other three fields and these. -/
theorem digitsLeft_of (x : First.Look.Place) (tlD : HTailF2) (D : First.Look.Sent)
    (rad : OracleShape → ℕ) (seatT : Fin (digList x D rad).length → ℕ × ℕ) (arr : ℕ → ℕ → ℕ)
    (own : List (ℕ × ℕ)) (rdW : Desc.Wit Cells Tok MsgT → ℕ × ℕ → MsgQ)
    (ctx : S × F.E.Str → Desc.Wit Cells Tok MsgT → Prop) {a : S × F.E.Str}
    {w : Desc.Wit Cells Tok MsgT} {y : Bound Cb.Gl.E} {pa : K9.Part}
    (hb : boundAt atS (fun a w => tabAt own (rdW w) a.1) ctx a w y)
    (hpa : atS.get? a.1 = some pa) {L : LinkCtx} {c : List Claim}
    (A : LeftAsks x tlD D rad seatT arr own (rdW w) w pa L c) {g : Forest.Heard} {tl : HTailF2}
    (h1 : tl.f9 = g.shape) (h2 : 5 ≤ g.shape.kT + g.shape.cK)
    (h3 : ∀ q < 2, (g.zk.getD q #[]).size = (tl.zOf q).call.n) :
    DigitsLeft x tlD D rad seatT arr w g tl c L y :=
  let T := left_three x tlD D rad seatT arr own rdW ctx hb hpa A
  ⟨h1, h2, h3, T.1, T.2.1, T.2.2⟩

end

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.bound_is
#print axioms VerifiableInference.Desc.LinkJoin.left_three
#print axioms VerifiableInference.Desc.LinkJoin.digitsLeft_of
