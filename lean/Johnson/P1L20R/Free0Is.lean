-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1L20R/Free0Is.lean: two terms for "how many
entries the fresh ledger of the index-mask message has" are one number, where a public test accepts.

  K1.free0Of G.first gp       (Johnson/K12LotR/FirstSendingFresh.lean) the count at the shape of
                    the last message that the first segment's opening sends: the term in which the
                    fact on the free rows along the run is shown (RoomFold.lean, RoomMake.lean)
  FillP1.free0Of cs M ix       (Johnson/Top/H0/Fill/D1At.lean) the count at the shape number ix of a
                    list M of shapes: the term that the composed meaning's side reads
  free0_is          at an opening of the maker: where FillP1.startB Z M ix accepts ("the plan's
                    request announces just one message at the chain's start, and its shape is the
                    shape number ix of M"): the two are equal

Limits. startB's yes is a premise: a test with code on public data; it is shown at no M and ix here.
No soundness statement.

-/
import Johnson.P1L20R.RoomMake
import Johnson.Top.H0.Fill.D1At

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace P1L20

open VerifiableInference.Desc (Block Chain FileDescription)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K1 (gpOf)
open ProofFile (Cl)

/-- **The two counts are one number, where the public test accepts.** -/
theorem free0_is {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
    {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl} {A : ProofFile.SharedSeat}
    {B : ProofFile.SecondSeat} (O : IM.Open o pol lay KL F Z Bs base c A B)
    {M : List OnBytes.OracleShape} {ix : ℕ}
    (hB : VerifiableInference.Desc.First.FillP1.startB Z M ix = true) :
    VerifiableInference.Desc.K1.free0Of Bs.G₀.first (gpOf Z) =
      VerifiableInference.Desc.First.FillP1.free0Of Z.first.codes M ix := by
  rw [ProofFile.Law.blankBy_first O.blank]
  unfold VerifiableInference.Desc.First.FillP1.startB at hB
  cases hM : M[ix]? with
  | none =>
    rw [hM] at hB
    cases hB
  | some sh =>
    rw [hM] at hB
    have h1 : Z.first.shape.atStart.map (·.shape) = [sh] := eq_of_beq hB
    obtain ⟨n, hn, -, -⟩ := ProofFile.Law.pub_atStart O.pub
    rw [hn] at h1
    have h2 : n.shape = sh := by simpa using h1
    unfold VerifiableInference.Desc.K1.free0Of VerifiableInference.Desc.K1.shLast
      VerifiableInference.Desc.First.FillP1.free0Of
    rw [ProofFile.Law.sent_last Z.first (gpOf Z) n hn, hM, h2]

end P1L20

#print axioms P1L20.free0_is
