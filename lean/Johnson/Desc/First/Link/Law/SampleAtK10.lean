-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/SampleAtK10.lean: K10On's CLAUSE "tied", WHAT CAN BE SAID OF ONE MEMBER,
FREE OF THE NUMBERING num AND OF pS: where the statement's sample rows of a message are kind K1's
one row at a seed (K1.SeedIs) and K1.Tie holds of its shape: THE SAMPLE THAT faK10
LAYS (smpNamed) HAS, AS ITS ANSWER, THAT ROW's TARGET; ITS SEED HAS THE SEED's SAMPLE MAP;
AND THE ROW NAMES THAT MESSAGE ALONE (NamesOne, Johnson/Desc/First/Close/Law/SampleTie.lean).
Theorems with their proofs.

  namesOne_sampleRow kind K1's sample row of message o has no coefficient on another message (by
                     K1's coefAt_sampleRow)
  sample_member      SeedIs · Tie · the seat is one of the plan's ⊢ there are the message x, its
                     one sample row r and the laid sample z: smpNamed … = some z · x.sampleRows =
                     #[r] · z.2 = fun _ => readE r.target · z's seed has ρ's sample map · NamesOne r
                     o

Limits. OF RowsTied's SECOND HALF (Johnson/Desc/First/Close/Law/AtPieceAll.lean) THIS GIVES, AT A
MEMBER, THE FIRST CLAUSE's CONTENT AND NamesOne. NOT TREATED: that rows[num (.inr as)] IS that row
(num is a letter) · pS · SampleFits (its two debts BlockAt and Middle are shown of nothing). SeedIs
and Tie at a reached state are premises. No soundness statement.

-/
import Johnson.Desc.Sound.SmpNamed
import Johnson.Desc.K1.Law.Means
import Johnson.Desc.K1.Law.SeedIs
import Johnson.Desc.First.Close.Law.SampleTie

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Slice OnBytes.Maker Johnson.Pack Cb
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Close (NamesOne)

/-- Kind K1's sample row names its message alone. -/
theorem namesOne_sampleRow (m : K1.Msg) (o : ℕ) (z : List E) (β : E) (i : ℕ) (y : E) :
    NamesOne (K1.sampleRow m o z β i y) o := by
  intro o' hne part e
  have h := K1.coefAt_sampleRow m o z β i y o' part e
  have hb : (o == o') = false := by simpa using fun e' : o = o' => hne e'.symm
  simp only [hb, Bool.false_and, Bool.false_eq_true, if_false, List.map_const', List.sum_replicate,
    smul_zero, add_zero] at h
  exact h

/-- **One member's sample, against its sample row.** -/
theorem sample_member {P : Type} (cs : OnBytes.Codes) (seats : List (ℕ × ℕ)) (a : P × S)
    (s : Sending) (i : Fin s.l.length) (hq : s.seat i ∈ seats)
    (ρ : (Fin (bitsZ cs (s.l.get i).1) → GE) × GEˣ) (y : GE) (hT : K1.Tie cs (s.l.get i).1)
    (h : K1.SeedIs cs (s.l.get i).1 a.2.st (numAt seats ⟨s, i⟩) ρ y) :
    ∃ (x : OnBytes.Oracle) (r : OnBytes.Row) (z : ((sigOf cs s.l).om i).Smp),
      a.2.st.oracles[numAt seats ⟨s, i⟩]? = some x ∧ x.sampleRows = #[r] ∧
      smpNamed cs seats a s i = some z ∧ z.2 = (fun _ => readE r.target) ∧
      ((sigOf cs s.l).om i).Z.val z.1 = ((sigOf cs s.l).om i).Z.val ρ ∧
      NamesOne r (numAt seats ⟨s, i⟩) := by
  obtain ⟨z, h1, h2, h3⟩ := smpNamed_of cs seats a s i hq ρ y hT h
  obtain ⟨-, x, zz, β, t, hx, -, -, hr, -, ht⟩ := h
  refine ⟨x, _, z, hx, hr, h1, ?_, h3, namesOne_sampleRow _ _ _ _ _ _⟩
  rw [h2]
  funext _
  rw [← ht]
  rfl

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.namesOne_sampleRow
#print axioms VerifiableInference.Desc.LinkJoin.sample_member
