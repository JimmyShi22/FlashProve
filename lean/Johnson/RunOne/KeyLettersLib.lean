-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/KeyLettersLib.lean: THEOREMS. **The candidates of KeyLetters.lean are the library's own candidates** (OMsg.Cand: a member of the list of the word, with the answers at the seed), at the sample that the
statement's record holds; and a word that is an encoding has one.
  cand_lib      Tie → SeedIs cs s St o ρ y → (Cand cs s e f St o msg ↔ (portOmZ cs s e).Cand f (ρ, fun _ => y) msg)   (by cand_iff)
  cand_of_enc   where the word sent, read as a native word of the code, IS an encoding of msg (hf), and the record's answer is the sample map's value at msg: msg is a candidate. NO f, msg, r THAT MEET hf ARE EXHIBITED HERE: a word as sent holds, table by
                table, symbols of that table's own field (RowTy), so hf can hold only of a msg and an r whose encoding lies in these fields: as empty as hf until a member is shown
  dec_of_enc    so there, under Sealed, the decoder returns msg
What is not claimed. That hf can be met. That an honest prover's strings, as a frame holds them, read as such a word (f: a letter). Nothing on soundness.

-/
import Johnson.RunOne.KeyLetters

set_option autoImplicit false

namespace Johnson.RunOne.KeyLetters

open OnBytes OnBytes.Params OnBytes.Model Desc.Plain
open OnBytes.Slice Johnson.Pack Cb Cb.Ood Prob
open VerifiableInference.Desc VerifiableInference.Desc.K1

theorem cand_lib {cs : Codes} {s : OracleShape} {e : Nat} {f : (portOmZ cs s e).Str} {St : Statement} {o : Nat} (hT : Tie cs s) {ρ : (Fin (bitsZ cs s) → GE) × GEˣ} {y : GE}
    (hI : SeedIs cs s St o ρ y) (msg : (portCode cs s).J → GE) : Cand cs s e f St o msg ↔ (portOmZ cs s e).Cand f (ρ, fun _ => y) msg := by
  obtain ⟨hc, x, z, β, t, hx, hs, _, hr, hread, hy⟩ := hI
  subst hc hs hy
  have hm : sampleRow (Msg.of St.codes x.shape) o z β 0 t ∈ x.sampleRows.toList := by rw [hr]; simp
  constructor
  · rintro ⟨hl, w, hw, hsay⟩
    exact (cand_iff St o x hx hT e f z β t ρ hread w msg hw).2 ⟨hl, hsay x hx _ hm⟩
  · intro h
    have c := (cand_iff St o x hx hT e f z β t ρ hread (fun _ => tabOf St.codes x.shape msg) msg rfl).1 h
    refine ⟨c.1, fun _ => tabOf St.codes x.shape msg, rfl, fun x' hx' r hr' => ?_⟩
    have ex : x' = x := Option.some.inj (hx'.symm.trans hx)
    subst ex
    rw [hr] at hr'
    have er : r = sampleRow (Msg.of St.codes x'.shape) o z β 0 t := by simpa using hr'
    rw [er]
    exact c.2

theorem cand_of_enc {cs : Codes} {s : OracleShape} {e : Nat} {f : (portOmZ cs s e).Str} {St : Statement} {o : Nat} (hT : Tie cs s) {ρ : (Fin (bitsZ cs s) → GE) × GEˣ} {y : GE}
    (hI : SeedIs cs s St o ρ y) (msg : (portCode cs s).J → GE) (r : (portCode cs s).Q → GE) (hf : (portOmZ cs s e).upW f = (portCode cs s).enc msg r)
    (hy : (portZ cs s).val ρ msg = fun _ => y) : Cand cs s e f St o msg := by
  refine (cand_lib hT hI msg).2 ⟨⟨r, ?_⟩, hy⟩
  show (portCode cs s).Near e ((portOmZ cs s e).upW f) ((portCode cs s).enc msg r)
  rw [hf]
  unfold LdCode.Near
  simp [cnt]

theorem dec_of_enc {cs : Codes} {s : OracleShape} {e : Nat} {f : (portOmZ cs s e).Str} {St : Statement} {o : Nat} (hT : Tie cs s) (hS : Sealed cs s e f St o) {ρ : (Fin (bitsZ cs s) → GE) × GEˣ} {y : GE}
    (hI : SeedIs cs s St o ρ y) (msg : (portCode cs s).J → GE) (r : (portCode cs s).Q → GE) (hf : (portOmZ cs s e).upW f = (portCode cs s).enc msg r)
    (hy : (portZ cs s).val ρ msg = fun _ => y) : decAt cs s e f St o = some msg :=
  decAt_eq hT hS (cand_of_enc hT hI msg r hf hy)

end Johnson.RunOne.KeyLetters

#print axioms Johnson.RunOne.KeyLetters.cand_lib
#print axioms Johnson.RunOne.KeyLetters.cand_of_enc
#print axioms Johnson.RunOne.KeyLetters.dec_of_enc
