-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/BodyEnd.lean: WHERE bodyAll (Johnson/Prover/Link/BodyAll.lean) STANDS AT THE
LAST STAGE. bodyAll hands out rounds, trees and groups, not the letters at which its recursion ends.
Here these letters are a structure, made by bodyAll's own recursion, argument by argument; and what
bodyAll hands out ends in lastOut at them. Definitions, statements and proofs.

  BEnd          the seven letters of a stage: its number · the stage · the declared rounds still to
                be dealt · the number of the next round · the verifier's state · the prover's state
                · the written column of the tree that holds the state's rows
  bodyEnd       these letters at the last stage
  BEnd.out      lastOut at them
  bodyAll_end   bodyAll's rounds, trees and groups are some lists, one group a stage, and then those
                of lastOut at bodyEnd
  bodyAll_last  so: bodyAll's last two rounds, last two trees and last group are lastOut's

Not shown here. Anything on the values in these letters. Nothing on a decision, on soundness or
on what any value that is sent discloses or does not disclose.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Prover.Link.BodyAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Johnson.Prover.Link
open OnBytes OnBytes.Params OnBytes.Slice Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.Pub (sgOf)

/-- The letters at which bodyAll stands in front of a stage. -/
structure BEnd where
  j : ℕ
  cur : Fmt.M1.Stage
  l : Laid
  o : ℕ
  t : T12
  P : PS
  col : ℕ → List UInt64

/-- **The letters at the last stage**, by bodyAll's own recursion. -/
def bodyEnd (p : P12) (K : BCoins) (D : ℕ → Fmt.Drawn) : List Fmt.M1.Stage → ℕ → Fmt.M1.Stage →
    Laid → ℕ → T12 → PS → (ℕ → List UInt64) → BEnd
  | [], j, cur, l, o, t, P, col => ⟨j, cur, l, o, t, P, col⟩
  | next :: rest, j, cur, l, o, t, P, col =>
    bodyEnd p K D rest (j + 1) next (l.drop (cur.k + 3)) (o + ((sgOf cur).h + (sgOf cur).g) + 3)
      (sT3 p K rest.isEmpty j cur next l o t P col (rowOf t) D)
      (sNext K rest.isEmpty j cur next o P (rowOf t) D)
      (sCol K rest.isEmpty j cur next o P (rowOf t) D)

/-- What the last stage shows, writes and is dealt, at these letters. -/
def BEnd.out (p : P12) (D : ℕ → Fmt.Drawn) (e : BEnd) : BOut :=
  lastOut p e.j e.cur e.o e.t e.P e.col (rowOf e.t) D

theorem bodyAll_end (p : P12) (K : BCoins) (D : ℕ → Fmt.Drawn) :
    ∀ (rest : List Fmt.M1.Stage) (j : ℕ) (cur : Fmt.M1.Stage) (l : Laid) (o : ℕ) (t : T12) (P : PS)
      (col : ℕ → List UInt64), ∃ F : BOut,
      (bodyAll p K rest j cur l o t P col D).rs =
        F.rs ++ ((bodyEnd p K D rest j cur l o t P col).out p D).rs ∧
      (bodyAll p K rest j cur l o t P col D).tr =
        F.tr ++ ((bodyEnd p K D rest j cur l o t P col).out p D).tr ∧
      (bodyAll p K rest j cur l o t P col D).gs =
        F.gs ++ ((bodyEnd p K D rest j cur l o t P col).out p D).gs ∧
      F.gs.length = rest.length
  | [], _, _, _, _, _, _, _ => ⟨⟨[], [], []⟩, rfl, rfl, rfl, rfl⟩
  | next :: rest, j, cur, l, o, t, P, col => by
    obtain ⟨F, h1, h2, h3, h4⟩ := bodyAll_end p K D rest (j + 1) next (l.drop (cur.k + 3))
      (o + ((sgOf cur).h + (sgOf cur).g) + 3)
      (sT3 p K rest.isEmpty j cur next l o t P col (rowOf t) D)
      (sNext K rest.isEmpty j cur next o P (rowOf t) D)
      (sCol K rest.isEmpty j cur next o P (rowOf t) D)
    refine ⟨⟨sRF K j cur o P (rowOf t) D ++ sRS p K j cur next l o t P (rowOf t) D ++ F.rs,
      (sRF K j cur o P (rowOf t) D).map (fun _ _ => []) ++
        [sCol K rest.isEmpty j cur next o P (rowOf t) D, fun _ => []] ++ F.tr,
      sGS cur o col D ++ F.gs⟩, ?_, ?_, ?_, ?_⟩
    · show _ ++ _ ++ (bodyAll p K rest _ _ _ _ _ _ _ D).rs = _
      rw [h1, ← List.append_assoc]
      rfl
    · show _ ++ _ ++ (bodyAll p K rest _ _ _ _ _ _ _ D).tr = _
      rw [h2, ← List.append_assoc]
      rfl
    · show _ ++ (bodyAll p K rest _ _ _ _ _ _ _ D).gs = _
      rw [h3, ← List.append_assoc]
      rfl
    · show (sGS cur o col D ++ F.gs).length = rest.length + 1
      rw [List.length_append, h4, Nat.add_comm]
      rfl

/-- **bodyAll's last two rounds, last two trees and last group are lastOut's at bodyEnd.** -/
theorem bodyAll_last (p : P12) (K : BCoins) (D : ℕ → Fmt.Drawn) (rest : List Fmt.M1.Stage) (j : ℕ)
    (cur : Fmt.M1.Stage) (l : Laid) (o : ℕ) (t : T12) (P : PS) (col : ℕ → List UInt64) :
    (bodyAll p K rest j cur l o t P col D).rs.drop
        ((bodyAll p K rest j cur l o t P col D).rs.length - 2) =
        ((bodyEnd p K D rest j cur l o t P col).out p D).rs ∧
      (bodyAll p K rest j cur l o t P col D).tr.drop
        ((bodyAll p K rest j cur l o t P col D).tr.length - 2) =
        ((bodyEnd p K D rest j cur l o t P col).out p D).tr ∧
      (bodyAll p K rest j cur l o t P col D).gs.drop rest.length =
        ((bodyEnd p K D rest j cur l o t P col).out p D).gs := by
  obtain ⟨F, h1, h2, h3, h4⟩ := bodyAll_end p K D rest j cur l o t P col
  refine ⟨?_, ?_, ?_⟩
  · rw [h1]
    refine List.drop_left' ?_
    rw [List.length_append]
    show F.rs.length = F.rs.length + 2 - 2
    omega
  · rw [h2]
    refine List.drop_left' ?_
    rw [List.length_append]
    show F.tr.length = F.tr.length + 2 - 2
    omega
  · rw [h3]
    exact List.drop_left' h4

end Johnson.Prover.Link

#print axioms Johnson.Prover.Link.bodyAll_end
#print axioms Johnson.Prover.Link.bodyAll_last
