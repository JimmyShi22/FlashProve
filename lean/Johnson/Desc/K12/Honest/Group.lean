-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K12/Honest/Group.lean: the word of a group whose members' words are code words is a
code word on the stage's tables. A proximity test's first stage (`Sg`, OnBytes/Slice/Stage.lean)
reads oracle messages that were sent earlier, each under a tree of its own. A group (`Gp`,
OnBytes/Slice/KeyGroup.lean) is a finite family of such messages, its members (`G.mb i`, a format
`Mb`). Each member has a seat (`G.seat i`, a `Site`), which gives every row of the member a place
among the rows of the stage's tables (`s.cIn`: main rows next to mask rows, the two kinds of rows).
That file makes, of the members' sent words, one word on the stage's tables (`Gp.word`). Here: if
each member's word is the code word of a message with tails, the group's word is the stage's code
word of the messages and tails, put at the places that the members' seats give. A code word is
`enc m r` of a code (`LdCode`, Cb/Ld/LdRel.lean): m is the message, r the tails. General: at every
stage s, every group G at s, all messages m and all tails r. Definitions, statements and proofs.
`word_enc` is called in Johnson/Desc/K12/Honest/GroupReads.lean; `layJ_ent`, `layQ_ent`,
`layJ_freeM` and `layJ_freeZ` in Johnson/Desc/K12/Honest/FirstState.lean. Nothing of the frame
(Johnson/Desc/ProofFile/Honest/Frame.lean: the types in which an honest prover is written) is used:
it is not imported.

  `word_enc`: `G.word (fun i => (G.mb i).cd.enc (m i) (r i)) = s.cIn.enc (layJ G m) (layQ G r)`,
    at every G, m and r. No hypothesis
  `layJ G m`, `layQ G r`: definitions: the members' messages, and their tails, on the stage's
    tables: an entry of the stage's row b is the sum, over the members' rows whose place is b, of
    these rows' entry of the same number; it is 0 where no row has the place b
  `Tails G`: a definition: the type of the members' tails: for each member i a function on the
    coordinates `Q` of its code `(G.mb i).cd`
  `layJ_ent`, `layQ_ent`: where no two rows of the group have the same place (`Gp.Apart`):
    `layJ G m` at `G.ent n` is `m n.1 n.2`, and `layQ G r` at `(G.seat i).atQ q` is `r i q`: a
    member's entry is at the place that the seat gives that entry
  `layJ_freeM`, `layJ_freeZ`: on a row of the stage's tables that is the place of no member's row,
    `layJ G m` is 0: one theorem for each of the two kinds of rows
  `row_main`, `row_mask`: for two equal codes (in `word_enc`: a member's and the stage's): a
    member's row under its own code, read at the member's own position, is the row under the
    stage's code at the stage's position
  `sum_rows`: a lemma on finite sums: the form in which `word_enc` uses that a row's symbol is
    linear in (message, tail)

By what. `word_enc` unfolds `Gp.word` (OnBytes/Slice/KeyGroup.lean), `Sg.cIn`
(OnBytes/Slice/Stage.lean), and `ldOf` and `ldRep` (OnBytes/Slice/LinkAt.lean). It rewrites each
member's row by `row_main` or `row_mask` and exchanges the sums by `sum_rows`. Of a seat it uses
the fields `hC` and `hZ` (a member's code, for a kind of row that the member has, is the stage's)
and `hz` (the member's code Z is not longer than the member's tree). `row_mask` calls
`Nat.mod_mod_of_dvd`. `layJ_ent` and `layQ_ent` call `Finset.sum_eq_single` with the two fields of
`Gp.Apart`; `layJ_freeM` and `layJ_freeZ` call `Finset.sum_eq_zero`.

Limits. `word_enc` holds at every group, also at one in which two rows have the same place: there
both sides have the rows' sum. At a group without a member both sides are 0. That `layQ G r` is 0 on
a row that is the place of no member's row is not stated here. Nothing on which columns a verifier
is handed, on trees or on hashes. Nothing on a decision, on completeness, on soundness or on what is
hidden.
-/
import OnBytes.Slice.KeyGroup

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12
open OnBytes.Slice Cb

section Lay
variable {s : Sg} (G : Gp s)

/-- The type of the members' tails: for each member i a function on the coordinates `Q` of its
code. -/
abbrev Tails : Type := ∀ i, (G.mb i).cd.Q → GE

/-- The members' messages on the stage's tables. Entry j of the stage's row b is the sum, over the
members' rows whose place is b, of entry j of these rows' messages; 0 where no row has the place b.
The two cases are the two kinds of rows. -/
def layJ (m : G.Msgs) : s.cIn.J → GE
  | .inl x => ∑ n : G.RM, if (G.seat n.1).pM n.2 = x.1 then
      m n.1 (.inl (n.2, Fin.cast (congrArg Fmt.M1.Code.l ((G.seat n.1).hC n.2).symm) x.2)) else 0
  | .inr x => ∑ n : G.RZ, if (G.seat n.1).pZ n.2 = x.1 then
      m n.1 (.inr (n.2, Fin.cast (congrArg Fmt.M1.Code.l ((G.seat n.1).hZ n.2).symm) x.2)) else 0

/-- The members' tails on the stage's tables, by the same rule as `layJ`. -/
def layQ (r : Tails G) : s.cIn.Q → GE
  | .inl x => ∑ n : G.RM, if (G.seat n.1).pM n.2 = x.1 then
      r n.1 (.inl (n.2, Fin.cast (congrArg Fmt.M1.Code.r ((G.seat n.1).hC n.2).symm) x.2)) else 0
  | .inr x => ∑ n : G.RZ, if (G.seat n.1).pZ n.2 = x.1 then
      r n.1 (.inr (n.2, Fin.cast (congrArg Fmt.M1.Code.r ((G.seat n.1).hZ n.2).symm) x.2)) else 0

end Lay

/-- A lemma on finite sums. Take the weighted sum, with weights u and v, of two vectors: the sum of
the g n, and the sum of the f n, over those n that satisfy c. It is the sum, over those n, of the
weighted sums of g n and f n. In `word_enc`: g n is a row's tail and f n its message. -/
theorem sum_rows {ι : Type} [Fintype ι] (c : ι → Prop) [DecidablePred c] {a b : ℕ}
    (u : Fin a → GE) (v : Fin b → GE) (g : ι → Fin a → GE) (f : ι → Fin b → GE) :
    ((∑ q, u q * ∑ n, if c n then g n q else 0) + ∑ j, v j * ∑ n, if c n then f n j else 0) =
      ∑ n, if c n then (∑ q, u q * g n q) + ∑ j, v j * f n j else 0 := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm, Finset.sum_comm (s := Finset.univ (α := Fin b)), ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  by_cases h : c n
  · simp [h]
  · simp [h]

/-- A main row under a code that is the stage's, at the stage's position. If C = C', the symbol of
the code word of (m, r) under `ldOf C a`, at the position x carried along the equation, is the
symbol at x of the code word under `ldOf C' a'` of m and r carried along the equation. a and a' are
free parameters: `enc` of `ldOf` does not read them. -/
theorem row_main {C C' : Fmt.M1.Code} (h : C = C') (a a' : ℕ) (x : Fin (2 ^ C'.a))
    (m : Fin C.l → GE) (r : Fin C.r → GE) :
    (ldOf C a).enc m r (Fin.cast (congrArg (fun C : Fmt.M1.Code => 2 ^ C.a) h.symm) x) () =
      (ldOf C' a').enc (fun j => m (Fin.cast (congrArg Fmt.M1.Code.l h.symm) j))
        (fun q => r (Fin.cast (congrArg Fmt.M1.Code.r h.symm) q)) x () := by
  subst h
  rfl

/-- A mask row under a code that is the stage's, read at the position modulo the length of the
member's tree. If Z = Z' and Z.a ≤ a, the symbol of the code word of (m, r) under `ldRep Z a`, at
the position x modulo 2 ^ a, is the symbol at x of the code word under `ldRep Z' a'` of m and r
carried along the equation. -/
theorem row_mask {Z Z' : Fmt.M1.Code} (h : Z = Z') (a a' : ℕ) (hz : Z.a ≤ a) (x : Fin (2 ^ a'))
    (m : Fin Z.l → GE) (r : Fin Z.r → GE) :
    (ldRep Z a).enc m r ⟨x.val % 2 ^ a, Nat.mod_lt _ (Nat.two_pow_pos _)⟩ () =
      (ldRep Z' a').enc (fun j => m (Fin.cast (congrArg Fmt.M1.Code.l h.symm) j))
        (fun q => r (Fin.cast (congrArg Fmt.M1.Code.r h.symm) q)) x () := by
  subst h
  have hp : posIn Z (⟨x.val % 2 ^ a, Nat.mod_lt _ (Nat.two_pow_pos _)⟩ : Fin (2 ^ a)) =
      posIn Z x := Fin.ext (Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 hz))
  show (∑ q, genOf Z (posIn Z _) _ * r q) + ∑ j, genOf Z (posIn Z _) _ * m j = _
  rw [hp]
  rfl

section Laws
variable {s : Sg} (G : Gp s)

/-- **The word of a group whose members' words are code words is a code word of the stage:** that
of the message `layJ G m` with the tails `layQ G r`. No hypothesis on the group. -/
theorem word_enc (m : G.Msgs) (r : Tails G) :
    G.word (fun i => (G.mb i).cd.enc (m i) (r i)) = s.cIn.enc (layJ G m) (layQ G r) := by
  funext p
  rcases p with x | x
  · funext b
    obtain ⟨b, ⟨⟩⟩ := b
    show (∑ n : G.RM, if (G.seat n.1).pM n.2 = b then
        (ldOf (G.mb n.1).C (G.mb n.1).a).enc (fun j => m n.1 (.inl (n.2, j)))
          (fun q => r n.1 (.inl (n.2, q)))
          (Fin.cast (congrArg (fun C : Fmt.M1.Code => 2 ^ C.a) ((G.seat n.1).hC n.2).symm) x) ()
        else 0) =
      (∑ q, genOf s.C x (Fin.castAdd s.C.l q) * layQ G r (.inl (b, q))) +
        ∑ j, genOf s.C x (Fin.natAdd s.C.r j) * layJ G m (.inl (b, j))
    refine Eq.trans (Finset.sum_congr rfl fun n _ => ?_)
      (sum_rows (fun n : G.RM => (G.seat n.1).pM n.2 = b) _ _
        (fun n q => r n.1 (.inl (n.2,
          Fin.cast (congrArg Fmt.M1.Code.r ((G.seat n.1).hC n.2).symm) q)))
        (fun n j => m n.1 (.inl (n.2,
          Fin.cast (congrArg Fmt.M1.Code.l ((G.seat n.1).hC n.2).symm) j)))).symm
    rw [row_main ((G.seat n.1).hC n.2) (G.mb n.1).a s.C.a x]
  · funext b
    obtain ⟨b, ⟨⟩⟩ := b
    show (∑ n : G.RZ, if (G.seat n.1).pZ n.2 = b then
        (ldRep (G.mb n.1).Z (G.mb n.1).a).enc (fun j => m n.1 (.inr (n.2, j)))
          (fun q => r n.1 (.inr (n.2, q))) (Site.red (G.mb n.1) x) () else 0) =
      (∑ q, genOf s.Z (posIn s.Z x) (Fin.castAdd s.Z.l q) * layQ G r (.inr (b, q))) +
        ∑ j, genOf s.Z (posIn s.Z x) (Fin.natAdd s.Z.r j) * layJ G m (.inr (b, j))
    refine Eq.trans (Finset.sum_congr rfl fun n _ => ?_)
      (sum_rows (fun n : G.RZ => (G.seat n.1).pZ n.2 = b) _ _
        (fun n q => r n.1 (.inr (n.2,
          Fin.cast (congrArg Fmt.M1.Code.r ((G.seat n.1).hZ n.2).symm) q)))
        (fun n j => m n.1 (.inr (n.2,
          Fin.cast (congrArg Fmt.M1.Code.l ((G.seat n.1).hZ n.2).symm) j)))).symm
    have e := row_mask ((G.seat n.1).hZ n.2) (G.mb n.1).a s.C.a ((G.seat n.1).hz n.2) x
      (fun j => m n.1 (.inr (n.2, j))) (fun q => r n.1 (.inr (n.2, q)))
    exact congrArg (fun y => if (G.seat n.1).pZ n.2 = b then y else 0) e

/-- Where no two rows of the group have the same place, `layJ G m` has a member's entry at the place
that the member's seat gives that entry (`G.ent n`). -/
theorem layJ_ent (hA : G.Apart) (m : G.Msgs) (n : G.J) : layJ G m (G.ent n) = m n.1 n.2 := by
  obtain ⟨i, j⟩ := n
  rcases j with ⟨ρ, j⟩ | ⟨ρ, j⟩
  · show (∑ n : G.RM, if (G.seat n.1).pM n.2 = (G.seat i).pM ρ then _ else 0) = _
    refine (Finset.sum_eq_single (⟨i, ρ⟩ : G.RM)
      (fun n _ hne => if_neg fun h => hne (hA.main _ _ h))
      (fun h => absurd (Finset.mem_univ _) h)).trans ?_
    rw [if_pos rfl]
    rfl
  · show (∑ n : G.RZ, if (G.seat n.1).pZ n.2 = (G.seat i).pZ ρ then _ else 0) = _
    refine (Finset.sum_eq_single (⟨i, ρ⟩ : G.RZ)
      (fun n _ hne => if_neg fun h => hne (hA.mask _ _ h))
      (fun h => absurd (Finset.mem_univ _) h)).trans ?_
    rw [if_pos rfl]
    rfl

/-- The same for the tails: `layQ G r` at `(G.seat i).atQ q` is `r i q`. -/
theorem layQ_ent (hA : G.Apart) (r : Tails G) (i : G.ι) (q : (G.mb i).cd.Q) :
    layQ G r ((G.seat i).atQ q) = r i q := by
  rcases q with ⟨ρ, q⟩ | ⟨ρ, q⟩
  · show (∑ n : G.RM, if (G.seat n.1).pM n.2 = (G.seat i).pM ρ then _ else 0) = _
    refine (Finset.sum_eq_single (⟨i, ρ⟩ : G.RM)
      (fun n _ hne => if_neg fun h => hne (hA.main _ _ h))
      (fun h => absurd (Finset.mem_univ _) h)).trans ?_
    rw [if_pos rfl]
    rfl
  · show (∑ n : G.RZ, if (G.seat n.1).pZ n.2 = (G.seat i).pZ ρ then _ else 0) = _
    refine (Finset.sum_eq_single (⟨i, ρ⟩ : G.RZ)
      (fun n _ hne => if_neg fun h => hne (hA.mask _ _ h))
      (fun h => absurd (Finset.mem_univ _) h)).trans ?_
    rw [if_pos rfl]
    rfl

/-- On a main row of the stage's tables that is the place of no member's row, `layJ G m` is 0. -/
theorem layJ_freeM (m : G.Msgs) (b : Fin (s.h + s.g) → Bool)
    (hb : ∀ n : G.RM, (G.seat n.1).pM n.2 ≠ b) (j : Fin s.C.l) : layJ G m (.inl (b, j)) = 0 :=
  Finset.sum_eq_zero fun n _ => if_neg (hb n)

/-- On a mask row that no member has the laid message is 0. The laid message is `layJ G m`. -/
theorem layJ_freeZ (m : G.Msgs) (b : Fin s.h → Bool)
    (hb : ∀ n : G.RZ, (G.seat n.1).pZ n.2 ≠ b) (j : Fin s.Z.l) : layJ G m (.inr (b, j)) = 0 :=
  Finset.sum_eq_zero fun n _ => if_neg (hb n)

end Laws

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.sum_rows
#print axioms ProofFile.Honest.K12.row_main
#print axioms ProofFile.Honest.K12.row_mask
#print axioms ProofFile.Honest.K12.word_enc
#print axioms ProofFile.Honest.K12.layJ_ent
#print axioms ProofFile.Honest.K12.layQ_ent
#print axioms ProofFile.Honest.K12.layJ_freeM
#print axioms ProofFile.Honest.K12.layJ_freeZ
#print axioms ProofFile.Honest.K12.Tails
#print axioms ProofFile.Honest.K12.layJ
#print axioms ProofFile.Honest.K12.layQ
