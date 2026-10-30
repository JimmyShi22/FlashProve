-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K2/Honest/Inner/NewWordsAt.lean: WHAT THE WORDS `newWords` (Inner/Statement.lean) ARE
AT THE CARRYING MESSAGE AND AT A COPY, WRITTEN AT THE TARGET's OWN SHAPES: message number 0, or 1 +
a, of the new sending, laid out by the shape that the target gives it. Under the public premises of
`SwitchRowsHold`: `newWords_copy` takes them as a record A, which `atPublic` (Inner/Public.lean)
makes of them. Three statements with their proofs; no definition. No coin, no round, no frame.

  `word_of_three` a message's two tables by index (`Rows.word`, Johnson/Prover/Send/Core.lean) read
                    of a shape three numbers alone: the main rows, the main degree, the mask rows
  `newWords_g` at g: `(V 0).word` at the target's shape. By unfolding
  `newWords_copy` at the copy number a: `(V (1 + a)).word` AT THE SHAPE OF THE TARGET's ENTRY a

WHY. `newWords` lays a copy out by the shape of the OLD kept member (`sizesAt`'s list kept). Whoever
meets these words with a sending's held words (`held_new`, Johnson/Prover/Send/Held.lean) has the
NEW message's shape there. The two shapes need not be one; the target's test ties just the three
numbers that the layout reads (`KeptFits`, Johnson/Top/H0/Tw/K2/TargetMeans.lean: as many main rows,
the same degree, no mask row at either).

By: `kept_shape` (Inner/PadsProof.lean) · `Lists.idxOf_at` (Inner/Words.lean). Kin, not called:
`word_g`, `word_copy` (Inner/Words.lean) and `word_off` (Inner/Value.lean) say WHICH VALUES stand in
`newWords`, under `HonestMain`, off the pads; here V is any letter and every index is meant.

Limits. On the layout alone: nothing on any value. V is a letter. Nothing on any property.
-/
import Johnson.Desc.K2.Honest.Inner.PadsProof

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K2.Honest
open OnBytes
open OnBytes.Slice (GE)
open Johnson.Prover.Send (Rows)

/-- A message's two tables by index read of a shape three numbers alone. -/
theorem word_of_three (R : Rows) {s n : OracleShape} (h1 : n.mainRows = s.mainRows)
    (h2 : n.mainDeg = s.mainDeg) (h3 : n.maskRows = s.maskRows) (part : Part) (i : Nat) :
    R.word s part i = R.word n part i := by
  cases part <;> simp only [Rows.word, h1, h2, h3]

/-- At the carrying message. -/
theorem newWords_g (Z : Sizes) (g : Nat) (anew : Array Nat) (V : Nat → Rows) (part : Part)
    (i : Nat) : newWords Z g anew V g part i = (V 0).word Z.target.shape part i := by
  show (if g = g then _ else _) = _
  rw [if_pos rfl]

variable {S : Statement} {old : SingleRows} {T : SwitchTarget} {g : Nat} {anew : Array Nat}
  {W : Left} {V₀ : Nat → Rows}

/-- **At a copy, at the target's own shape.** A: for its public fields alone. V: any messages. -/
theorem newWords_copy (A : AtSwitch S old T g anew W V₀) (V : Nat → Rows) (a : Nat)
    (k : KeptTarget) (hk : T.kept[a]? = some k) (o : Nat) (ho : anew.toList[a]? = some o)
    (part : Part) (i : Nat) :
    newWords (sizesAt S old T) g anew V o part i = (V (1 + a)).word k.shape part i := by
  have hap := A.seated.apart
  rw [List.cons_append, List.nodup_cons, List.nodup_append] at hap
  have hne : o ≠ g := fun e => hap.1 (List.mem_append_left _ (e ▸ List.mem_of_getElem? ho))
  have hidx := Lists.idxOf_at anew.toList a o hap.2.1 ho
  obtain ⟨s, hs, K⟩ := kept_shape A a k hk
  have hget : (sizesAt S old T).kept.getD a {} = s := by
    rw [List.getD_eq_getElem?_getD, hs]
    rfl
  show (if o = g then _ else
    match anew.toList.idxOf? o with
    | some a => (V (1 + a)).word ((sizesAt S old T).kept.getD a {}) part i
    | none => 0) = _
  rw [if_neg hne, hidx]
  show (V (1 + a)).word ((sizesAt S old T).kept.getD a {}) part i = _
  rw [hget]
  exact word_of_three _ K.rows K.degree (K.newBare.trans K.oldBare.symm) part i

end VerifiableInference.Desc.K2.Honest

#print axioms VerifiableInference.Desc.K2.Honest.word_of_three
#print axioms VerifiableInference.Desc.K2.Honest.newWords_g
#print axioms VerifiableInference.Desc.K2.Honest.newWords_copy
