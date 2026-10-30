-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdWfMasksLkp.lean: the lookups of the preamble of weights-formedness: the parameters of their
item "masked messages" as values, and the three conditions on them that "masks sent in advance"
asks.

Definitions, statements (in `Cb.Spec`) and proofs. Glue.
The preamble of weights-formedness (`LdWfP.Blk.wf`, Cb/Ld/LdWf.lean) is the sub-protocol for the
claim that the encoded index decodes to a message that holds an index. It sends a family of oracle
messages and then runs, for each l ≤ `P.n`, a lookup (`Sub`, Cb/Ld/LdLkp.lean): the sub-protocol for
the claim that every key of one group of the message's keys is an entry of that group's table
(`Lkp.InTable`). Named entries are the values `P.ent m n`, n in `P.N`, read off the messages m sent.
The item "masked messages" is `Honest.MM`, its parameters a record `MaskData` (Ior/Masked.lean).
"Masks sent in advance" names the fields `fresh`, `freshB` of `LdWfP.Blk.Hyp`.

Cb/Ld/LdWfMasksStd.lean derives the two hypotheses on masks of Cb/Ld/LdWf.lean from one named
condition `Q.OK` and `B.D.Nn.Hides (P.S.budT B.t)` (`Spec.ldWfMS_hyp`; `Q.OK` is
`LdWfP.Blk.Places.OK`). Three clauses of `Q.OK` concern the lookups' own parameters: `kc` (a lookup
reads the entries in a set of its own of the tuple "matrix of the prover's index message, named
entries"), `put` (its overwriting is the overwriting of named entries), `blind` (a lookup does not
look at the masks of a later block, for the wide reading: `wfWide`, Cb/Ld/LdWfMasks.lean).
The lookups are values (Cb/Ld/LdWfBlocks.lean: `K.sub l`, the assembled lookup on the keys of the
index).

Main names:
  `K.dc` (by `mjChain`, Cb/Ld/LdLkpMaskAsm2.lean), `K.dm` (by `dmIN`, Cb/Ld/LdLkpMaskLift2.lean):
  see their docstrings.
  `K.pl Rl l`: the places of `K.sub l`'s own masks (by `plChain`, Cb/Ld/LdLkpMaskPutLkp2.lean).
  `Spec.ldWfML_kc`: `(K.dm Rl Cc l).kc w = wfCutJ (Rl l) w`: by definition.
  `Spec.ldWfML_put`: if the places are as Cb/Ld/LdLkpMaskPut.lean says (`MJ.Pl.OK`) and are the
    named entries atL i: atL is injective, and `(K.dm Rl Cc l).put M k` is k overwritten at the
    named entries atL i by the vector `(K.pl Rl l).ve M`.
  `Spec.ldWfML_blind`: `K.sub j` does not look at masks at the places nAt (atN i), for the wide
    reading, if:
      `P.EntAt nAt`;
      the chain of lookup j, started with Cc j, is a link whose messages read Sr (`MJ.Link`,
      Cb/Ld/LdLkpMaskSp.lean; `Sw`: the set of its clause `writes`: any);
      Sr lies in Rl j;
      Cc j reads Sr only;
      every named entry in Sr is shown by the wide reading and is none of the places atN i.

The conclusion of `Spec.ldWfML_blind` is `Honest.Blind` (Ior/KnowCollRulesMask.lean) of
`(K.sub j).H`. `H.Blind kci kco Mk puti puto` (`Honest.Blind`) asks that, for all input witnesses w
and w', every M in `Mk`, every explicit part x of an input statement, all coins c of the honest
prover and every value ρ of the verifier's randomness, if `kci w' = puti M (kci w)`, then the honest
prover's runs from w' and from w, at x, c and ρ, have the same full transcript and end with the same
explicit part of the output statement, and `kco` of the output witness with which the run from w'
ends is `puto M` of `kco` of the output witness with which the run from w ends.

Limits: this file does not say that the chain is such a link (`Spec.ldLkpMaskAsm2_link`,
Cb/Ld/LdLkpMaskAsm2.lean, under its hypotheses). It does not say that the places are named entries
(they are, by the definition of `K.asm`; here a premise of `Spec.ldWfML_put`: the equation with
atL). It says nothing on the other clauses of `Q.OK`, but for `inj` (atL is injective) and `ent` (a
premise of `Spec.ldWfML_blind`).

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdWfMasksStd
import Cb.Ld.LdWfBlocksProofs
import Cb.Ld.LdLkpMaskLift2
import Cb.Ld.LdLkpMaskPutLkp2
import Cb.Ld.LdLkpAsm2Fmt
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop IOR Cb.LdLkp

namespace LdWfP.Lks
variable {E : Type} [Field E] [Fintype E] {C : ConfigurationWithOutOfDomainSample} {P : LdWfP E C} (K : P.Lks)

/-- The parameters (a record `MJ`, Cb/Ld/LdLkpMaskChain.lean) of the chain of lookup l, reading the
entries in `Rl l`. -/
def dc (Rl : ℕ → P.bt.J → Prop) (l : ℕ) :
    MJ E (K.asm l).J ((K.asm l).chainA C.E0 (C.Msg × P.S.Msg) Unit Unit P.msg).R :=
  (K.asm l).mjChain C.E0 (C.Msg × P.S.Msg) Unit Unit P.msg (Rl l)

/-- The parameters (a record `MaskData`, Ior/Masked.lean) of the item "masked messages" of
`K.sub l`, started with the claim `Cc l`. -/
def dm (Rl : ℕ → P.bt.J → Prop) (Cc : ℕ → P.WSt → (P.bt.J → E) → Prop) (l : ℕ) :
    MaskData (K.sub l).R P.W :=
  (K.asm l).dmIN (N := P.N) Sum.inr C P.S (K.dc Rl l) (Cc l) fun w => mjCut (Rl l) (P.msg w.1)

/-- The places of the own masks of `K.sub l`. -/
def pl (Rl : ℕ → P.bt.J → Prop) (l : ℕ) : (K.dc Rl l).Pl :=
  (K.asm l).plChain C.E0 (C.Msg × P.S.Msg) Unit Unit P.msg (Rl l)

end LdWfP.Lks

namespace Spec
section
variable (E : Type) [Field E] [Fintype E]

def ldWfML_kc : Prop :=
  ∀ (C : ConfigurationWithOutOfDomainSample) (P : LdWfP E C) (K : P.Lks) (Rl : ℕ → P.bt.J → Prop)
      (Cc : ℕ → P.WSt → (P.bt.J → E) → Prop) (l : ℕ) (w : P.W),
    (K.dm Rl Cc l).kc w = wfCutJ (Rl l) w

def ldWfML_put : Prop :=
  ∀ (C : ConfigurationWithOutOfDomainSample) (P : LdWfP E C) (K : P.Lks) (Rl : ℕ → P.bt.J → Prop)
      (Cc : ℕ → P.WSt → (P.bt.J → E) → Prop) (l : ℕ) (atL : (K.pl Rl l).I → P.N),
    (K.pl Rl l).OK → (∀ i, (K.pl Rl l).pl i = (Sum.inr (atL i) : P.bt.J)) →
    Function.Injective atL ∧
    ∀ (M : (K.dm Rl Cc l).Mk) (k : P.bt.J → E), (K.dm Rl Cc l).put M k =
      Function.extend (fun i => (Sum.inr (atL i) : P.bt.J)) ((K.pl Rl l).ve M) k

def ldWfML_blind : Prop :=
  ∀ (C : ConfigurationWithOutOfDomainSample) (P : LdWfP E C) (K : P.Lks) (Rl : ℕ → P.bt.J → Prop)
      (Cc : ℕ → P.WSt → (P.bt.J → E) → Prop) (j : ℕ) (Sr Sw : P.bt.J → Prop) (nAt : P.N → P.S.Ent)
      (RdW : P.S.Ent → Prop) (I Mk : Type) (atN : I → P.N) (v : Mk → I → E),
    (K.dc Rl j).Link ((K.asm j).chainA C.E0 (C.Msg × P.S.Msg) Unit Unit P.msg).H
      (fun w => mjCut (Rl j) (P.msg w.1)) (fun w => mjCut (Rl j) (P.msg w.1)) Sr Sw (Cc j) →
    (∀ a, Sr a → Rl j a) → (∀ k k' st, (∀ a, Sr a → k a = k' a) → Cc j st k → Cc j st k') →
    P.EntAt nAt → (∀ n, Sr (Sum.inr n) → RdW (nAt n) ∧ ∀ i, n ≠ atN i) →
    (K.sub j).H.Blind (wfWide RdW) (wfWide RdW) Mk
      (wfPut (fun i => nAt (atN i)) v) (wfPut (fun i => nAt (atN i)) v)

end
end Spec

section
variable {E : Type} [Field E] [Fintype E]

theorem ldWfML_kc : Spec.ldWfML_kc E := fun _ _ _ _ _ _ _ => rfl

theorem ldWfML_put : Spec.ldWfML_put E := by
  intro C P K Rl Cc l atL hOK hat
  have e : (K.pl Rl l).pl = fun i => (Sum.inr (atL i) : P.bt.J) := funext hat
  refine ⟨fun i i' h => hOK.inj (by rw [hat, hat, h]), fun M k => ?_⟩
  rw [← e]
  exact hOK.put M k

theorem ldWfML_blind : Spec.ldWfML_blind E := by
  intro C P K Rl Cc j Sr Sw nAt RdW I Mk atN v hL hRd hcl hE hS
  have hN := mjLift2_baseN E (K.asm j) P.N Sum.inr C.E0 (C.Msg × P.S.Msg) Unit Unit P.msg
    (K.dc Rl j) (fun w => mjCut (Rl j) (P.msg w.1)) Sr Sw (Cc j) hL
  have hP := mjp_full
    (b := (K.asm j).baseN (N := P.N) Sum.inr C.E0 (C.Msg × P.S.Msg) Unit Unit P.msg) hN
    (ldLkpAsm2N_plain E (K.asm j) P.N Sum.inr C.E0 (C.Msg × P.S.Msg) Unit Unit P.msg) hRd hcl
  exact ldLkpFmt2_blindIdx E (K.asm j) P.N Sum.inr C P.S P.msg _ Sr Sw hP _ (wfWide RdW) Mk
    (wfPut (fun i => nAt (atN i)) v)
    fun w w' m hk a ha => ldWfMS_same C P nAt RdW I Mk atN v Sr hE hS w w' m hk a ha

end
end Cb
