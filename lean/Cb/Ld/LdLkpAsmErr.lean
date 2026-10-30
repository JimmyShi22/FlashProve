-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLkpAsmErr.lean: the errors of the assembled lookup, as one list, in the order of the rounds.

Definitions and statements (in `Cb.Spec`); the proofs are in Cb/Ld/LdLkpAsmErrProofs.lean. The data
of the assembled lookup are an `LkAsm` (Cb/Ld/LdLkpAsm.lean).
The lookup is the sub-protocol for the claim that every key is an entry of a table (`Lk.inR`,
Cb/Ld/LdLkp.lean). This file lists, round by round, the error numbers of its knowledge soundness. An
error is a count: a bound on the number of bad values of the round's verifier message (`Iop.Err`);
beside it is the number of all values of that message. q is the number of elements of the field.

Main names:
  `pscErrs k n D`: the errors of one sumcheck for a polynomial summand with k variables of degree n
    and the dummy variable (`pDummy`, Cb/Ld/LdPsc.lean) of degree D: 1 (the coefficient ε; of q
    values); n for each of the k variables (of q); D (the dummy variable; of q - 1: it is not 0); 0
    (the values; no verifier message).
  `A.errs q`: the list. In order:
    2^v - 1: the first challenge λ (v = v' + 1: 2^v keys);
    pscErrs 0 _ 1: the tie's first step (`TieP`, Cb/Ld/LdLkpTie.lean; summand of degree 1 in the
    dummy variable);
    pscErrs 0 _ 3, n times: the tie's further steps (a square times a factor: degree 3);
    pscErrs l 2 2, then 1, for l < v: the keys' tree: level l: the sumcheck with l variables; the
    line step (`lineA`, Cb/Ld/LdLkpTreeP.lean);
    w q^(w-1): the point of the table's forest (`forest`, Cb/Ld/LdLkpSegT.lean; w coordinates);
    pscErrs (w + l) 2 2, then 1, for l < d: the forest: level l; the line step;
    pscErrs (w + d) 2 1: the closing (`LkEnd`, Cb/Ld/LdLkpEnd.lean) of the forest's top claim;
    (w + d) q^(w+d-1): the point of the bit test's zerocheck (`LkBit`, Cb/Ld/LdLkpBit.lean; w + d
    coordinates);
    pscErrs (w + d) 2 2: the bit test's sumcheck.
  `ldLkpAsmE_errs`: the errors of `A.baseN ι` (so of `A.subN ι`, `A.subIN ι`: `ldLkpAsmE_sub`) are
    that list.
  `ldLkpAsmE_vals`: the numbers of values of its verifier messages are `A.vals q`.
  `ldLkpAsmE_len`: both lists have as many entries as `ldLkpAsm_rounds` (Cb/Ld/LdLkpAsm.lean) counts
    rounds of `A.baseA`.
  `ldLkpAsmE_small`: every error is below its number of values if 2^v ≤ q, 5 ≤ q, w + d < q (with w
    = 0 or w + d = 0 the point's error is 0).

Limits: not in the list, rightly: the error of a random shift that joins several tables into one
(the size of the joint table, of q): that is a block before the lookup (Cb/Ld/LdLkpShift.lean).
Four differences to a write-up of ours (lean/CREDITS.md), which writes the lookup out, are
declared: (1) to (4) below (by a reading). `LkAsm2` (Cb/Ld/LdLkpAsm2.lean),
Cb/Ld/LdLkpAsm2*.lean, removes (1), (3), (4); at (2) it has the same block, `RootP.rootA`, one
round, drawn earlier. `LkAsm` (Cb/Ld/LdLkpAsm.lean) is superseded under all callers: no protocol,
toy or top stands on it any more. Its files stay because files of `LkAsm2` quote their generic
parts.
   (1) Order. There the one claim on the table's products comes right after the tie, before the
       keys' grand product; here the forest's point is drawn after the keys' tree.
   (2) The forest's first point. There a line step on a map with as many parts as there are bit
       positions, counting and idle ones together (a power of two): one round; here a round of its
       own for the point (declared as ours in the head of Cb/Ld/LdLkpAsm.lean).
   (3) Idle bit positions. There the table's factor carries a public factor, 1 at the counting
       positions and 0 at the others, so the product at an idle position is 1 for all messages and
       the claim "product = 1" there needs nothing; here that claim is added after the challenge and
       rides along, true because honest bits are 0 there: a hypothesis (`H.Idle`) that falls with
       the public factor.
   (4) The table's factor. There it is closed without revealing a map (two rounds fewer, one row);
       here by the closing that reveals (two rows). This bears on what the verifier sees, so on the
       block's item "masked messages" too, not only on counts.
This file says nothing on a sum of quotients, nothing on a bound "in bits": the list is what a
composition takes. It says nothing on list factors: the lookup reads no oracle and has none.
Terms: lean/GLOSSARY.md.
"The write-up": one of our own texts on this protocol (lean/CREDITS.md); it is not in this
repository.
-/
import Cb.Ld.LdLkpAsmPull
import Ior.KnowCollRulesChainErr

set_option autoImplicit false

namespace Cb.LdLkp
open Iop IOR Hiop Prob

/-- the errors of one sumcheck; the numbers of values beside them (`pscVals`) -/
def pscErrs (k n D : ℕ) : List ℕ := 1 :: (List.replicate k n ++ [D, 0])
def pscVals (q k : ℕ) : List ℕ := q :: (List.replicate k q ++ [q - 1, 1])

namespace LkAsm
variable {E : Type} [Field E] [Fintype E] (A : LkAsm E)

/-- The errors, in the order of the rounds. -/
def errs (q : ℕ) : List ℕ :=
  (([2 ^ (A.v' + 1) - 1] ++ (pscErrs 0 2 1 ++ (List.range A.n).flatMap fun _ => pscErrs 0 2 3)) ++
      (List.range (A.v' + 1)).flatMap fun l => pscErrs (0 + l) 2 2 ++ [1]) ++
    ((([A.w * q ^ (A.w - 1)] ++ (List.range A.d).flatMap fun l => pscErrs (A.w + l) 2 2 ++ [1]) ++
        pscErrs (A.w + A.d) 2 1) ++
      ([(A.w + A.d) * q ^ (A.w + A.d - 1)] ++ pscErrs (A.w + A.d) 2 2))

/-- The numbers of values of the verifier messages, in the same order. -/
def vals (q : ℕ) : List ℕ :=
  (([q] ++ (pscVals q 0 ++ (List.range A.n).flatMap fun _ => pscVals q 0)) ++
      (List.range (A.v' + 1)).flatMap fun l => pscVals q (0 + l) ++ [q]) ++
    ((([q ^ A.w] ++ (List.range A.d).flatMap fun l => pscVals q (A.w + l) ++ [q]) ++
        pscVals q (A.w + A.d)) ++
      ([q ^ (A.w + A.d)] ++ pscVals q (A.w + A.d)))

end LkAsm
end Cb.LdLkp

namespace Cb.Spec
open Iop IOR Hiop Prob Cb.LdLkp

section
variable (E : Type) [Field E] [Fintype E]

/-- The errors. -/
def ldLkpAsmE_errs : Prop :=
  ∀ (A : LkAsm E) (N : Type) (ι : N → A.J) (Ex : ExtSpec) (M Wp Kc : Type) (msg : M → A.J → E),
    (A.baseN ι Ex M Wp Kc msg).P.err.toList = A.errs (Fintype.card E)

/-- The numbers of values. -/
def ldLkpAsmE_vals : Prop :=
  ∀ (A : LkAsm E) (N : Type) (ι : N → A.J) (Ex : ExtSpec) (M Wp Kc : Type) (msg : M → A.J → E),
    (A.baseN ι Ex M Wp Kc msg).R.shape.chalList = A.vals (Fintype.card E)

/-- Over a signature, and with an encoded index: the same lists. -/
def ldLkpAsmE_sub : Prop :=
  (∀ (A : LkAsm E) (N : Type) (ι : N → A.J) (S : Sig E) (E₀ : ExtSpec)
        (Kc Wp : Type) (msg : S.Msg → A.J → E),
      (A.subN ι S E₀ Kc Wp msg).P.err.toList = A.errs (Fintype.card E) ∧
      (A.subN ι S E₀ Kc Wp msg).R.shape.chalList = A.vals (Fintype.card E)) ∧
  ∀ (A : LkAsm E) (N : Type) (ι : N → A.J) (C : ConfigurationWithOutOfDomainSample) (S : Sig E) (msg : C.Msg × S.Msg → A.J → E),
    (A.subIN ι C S msg).P.err.toList = A.errs (Fintype.card E) ∧
    (A.subIN ι C S msg).R.shape.chalList = A.vals (Fintype.card E)

def ldLkpAsmE_len : Prop :=
  ∀ (A : LkAsm E) (q : ℕ),
    (A.errs q).length = (A.vals q).length ∧
    (A.errs q).length =
      (1 + 3 * (A.n + 1)) + (∑ l ∈ Finset.range (A.v' + 1), (0 + l + 3 + 1)) +
        ((1 + ∑ l ∈ Finset.range A.d, (A.w + l + 3 + 1)) + (A.w + A.d + 3) + (1 + (A.w + A.d + 3)))

/-- Under the hypotheses below, every error is below its number of values. -/
def ldLkpAsmE_small : Prop :=
  ∀ (A : LkAsm E) (N : Type) (ι : N → A.J) (Ex : ExtSpec) (M Wp Kc : Type) (msg : M → A.J → E),
    2 ^ (A.v' + 1) ≤ Fintype.card E → 5 ≤ Fintype.card E →
    A.w + A.d < Fintype.card E → (A.baseN ι Ex M Wp Kc msg).P.err.Small

end
end Cb.Spec
