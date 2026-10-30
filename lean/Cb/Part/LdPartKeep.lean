-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Part/LdPartKeep.lean: from what rides through a segment's front (the relation `P.ride`) to what
rides behind its read stage (`P.rideB` at `Ok.pull r`): the second reads kept messages only.

Definitions and three statements (`Cb.Spec.ldPartKeep_fw`, `Cb.Spec.ldPartKeep_bw`,
`Cb.Spec.ldPartKeep_pull`); the proofs are in Cb/Part/LdPartKeepProofs.lean. For arbitrary
parameters: no block occurs.
A reading here (`LdPartOut`, Cb/Part/LdPartRide.lean) has the cells A read off messages and two
predicates "packed": pkX (exact), pkR (relaxed). `P.ride K k O ..` (the same file) has among its
clauses O.pkX (exact), O.pkR (relaxed) and the conditions of all segments j > k. `P.rideB`
(Cb/Part/LdPartNext.lean) is `P.ride` without O.pkR in its relaxed part.

Why: through the front of segment k rides Cb/Part/LdPartRide.lean's relation at a reading O of all
rows of the body's matrix, own and kept. A segment that is built after the one before it
requires that the model's part of "what
else is claimed" behind the rows is a relation on the kept messages, read at the restriction:
equivalences and an equation, for all messages. The front's relation is not: it reads the segment's
own rows, most of which no later segment reads. So at the front's last step the riding relation must
be weakened, forth (`Spec.ldPartKeep_fw`), and won back, backwards (`Spec.ldPartKeep_bw`); there the
read stage's own clause "packed" is at hand (the premise O.pkR m).

Main names:
  `LdPartKeepTie`: the ties between the reading O of all rows and the reading Ok of the kept ones.
    Exact: all rows packed ⇒ the kept rows packed. Relaxed: all rows packed ⇒ the two readings
    agree on the rows kept behind k, in all columns.
  `Spec.ldPartKeep_fw`: the ties ⇒ the front's riding relation (exact) gives the one behind the
    read stage at `Ok.pull r`.
  `Spec.ldPartKeep_bw`: `P.Props p`, the ties, O.pkR m ⇒ the relaxed relation behind the read stage
    at `Ok.pull r` gives the front's relaxed riding relation. Used of the partition: a row of a
    segment ≤ k that a segment j > k reads is kept behind k (keeps); well-formedness (wf).
  `Spec.ldPartKeep_pull`: the relation behind the read stage at `Ok.pull r` is that at Ok, read at
    r m, in all four parts, by definition. So the four clauses that are asked hold with `Amk` :=
    the relation at Ok.

Limits:
How this stands to a write-up of ours (lean/CREDITS.md; by inspection): the step is
Lean's, what it yields is the write-up's. There nothing is weakened, because what rides here
in one letter are two predicates
from the start: segment k's own range predicate, which is used up at the range check, and the later
segments' conditions, which every block hands on and which read kept messages alone. This step parts
the two.
The one-sidedness of what rides behind the read stage (exact: the kept rows are packed below B in
absolute value; relaxed: no packing of kept rows is claimed) is declared in the head of
Cb/Part/LdPartNext.lean, (1). This file does not say that the ties hold. It does not say that the
front's last step takes two riding relations. Nothing on masks.


"The write-up": one of our own texts on this protocol (lean/CREDITS.md); it is not in this
repository.
-/
import Cb.Part.LdPartNext

set_option autoImplicit false

namespace Cb

open Iop Prob Hiop Blocks Finset Cb.RngPk IOR

/-- a reading of the messages Sk, as a reading of the messages S, along r (say the restriction to
the kept messages) -/
def LdPartOut.pull {E : Type} [Field E] {S Sk : Sig E} (O : LdPartOut E Sk) (r : S.Msg → Sk.Msg) :
    LdPartOut E S :=
  ⟨fun m => O.A (r m), fun m g => O.pkX (r m) g, fun m => O.pkR (r m)⟩

/-- The ties. -/
structure LdPartKeepTie {F E : Type} [Field F] [Field E] [Algebra F E]
    {Cf : LdCf F E} (P : LdPartD Cf) (k : ℕ) {S Sk : Sig E} (O : LdPartOut E S)
    (Ok : LdPartOut E Sk) (r : S.Msg → Sk.Msg) : Prop where
  pkX    : ∀ m g, O.pkX m g → Ok.pkX (r m) g
  rdKept : ∀ m, O.pkR m → ∀ q ∈ P.kept k, ∀ c, O.A m q.1 q.2 c = Ok.A (r m) q.1 q.2 c

namespace Spec

def ldPartKeep_fw : Prop :=
  ∀ (F E : Type) [Field F] [Fintype F] [Field E] [Algebra F E] (Cf : LdCf F E) (P : LdPartD Cf)
      (K : LdPartPk) (k : ℕ) (S Sk : Sig E) (O : LdPartOut E S) (Ok : LdPartOut E Sk)
      (r : S.Msg → Sk.Msg) (St : Type) (x : St → Cf.Xm) (rc : St → Cf.conf.Rec)
      (bitX : ℕ → Cf.Xm → (ℕ → ℕ → F) → LdPartGh → (ℕ → E) → Prop),
    LdPartKeepTie P k O Ok r →
    ∀ st y t, (P.ride K k O x rc bitX).rel st y t → (P.rideB K k (Ok.pull r) x rc bitX).rel st y t

def ldPartKeep_bw : Prop :=
  ∀ (F E : Type) [Field F] [Fintype F] [Field E] [Algebra F E] (Cf : LdCf F E) (P : LdPartD Cf)
      (K : LdPartPk) (p k : ℕ) (S Sk : Sig E) (O : LdPartOut E S) (Ok : LdPartOut E Sk)
      (r : S.Msg → Sk.Msg) (St : Type) (x : St → Cf.Xm) (rc : St → Cf.conf.Rec)
      (bitX : ℕ → Cf.Xm → (ℕ → ℕ → F) → LdPartGh → (ℕ → E) → Prop),
    P.Props p → LdPartKeepTie P k O Ok r →
    ∀ a t,
      O.pkR t.1.2 → (P.rideB K k (Ok.pull r) x rc bitX).relR a t → (P.ride K k O x rc bitX).relR a t

def ldPartKeep_pull : Prop :=
  ∀ (F E : Type) [Field F] [Fintype F] [Field E] [Algebra F E] (Cf : LdCf F E) (P : LdPartD Cf)
      (K : LdPartPk) (k : ℕ) (S Sk : Sig E) (Ok : LdPartOut E Sk) (r : S.Msg → Sk.Msg) (St : Type)
      (x : St → Cf.Xm) (rc : St → Cf.conf.Rec)
      (bitX : ℕ → Cf.Xm → (ℕ → ℕ → F) → LdPartGh → (ℕ → E) → Prop),
    (∀ st y U m wp,
      (P.rideB K k (Ok.pull r) x rc bitX).rel st y ((U, m), wp) ↔
      (P.rideB K k Ok x rc bitX).rel st y ((U, r m), wp)) ∧
    (∀ a U m wp,
      (P.rideB K k (Ok.pull r) x rc bitX).relR a ((U, m), wp) ↔
      (P.rideB K k Ok x rc bitX).relR a ((U, r m), wp)) ∧
    (∀ a, (P.rideB K k (Ok.pull r) x rc bitX).on a ↔ (P.rideB K k Ok x rc bitX).on a) ∧
    (∀ U m wp, (P.rideB K k Ok x rc bitX).core ((U, r m), wp) =
      (P.rideB K k (Ok.pull r) x rc bitX).core ((U, m), wp))

end Spec

end Cb
