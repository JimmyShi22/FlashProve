-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/KeyLookup/HKey.lean: the statement that the lookup with parts `A.lamS`, at the public numbers
of the two lookups of a key of full size and for all data, is knowledge sound, as one closed
proposition; and, beside it, what is proved of the same reductions without it.

The key's first chain holds two lookups. Each says of many keys, which come in parts, that every key
is a row of a table. Their public numbers
(`pubFull₁`, `pubFull₂`, Cb/Pv/KeyLookup/FullPub.lean): 12 parts of 2^36 and of 2^35 keys; tables of
2^8 and 2^13 rows; 40 and 39 live planes of 64; runs of
padding in the last part; the last level of each part's tree binds the variables 2, 1, 0, 5, 4, 3,
8, 7, 6 first.

The reduction. `A.lamS P Ex` (Cb/Pv/KeyLookup/Lam1Short.lean): the lookup with parts as one chain of
reductions:
a draw, the tie of the two sides' roots, the parts' steps, a point that joins the planes' claims, a
product tree for each part, the table's tree, the
closing, the test that the bits are bits; every sumcheck in its short form (one coefficient of each
round's polynomial is not sent).

  `sizesKeyLookup` the written list of the two public records.
  `HKeyLookup`     THE STATEMENT. A closed proposition: no parameter. For each public record S of
                   that list, and for ALL THAT IS STILL A LETTER, bound inside:
                   the data A over the field `Cb.Gl.E` with `A.toPub = S` (states, entries, the keys
                   as functions of state and entries, the table, where the live
                   planes' bits are); the places P of the lookup's own mask entries; the further
                   oracles Ex; the types Kc, M, Wp; a joint R0 that rides along; the reading
                   msg of the entries off the messages; a predicate Mu, which the statement does not
                   read; a tuple m of messages:
                   the reduction is knowledge sound (`Reduction.Know`) from «R0, and every key of
                   every part is a row of the table» to «R0, and for each part the
                   extension of its keys at its point plus its mask form is its target, and all rows
                   hold», with the identity as extractor and the reduction's own list of
                   errors. It is the field `know` of the record `KnowAt` at `(A.lamS P Ex).R`,
                   `A.jtIn R0 msg Mu`, `A.jtOut R0 msg`, the identity, `(A.lamS P Ex).e`.
                   NO LETTER IS SET AT A VALUE OF THE HOUSE ABOVE (its states, entries, messages,
                   keys): whoever uses the statement puts them in.
  BESIDE IT, PROVED HERE, at the same two records and for the same letters:
  `hKey_point`, `hKey_isLocal`, `hKey_onOut`   the record's three other fields.
  `hKey_copies`, `hKey_passes`   the reduction only copies its oracles; it hands the caller's state
                    on unchanged.
  `hKey_errs`      ARITHMETIC, at the same errors: read by the library's `Err.toList` and
                   `Shape.chalList`, the reduction's errors and the numbers of values of its
                   verifier's
                   messages are the columns c and n of the computable list `Lam q S`
                   (Cb/Pv/KeyLookup/Lam.lean), q the number of elements of the field.
  `hKey_sent`      round by round the prover's message has q ^ sent values, `sent` that list's
                   column in its short form.

Not shown here: `HKeyLookup` itself: it is a statement, and no theorem of this library has it as its
conclusion. Its body is the field `know` of the record that `lamS_know`
(Cb/Pv/KeyLookup/Lam1Short.lean) proves under `A.toPub.Adm p`, and `adm_full` below gives `Adm` at
the two records. That the list is the planner's (OnBytes/Tie/Pv/KeyLookup/LamList.lean, for all
sizes). That the two records are those of a key's public files.
That this reduction binds the variables in the program's order, or that its
points and end claims are the program's. That an honest prover's run meets the relation that it
arrives at. The statement fixes the tuple m of messages before the
reduction's first draw: that in a protocol which uses the lookup the messages that hold the keys,
the planes' bits and every entry that P names are sent before that
draw is not shown here. Anything on an honest prover. Anything on zero knowledge.

-/
import Cb.Pv.KeyLookup.Lam1Short
import Cb.Pv.KeyLookup.FullPub
import Cb.Gl.GlField

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lk6
open Iop IOR Cb Cb.LdLkp Cb.LdLkp.Kn

/-- The sizes at which the statement is made: a written list of two. Where they come from: the head
of Cb/Pv/KeyLookup/FullPub.lean says it. -/
def sizesKeyLookup : List Pub := [pubFull₁, pubFull₂]

/-- The lookup with parts `A.lamS`, at the public numbers of the two lookups of a key of full size
and
for all data, is knowledge sound. -/
def HKeyLookup : Prop :=
  ∀ S ∈ sizesKeyLookup, ∀ A : Dat Cb.Gl.E, A.toPub = S →
    ∀ (P : Pl A) (Ex : ExtSpec) (Kc M Wp : Type) (R0 : Rels Kc A.St Ex (M × Wp))
      (msg : M → A.J → Cb.Gl.E) (Mu : A.St → (A.J → Cb.Gl.E) → Prop) (m : M),
      (A.lamS P Ex).R.red.Know (A.jtIn R0 msg Mu).on
        (fun a wp => (A.jtIn R0 msg Mu).relR a (m, wp)) (fun b wp => (A.jtOut R0 msg).relR b (m,
            wp))
        (fun _ _ wp => wp) (A.lamS P Ex).e

/-- Both records are admissible at the field's characteristic. -/
theorem adm_full : ∀ S ∈ sizesKeyLookup, S.Adm Cb.Gl.p := by
  intro S hS
  rcases List.mem_cons.1 hS with rfl | hS
  · exact adm_pubFull₁ _ (by decide)
  · rw [List.mem_singleton.1 hS]
    exact adm_pubFull₂ _ (by decide)

section
variable (S : Pub) (hS : S ∈ sizesKeyLookup) (A : Dat Cb.Gl.E) (hA : A.toPub = S) (P : Pl A)
  (Ex : ExtSpec)
include hS hA

theorem hKey_point : Nonempty (A.lamS P Ex).R.shape.IsPoint :=
  (lamS_know Cb.Gl.p A P Ex Unit Unit Unit ⟨fun _ _ _ => True, fun _ _ => True, fun _ => True, fun _
      => ()⟩
    (fun _ _ => 0) (fun _ _ => True) (hA ▸ adm_full S hS)).point

theorem hKey_isLocal : (A.lamS P Ex).R.IsLocal :=
  (lamS_know Cb.Gl.p A P Ex Unit Unit Unit ⟨fun _ _ _ => True, fun _ _ => True, fun _ => True, fun _
      => ()⟩
    (fun _ _ => 0) (fun _ _ => True) (hA ▸ adm_full S hS)).isLocal

theorem hKey_onOut (Kc M Wp : Type) (R0 : Rels Kc A.St Ex (M × Wp)) (msg : M → A.J → Cb.Gl.E)
    (Mu : A.St → (A.J → Cb.Gl.E) → Prop) :
    ∀ a τ b, (A.jtIn R0 msg Mu).on a → (A.lamS P Ex).R.red.out a τ = some b → (A.jtOut R0 msg).on b
        :=
  (lamS_know Cb.Gl.p A P Ex Kc M Wp R0 msg Mu (hA ▸ adm_full S hS)).onOut

theorem hKey_errs : IsL (A.lamS P Ex) (Lam (Fintype.card Cb.Gl.E) S) :=
  hA ▸ lamS_isL_adm Cb.Gl.p A P Ex (hA ▸ adm_full S hS)

theorem hKey_sent :
    IsS (Fintype.card Cb.Gl.E) (A.lamS P Ex) ((Lam (Fintype.card Cb.Gl.E) S).map LRow.short) := by
  have h : A.toPub.Adm Cb.Gl.p := hA ▸ adm_full S hS
  exact hA ▸ lamS_isS A P Ex h.planes h.some (fun i hi => (h.bits i hi).1) h.tabs

end

theorem hKey_copies (A : Dat Cb.Gl.E) (P : Pl A) (Ex : ExtSpec) : (A.lamS P Ex).R.OnlyCopies :=
  lamS_copies A P Ex

theorem hKey_passes (A : Dat Cb.Gl.E) (P : Pl A) (Ex : ExtSpec) :
    (A.lamS P Ex).R.Passes id (fun o => o.1) :=
  lamS_passes A P Ex

end Lk6

#print axioms Lk6.adm_full
#print axioms Lk6.hKey_point
#print axioms Lk6.hKey_isLocal
#print axioms Lk6.hKey_onOut
#print axioms Lk6.hKey_errs
#print axioms Lk6.hKey_sent
#print axioms Lk6.hKey_copies
#print axioms Lk6.hKey_passes
