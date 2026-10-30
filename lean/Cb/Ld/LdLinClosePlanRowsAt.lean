-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLinClosePlanRowsAt.lean: this file treats rows that are filed in the claim, each on named
places, and states "each row reads entries of one group" as a condition on places alone.

Linear algebra on supports, for the book-keeping of the last part of an interactive oracle proof.
Linear constraints on the messages that the prover's oracles encode are to be sorted into sets, one
for each group of oracles that is tested together. Here the constraints' coefficients are data of
the statement's explicit part, and the file says, by the coordinates at which a constraint may be
non-zero, when each constraint touches one group only.
Definitions, statements and proofs.
It uses Cb/Ld/LdLinClosePlanRows.lean (a finite family of rows on all entries, sorted into whole
tests; `LdRowsD`, the data X of one test; the named condition `X.Supp`: a row of the test's group
vanishes outside the group, every other row vanishes outside what is kept: `X.kp`, the oracle
messages that something after the test still reads), Cb/Ld/LdLinCloseForms.lean (`Slf.push`:
coefficients on some entries as a form on all) and Cb/Ld/LdLkpTree.lean (`Row`: coefficients and a
public target; `r.Holds μ`: ∑ i, r.cf i * μ i = r.tg).
An entry (`Sig.Ent`, Cb/Ld/LdBatSig.lean) is one coordinate of one oracle message's message. The
claim cl is the part of the explicit statement from which the rows are read: as forms on all entries
(`Slf`, Cb/Ld/LdRel.lean) they have it as their state.

Why: a preamble files its rows in the claim (coefficients and target of a row are data of the
state). The statements on a closing are asked at all states. So "this row vanishes outside its
group" can hold only if the type of the filed row says where it may be non-zero.

B names the rows, Nb b names the places of row b, pl b n : S.Ent is the place, and row cl b : Row E
(Nb b) is the row filed in the claim cl.

Main names:
  `Spec.ldRowsAt_hold`: the forms `rowsAt pl row` all hold of the messages, with the targets
    `tgAt row`, if and only if every filed row holds of the entries at its places.
  `Spec.ldRowsAt_supp`: `X.Supp` holds if every place of a row of the test's group (`X.now b`) lies
    in a member of the group (`X.G`) and every place of another row lies in an oracle message that
    is kept (`X.kp`).
  `Spec.ldRowsAt_only`: the converse, where every row can be filed (for each b, n there is a claim
    whose row b has coefficient 1 at n and 0 elsewhere) and the places of a row are different:
    `X.Supp` holds only if the places lie so. So if all rows have one type of places (Nb b the same
    for all b, the same pl), a sorting into tests has `X.Supp` only if the group of each test that
    has a row of its own (`X.now b` for some b) holds all places: no sorting at all. (This last
    sentence is a remark: no theorem here states it.)
  `Spec.ldRowsAt_cut`: for a preamble whose state keeps free coefficients but reads each row cut to
    public places g: the cut row holds if and only if the row pulled to the subtype of g holds. So
    such rows are rows on named places (Nb b := the subtype), and `ldRowsAt_supp` applies.

Limits: this file does not say which places a given preamble's rows have.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdLinClosePlanRowsProofs
import Cb.Ld.LdLinCloseForms
import Cb.Ld.LdLkpTree

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR Cb.LdLkp

section
variable {E : Type} [Field E] {S : Sig E} {Cl B : Type} {Nb : B → Type} [∀ b, Fintype (Nb b)]

/-- the filed rows as forms on all entries; their targets (`tgAt`) -/
def rowsAt (pl : ∀ b, Nb b → S.Ent) (row : Cl → ∀ b, Row E (Nb b)) : B → Slf E Cl S.Ent := fun b =>
  Slf.push (pl b) fun cl n => (row cl b).cf n
omit [Field E] [∀ b, Fintype (Nb b)] in
def tgAt (row : Cl → ∀ b, Row E (Nb b)) : Cl → B → E := fun cl b => (row cl b).tg

end

namespace Spec

def ldRowsAt_hold : Prop :=
  ∀ (E : Type) [Field E] (S : Sig E) (Cl B : Type) (Nb : B → Type) [∀ b, Fintype (Nb b)]
      (pl : ∀ b, Nb b → S.Ent) (row : Cl → ∀ b, Row E (Nb b)) (cl : Cl) (m : S.Msg),
    rowsHold (rowsAt pl row) (tgAt row) cl (S.ents m) ↔
    ∀ b, (row cl b).Holds fun n => S.ents m (pl b n)

/-- The named condition `X.Supp`, from places alone. -/
def ldRowsAt_supp : Prop :=
  ∀ (E : Type) [Field E] [Fintype E] (S : Sig E) (E₀ : ExtSpec) (Wp Cl B : Type) [Fintype B]
      (Nb : B → Type) [∀ b, Fintype (Nb b)] (pl : ∀ b, Nb b → S.Ent)
      (row : Cl → ∀ b, Row E (Nb b)) (X : LdRowsD S E₀ Wp (rowsAt pl row)),
    (∀ b, X.now b → ∀ n, X.G.mem (pl b n).1) → (∀ b, ¬ X.now b → ∀ n, X.kp (pl b n).1) → X.Supp

/-- The converse of `ldRowsAt_supp`, under the first two premises below. -/
def ldRowsAt_only : Prop :=
  ∀ (E : Type) [Field E] [Fintype E] (S : Sig E) (E₀ : ExtSpec) (Wp Cl B : Type) [Fintype B]
      (Nb : B → Type) [∀ b, Fintype (Nb b)] [∀ b, DecidableEq (Nb b)] (pl : ∀ b, Nb b → S.Ent)
      (row : Cl → ∀ b, Row E (Nb b)) (X : LdRowsD S E₀ Wp (rowsAt pl row)),
    (∀ b, Function.Injective (pl b)) → (∀ b n, ∃ cl, (row cl b).cf = Pi.single n 1) → X.Supp →
    (∀ b, X.now b → ∀ n, X.G.mem (pl b n).1) ∧ ∀ b, ¬ X.now b → ∀ n, X.kp (pl b n).1

/-- States: a row cut to public places holds if and only if the row pulled to these places holds. -/
def ldRowsAt_cut : Prop :=
  ∀ (E N : Type) [Field E] [Fintype N] (g : N → Prop) [DecidablePred g] (r : Row E N) (μ : N → E),
    (∑ n, (if g n then r.cf n else 0) * μ n = r.tg) ↔
    (⟨fun n : {n // g n} => r.cf n.1, r.tg⟩ : Row E {n // g n}).Holds fun n => μ n.1

end Spec

theorem ldRowsAt_cut : Spec.ldRowsAt_cut := by
  intro E N _ _ g _ r μ
  have e : ∑ n : {n // g n}, r.cf n.1 * μ n.1 = ∑ n, (if g n then r.cf n else 0) * μ n := by
    rw [← sum_subtype_zero g (fun n => (if g n then r.cf n else 0) * μ n) fun n hn => by
        beta_reduce; rw [if_neg hn, zero_mul]]
    exact Finset.sum_congr rfl fun n _ => by rw [if_pos n.2]
  exact ⟨fun h => e.trans h, fun h => e.symm.trans h⟩

theorem ldRowsAt_hold : Spec.ldRowsAt_hold := by
  intro E _ S Cl B Nb _ pl row cl m
  have e : ∀ b, (rowsAt pl row b).val cl (S.ents m) = ∑ n, (row cl b).cf n * S.ents m (pl b n) :=
    fun b => ldForm_push E Cl (Nb b) S.Ent (pl b) (fun cl n => (row cl b).cf n) cl (S.ents m)
  exact ⟨fun h b => (e b).symm.trans (h b), fun h b => (e b).trans (h b)⟩

/-- a pushed form vanishes at an entry that is no place -/
theorem Slf.push_zero {E St I J : Type} [Field E] [Fintype I] [DecidableEq J] (φ : I → J)
    (a : St → I → E) (st : St) (j : J) (h : ∀ i, φ i ≠ j) : Slf.push φ a st j = 0 :=
  Finset.sum_eq_zero fun i _ => if_neg (h i)

/-- at a place, if the places are different, a pushed form is the coefficient -/
theorem Slf.push_at {E St I J : Type} [Field E] [Fintype I] [DecidableEq J] (φ : I → J)
    (hφ : Function.Injective φ) (a : St → I → E) (st : St) (i : I) :
    Slf.push φ a st (φ i) = a st i := by
  unfold Slf.push
  rw [Finset.sum_eq_single i]
  · rw [if_pos rfl]
  · intro i' _ hi
    exact if_neg fun e => hi (hφ e)
  · exact fun h => absurd (Finset.mem_univ _) h

theorem ldRowsAt_supp : Spec.ldRowsAt_supp := by
  intro E _ _ S E₀ Wp Cl B _ Nb _ pl row X h1 h2
  exact ⟨fun b hb st n hn => Slf.push_zero _ _ st n fun i e => hn (e ▸ h1 b hb i),
    fun b hb st n hn => Slf.push_zero _ _ st n fun i e => hn (e ▸ h2 b hb i)⟩

theorem ldRowsAt_only : Spec.ldRowsAt_only := by
  intro E _ _ S E₀ Wp Cl B _ Nb _ _ pl row X hinj hall hS
  have one : ∀ b n, ∃ cl, rowsAt pl row b cl (pl b n) = 1 := by
    intro b n
    obtain ⟨cl, hcl⟩ := hall b n
    refine ⟨cl, ?_⟩
    show Slf.push (pl b) (fun cl n => (row cl b).cf n) cl (pl b n) = 1
    rw [Slf.push_at _ (hinj b), hcl, Pi.single_eq_same]
  refine ⟨fun b hb n => ?_, fun b hb n => ?_⟩
  · by_contra hn
    obtain ⟨cl, hcl⟩ := one b n
    exact one_ne_zero (hcl.symm.trans (hS.mine b hb cl _ hn))
  · by_contra hn
    obtain ⟨cl, hcl⟩ := one b n
    exact one_ne_zero (hcl.symm.trans (hS.other b hb cl _ hn))

end Cb
