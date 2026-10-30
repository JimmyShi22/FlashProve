-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLkpKit.lean: joints of a base chain as "a riding joint, and claims on the entries"; the
lookup's first challenge at the base; the tree's joints in that form.

Definitions, statements (in `Cb.Spec`) and proofs. Glue for the assembly of the lookup; no new
protocol.
A joint (`IOR.Rels`; with its types, `IOR.Joint`) consists of, for one kind of statement and of
witness: the honest relation; a second relation, called relaxed, of which round-by-round knowledge
soundness speaks; the set of statements of which that soundness speaks; and a map from a witness to
its core.
`GoodAt R H A B ext P` (Cb/Ld/LdSigLift.lean) has among its fields completeness from A to B in the
sense of `Honest.Acc` (Ior/Honest.lean) and, for each fixed tuple of messages, round-by-round
knowledge soundness (`Know`, Ior/Know.lean) from B back to A, with extractor ext and errors `P.err`,
bounds on the counts of bad verifier messages.
A lookup claim `B : LkB` (Cb/Ld/LdLkp.lean) says that each of 2^v keys is an entry of a table of 2^d
entries, with the multiplicities written in bits; `B.Adm p` is its conditions on numbers
(`B.W ≤ 2 ^ B.w ∧ 2 ^ B.v < 2 ^ B.W ∧ 2 ^ B.d * (2 ^ B.W - 1) < p`).
Many statements of this library are written twice: a definition in the namespace `Spec` states a
proposition, and a theorem of the same name outside that namespace proves it (lean/GLOSSARY.md).

Why: the blocks of the lookup are stated at the base (`GoodAt`), each beside any joint that rides
along (at the base: between joints in which the tuple of messages is a part of the witness, before
the lift over a signature, Cb/Ld/LdSigLift.lean). In a chain, what rides along past one block is the
caller's joint R0, and the claims that wait or are done. All these claims are predicates on
(explicit part, entries m : J → E). So every joint of the chain has one form, `cj`.

Main names:
  `cj R0 msg pr Φ ΦR`: explicit part X; pr : X → St reads the caller's state; m = msg (tuple of
    messages). Exact (`rel`): R0 at pr x, and Φ x m. Relaxed (`relR`): R0 at pr x, and ΦR x m. The
    condition (`on`) is R0's at pr x; the core (`core`) is R0's.
  `ldLkpK_and`: a joint of this form, and one more claim, is a joint of this form.
  `ldLkpK_congr`: claims that say the same give the same joint.
  `ldLkpK_ride`: read at an older state (`PscIn.ride`, Cb/Ld/LdZero.lean, and the like), it is again
    of this form.
  `ldLkpK_lambda`: the first challenge at the base, for any tuple type and any B. Under `B.Adm p`, p
    the characteristic of E, the round in which the verifier draws λ from E is `GoodAt` from the
    joint (R0, `B.inR`) to the joint (R0, `B.mid`). `B.inR`: every key in the table, and `B.more`.
    `B.mid`: the claim after λ. The exact relations (`rel`) have `B.inP B.IsMult` and `B.midP` in
    their places: and the bits are the honest ones. One round, error 2^v - 1 (a bound on the count
    of bad values of λ among the elements of E; v is `B.v`).
  `ldLkpK_tree`: the tree's joint at level l (`jtAt`, Cb/Ld/LdLkpTreeP.lean), entered beside a joint
    of this form, is of this form: the claims with which it was entered, at the state with which it
    was entered; the rows of the levels below l; the sum claim of level l.

Limits: this file says nothing new on any block.
Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdLkp
import Cb.Ld.LdLkpProofs
import Cb.Ld.LdLkpTreeRows

set_option autoImplicit false

namespace Cb.LdLkp
open Iop IOR Hiop Prob

/-- A riding joint, and claims on the entries. -/
@[reducible] def cj {E Kc St M Wp J X : Type} {Ex : ExtSpec} (R0 : Rels Kc St Ex (M × Wp))
    (msg : M → J → E) (pr : X → St) (Φ ΦR : X → (J → E) → Prop) : Rels Kc X Ex (M × Wp) :=
  ⟨fun x y w => R0.rel (pr x) y w ∧ Φ x (msg w.1),
    fun a w => R0.relR (pr a.1, a.2) w ∧ ΦR a.1 (msg w.1),
    fun a => R0.on (pr a.1, a.2),
    R0.core⟩

end Cb.LdLkp

namespace Cb.Spec
open Iop IOR Hiop Prob Cb.LdLkp

def ldLkpK_and : Prop :=
  ∀ (E Kc St M Wp J X : Type) (Ex : ExtSpec) (R0 : Rels Kc St Ex (M × Wp)) (msg : M → J → E)
      (pr : X → St) (Φ ΦR Ψ ΨR : X → (J → E) → Prop),
    (⟨fun x y w => (cj R0 msg pr Φ ΦR).rel x y w ∧ Ψ x (msg w.1),
        fun a w => (cj R0 msg pr Φ ΦR).relR a w ∧ ΨR a.1 (msg w.1),
        (cj R0 msg pr Φ ΦR).on,
        (cj R0 msg pr Φ ΦR).core⟩ : Rels Kc X Ex (M × Wp)) =
      cj R0 msg pr (fun x m => Φ x m ∧ Ψ x m) fun x m => ΦR x m ∧ ΨR x m

def ldLkpK_congr : Prop :=
  ∀ (E Kc St M Wp J X : Type) (Ex : ExtSpec) (R0 : Rels Kc St Ex (M × Wp)) (msg : M → J → E)
      (pr : X → St) (Φ ΦR Φ' ΦR' : X → (J → E) → Prop),
    (∀ x m, Φ x m ↔ Φ' x m) → (∀ x m, ΦR x m ↔ ΦR' x m) → cj R0 msg pr Φ ΦR = cj R0 msg pr Φ' ΦR'

def ldLkpK_ride : Prop :=
  ∀ (E Kc St M Wp J X X' : Type) (Ex : ExtSpec) (R0 : Rels Kc St Ex (M × Wp)) (msg : M → J → E)
      (pr : X → St) (Φ ΦR : X → (J → E) → Prop) (old : X' → X),
    (⟨fun x y w => (cj R0 msg pr Φ ΦR).rel (old x) y w,
        fun a w => (cj R0 msg pr Φ ΦR).relR (old a.1, a.2) w,
        fun a => (cj R0 msg pr Φ ΦR).on (old a.1, a.2),
        (cj R0 msg pr Φ ΦR).core⟩ : Rels Kc X' Ex (M × Wp)) =
      cj R0 msg (fun x => pr (old x)) (fun x m => Φ (old x) m) fun x m => ΦR (old x) m

/-- The first challenge, at the base. -/
def ldLkpK_lambda : Prop :=
  ∀ (E : Type) [Field E] [Fintype E] (p : ℕ) [CharP E p] (Ex : ExtSpec) (Kc St M Wp J N : Type)
      (B : LkB E St (J → E) N) (R0 : Rels Kc St Ex (M × Wp)) (msg : M → J → E),
    B.Adm p →
    GoodAt (IOR.draw E Prod.mk Ex) (Honest.draw E Prod.mk Ex (M × Wp))
      (cj R0 msg id (B.inP B.IsMult) B.inR) (cj R0 msg Prod.fst B.midP B.mid) (fun _ _ _ wp => wp)
      (Nums.draw Kc E Prod.mk Ex (2 ^ B.v - 1))

/-- The tree's joint at level l. -/
def ldLkpK_tree : Prop :=
  ∀ (E : Type) [Field E] [Fintype E] (D : TreeP E) (Ex : ExtSpec) (Kc St M Wp : Type)
      (R0 : Rels Kc St Ex (M × Wp)) (msg : M → D.J → E) (pr : (D.lv 0).T.St → St)
      (Φ ΦR : (D.lv 0).T.St → (D.J → E) → Prop) (l : ℕ),
    D.jtAt msg (cj R0 msg pr Φ ΦR) l =
      cj R0 msg (fun x => pr (D.root l x.2))
        (fun x m =>
          (Φ (D.root l x.2) m ∧ RowsHold (D.rowsAt l x.2) m) ∧
          (D.lv l).T.SumHolds x fun j => m ((D.lv l).toJ j))
        (fun x m =>
          (ΦR (D.root l x.2) m ∧ RowsHold (D.rowsAt l x.2) m) ∧
          (D.lv l).T.SumHolds x fun j => m ((D.lv l).toJ j))

end Cb.Spec

namespace Cb
open Iop IOR Hiop Prob Cb.LdLkp

theorem ldLkpK_and : Spec.ldLkpK_and := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
  rels_ext (funext fun _ => funext fun _ => funext fun _ => propext and_assoc)
    (funext fun _ => funext fun _ => propext and_assoc) rfl rfl

theorem ldLkpK_congr : Spec.ldLkpK_congr := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h hR =>
  rels_ext (funext fun _ =>
      funext fun _ => funext fun _ => propext (and_congr_right fun _ => h _ _))
    (funext fun _ => funext fun _ => propext (and_congr_right fun _ => hR _ _)) rfl rfl

theorem ldLkpK_ride : Spec.ldLkpK_ride := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => rfl

theorem ldLkpK_lambda : Spec.ldLkpK_lambda := by
  intro E _ _ p _ Ex Kc St M Wp J N B R0 msg hA
  refine goodAt_draw Kc M St (St × E) Ex Wp E Prod.mk _ _ (2 ^ B.v - 1) ?_
    (fun _ _ _ h => h) (fun _ => rfl) ?_
  · intro st y w β h
    exact ⟨h.1, ldLkp_lambda_fwd E St (J → E) N B p st (msg w.1) β hA h.2⟩
  · intro st y m _
    refine (cnt_mono fun β hβ => ?_).trans (ldLkp_lambda_cnt E St (J → E) N p B st (msg m) hA)
    obtain ⟨wp, h1, h2⟩ := hβ
    exact ⟨h1.2, fun h => h2 ⟨h1.1, h⟩⟩

theorem ldLkpK_tree : Spec.ldLkpK_tree := by
  intro E _ _ D Ex Kc St M Wp R0 msg pr Φ ΦR l
  obtain ⟨h1, h2, h3, h4⟩ := ldLkpP_ride E D Ex M Wp Kc msg (cj R0 msg pr Φ ΦR) l
  refine rels_ext (funext fun x => funext fun y => funext fun w => propext ?_)
    (funext fun a => funext fun w => propext ?_) (funext fun a => propext (h3 a.1.2 a.2)) h4
  · show (D.ride msg (cj R0 msg pr Φ ΦR) l).rel x.2 y w ∧ _ ↔ _
    rw [h1]
    exact ⟨fun h => ⟨h.1.1.1, ⟨h.1.1.2, h.1.2⟩, h.2⟩, fun h => ⟨⟨⟨h.1, h.2.1.1⟩, h.2.1.2⟩, h.2.2⟩⟩
  · show (D.ride msg (cj R0 msg pr Φ ΦR) l).relR (a.1.2, a.2) w ∧ _ ↔ _
    rw [h2]
    exact ⟨fun h => ⟨h.1.1.1, ⟨h.1.1.2, h.1.2⟩, h.2⟩, fun h => ⟨⟨⟨h.1, h.2.1.1⟩, h.2.1.2⟩, h.2.2⟩⟩

end Cb
