-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Req1/LdSegAfterRows.lean: under `D.Lin` and whatever the arguments hold as proofs, what is
claimed after the locations of a closing, of the messages (`D.After`), is a family of linear rows,
with public targets, on the entries of the oracle messages that are left.

Definitions, statement (`Cb.Spec.ldLoc_after_rows`) and proof.

Why: where a preamble ends with a closing, the closing's last step, the locations, is the query
phase of a proximity test (the verifier draws positions of the open word; it rejects nothing)
(`LdLocD`, `D.After`: Cb/Req1/LdSegKit.lean); and some tests take what is left as rows on all
entries of a family (`Slf.All`, Cb/Ld/LdBat.lean; "more", Cb/Obj/LdObjectLinStd2.lean). This file
joins the two. A row is a linear equation: the sum of coefficient times entry is the target
(`Slf.Holds`, Cb/Ld/LdRel.lean).
`D.After x m` says three things of the messages m: (1) the claim Φ on the open word's message; (2)
the old samples' answers on the slots of the messages held in the open word; (3) the long symbols
read at the locations are those of the encoding of (message, randomness). All three read m through
`D.cut m` = (message, randomness) of the open word.

Main names:
  `D.Lin pJ pQ φ xφ`: the hypothesis. cut reads entries: the coordinate j of the open word's message
    is the entry pJ j of the messages, the coordinate q of its randomness the entry pQ q. Φ is a
    linear row: Φ xc u ⇔ ⟨φ(state of xc), u⟩ = target of xc. The open word's code has its laws (so
    its encoding, read under the transformation, is linear).
  `D.rowsOf pJ pQ φ xφ x`: the rows: targets and coefficient vectors on `D.S.Ent`; the state of a
    row is its coefficient vector (`Slf.idf`). Their names, `D.RowN`: one for the claim; one for
    each answer of each held message's sample; one for each coordinate of each long symbol read: the
    generator's row behind it (`C.row`, Cb/Ld/LdRel.lean).
  `Spec.ldLoc_after_rows`: under `D.Lin pJ pQ φ xφ` and whatever the arguments hold as proofs:
    D.After x m ⇔ Slf.All (fun _ => Slf.idf) (D.rowsOf .. x) (D.S.ents m). Targets and coefficients
    are public: functions of x (the claim's explicit part, the old samples, the locations and the
    symbols read).

Limits: this file does not say that a given cut reads entries (for a cut by places: by definition).
It says nothing on any protocol, and nothing on the number of positions that a later test may read
of these messages.

Terms: lean/GLOSSARY.md.
-/
import Cb.Req1.LdSegKit
import Cb.Ld.LdRelProofsCode
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

open Classical in
/-- coefficients on I, carried to J along p -/
def pushTo {E I J : Type} [AddCommMonoid E] [Fintype I] (p : I → J) (c : I → E) :
    J → E :=
  fun n => ∑ i, if p i = n then c i else 0

namespace LdLocD
variable {E Kc : Type} [Field E] [Fintype E] (D : LdLocD E Kc)

/-- the names of the rows -/
abbrev RowN : Type := Unit ⊕ (Σ k, (D.hd.o k).Z.S) ⊕ (Fin D.t × D.C.Aa)

variable {Xφ : Type} (pJ : D.C.J → D.S.Ent) (pQ : D.C.Q → D.S.Ent)
  (φ : Slf E Xφ D.C.J) (xφ : D.Xc → E × Xφ)

/-- What is asked. -/
structure Lin : Prop where
  cutJ : ∀ m j, (D.cut m).1 j = D.S.ents m (pJ j)
  cutQ : ∀ m q, (D.cut m).2 q = D.S.ents m (pQ q)
  form : ∀ xc u, D.Φ xc u ↔ φ.Holds (xφ xc) u
  laws : D.C.Laws

/-- The rows: targets, coefficient vectors. -/
def rowsOf (x : (D.Xc × D.hd.Smp) × D.Lc) : (D.RowN → E) × (D.RowN → D.S.Ent → E) :=
  (fun b => match b with
    | .inl _ => (xφ x.1.1).1
    | .inr (.inl ks) => (x.1.2 ks.1).2 ks.2
    | .inr (.inr iα) => x.2.2 iα.1 iα.2,
   fun b => match b with
    | .inl _ => pushTo pJ (φ (xφ x.1.1).2)
    | .inr (.inl ks) =>
      pushTo (fun j => pJ (D.hd.sJ ks.1 j)) ((D.hd.o ks.1).Z.mat (x.1.2 ks.1).1 ks.2)
    | .inr (.inr iα) =>
      fun n =>
        pushTo pJ (fun j => D.C.row (x.2.1 iα.1) iα.2 (.inl j)) n +
          pushTo pQ (fun q => D.C.row (x.2.1 iα.1) iα.2 (.inr q)) n)

end LdLocD

namespace Spec

def ldLoc_after_rows : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (D : LdLocD E Kc) (Xφ : Type) (pJ : D.C.J → D.S.Ent)
      (pQ : D.C.Q → D.S.Ent) (φ : Slf E Xφ D.C.J) (xφ : D.Xc → E × Xφ),
    D.Lin pJ pQ φ xφ →
    ∀ (x : (D.Xc × D.hd.Smp) × D.Lc) (m : D.S.Msg),
      D.After x m ↔
      Slf.All (fun _ : D.RowN => (Slf.idf : Slf E (D.S.Ent → E) D.S.Ent))
        (D.rowsOf pJ pQ φ xφ x) (D.S.ents m)

end Spec

theorem pushTo_sum {E I J : Type} [Field E] [Fintype I] [Fintype J] (p : I → J)
    (c : I → E) (v : J → E) :
    ∑ n, pushTo p c n * v n = ∑ i, c i * v (p i) := by
  classical
  unfold pushTo
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem ldLoc_after_rows : Spec.ldLoc_after_rows := by
  intro E Kc _ _ D Xφ pJ pQ φ xφ h x m
  have r1 : D.Φ x.1.1 (D.cut m).1 ↔
      ∑ n, pushTo pJ (φ (xφ x.1.1).2) n * D.S.ents m n = (xφ x.1.1).1 := by
    rw [h.form, pushTo_sum]
    show ∑ j, φ (xφ x.1.1).2 j * (D.cut m).1 j = _ ↔ _
    simp only [h.cutJ]
  have r2 : ∀ (k : D.hd.K) (s : (D.hd.o k).Z.S),
      (D.hd.o k).Z.val (x.1.2 k).1 (D.hd.msg (D.cut m).1 k) s =
        ∑ n,
          pushTo (fun j => pJ (D.hd.sJ k j)) ((D.hd.o k).Z.mat (x.1.2 k).1 s) n * D.S.ents m n := by
    intro k s
    rw [pushTo_sum]
    show ∑ j, (D.hd.o k).Z.mat (x.1.2 k).1 s j * (D.cut m).1 (D.hd.sJ k j) = _
    simp only [h.cutJ]
  have r3 : ∀ (i : Fin D.t) (α : D.C.Aa), D.C.T (D.C.enc (D.cut m).1 (D.cut m).2) (x.2.1 i) α =
      ∑ n, (pushTo pJ (fun j => D.C.row (x.2.1 i) α (.inl j)) n +
          pushTo pQ (fun q => D.C.row (x.2.1 i) α (.inr q)) n) *
        D.S.ents m n := by
    intro i α
    rw [ld_row_spec E D.P D.C h.laws]
    simp only [add_mul, Finset.sum_add_distrib, pushTo_sum, h.cutJ, h.cutQ]
  constructor
  · rintro ⟨h1, h2, h3⟩ b
    rcases b with _ | ⟨k, s⟩ | ⟨i, α⟩
    · exact r1.1 h1
    · exact (r2 k s).symm.trans (congrFun (h2 k) s)
    · exact (r3 i α).symm.trans (congrFun (congrFun h3 i) α)
  · intro hb
    refine ⟨r1.2 (hb (.inl ())),
      fun k => funext fun s => (r2 k s).trans (hb (.inr (.inl ⟨k, s⟩))),
      funext fun i => funext fun α => (r3 i α).trans (hb (.inr (.inr (i, α))))⟩

end Cb
