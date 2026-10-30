-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLkpAsmMore.lean: the assembled lookup: its condition on the multiplicities discharged, and
the number of its rows.

Definitions, statements (in `Cb.Spec`) and proofs. It adds to Cb/Ld/LdLkpAsm.lean, which has the
data `LkAsm`.
The lookup is the sub-protocol for the claim that every key is an entry of a table (`Lk.inR`,
Cb/Ld/LdLkp.lean). Its theorem (`ldLkpAsm_ok`, Cb/Ld/LdLkpAsm.lean) takes a predicate Mu on the
prover's multiplicities as a parameter, under one condition. This file shows that one such
predicate, `A.ValidMu`, meets the condition if n + 1 ≤ 2^w, applies the theorem to it and to a
second one (`A.H.lkb.IsMult`; under `A.H.lkb.Adm p` it meets the condition by `ldLkpHead_muOK`,
Cb/Ld/LdLkpHead.lean), and counts the rows, linear claims on the entries, that the lookup leaves.

Main names:
  `A.ValidMu`: "the vector is the multiplicities", wide form (`Valid`, Cb/Ld/LdLkpMult.lean): all
    are bits; 0 at the idle positions; for every value the multiplicities of the table entries with
    that value add up to the number of keys with that value. (Tables with repeated entries; a joint
    table after a random shift.)
  `ldLkpAsm_muValid`: it meets the one condition `H.MuOK` of the lookup's head (`LkHead`,
    Cb/Ld/LdLkpHead.lean), if n + 1 ≤ 2^w.
  `ldLkpAsm_ok_valid`, `ldLkpAsm_ok_first`: so the assembled lookup meets the interface (`SubR.OK`,
    Cb/Ld/LdLkp.lean) under conditions on numbers only (`A.H.lkb.Adm p`, p the characteristic of E):
    with the wide form; with the bits of "the number of keys equal to this entry and to no earlier
    one".
  `A.nRows`: the number of rows: 1 + (n + 1) + (v' + 1) + (4 + d): the row on the number of keys
    (`A.numRow`); the tie's steps; the keys' levels; bit test and closing, two each; the forest's
    levels.
  `ldLkpAsm_len`: the read-out always lists that many rows.
  `ldLkpAsm_out_len`, `ldLkpAsm_sub_len`: a fact on the verifier alone, at all transcripts: every
    explicit part that it puts out lists that many rows; at the base (see Cb/Ld/LdLkpFormat.lean),
    and over a signature. (So a step from the list to a family over a fixed finite type can be
    written.)
Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdLkpAsmProofs
import Cb.Ld.LdLkpMultProofs

set_option autoImplicit false

namespace Cb.LdLkp
open Iop IOR Hiop Prob Cb.Lkp

namespace LkAsm
variable {E : Type} [Field E] [Fintype E] (A : LkAsm E)

/-- The vector is the multiplicities, wide form. -/
def ValidMu : A.St → (A.J → E) → Prop := fun st m =>
  Valid (A.v' + 1) A.d A.w (A.n + 1) (A.key st m) (A.tab st) (A.H.bit m)

/-- The number of rows. -/
def nRows : ℕ := 1 + ((A.n + 1) + ((A.v' + 1) + (4 + A.d)))

end LkAsm
end Cb.LdLkp

namespace Cb.Spec
open Iop IOR Hiop Prob Cb.LdLkp Cb.Lkp

section
variable (E : Type) [Field E] [Fintype E]

def ldLkpAsm_muValid : Prop := ∀ A : LkAsm E, A.n + 1 ≤ 2 ^ A.w → A.H.MuOK A.ValidMu

def ldLkpAsm_ok_valid : Prop :=
  ∀ (p : ℕ) [CharP E p] (A : LkAsm E) (S : Sig E) (E₀ : ExtSpec) (Kc Wp : Type)
      (R0 : Rels Kc A.St E₀ (S.Msg × Wp)) (msg : S.Msg → A.J → E),
    A.H.lkb.Adm p →
    (A.sub S E₀ Kc Wp msg).OK
      ⟨A.v' + 1, A.d, fun st ym => A.key st (msg ym.2), A.tab, fun _ _ => True⟩
      (fun st ym => A.ValidMu st (msg ym.2)) R0 fun ym => msg ym.2

def ldLkpAsm_ok_first : Prop :=
  ∀ (p : ℕ) [CharP E p] (A : LkAsm E) (S : Sig E) (E₀ : ExtSpec) (Kc Wp : Type)
      (R0 : Rels Kc A.St E₀ (S.Msg × Wp)) (msg : S.Msg → A.J → E),
    A.H.lkb.Adm p →
    (A.sub S E₀ Kc Wp msg).OK
      ⟨A.v' + 1, A.d, fun st ym => A.key st (msg ym.2), A.tab, fun _ _ => True⟩
      (fun st ym => A.H.lkb.IsMult st (msg ym.2)) R0 fun ym => msg ym.2

def ldLkpAsm_len : Prop := ∀ (A : LkAsm E) (o : A.Q.XB), (A.rd o).2.2.length = A.nRows

def ldLkpAsm_out_len : Prop :=
  ∀ (A : LkAsm E) (Ex : ExtSpec) (M Wp Kc : Type) (msg : M → A.J → E) x y τ xo,
    (A.baseA Ex M Wp Kc msg).R.out x y τ = some xo → xo.2.2.length = A.nRows

def ldLkpAsm_sub_len : Prop :=
  ∀ (A : LkAsm E) (S : Sig E) (E₀ : ExtSpec) (Kc Wp : Type) (msg : S.Msg → A.J → E) x y τ xo,
    (A.sub S E₀ Kc Wp msg).R.out x y τ = some xo → xo.1.2.2.length = A.nRows

end
end Cb.Spec

namespace Cb
open Iop IOR Hiop Prob Cb.LdLkp Cb.Lkp

section
variable (E : Type) [Field E] [Fintype E]

theorem ldLkpAsm_muValid : Spec.ldLkpAsm_muValid E := fun A hW st m hin hv lam =>
  ⟨⟨ldLkpMult_mid E (A.v' + 1) A.d A.w (A.n + 1) (A.key st m) (A.tab st)
        (A.H.bit m) hW hin.1 hv lam,
      trivial⟩,
    fun j hj hjw =>
      ldLkpMult_idle E (A.v' + 1) A.d A.w (A.n + 1) (A.key st m) (A.tab st)
        (A.H.bit m) hv lam j hj hjw⟩

theorem ldLkpAsm_ok_valid : Spec.ldLkpAsm_ok_valid E := fun p _ A S E₀ Kc Wp R0 msg hA =>
  ldLkpAsm_ok E p A A.ValidMu S E₀ Kc Wp R0 msg hA (ldLkpAsm_muValid E A hA.1)

theorem ldLkpAsm_ok_first : Spec.ldLkpAsm_ok_first E := fun p _ A S E₀ Kc Wp R0 msg hA =>
  ldLkpAsm_ok E p A A.H.lkb.IsMult S E₀ Kc Wp R0 msg hA (ldLkpHead_muOK E p A.H hA)

/-- An auxiliary lemma: the lengths of the lists of rows. -/
theorem LdLkp.TreeP.rowsAt_len (D : TreeP E) :
    ∀ (l : ℕ) (s : (D.lv l).T.St), (D.rowsAt l s).length = l
  | 0, _ => rfl
  | l + 1, s => congrArg (· + 1) (rowsAt_len D l s.1.st)

theorem LdLkp.TieP.rowsAt_len (D : TieP E) :
    ∀ (l : ℕ) (s : (D.lv l).T.St), (D.rowsAt l s).length = l
  | 0, _ => rfl
  | l + 1, s => congrArg (· + 1) (rowsAt_len D l s.st)

theorem ldLkpAsm_len : Spec.ldLkpAsm_len E := by
  intro A o
  show (A.numRow :: (A.rows2 (A.o4 (A.Q.oldT o)) ++ (A.rows4 (A.Q.oldT o) ++ A.rowsB o))).length =
    A.nRows
  have h2 : (A.rows2 (A.o4 (A.Q.oldT o))).length = A.n + 1 := A.H.tie.rowsAt_len E (A.n + 1) _
  have h4 : (A.rows4 (A.Q.oldT o)).length = A.v' + 1 :=
    (A.IK.setV (A.v' + 1)).DK.rowsAt_len E (A.v' + 1) _
  have hB : (A.rowsB o).length = 4 + A.d := by
    show (A.Q.D.rowsAt A.Q.I.d (A.Q.outE o).st).length + 1 + 1 + 1 + 1 = 4 + A.d
    rw [A.Q.D.rowsAt_len E A.Q.I.d _]
    show A.d + 1 + 1 + 1 + 1 = 4 + A.d
    omega
  rw [List.length_cons, List.length_append, List.length_append, h2, h4, hB]
  unfold LkAsm.nRows
  omega

theorem ldLkpAsm_out_len : Spec.ldLkpAsm_out_len E := by
  intro A Ex M Wp Kc msg x y τ xo h
  obtain ⟨o, _, ho⟩ := Option.bind_eq_some_iff.mp h
  rw [← Option.some.inj ho]
  exact ldLkpAsm_len E A o

theorem ldLkpAsm_sub_len : Spec.ldLkpAsm_sub_len E := by
  intro A S E₀ Kc Wp msg x y τ xo h
  obtain ⟨x', hx', rfl⟩ := Option.map_eq_some_iff.mp h
  exact ldLkpAsm_out_len E A E₀ S.Msg Wp Kc msg _ _ _ _ hx'

end
end Cb
