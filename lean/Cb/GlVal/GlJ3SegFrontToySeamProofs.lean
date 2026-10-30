-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
In this library the records through which a count for agreement is claimed (`IsGlJ`, `IsGlS`:
Cb/Gl/GlLdJ.lean; `IsGlCpJ`: Cb/Gl/GlCopy.lean) do not ask a
radius within half the distance, and the fact on agreement, `Gl.AgreeJ`, is stated nowhere as a
separate theorem: it follows, by one application that is written down nowhere, from `Cb.BCHKS46At`
(`Cb.Gl.glAg_ofAt`, Cb/Gl/GlFinalAg.lean), which this library proves in Cb/Bridge (bchks46At), from
files adapted from ArkLib and Mathlib (lean/LIMITS.md,
L15), and applies in second forms of some of its theorems (files named `…Codes.lean` under
Johnson/; a bound on the entry file's closed check); this file
does not apply that proof.
So read the Lean text, not the words below, to see
what is a hypothesis here: neither "the statement on codes" nor "the fact on agreement" in these
words tells whether it is one.
A theorem with no premise rests on nothing unproved beyond Lean's three axioms (a theorem's premises
are the hypotheses in its statement; how the axioms are checked: lean/CHECKING.md). A theorem that
has the premise Gl.AgreeJ takes it as a hypothesis: this library states it nowhere as a separate
theorem (only its conclusion within half the distance: agreeHalf, Cb/Gl/GlAgreeHalf.lean). A
statement that has the premise Cb.BCHKS46, BCHKS46F or BCHKS46At takes it as a hypothesis; this file
does not prove it. Cb/Bridge/ proves BCHKS46 and BCHKS46At from the files under ThirdParty/,
which are adapted from ArkLib and Mathlib, and BCHKS46F follows from the first by one
line
(Cb.bchks46F_of_wide). Its
source: Theorem 4.6 of the full version (ePrint 2025/2055) of a paper published at STOC 2026; the
theorem is not in the proceedings, which state the plain form (their Theorem 1.5). Of a statement
with any other premise these lines say nothing: it rests on what that premise asks. (More on the
source, of which no full proof was checked for this library: the head of
Cb/Gen/CodeListRS.lean.) Cb/GlVal/GlJ3SegFrontToySeamProofs.lean: proof of
`Cb.GlJ3.Spec.ldSegFront_toySeam` and
`Cb.GlJ3.Spec.ldSegFront_toyRide` (Cb/GlVal/GlJ3SegFrontToySeam.lean).

Main names (statements and hypotheses: Cb/GlVal/GlJ3SegFrontToySeam.lean):
  `ldSegFront_toySeam`: the toy front's end and the stage of the toy body's step "read"
  `ldSegFront_toyRide`: the forms `sCo o j` at the entries `rAt r`

Conventions of this namespace's toys, said of the toys' own oracle messages and groups, not of what
a statement takes as a parameter (of the names declared in Cb/GlVal/ and Cb/Gl/GlField.lean this
file uses only the field E, the data of Cb/GlVal/GlJ3SegFrontToy.lean and
Cb/GlVal/GlJ3SegFrontToySeam.lean, the facts `a_ne_r`, `c_ne_r`, `z_ne_r`, `preOK`, `vOK`,
Cb/GlVal/GlJ3SegFrontToyProofs.lean, `datAt`, Cb/GlVal/GlJ3RefKit.lean, `RefToy.p`, `RefToy.Jn`,
Cb/GlVal/GlJ3SegRefToy.lean, `RefToy.Cc`, `RefToy.Gh`, `ldSegRef_toyAll`,
Cb/GlVal/GlJ3SegRefToyAll.lean, `Nm`, Cb/GlVal/GlToyLkpNames.lean, and `pK`,
Cb/GlVal/GlToyNum.lean):
the fields are F, the integers modulo 2^64 - 2^32 + 1, and E = F[x] / (x^3 - 2)
(Cb/Gl/GlField.lean). The toys' code is that of Cb/GlVal/GlToyBase4.lean: eight points, dimension 4,
distance 5, hides 3.
The radius, the bounds on lists, the counts for agreement and the pad's coefficient of these toys
are told in the head of Cb/GlVal/GlJ3Base.lean: read it before quoting.
This is not said of the offline side (configuration, index, lookup tables, weights-formedness).

Limits: what the head of Cb/GlVal/GlJ3SegFrontToySeam.lean lists as not said is not said here
either.

Terms: lean/GLOSSARY.md.
-/
import Cb.GlVal.GlToyNum
import Cb.GlVal.GlToyLkpNames
import Cb.GlVal.GlJ3Send
import Cb.GlVal.GlToyConfM
import Cb.GlVal.GlJ3PackNames
import Cb.GlVal.GlJ3SegFrontToySeam
import Cb.Ld.LdLkpAsm2PullProofs

set_option autoImplicit false

namespace Cb.GlJ3
open Cb.Gl hiding p
namespace FrontToy
open Iop Prob Hiop IOR Cb.Gl.LkpToy Cb.LdLkp Cb.Lkp Cb.Rng Cb.RngPk

/-! ### The real entries -/

theorem nr_inj : Function.Injective nr := by
  rintro (((a | a) | a) | a) (((b | b) | b) | b) h
    <;> simp only [nr, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq] at h <;> first
    | (subst h; rfl)
    | rfl

theorem allOf_nr (cell : Bool → E) (e : Nr → E) (n : Nr) : allOf cell e (nr n) = e n := by
  rcases n with ((a | a) | a) | a <;> rfl

/-- the real entries are those in the range of nr -/
def Gr : JJ → Prop := fun j => j ∈ Set.range nr

theorem gr_inr (x : X) : Gr (.inr x) := ⟨.inr x, rfl⟩
theorem gr_ι (n : Nm) : Gr (tι n) := by
  rcases n with ub | x
  · exact ⟨.inl (.inl (.inl ub)), rfl⟩
  · exact ⟨.inl (.inl (.inr x)), rfl⟩

/-- a form that is 0 at the keys: its value on all entries is its value on the real ones -/
theorem sum_real (c : JJ → E) (hc : SuppIn Gr c) (cell : Bool → E) (e : RefToy.Jn Nr → E) :
    ∑ n : RefToy.Jn Nr, (match n with | .inl n' => c (nr n') | .inr _ => 0) * e n =
      ∑ j, c j * allOf cell (fun n => e (.inl n)) j := by
  rw [Fintype.sum_sum_type]
  simp only [zero_mul, Finset.sum_const_zero, add_zero]
  rw [← ldLkpSupp_sum E JJ Nr nr nr_inj c hc (allOf cell fun n => e (.inl n))]
  exact Finset.sum_congr rfl fun n _ => by rw [allOf_nr]

/-- the real entries that do not ride -/
def Gq : JJ → Prop := fun j => Gr j ∧ ∀ r, j ≠ rAt r

theorem gq_ι (n : Nm) : Gq (tι n) := ⟨gr_ι n, fun _ => Sum.inl_ne_inr⟩
theorem gq_a (b : Fin 1 → Bool) : Gq (aAt b) := ⟨gr_inr _, a_ne_r b⟩
theorem gq_z (i : WZ ⊕ Unit) : Gq (zAt i) := ⟨gr_inr _, z_ne_r i⟩
theorem gq_c (i : WC ⊕ Unit) : Gq (FrontToy.cAt i) := ⟨gr_inr _, c_ne_r i⟩

theorem supp_cq (o : SSt) (j : SJc) : SuppIn Gq (sCo o j) := by
  rcases j with _ | i | _ | _ | _
  · exact supp_pushJ tι _ Gq fun n hn => absurd (gq_ι n) hn
  · exact supp_pushJ tι _ Gq fun n hn => absurd (gq_ι n) hn
  · exact supp_slU tBit.zc.next.par (inferInstanceAs (IsEmpty Empty)) (fun _ b => b.elim) o.st Gq
      (fun _ => gq_z _) fun _ _ => rfl
  · exact supp_slU tEnd.psc.par (inferInstanceAs (IsEmpty Empty)) (fun _ b => b.elim) o Gq
      (fun _ => gq_c _) fun j hj => if_neg fun e : j = zAt (.inr ()) => hj (e ▸ gq_z _)
  · exact supp_endRow tEnd Gq gq_a (gq_c _) o

theorem supp_co (o : SSt) (j : SJc) : SuppIn Gr (sCo o j) := fun i hi =>
  supp_cq o j i fun h => hi h.1

/-- No claim reads an entry that rides. -/
theorem co_ride (o : SSt) (j : SJc) (r : Ride) : sCo o j (rAt r) = 0 :=
  supp_cq o j (rAt r) fun h => h.2 r rfl

/-! ### The claims, one by one -/

section
variable (o : SSt) (ms : SS.Msg)

/-- the left side of a claim, but for constant and reads -/
theorem ms_sum (j : SJc) : ∑ n, sCl.ms o j n * datAt ms (.inr n) = ∑ i, sCo o j i * sAll ms i :=
  sum_real (sCo o j) (supp_co o j) (sCell ms) fun n => datAt ms (.inr n)

/-- a claim without a read -/
theorem plain_claim (j : Fin tA0.nRows ⊕ (Unit ⊕ (Unit ⊕ Unit))) (Y : RefToy.p.Cells) :
    (sCl.k0 o (.inr j) + ∑ k, ∑ c, sCl.cw o (.inr j) k c * readsOf (sW o) Y k c +
        ∑ n, sCl.ms o (.inr j) n * datAt ms (.inr n) =
      sCl.v o (.inr j)) ↔
    ∑ i, sCo o (.inr j) i * sAll ms i = sTg o (.inr j) := by
  rw [ms_sum]
  show (0 : E) + ∑ k : Unit, ∑ c : Unit, (0 : E) * readsOf (sW o) Y k c + _ = _ ↔ _
  simp only [zero_mul, Finset.sum_const_zero, zero_add]
  exact Iff.rfl

/-- the claim on the keys -/
theorem key_claim :
    (sCl.k0 o (.inl ()) +
        ∑ k, ∑ c, sCl.cw o (.inl ()) k c *
          readsOf (sW o) (cells RefToy.p.P (2 * RefToy.p.D) RefToy.p.rdx (sPk ms)) k c +
        ∑ n, sCl.ms o (.inl ()) n * datAt ms (.inr n) =
      sCl.v o (.inl ())) ↔
    (xL o).2.1.Holds tA.lk.v (tA.lk.key (xL o).1 (sAll ms)) (tA.entN tι (sAll ms)) := by
  rw [ms_sum]
  have e1 : ∑ i, sCo o (.inl ()) i * sAll ms i = ∑ n, (xL o).2.1.mf n * tA.entN tι (sAll ms) n :=
    ldLkpP_push E Nm JJ tι (xL o).2.1.mf (sAll ms)
  have e2 : Blocks.ext 1 (tA.lk.key (xL o).1 (sAll ms)) (xL o).2.1.pt =
      Blocks.ext 1 (fun _ => 5 + 1 * th o) (xL o).2.1.pt +
        ∑ k : Unit, ∑ c : Unit, (2 : E) *
          readsOf (sW o) (cells RefToy.p.P (2 * RefToy.p.D) RefToy.p.rdx (sPk ms)) k c := by
    unfold Blocks.ext readsOf
    simp only [Finset.univ_unique, Finset.sum_singleton, Fintype.sum_prod_type, Fin.sum_univ_two]
    rw [show (2 : ℕ) ^ 1 = 2 from rfl, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_zero, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
    show 0 + Blocks.eqN 1 0 (xL o).2.1.pt 0 * (5 + 2 * sCell ms false + 1 * th o) +
        Blocks.eqN 1 0 (xL o).2.1.pt 1 * (5 + 2 * sCell ms true + 1 * th o) =
      0 + Blocks.eqN 1 0 (xL o).2.1.pt 0 * (5 + 1 * th o) +
        Blocks.eqN 1 0 (xL o).2.1.pt 1 * (5 + 1 * th o) +
        2 * (Blocks.eqN 1 0 (xL o).2.1.pt 0 * sCell ms false +
            Blocks.eqN 1 0 (xL o).2.1.pt 1 * sCell ms true)
    ring
  show Blocks.ext 1 (fun _ => 5 + 1 * th o) (xL o).2.1.pt +
        ∑ k : Unit, ∑ c : Unit,
          (2 : E) * readsOf (sW o) (cells RefToy.p.P (2 * RefToy.p.D) RefToy.p.rdx (sPk ms)) k c +
        _ = (xL o).2.1.tg ↔
    Blocks.ext 1 (tA.lk.key (xL o).1 (sAll ms)) (xL o).2.1.pt +
        ∑ n, (xL o).2.1.mf n * tA.entN tι (sAll ms) n = (xL o).2.1.tg
  rw [e1, e2]

end

theorem meets : sMeets := by
  intro o ms
  have kR : ∀ i,
      (∑ j, sCo o (.inr (.inl i)) j * sAll ms j = sTg o (.inr (.inl i))) ↔
      ((xL o).2.2 i).Holds (tA.entN tι (sAll ms)) := fun i => by
    have e : ∑ j, sCo o (.inr (.inl i)) j * sAll ms j =
        ∑ n, ((xL o).2.2 i).cf n * tA.entN tι (sAll ms) n :=
      ldLkpP_push E Nm JJ tι ((xL o).2.2 i).cf (sAll ms)
    rw [e]
    exact Iff.rfl
  have kU : (∑ j, sCo o (.inr (.inr (.inl ()))) j * sAll ms j = sTg o (.inr (.inr (.inl ())))) ↔
      tBit.zc.next.par.UHolds o.st (sAll ms) :=
    (psc_row_U E tBit.zc.next.par (fun _ b => b.elim) (fun _ _ b _ => b.elim) o.st (sAll ms)).symm
  have kE := ldLkpEnd_rows E tEnd o (sAll ms)
  constructor
  · intro h
    refine ⟨⟨(key_claim o ms).1 (h (.inl ())),
        fun i => (kR i).1 ((plain_claim o ms (.inl i) _).1 (h (.inr (.inl i)))),
        trivial⟩,
      kU.1 ((plain_claim o ms (.inr (.inl ())) _).1 (h (.inr (.inr (.inl ()))))),
      ?_⟩
    exact kE.2
      ⟨(plain_claim o ms (.inr (.inr (.inl ()))) _).1 (h (.inr (.inr (.inr (.inl ()))))),
        (plain_claim o ms (.inr (.inr (.inr ()))) _).1 (h (.inr (.inr (.inr (.inr ())))))⟩
  · rintro ⟨⟨h1, h2, _⟩, h3, h4⟩ (⟨⟩ | i | ⟨⟩ | ⟨⟩ | ⟨⟩)
    · exact (key_claim o ms).2 h1
    · exact (plain_claim o ms (.inl i) _).2 ((kR i).2 (h2 i))
    · exact (plain_claim o ms (.inr (.inl ())) _).2 (kU.2 h3)
    · exact (plain_claim o ms (.inr (.inr (.inl ()))) _).2 (kE.1 h4).1
    · exact (plain_claim o ms (.inr (.inr (.inr ()))) _).2 (kE.1 h4).2

theorem sOK : sV.OK pK where
  pre := preOK RefToy.Gh SS RefToy.Cc.E0 SWp sAll sRx
  link := ldZero_link E tBit.zc
  back := ldZero_back E tBit.zc
  ev := ldZero_ok E tBit.zc (ldZero_ok_one E)
  psc0 := (vOK RefToy.Gh SS RefToy.Cc.E0 SWp sAll sRx).psc0
  psc := (vOK RefToy.Gh SS RefToy.Cc.E0 SWp sAll sRx).psc
  step0 := (vOK RefToy.Gh SS RefToy.Cc.E0 SWp sAll sRx).step0
  step := fun i hi => absurd hi (Nat.not_lt_zero i)
  post :=
    ⟨fun o _ w h => ⟨h.1.1.1.1, (meets o w.1).2 ⟨h.1.1.2, h.1.2, h.2⟩, h.1.1.1.2⟩,
      fun _ _ h => h, fun _ => rfl,
      fun o _ w _ h =>
        ⟨⟨⟨⟨h.1, h.2.2⟩, ((meets o w.1).1 h.2.1).1⟩, ((meets o w.1).1 h.2.1).2.1⟩,
          ((meets o w.1).1 h.2.1).2.2⟩⟩

end FrontToy

open FrontToy in
theorem ldSegFront_toySeam : Spec.ldSegFront_toySeam :=
  ⟨meets, sOK, ((ldSegRef_toyAll sP sV).2.2.2 sOK).1, ((ldSegRef_toyAll sP sV).2.2.2 sOK).2⟩

theorem ldSegFront_toyRide : Spec.ldSegFront_toyRide := FrontToy.co_ride

end Cb.GlJ3
