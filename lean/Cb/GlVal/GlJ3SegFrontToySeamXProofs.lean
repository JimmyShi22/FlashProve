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
Cb/Gen/CodeListRS.lean.) Cb/GlVal/GlJ3SegFrontToySeamXProofs.lean: proof of
`Cb.GlJ3.Spec.ldSegFront_toySeamX`
(Cb/GlVal/GlJ3SegFrontToySeamX.lean), as in Cb/GlVal/GlJ3SegFrontToySeamProofs.lean.

Main names (statement and hypotheses: Cb/GlVal/GlJ3SegFrontToySeamX.lean):
  `ldSegFront_toySeamX`: the end of the toy front with a state that rides, and the stage at which
    the toy body's step "read" begins

Conventions of this namespace's toys, said of the toys' own oracle messages and groups, not of what
a statement takes as a parameter (of the names declared in Cb/GlVal/ and Cb/Gl/GlField.lean this
file uses only the field E, the data of Cb/GlVal/GlJ3SegFrontToy.lean,
Cb/GlVal/GlJ3SegFrontToyX.lean, Cb/GlVal/GlJ3SegFrontToySeam.lean,
Cb/GlVal/GlJ3SegFrontToySeamS.lean and Cb/GlVal/GlJ3SegFrontToySeamX.lean, the facts `inc_off`,
`preOK`, `vOK`, Cb/GlVal/GlJ3SegFrontToyXProofs.lean, and `Gq`, `Gr`, `gq_a`, `gq_c`, `gq_z`,
`gq_ι`, `sum_real`, Cb/GlVal/GlJ3SegFrontToySeamProofs.lean, `RefToy.p`, `RefToy.So`,
Cb/GlVal/GlJ3SegRefToy.lean, `RefToy.Cc`, `RefToy.Gh`, Cb/GlVal/GlJ3SegRefToyAll.lean,
`ldSegRef_toyAllS`, Cb/GlVal/GlJ3SegRefToyAllS.lean, `Nm`, Cb/GlVal/GlToyLkpNames.lean, and `pK`,
Cb/GlVal/GlToyNum.lean; Sx, S, `at'`, W₁, `w₁0`, `rc`, `rel0`, `relR0`, `on0` are parameters):
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
import Cb.GlVal.GlJ3SegFrontToySeamX
import Cb.Ld.LdLkpAsm2PullProofs

set_option autoImplicit false

namespace Cb.GlJ3
open Cb.Gl hiding p
namespace FrontToyX
open Iop Prob Hiop IOR Cb.Gl.LkpToy Cb.LdLkp Cb.Lkp Cb.Rng Cb.RngPk
open FrontToy
  (WZ WC Ride X JJ eL aAt zAt cAt rAt tA0 tι tDt tRdK tRd0 tRd1 Nr nr allOf SJc Gr Gq gq_ι
    gq_a gq_z gq_c sum_real)
open FrontToyS (sPk sCell sAll)

variable {Sx : Type}

theorem supp_cq (o : SSt Sx) (j : SJc) : SuppIn Gq (sCo o j) := by
  rcases j with _ | i | _ | _ | _
  · exact supp_pushJ tι _ Gq fun n hn => absurd (gq_ι n) hn
  · exact supp_pushJ tι _ Gq fun n hn => absurd (gq_ι n) hn
  · exact supp_slU (tBit Sx).zc.next.par (inferInstanceAs (IsEmpty Empty)) (fun _ b => b.elim)
      o.st Gq (fun _ => gq_z _) fun _ _ => rfl
  · exact supp_slU (tEnd Sx).psc.par (inferInstanceAs (IsEmpty Empty)) (fun _ b => b.elim) o Gq
      (fun _ => gq_c _) fun j hj => inc_off Sx _ j fun e => hj (e ▸ gq_z _)
  · exact supp_endRow (tEnd Sx) Gq gq_a (gq_c _) o

theorem supp_co (o : SSt Sx) (j : SJc) : SuppIn Gr (sCo o j) := fun i hi =>
  supp_cq o j i fun h => hi h.1

theorem co_ride (o : SSt Sx) (j : SJc) (r : Ride) : sCo o j (rAt r) = 0 :=
  supp_cq o j (rAt r) fun h => h.2 r rfl

section
variable (S : Sig E) (at' : RefToy.So Nr → S.Ent) (o : SSt Sx) (ms : S.Msg)

theorem ms_sum (j : SJc) :
    ∑ n, (sClX Sx).ms o j n * S.ents ms (at' (.inr n)) = ∑ i, sCo o j i * sAll S at' ms i :=
  sum_real (sCo o j) (supp_co o j) (sCell S at' ms) fun n => S.ents ms (at' (.inr n))

theorem plain_claim (j : Fin tA0.nRows ⊕ (Unit ⊕ (Unit ⊕ Unit))) (Y : RefToy.p.Cells) :
    ((sClX Sx).k0 o (.inr j) + ∑ k, ∑ c, (sClX Sx).cw o (.inr j) k c * readsOf (sW Sx o) Y k c +
        ∑ n, (sClX Sx).ms o (.inr j) n * S.ents ms (at' (.inr n)) =
      (sClX Sx).v o (.inr j)) ↔
    ∑ i, sCo o (.inr j) i * sAll S at' ms i = sTg o (.inr j) := by
  rw [ms_sum]
  show (0 : E) + ∑ k : Unit, ∑ c : Unit, (0 : E) * readsOf (sW Sx o) Y k c + _ = _ ↔ _
  simp only [zero_mul, Finset.sum_const_zero, zero_add]
  exact Iff.rfl

theorem key_claim :
    ((sClX Sx).k0 o (.inl ()) +
        ∑ k, ∑ c, (sClX Sx).cw o (.inl ()) k c *
          readsOf (sW Sx o) (cells RefToy.p.P (2 * RefToy.p.D) RefToy.p.rdx (sPk S at' ms)) k c +
        ∑ n, (sClX Sx).ms o (.inl ()) n * S.ents ms (at' (.inr n)) =
      (sClX Sx).v o (.inl ())) ↔
    (xL o).2.1.Holds (tA Sx).lk.v ((tA Sx).lk.key (xL o).1 (sAll S at' ms))
      ((tA Sx).entN tι (sAll S at' ms)) := by
  rw [ms_sum]
  have e1 : ∑ i, sCo o (.inl ()) i * sAll S at' ms i =
      ∑ n, (xL o).2.1.mf n * (tA Sx).entN tι (sAll S at' ms) n :=
    ldLkpP_push E Nm JJ tι (xL o).2.1.mf (sAll S at' ms)
  have e2 : Blocks.ext 1 ((tA Sx).lk.key (xL o).1 (sAll S at' ms)) (xL o).2.1.pt =
      Blocks.ext 1 (fun _ => 5 + 1 * th o) (xL o).2.1.pt +
        ∑ k : Unit, ∑ c : Unit, (2 : E) *
          readsOf (sW Sx o)
            (cells RefToy.p.P (2 * RefToy.p.D) RefToy.p.rdx (sPk S at' ms)) k c := by
    unfold Blocks.ext readsOf
    simp only [Finset.univ_unique, Finset.sum_singleton, Fintype.sum_prod_type, Fin.sum_univ_two]
    rw [show (2 : ℕ) ^ 1 = 2 from rfl, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_zero, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
    show 0 + Blocks.eqN 1 0 (xL o).2.1.pt 0 * (5 + 2 * sCell S at' ms false + 1 * th o) +
        Blocks.eqN 1 0 (xL o).2.1.pt 1 * (5 + 2 * sCell S at' ms true + 1 * th o) =
      0 + Blocks.eqN 1 0 (xL o).2.1.pt 0 * (5 + 1 * th o) +
        Blocks.eqN 1 0 (xL o).2.1.pt 1 * (5 + 1 * th o) +
        2 * (Blocks.eqN 1 0 (xL o).2.1.pt 0 * sCell S at' ms false +
            Blocks.eqN 1 0 (xL o).2.1.pt 1 * sCell S at' ms true)
    ring
  show Blocks.ext 1 (fun _ => 5 + 1 * th o) (xL o).2.1.pt +
        ∑ k : Unit, ∑ c : Unit, (2 : E) *
          readsOf (sW Sx o) (cells RefToy.p.P (2 * RefToy.p.D) RefToy.p.rdx (sPk S at' ms)) k c +
        _ = (xL o).2.1.tg ↔
    Blocks.ext 1 ((tA Sx).lk.key (xL o).1 (sAll S at' ms)) (xL o).2.1.pt +
        ∑ n, (xL o).2.1.mf n * (tA Sx).entN tι (sAll S at' ms) n = (xL o).2.1.tg
  rw [e1, e2]

end

variable (Sx) (S : Sig E) (at' : RefToy.So Nr → S.Ent)

theorem meets : sMeets Sx S at' := by
  intro o ms
  have kR : ∀ i,
      (∑ j, sCo o (.inr (.inl i)) j * sAll S at' ms j = sTg o (.inr (.inl i))) ↔
      ((xL o).2.2 i).Holds ((tA Sx).entN tι (sAll S at' ms)) := fun i => by
    have e : ∑ j, sCo o (.inr (.inl i)) j * sAll S at' ms j =
        ∑ n, ((xL o).2.2 i).cf n * (tA Sx).entN tι (sAll S at' ms) n :=
      ldLkpP_push E Nm JJ tι ((xL o).2.2 i).cf (sAll S at' ms)
    rw [e]
    exact Iff.rfl
  have kU : (∑ j, sCo o (.inr (.inr (.inl ()))) j * sAll S at' ms j =
        sTg o (.inr (.inr (.inl ())))) ↔
      (tBit Sx).zc.next.par.UHolds o.st (sAll S at' ms) :=
    (psc_row_U E (tBit Sx).zc.next.par (fun _ b => b.elim) (fun _ _ b _ => b.elim)
      o.st (sAll S at' ms)).symm
  have kE := ldLkpEnd_rows E (tEnd Sx) o (sAll S at' ms)
  constructor
  · intro h
    refine ⟨⟨(key_claim S at' o ms).1 (h (.inl ())),
        fun i => (kR i).1 ((plain_claim S at' o ms (.inl i) _).1 (h (.inr (.inl i)))),
        trivial⟩,
      kU.1 ((plain_claim S at' o ms (.inr (.inl ())) _).1 (h (.inr (.inr (.inl ()))))),
      ?_⟩
    exact kE.2
      ⟨(plain_claim S at' o ms (.inr (.inr (.inl ()))) _).1 (h (.inr (.inr (.inr (.inl ()))))),
        (plain_claim S at' o ms (.inr (.inr (.inr ()))) _).1 (h (.inr (.inr (.inr (.inr ())))))⟩
  · rintro ⟨⟨h1, h2, _⟩, h3, h4⟩ (⟨⟩ | i | ⟨⟩ | ⟨⟩ | ⟨⟩)
    · exact (key_claim S at' o ms).2 h1
    · exact (plain_claim S at' o ms (.inl i) _).2 ((kR i).2 (h2 i))
    · exact (plain_claim S at' o ms (.inr (.inl ())) _).2 (kU.2 h3)
    · exact (plain_claim S at' o ms (.inr (.inr (.inl ()))) _).2 (kE.1 h4).1
    · exact (plain_claim S at' o ms (.inr (.inr (.inr ()))) _).2 (kE.1 h4).2

variable (hat : Function.Injective at') (W₁ : Type) (w₁0 : W₁) (rc : Sx → RefToy.Cc.Rec)
  (rel0 : Sx → RefToy.Cc.E0.Str → (RefToy.Cc.Msg × S.Msg) × (W₁ × RefToy.Gh) → Prop)
  (relR0 : Sx × RefToy.Cc.E0.Str → (RefToy.Cc.Msg × S.Msg) × (W₁ × RefToy.Gh) → Prop)
  (on0 : Sx × RefToy.Cc.E0.Str → Prop)

theorem sOK : (sV Sx S at' hat W₁ w₁0 rc rel0 relR0 on0).OK pK where
  pre := preOK Sx RefToy.Gh S RefToy.Cc.E0 (SWp W₁) (sAll S at') (sRx Sx S at' W₁ rc rel0 relR0 on0)
  link := ldZero_link E (tBit Sx).zc
  back := ldZero_back E (tBit Sx).zc
  ev := ldZero_ok E (tBit Sx).zc (ldZero_ok_one E)
  psc0 :=
    (vOK Sx RefToy.Gh S RefToy.Cc.E0 (SWp W₁) (sAll S at') (sRx Sx S at' W₁ rc rel0 relR0 on0)).psc0
  psc :=
    (vOK Sx RefToy.Gh S RefToy.Cc.E0 (SWp W₁) (sAll S at') (sRx Sx S at' W₁ rc rel0 relR0 on0)).psc
  step0 := (vOK Sx RefToy.Gh S RefToy.Cc.E0 (SWp W₁) (sAll S at')
    (sRx Sx S at' W₁ rc rel0 relR0 on0)).step0
  step := fun i hi => absurd hi (Nat.not_lt_zero i)
  post :=
    ⟨fun o _ w h => ⟨h.1.1.1.1, (meets Sx S at' o w.1).2 ⟨h.1.1.2, h.1.2, h.2⟩, h.1.1.1.2⟩,
      fun _ _ h => h, fun _ => rfl,
      fun o _ w _ h =>
        ⟨⟨⟨⟨h.1, h.2.2⟩, ((meets Sx S at' o w.1).1 h.2.1).1⟩, ((meets Sx S at' o w.1).1 h.2.1).2.1⟩,
          ((meets Sx S at' o w.1).1 h.2.1).2.2⟩⟩

end FrontToyX

open FrontToyX in
theorem ldSegFront_toySeamX :
    Spec.ldSegFront_toySeamX := fun Sx S at' hat W₁ w₁0 rc rel0 relR0 on0 =>
  ⟨meets Sx S at', co_ride,
    sOK Sx S at' hat W₁ w₁0 rc rel0 relR0 on0,
    ((ldSegRef_toyAllS (sP Sx S at' hat W₁ w₁0 rc rel0 relR0 on0)
        (sV Sx S at' hat W₁ w₁0 rc rel0 relR0 on0)).2.2.2
      (sOK Sx S at' hat W₁ w₁0 rc rel0 relR0 on0)).1,
    ((ldSegRef_toyAllS (sP Sx S at' hat W₁ w₁0 rc rel0 relR0 on0)
        (sV Sx S at' hat W₁ w₁0 rc rel0 relR0 on0)).2.2.2
      (sOK Sx S at' hat W₁ w₁0 rc rel0 relR0 on0)).2⟩

end Cb.GlJ3
