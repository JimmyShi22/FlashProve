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
Cb/Gen/CodeListRS.lean.) Cb/GlVal/GlJ3SegFrontToyXProofs.lean: proof of
`Cb.GlJ3.Spec.ldSegFront_toyX`
(Cb/GlVal/GlJ3SegFrontToyX.lean), as in Cb/GlVal/GlJ3SegFrontToyProofs.lean.

Conventions of this namespace's toys, said of the toys' own oracle messages and groups, not of what
a statement takes as a parameter (of the names declared in Cb/GlVal/ and Cb/Gl/GlField.lean this
file uses only the field E, the data of Cb/GlVal/GlJ3SegFrontToy.lean and
Cb/GlVal/GlJ3SegFrontToyX.lean, the facts `a_ne_c`, `a_ne_z`, `z_ne_c`, `rd0_ne_c`, `rdK_ne_inr`,
`zAt_inj`, `cAt_inj`, Cb/GlVal/GlJ3SegFrontToyProofs.lean, the toy lookup's names and facts,
Cb/GlVal/GlToyLkpNames.lean, and `pK`, Cb/GlVal/GlToyNum.lean; Sx, Kc, S, E₀, Wp, `all`, `Rx` are
parameters):
the fields are F, the integers modulo 2^64 - 2^32 + 1, and E = F[x] / (x^3 - 2)
(Cb/Gl/GlField.lean). The toys' code is that of Cb/GlVal/GlToyBase4.lean: eight points, dimension 4,
distance 5, hides 3.
The radius, the bounds on lists, the counts for agreement and the pad's coefficient of these toys
are told in the head of Cb/GlVal/GlJ3Base.lean: read it before quoting.
This is not said of the offline side (configuration, index, lookup tables, weights-formedness).

Limits: what the head of Cb/GlVal/GlJ3SegFrontToy.lean lists as not said is not said here either.

Terms: lean/GLOSSARY.md.
-/
import Cb.GlVal.GlToyNum
import Cb.GlVal.GlToyLkpNames
import Cb.GlVal.GlJ3Send
import Cb.GlVal.GlToyConfM
import Cb.GlVal.GlJ3PackNames
import Cb.GlVal.GlJ3SegFrontToyX

set_option autoImplicit false

namespace Cb.GlJ3
open Cb.Gl hiding p
namespace FrontToyX
open Iop Prob Hiop IOR Cb.Gl.LkpToy Cb.LdLkp Cb.Lkp
open FrontToy
  (WZ WC Ride X JJ eL aAt zAt cAt rAt tA0 tι ValidU tDt tRdK tRd0 tRd1 zAt_inj cAt_inj a_ne_z a_ne_c
    z_ne_c rdK_ne_inr rd0_ne_c)

variable (Sx : Type)

theorem tPlacesIn : (tA Sx).PlacesIn fun j => j ∈ Set.range tι := re2_placesIn toyA eL _ _ iN places

theorem tPlacesOK : (tA Sx).PlacesOK tDt :=
  re2_placesOK toyA eL _ _ Sum.inl_injective mkPlacesOK.inj mkPlacesOK.out
      mkPlacesOK.bits (fun j h => ⟨j, rfl, h⟩)
      (fun j ⟨_, e, h⟩ => (Sum.inl_injective e) ▸ h) fun st m m' hm => funext fun X => by
    show m (eL (kAt (decide (X % 2 ^ 1 = 1)))) + _ = m' (eL (kAt (decide (X % 2 ^ 1 = 1)))) + _
    have e := hm (eL (kAt (decide (X % 2 ^ 1 = 1)))) ⟨_, rfl, ⟨.inl _, rfl⟩⟩
    rw [e]

theorem tSr (j : JJ) (h : (tA Sx).srAll tDt j) : tRdK j := by
  rcases h with ⟨j0, rfl, hd⟩ | hw
  · exact ⟨j0, rfl, mkRd_keeps j0 (Or.inl hd)⟩
  · obtain ⟨i, rfl⟩ := (ldLkpPlaces2_sw E (tA Sx) j).1 hw
    exact ⟨_, re2_plN toyA eL _ _ i, mkRd_keeps _ (Or.inr ((ldLkpPlaces2_sw E toyA _).2 ⟨_, rfl⟩))⟩

theorem zEl (i : WZ ⊕ Unit) : Sum.elim (tBit Sx).wAt (fun _ : Unit => (tBit Sx).cAt) i = zAt i := by
  rcases i with i | ⟨⟩ <;> rfl
theorem cEl (i : WC ⊕ Unit) : Sum.elim (tEnd Sx).wAt (fun _ : Unit => (tEnd Sx).cAt) i = cAt i := by
  rcases i with i | ⟨⟩ <;> rfl

theorem ownBit : (tBit Sx).zc.next.OwnOur tRd0 :=
  bit_ownOur (tBit Sx) tRd0 (fun a b h => by rw [zEl, zEl] at h; exact zAt_inj h)
    (fun i => Or.inr (Or.inr ⟨i, zEl Sx i⟩)) (fun b : Fin 1 → Bool => Or.inr (Or.inl ⟨b 0, rfl⟩))
    fun b i => by rw [zEl]; exact a_ne_z b i

theorem inc_at (o : (tEnd Sx).X) : (tEnd Sx).inc o (zAt (.inr ())) = bet Sx o := by
  classical
  show (if zAt (.inr ()) = zAt (.inr ()) then bet Sx o else 0) = bet Sx o
  exact if_pos rfl
theorem inc_off (o : (tEnd Sx).X) (j : JJ) (hj : j ≠ zAt (.inr ())) : (tEnd Sx).inc o j = 0 := by
  classical
  show (if j = zAt (.inr ()) then bet Sx o else 0) = 0
  exact if_neg hj

theorem ownEnd : (tEnd Sx).psc.OwnOur tRd1 :=
  end_ownOur (tEnd Sx) tRd1 (fun a b h => by rw [cEl, cEl] at h; exact cAt_inj h)
    (fun i => Or.inr ⟨i, cEl Sx i⟩) (fun b : Fin 1 → Bool => Or.inl (Or.inr (Or.inl ⟨b 0, rfl⟩)))
    (fun b i => by rw [cEl]; exact a_ne_c b i)
    (fun o j hj => inc_off Sx o j fun e => hj (Or.inl (Or.inr (Or.inr ⟨_, e⟩)))) fun o i => by
      rw [cEl]
      exact inc_off Sx o _ fun e => z_ne_c _ _ e.symm

theorem allHold_iff (st : FXt Sx) (m : JJ → E) :
    (tBit Sx).zc.toIn.AllHold st m ↔ (tBit Sx).AllBits m :=
  (ldZero_all E (tBit Sx).zc st m).trans (ldLkpBit_zero E (tBit Sx) st m)

theorem take (o : (tBit Sx).zc.next.par.Out) (m : JJ → E) :
    (tBit Sx).zc.next.par.EHolds o m () ↔ (tEnd Sx).psc.SumHolds (o.vals () + 1, o) m :=
  (ldLkpBit_row E (tBit Sx) o m).trans
    (end_takes (tEnd Sx) o m (zAt (.inr ())) (bet Sx o) (o.vals ()) (fun _ => rfl)
      (inc_at Sx o) (inc_off Sx o)).symm

section
variable (Kc : Type) (S : Sig E) (E₀ : ExtSpec) (Wp : Type)
  (all : S.Msg → JJ → E) (Rx : Rels Kc Sx E₀ (S.Msg × Wp))

theorem preOK : (tF Sx Kc S E₀ Wp all Rx).OK pK where
  tags := fun _ hf _ hf' _ => (Nat.lt_one_iff.1 hf).trans (Nat.lt_one_iff.1 hf').symm
  numV := rfl
  numD := rfl
  muFrom := pre_muFrom (tF Sx Kc S E₀ Wp all Rx) rfl rfl rfl fun _ _ _ h => h.2.2
  inj := fun _ _ h => iN_inj (Sum.inl_injective h)
  places := tPlacesIn Sx
  adm := adm
  muOK := ldLkpAsm2_muValid E (tA Sx) (le_refl 2)
  lastFw := fun x _ w h => ⟨⟨h.1.1, h.2⟩, (allHold_iff Sx x (all w.1)).2 h.1.2.1⟩
  lastOn := fun _ _ h => h
  lastCo := fun _ => rfl
  lastBw := fun x _ w _ h => ⟨⟨h.1.1, (allHold_iff Sx x (all w.1)).1 h.2⟩, h.1.2⟩

theorem vOK : (tV Sx Kc S E₀ Wp all Rx).OK pK where
  pre := preOK Sx Kc S E₀ Wp all Rx
  link := ldZero_link E (tBit Sx).zc
  back := ldZero_back E (tBit Sx).zc
  ev := ldZero_ok E (tBit Sx).zc (ldZero_ok_one E)
  psc0 := ⟨(ldZero_vars E (tBit Sx).zc).1,
    ldLkpBit_degX E (tBit Sx),
    ldLkpBit_degY E (tBit Sx),
    (ldZero_vars E (tBit Sx).zc).2⟩
  psc := fun _ _ =>
    ⟨(ldLkpEnd_vars E (tEnd Sx)).1,
      ldLkpEnd_degX E (tEnd Sx),
      ldLkpEnd_degY E (tEnd Sx),
      (ldLkpEnd_vars E (tEnd Sx)).2⟩
  step0 := ⟨fun o _ w h => ⟨⟨h.1, h.2.1⟩, (take Sx o (all w.1)).1 (h.2.2 ())⟩,
    fun _ _ h => h, fun _ => rfl,
    fun o _ w _ h => ⟨h.1.1, h.1.2, fun _ => (take Sx o (all w.1)).2 h.2⟩⟩
  step := fun i hi => absurd hi (Nat.not_lt_zero i)
  post := ⟨fun _ _ _ h => h, fun _ _ h => h, fun _ => rfl, fun _ _ _ _ h => h⟩

theorem zkOK : (tF Sx Kc S E₀ Wp all Rx).ZkOK pK tDt tRdK (tC Sx) :=
  pre_zkOK (tF Sx Kc S E₀ Wp all Rx) pK tDt tRdK rfl
    (preOK Sx Kc S E₀ Wp all Rx) (tPlacesOK Sx) (tSr Sx)

theorem q1 : ldQuiet S ((tV Sx Kc S E₀ Wp all Rx).tab.f0 tRd0) all ((tA Sx).srAll tDt) :=
  psc_quiet Kc (tBit Sx).zc.next S E₀ Wp _ all tRd0 _
      (fun j h => Or.inl (tSr Sx j h)) fun j h i => by
    show j ≠ Sum.elim (tBit Sx).wAt (fun _ : Unit => (tBit Sx).cAt) i
    rw [zEl]
    exact rdK_ne_inr j (tSr Sx j h) _

theorem q2 (i : ℕ) : ldQuiet S ((tV Sx Kc S E₀ Wp all Rx).tab.f i tRd1) all ((tA Sx).srAll tDt) :=
  psc_quiet Kc (tEnd Sx).psc S E₀ Wp _ all tRd1 _
      (fun j h => Or.inl (Or.inl (tSr Sx j h))) fun j h i => by
    show j ≠ Sum.elim (tEnd Sx).wAt (fun _ : Unit => (tEnd Sx).cAt) i
    rw [cEl]
    exact rdK_ne_inr j (tSr Sx j h) _

theorem q3 (i : ℕ) : ldQuiet S ((tV Sx Kc S E₀ Wp all Rx).tab.f i tRd1) all tRd0 :=
  psc_quiet Kc (tEnd Sx).psc S E₀ Wp _ all tRd1 _ (fun _ h => Or.inl h) fun j h i => by
    show j ≠ Sum.elim (tEnd Sx).wAt (fun _ : Unit => (tEnd Sx).cAt) i
    rw [cEl]
    exact rd0_ne_c j h i

theorem rounds : (tV Sx Kc S E₀ Wp all Rx).prog.nAll = 36 := by
  rw [ldSegFrontRef_nums E Kc _ (tV Sx Kc S E₀ Wp all Rx)]
  have e : (tV Sx Kc S E₀ Wp all Rx).Fp.lkBk.R.shape.nAll = 26 :=
    (ldLkpAsm2_rounds E (tA Sx) E₀ S.Msg Wp Kc all).trans
      (show 1 + 3 * (toyA.n + 1) + 1 +
          (∑ l ∈ Finset.range (toyA.v' + 1), (0 + l + 3 + 1) +
            ∑ l ∈ Finset.range toyA.d, (toyA.w + l + 3 + 1)) +
          (toyA.w + toyA.d + 1) + (1 + (toyA.w + toyA.d + 3)) = 26 by decide)
  rw [e]
  rfl

end
end FrontToyX

open Iop IOR Cb.Gl.LkpToy FrontToyX Cb.LdLkp in
open FrontToy (tDt tRdK tRd0 tRd1) in
theorem ldSegFront_toyX : Spec.ldSegFront_toyX := by
  intro Sx Kc S E₀ _ Wp all Rx
  refine ⟨vOK Sx Kc S E₀ Wp all Rx, zkOK Sx Kc S E₀ Wp all Rx, ownBit Sx, ownEnd Sx,
    q1 Sx Kc S E₀ Wp all Rx, q2 Sx Kc S E₀ Wp all Rx 0, q3 Sx Kc S E₀ Wp all Rx 0, ?_,
    ?_, rounds Sx Kc S E₀ Wp all Rx⟩
  · exact ldSegFrontRef_hyp E pK Kc _ (tV Sx Kc S E₀ Wp all Rx) (vOK Sx Kc S E₀ Wp all Rx)
  · exact ldSegFrontRefZk E pK Kc _ (tV Sx Kc S E₀ Wp all Rx) tDt tRdK (tC Sx) tRd0 (fun _ => tRd1)
      (tBase Sx Kc S E₀ Wp all Rx) (vOK Sx Kc S E₀ Wp all Rx) (zkOK Sx Kc S E₀ Wp all Rx)
      (ownBit Sx) (fun _ _ => ownEnd Sx) (Or.inl rfl) (Or.inr (Or.inl rfl))
      (q1 Sx Kc S E₀ Wp all Rx) (fun i hi => Or.inr (Or.inr ⟨i, hi, rfl⟩))
      (fun i _ => q2 Sx Kc S E₀ Wp all Rx i) (fun i _ => q3 Sx Kc S E₀ Wp all Rx i)
      fun i hi j hj => absurd (Nat.lt_of_lt_of_le hj hi) (Nat.not_lt_zero j)

end Cb.GlJ3
