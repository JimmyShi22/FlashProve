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
Cb/Gen/CodeListRS.lean.) Cb/GlVal/GlJ3SegFrontToyProofs.lean: proof of `Cb.GlJ3.Spec.ldSegFront_toy`
(Cb/GlVal/GlJ3SegFrontToy.lean).

Conventions of this namespace's toys, said of the toys' own oracle messages and groups, not of what
a statement takes as a parameter (of the names declared in Cb/GlVal/ and Cb/Gl/GlField.lean this
file uses only the field E, the data of Cb/GlVal/GlJ3SegFrontToy.lean, the toy lookup's names and
facts, Cb/GlVal/GlToyLkpNames.lean, and `pK`, Cb/GlVal/GlToyNum.lean; Kc, S, E₀, Wp, `all`, `Rx` are
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
import Cb.GlVal.GlJ3SegFrontToy
import Cb.Ld.LdLkpBitProofs
import Cb.Ld.LdLkpEndProofs

set_option autoImplicit false

namespace Cb.GlJ3
open Cb.Gl hiding p
namespace FrontToy
open Iop Prob Hiop IOR Cb.Gl.LkpToy Cb.LdLkp Cb.Lkp

/-! ### Places -/

theorem tPlacesIn : tA.PlacesIn fun j => j ∈ Set.range tι := re2_placesIn toyA eL _ _ iN places

theorem tPlacesOK : tA.PlacesOK tDt :=
  re2_placesOK toyA eL _ _ Sum.inl_injective mkPlacesOK.inj mkPlacesOK.out
      mkPlacesOK.bits (fun j h => ⟨j, rfl, h⟩)
      (fun j ⟨_, e, h⟩ => (Sum.inl_injective e) ▸ h) fun st m m' hm => funext fun X => by
    show m (eL (kAt (decide (X % 2 ^ 1 = 1)))) + _ = m' (eL (kAt (decide (X % 2 ^ 1 = 1)))) + _
    have e := hm (eL (kAt (decide (X % 2 ^ 1 = 1)))) ⟨_, rfl, ⟨.inl _, rfl⟩⟩
    rw [e]

theorem tSr (j : JJ) (h : tA.srAll tDt j) : tRdK j := by
  rcases h with ⟨j0, rfl, hd⟩ | hw
  · exact ⟨j0, rfl, mkRd_keeps j0 (Or.inl hd)⟩
  · obtain ⟨i, rfl⟩ := (ldLkpPlaces2_sw E tA j).1 hw
    exact ⟨_, re2_plN toyA eL _ _ i, mkRd_keeps _ (Or.inr ((ldLkpPlaces2_sw E toyA _).2 ⟨_, rfl⟩))⟩

theorem zEl (i : WZ ⊕ Unit) : Sum.elim tBit.wAt (fun _ : Unit => tBit.cAt) i = zAt i := by
  rcases i with i | ⟨⟩ <;> rfl
theorem cEl (i : WC ⊕ Unit) : Sum.elim tEnd.wAt (fun _ : Unit => tEnd.cAt) i = FrontToy.cAt i := by
  rcases i with i | ⟨⟩ <;> rfl
theorem zAt_inj : Function.Injective zAt := fun _ _ h =>
  Sum.inl_injective (Sum.inr_injective (Sum.inr_injective h))
theorem cAt_inj : Function.Injective FrontToy.cAt := fun _ _ h =>
  Sum.inl_injective (Sum.inr_injective (Sum.inr_injective (Sum.inr_injective h)))
theorem a_ne_r (b : Fin 1 → Bool) (r : Ride) : aAt b ≠ rAt r := fun h =>
  Sum.inl_ne_inr (Sum.inr_injective h)
theorem z_ne_r (i : WZ ⊕ Unit) (r : Ride) : zAt i ≠ rAt r := fun h =>
  Sum.inl_ne_inr (Sum.inr_injective (Sum.inr_injective h))
theorem c_ne_r (i : WC ⊕ Unit) (r : Ride) : FrontToy.cAt i ≠ rAt r := fun h =>
  Sum.inl_ne_inr (Sum.inr_injective (Sum.inr_injective (Sum.inr_injective h)))
theorem a_ne_z (b : Fin 1 → Bool) (i : WZ ⊕ Unit) : aAt b ≠ zAt i := fun h =>
  Sum.inl_ne_inr (Sum.inr_injective h)
theorem a_ne_c (b : Fin 1 → Bool) (i : WC ⊕ Unit) : aAt b ≠ FrontToy.cAt i := fun h =>
  Sum.inl_ne_inr (Sum.inr_injective h)
theorem z_ne_c (i : WZ ⊕ Unit) (i' : WC ⊕ Unit) : zAt i ≠ FrontToy.cAt i' := fun h =>
  Sum.inl_ne_inr (Sum.inr_injective (Sum.inr_injective h))
theorem rdK_ne_inr (j : JJ) (h : tRdK j) (x : X) : j ≠ .inr x := by
  obtain ⟨j0, rfl, _⟩ := h
  exact Sum.inl_ne_inr

theorem rd0_ne_c (j : JJ) (h : tRd0 j) (i : WC ⊕ Unit) : j ≠ FrontToy.cAt i := by
  rcases h with h | ⟨b, rfl⟩ | ⟨i', rfl⟩
  · exact rdK_ne_inr j h _
  · exact fun h => Sum.inl_ne_inr (Sum.inr_injective h)
  · exact z_ne_c i' i

theorem rd1_ne_r (j : JJ) (h : tRd1 j) (r : Ride) : j ≠ rAt r := by
  rcases h with (h | ⟨b, rfl⟩ | ⟨i, rfl⟩) | ⟨i, rfl⟩
  · exact rdK_ne_inr j h _
  · exact fun h => Sum.inl_ne_inr (Sum.inr_injective h)
  · exact z_ne_r i r
  · exact c_ne_r i r

theorem ownBit : tBit.zc.next.OwnOur tRd0 :=
  bit_ownOur tBit tRd0 (fun a b h => by rw [zEl, zEl] at h; exact zAt_inj h)
    (fun i => Or.inr (Or.inr ⟨i, zEl i⟩)) (fun b : Fin 1 → Bool => Or.inr (Or.inl ⟨b 0, rfl⟩))
    fun b i => by rw [zEl]; exact a_ne_z b i

theorem ownEnd : tEnd.psc.OwnOur tRd1 :=
  end_ownOur tEnd tRd1 (fun a b h => by rw [cEl, cEl] at h; exact cAt_inj h)
    (fun i => Or.inr ⟨i, cEl i⟩) (fun b : Fin 1 → Bool => Or.inl (Or.inr (Or.inl ⟨b 0, rfl⟩)))
    (fun b i => by rw [cEl]; exact a_ne_c b i)
    (fun _ j hj => if_neg fun e : j = zAt (.inr ()) => hj (Or.inl (Or.inr (Or.inr ⟨_, e⟩))))
    fun o i => by
      classical
      rw [cEl]
      show (if FrontToy.cAt i = zAt (.inr ()) then bet o else 0) = 0
      exact if_neg fun e => z_ne_c _ _ e.symm

/-! ### The claims -/

theorem allHold_iff (st : FXt) (m : JJ → E) : tBit.zc.toIn.AllHold st m ↔ tBit.AllBits m :=
  (ldZero_all E tBit.zc st m).trans (ldLkpBit_zero E tBit st m)

theorem inc_at (o : tEnd.X) : tEnd.inc o (zAt (.inr ())) = bet o := by
  classical
  show (if zAt (.inr ()) = zAt (.inr ()) then bet o else 0) = bet o
  exact if_pos rfl
theorem inc_off (o : tEnd.X) (j : JJ) (hj : j ≠ zAt (.inr ())) : tEnd.inc o j = 0 := by
  classical
  show (if j = zAt (.inr ()) then bet o else 0) = 0
  exact if_neg hj

/-- the value row of the bit test's sumcheck is the input claim of the further sumcheck -/
theorem take (o : tBit.zc.next.par.Out) (m : JJ → E) :
    tBit.zc.next.par.EHolds o m () ↔ tEnd.psc.SumHolds (o.vals () + 1, o) m :=
  (ldLkpBit_row E tBit o m).trans
    (end_takes tEnd o m (zAt (.inr ())) (bet o) (o.vals ()) (fun _ => rfl)
      (inc_at o) (inc_off o)).symm

section
variable (Kc : Type) (S : Sig E) (E₀ : ExtSpec) (Wp : Type)
  (all : S.Msg → JJ → E) (Rx : Rels Kc Unit E₀ (S.Msg × Wp))

theorem preOK : (tF Kc S E₀ Wp all Rx).OK pK where
  tags := fun _ hf _ hf' _ => (Nat.lt_one_iff.1 hf).trans (Nat.lt_one_iff.1 hf').symm
  numV := rfl
  numD := rfl
  muFrom := pre_muFrom (tF Kc S E₀ Wp all Rx) rfl rfl rfl fun _ _ _ h => h.2.2
  inj := fun _ _ h => iN_inj (Sum.inl_injective h)
  places := tPlacesIn
  adm := adm
  muOK := ldLkpAsm2_muValid E tA (le_refl 2)
  lastFw := fun x _ w h => ⟨⟨h.1.1, h.2⟩, (allHold_iff x (all w.1)).2 h.1.2.1⟩
  lastOn := fun _ _ h => h
  lastCo := fun _ => rfl
  lastBw := fun x _ w _ h => ⟨⟨h.1.1, (allHold_iff x (all w.1)).1 h.2⟩, h.1.2⟩

theorem vOK : (tV Kc S E₀ Wp all Rx).OK pK where
  pre := preOK Kc S E₀ Wp all Rx
  link := ldZero_link E tBit.zc
  back := ldZero_back E tBit.zc
  ev := ldZero_ok E tBit.zc (ldZero_ok_one E)
  psc0 := ⟨(ldZero_vars E tBit.zc).1, ldLkpBit_degX E tBit,
    ldLkpBit_degY E tBit, (ldZero_vars E tBit.zc).2⟩
  psc := fun _ _ =>
    ⟨(ldLkpEnd_vars E tEnd).1, ldLkpEnd_degX E tEnd, ldLkpEnd_degY E tEnd, (ldLkpEnd_vars E tEnd).2⟩
  step0 := ⟨fun o _ w h => ⟨⟨h.1, h.2.1⟩, (take o (all w.1)).1 (h.2.2 ())⟩,
    fun _ _ h => h, fun _ => rfl,
    fun o _ w _ h => ⟨h.1.1, h.1.2, fun _ => (take o (all w.1)).2 h.2⟩⟩
  step := fun i hi => absurd hi (Nat.not_lt_zero i)
  post := ⟨fun _ _ _ h => h, fun _ _ h => h, fun _ => rfl, fun _ _ _ _ h => h⟩

theorem zkOK : (tF Kc S E₀ Wp all Rx).ZkOK pK tDt tRdK tC :=
  pre_zkOK (tF Kc S E₀ Wp all Rx) pK tDt tRdK rfl (preOK Kc S E₀ Wp all Rx) tPlacesOK tSr

theorem q1 : ldQuiet S ((tV Kc S E₀ Wp all Rx).tab.f0 tRd0) all (tA.srAll tDt) :=
  psc_quiet Kc tBit.zc.next S E₀ Wp _ all tRd0 _ (fun j h => Or.inl (tSr j h)) fun j h i => by
    show j ≠ Sum.elim tBit.wAt (fun _ : Unit => tBit.cAt) i
    rw [zEl]
    exact rdK_ne_inr j (tSr j h) _

theorem q2 (i : ℕ) : ldQuiet S ((tV Kc S E₀ Wp all Rx).tab.f i tRd1) all (tA.srAll tDt) :=
  psc_quiet Kc tEnd.psc S E₀ Wp _ all tRd1 _ (fun j h => Or.inl (Or.inl (tSr j h))) fun j h i => by
    show j ≠ Sum.elim tEnd.wAt (fun _ : Unit => tEnd.cAt) i
    rw [cEl]
    exact rdK_ne_inr j (tSr j h) _

theorem q3 (i : ℕ) : ldQuiet S ((tV Kc S E₀ Wp all Rx).tab.f i tRd1) all tRd0 :=
  psc_quiet Kc tEnd.psc S E₀ Wp _ all tRd1 _ (fun _ h => Or.inl h) fun j h i => by
    show j ≠ Sum.elim tEnd.wAt (fun _ : Unit => tEnd.cAt) i
    rw [cEl]
    exact rd0_ne_c j h i

theorem rounds : (tV Kc S E₀ Wp all Rx).prog.nAll = 36 := by
  rw [ldSegFrontRef_nums E Kc _ (tV Kc S E₀ Wp all Rx)]
  have e : (tV Kc S E₀ Wp all Rx).Fp.lkBk.R.shape.nAll = 26 :=
    (ldLkpAsm2_rounds E tA E₀ S.Msg Wp Kc all).trans (by decide)
  rw [e]
  rfl

end

/-! ### The entry claims can hold and can fail -/

theorem entry_of (r : Rw → E) (a : Bool → E)
    (h : toyA.lk.inP toyA.ValidMu () r) (ha : ∀ b, a b * (a b - 1) = 0) : EntryP (ent r a) := by
  refine ⟨fun f _ => h.1.1, fun b : Fin 1 → Bool => ha (b 0), fun f hf => ?_⟩
  obtain rfl : f = 0 := Nat.lt_one_iff.1 hf
  have e : (fun u j => ent r a (tA0.bAt (0 * 2 ^ tP.d + u) j)) = toyA.H.bit r := by
    funext u j
    show r (toyA.bAt (0 * 2 ^ tP.d + u) j) = r (toyA.bAt u j)
    rw [Nat.zero_mul, Nat.zero_add]
  rw [e]
  exact h.2

end FrontToy

open Iop IOR Cb.Gl.LkpToy FrontToy Cb.LdLkp in
theorem ldSegFront_toy : Spec.ldSegFront_toy := by
  refine ⟨fun Kc S E₀ _ Wp all Rx =>
      ⟨vOK Kc S E₀ Wp all Rx, zkOK Kc S E₀ Wp all Rx, ownBit, ownEnd, q1 Kc S E₀ Wp all Rx,
        q2 Kc S E₀ Wp all Rx 0, q3 Kc S E₀ Wp all Rx 0, ?_, ?_, rounds Kc S E₀ Wp all Rx⟩,
    ⟨?_, ?_, ?_, ?_, fun r h => rd1_ne_r _ h r rfl⟩,
    ?_, ?_, ?_, ?_⟩
  · exact ldSegFrontRef_hyp E pK Kc _ (tV Kc S E₀ Wp all Rx) (vOK Kc S E₀ Wp all Rx)
  · exact ldSegFrontRefZk E pK Kc _ (tV Kc S E₀ Wp all Rx) tDt tRdK tC tRd0 (fun _ => tRd1)
      (tBase Kc S E₀ Wp all Rx) (vOK Kc S E₀ Wp all Rx) (zkOK Kc S E₀ Wp all Rx) ownBit
      (fun _ _ => ownEnd) (Or.inl rfl) (Or.inr (Or.inl rfl)) (q1 Kc S E₀ Wp all Rx)
      (fun i hi => Or.inr (Or.inr ⟨i, hi, rfl⟩)) (fun i _ => q2 Kc S E₀ Wp all Rx i)
      (fun i _ => q3 Kc S E₀ Wp all Rx i)
      fun i hi j hj => absurd (Nat.lt_of_lt_of_le hj hi) (Nat.not_lt_zero j)
  · rintro ((⟨j0, e, p, hp⟩ | ⟨b, e⟩ | ⟨i, e⟩) | ⟨i, e⟩)
    · exact (plAt_ne p).1 (hp.symm.trans (Sum.inl_injective e).symm)
    · exact Sum.inl_ne_inr e
    · exact Sum.inl_ne_inr e
    · exact Sum.inl_ne_inr e
  · rintro ((⟨j0, e, p, hp⟩ | ⟨b, e⟩ | ⟨i, e⟩) | ⟨i, e⟩)
    · exact (plAt_ne p).2 (hp.symm.trans (Sum.inl_injective e).symm)
    · exact Sum.inl_ne_inr e
    · exact Sum.inl_ne_inr e
    · exact Sum.inl_ne_inr e
  · exact fun i h => rdK_ne_inr _ h _ rfl
  · exact fun i h => rd0_ne_c _ h i rfl
  · exact entry_of w57 _ in57 fun _ => by simp
  · exact entry_of w55 _ in55 fun b => by cases b <;> simp
  · exact fun h => out56 ⟨h.1 0 Nat.one_pos, trivial⟩
  · intro h
    have h1 : (2 : E) * (2 - 1) = 0 := h.2 fun _ => false
    exact absurd h1 (by decide)

end Cb.GlJ3
