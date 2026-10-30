-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/K3RiderTailDeg.lean: THE DEGREE OF THE INTERPOLATED FORM, AS A THEOREM: the function
of the lookup's key point z ↦ Σ_{t < 2^lt} eq(z's last lt places of zx, t) · g t has degree at most
1 in each place of the point; sharper: at most 1 in each of these lt places and 0 in every other.
And what the library's rider then counts against it AT THE LOOKUP's OWN ROUNDS: at most one bad
value of the challenge that binds one of the lt places, none of any other challenge.
Statements and proofs. NO SOUNDNESS OF ANY TEXT THAT RUNS IS CLAIMED.

Why. The rider's law (K3RiderTail.lean: tail_good) spends a degree. The calling kinds' files state
an interpolation identity («at any point the form is worth Σ_t eq zt t · (a value free of the
point)»), no degree. The degree of that interpolated form must be a line of
Lean before lt bad values are counted against it.

OBJECT: no text that runs: a function of the lookup's key point, and the library's rider's count.
Used by K3RiderK6.lean (Johnson/Top/H/), which calls eqN_congr alone.
LETTERS: h, lt, g free.
Compiled with the whole library.

Main names:
  `tailFn h lt g`: the interpolated form, as a function of the whole key point.
  `tailId_val_fn`: it is the worth of the guest's identity tailId (K3RiderTail.lean's tailId_val).
  `tail_degLE`: Alg.DegLE (fun _ => 1) (tailFn …): from K3HostLaw.lean's GuestId.degLE, which is the
    library's Blocks.degLE_ext_comp at the pick.
  `tailDeg h lt`: 1 at the lt places, 0 elsewhere.
  `tail_degLE_sharp`: DegLE (tailDeg h lt) (tailFn …).
  `tail_doomed`: a TOOL: the library's doomed_rider at that degree, on ANY list of rounds with any
    Binds b WHOSE NAMES ARE THE PLACES. b.Inj says that each binding round's map into the field is
    one-to-one, NOT that different rounds bind different places. IT IS NOT TO BE READ AT THE
    LOOKUP's OWN Binds: see the next.
  TWO NUMBERINGS. The lookup's own Binds forBB binds NAMES: the name k ≤ v'
    stands at PLACE v' − k of the point in the output statement (forB_carries). tailFn reads PLACES.
    So at the lookup's rounds the function that is handed to doomed_rider is tailFn READ BACKWARDS:
  `tailRev h lt g` := z ↦ tailFn h lt g (j ↦ z (v' − j)), a function of the NAMES' values.
  `tailRev_degLE`: DegLE (k ↦ tailDeg h lt (v' − k)) (tailRev h lt g), under lt ≤ dT.
  `tail_doomed_forB`: AT THE LOOKUP's OWN ROUNDS: if g is not 0 somewhere on the cube, the prover is
    doomed with respect to «tailFn is not 0 at the point», at the errors forBB.err (k ↦ tailDeg h lt
    (v' − k)): at most one bad value in a round that binds the name of one of the lt places, none in
    any other round.
  `tail_at_out`: whatever the lookup's verifier outputs, that point, at the lt places, is the point
    of the output statement's claim on the keys.
WHERE tail_good SPENDS THE DEGREE: NOT IN THIS FILE: lookupCR_good ← … ← Cb.Rider's sound_rider ←
Blocks.doomed_rider with Blocks.degLE_ext_comp, at DegLE (fun _ => 1), for the extension of any
array at the pick READ BACKWARDS (selIn_rev, Cb/G6/Rider/UsesK.lean). This file says the same of
tailFn by name and counts sharper; the law would stand without it.
Limits. g is a letter, free of the point. Nothing on a text's forms: that a kind's form at true
reads is worth tailFn at the point that was heard is that kind's interpolation identity with IsTail.
Not claimed: the soundness of any text that runs; anything on completeness or hiding.

-/
import Johnson.Top.H.K3RiderTail
import OnBytes.Tie.Pv.Lookup.Rider.ForB

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open Iop Prob Hiop IOR Cb Cb.LdLkp Cb.Lkp Cb.LdLkp.Kn TWhole
open Cb.Fo Cb.Rider

/-- **The interpolated form**, as a function of the whole key point. -/
noncomputable def tailFn (h : Sh) (lt : ℕ) (g : ℕ → Cb.Gl.E) (z : ℕ → Cb.Gl.E) : Cb.Gl.E :=
  ∑ t ∈ Finset.range (2 ^ lt), Blocks.eqN lt 0 (fun s => z (h.dT - lt + s)) t * g t

theorem tailId_val_fn {c : LookupCCaller} (lt : ℕ) (reads : List c.Sg.O)
    (g : c.St₀ → c.Sg.Msg → ℕ → Cb.Gl.E) (st : c.St₀) (m : c.Sg.Msg) :
    (tailId c lt reads g).val st m = tailFn c.h lt (g st m) :=
  funext fun z => tailId_val lt reads g st m z

/-- The places are different, whatever the record. -/
theorem tailPlaces_nodup (h : Sh) (lt : ℕ) : (tailPlaces h lt).Nodup := by
  show ((List.range lt).map fun t => h.dT - lt + t).Nodup
  refine (List.nodup_range (n := lt)).map_on fun t _ t' _ e => ?_
  exact Nat.add_left_cancel e

/-- **THE DEGREE**: at most 1 in each place of the key point. -/
theorem tail_degLE (h : Sh) (lt : ℕ) (g : ℕ → Cb.Gl.E) :
    Alg.DegLE (fun _ => 1) (tailFn h lt g) := by
  have h1 := Blocks.degLE_ext_comp (κ := ℕ) lt g (fun t => h.dT - lt + t)
    fun t _ t' _ e => Nat.add_left_cancel e
  exact h1

/-- The equality weight reads its m coordinates alone. -/
theorem eqN_congr {m off : ℕ} {a a' : ℕ → Cb.Gl.E} (e : ∀ t < m, a (off + t) = a' (off + t))
    (z : ℕ) : Blocks.eqN m off a z = Blocks.eqN m off a' z := by
  unfold Blocks.eqN
  exact Finset.prod_congr rfl fun t ht => by rw [e t (Finset.mem_range.1 ht)]

/-- 1 at the lt places, 0 elsewhere. -/
def tailDeg (h : Sh) (lt : ℕ) (k : ℕ) : ℕ := if k ∈ tailPlaces h lt then 1 else 0

/-- **THE DEGREE, SHARP**: at most 1 in each of the lt places, 0 in every other place. -/
theorem tail_degLE_sharp (h : Sh) (lt : ℕ) (g : ℕ → Cb.Gl.E) :
    Alg.DegLE (tailDeg h lt) (tailFn h lt g) := by
  intro z i
  by_cases hi : i ∈ tailPlaces h lt
  · obtain ⟨q, hq, he⟩ := tail_degLE h lt g z i
    exact ⟨q, by
      unfold tailDeg
      rw [if_pos hi]
      exact hq, he⟩
  · refine ⟨Polynomial.C (tailFn h lt g z), by
      unfold tailDeg
      rw [if_neg hi, Polynomial.natDegree_C], fun r => ?_⟩
    rw [Polynomial.eval_C]
    unfold tailFn
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [eqN_congr (a' := fun s => z (h.dT - lt + s)) (fun s hs =>
      Function.update_of_ne (fun e => hi (List.mem_map.2
        ⟨0 + s, List.mem_range.2 (by rw [Nat.zero_add]; exact hs), e⟩)) r z) t]

/-- The degrees add up to lt. -/
theorem tailDeg_sum (h : Sh) (lt : ℕ) : ((tailPlaces h lt).map (tailDeg h lt)).sum = lt := by
  have e : (tailPlaces h lt).map (tailDeg h lt) = (tailPlaces h lt).map fun _ => 1 :=
    List.map_congr_left fun k hk => by
      unfold tailDeg
      rw [if_pos hk]
  rw [e, List.map_const', List.sum_replicate, tailPlaces_len, smul_eq_mul, Nat.mul_one]

/-- A TOOL: the library's rider at the sharp degree, at a Binds whose names are the places. NOT TO
BE READ AT THE LOOKUP's OWN Binds, whose names run backwards: tail_doomed_forB. -/
theorem tail_doomed (h : Sh) (lt : ℕ) (g : ℕ → Cb.Gl.E) {s : Shape}
    (b : Blocks.Binds ℕ Cb.Gl.E s) (hb : b.Inj) (z : ℕ → Cb.Gl.E)
    (hv : ¬ Blocks.Vanishes (tailFn h lt g) z b.vars) :
    Doomed s (b.err (tailDeg h lt)) fun τ => tailFn h lt g (b.pt τ.rho z) ≠ 0 :=
  Blocks.doomed_rider (tail_degLE_sharp h lt g) b hb z hv

/-! ### at the lookup's own rounds: names, not places -/

/-- The interpolated form as a function of the NAMES' values: the name k stands at place v' − k. -/
noncomputable def tailRev (h : Sh) (lt : ℕ) (g : ℕ → Cb.Gl.E) (z : ℕ → Cb.Gl.E) : Cb.Gl.E :=
  tailFn h lt g fun j => z (FoNums.v' h - j)

/-- A place of the stretch lies in the point. -/
theorem tail_place_le {h : Sh} {lt s : ℕ} (hl : lt ≤ h.dT) (hs : s < lt) :
    h.dT - lt + s ≤ FoNums.v' h := by
  have h3 : h.v = h.dT + h.rK := rfl
  unfold FoNums.v'
  omega

theorem tail_name_inj {h : Sh} {lt : ℕ} (hl : lt ≤ h.dT) :
    ∀ t < lt, ∀ t' < lt,
      FoNums.v' h - (h.dT - lt + t) = FoNums.v' h - (h.dT - lt + t') → t = t' := by
  intro t ht t' ht' e
  have h1 := tail_place_le hl ht
  have h2 := tail_place_le hl ht'
  omega

/-- **THE DEGREE, IN THE NAMES.** -/
theorem tailRev_degLE (h : Sh) {lt : ℕ} (hl : lt ≤ h.dT) (g : ℕ → Cb.Gl.E) :
    Alg.DegLE (fun k => tailDeg h lt (FoNums.v' h - k)) (tailRev h lt g) := by
  intro z i
  obtain ⟨q, hq, he⟩ := Blocks.degLE_ext_comp (κ := ℕ) lt g
    (fun t => FoNums.v' h - (h.dT - lt + t)) (tail_name_inj hl) z i
  by_cases hi : ∃ s < lt, FoNums.v' h - (h.dT - lt + s) = i
  · obtain ⟨s, hs, rfl⟩ := hi
    refine ⟨q, hq.trans ?_, he⟩
    have h1 := tail_place_le hl hs
    have e : FoNums.v' h - (FoNums.v' h - (h.dT - lt + s)) = h.dT - lt + s := by omega
    show 1 ≤ tailDeg h lt (FoNums.v' h - (FoNums.v' h - (h.dT - lt + s)))
    rw [e]
    have hm : h.dT - lt + s ∈ tailPlaces h lt := List.mem_map.2 ⟨s, List.mem_range.2 hs, rfl⟩
    unfold tailDeg
    rw [if_pos hm]
  · refine ⟨Polynomial.C (tailRev h lt g z), by
      rw [Polynomial.natDegree_C]
      exact Nat.zero_le _, fun r => ?_⟩
    rw [Polynomial.eval_C]
    unfold tailRev tailFn
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [eqN_congr (a' := fun s => z (FoNums.v' h - (h.dT - lt + s))) (fun s hs =>
      Function.update_of_ne (fun e => hi ⟨0 + s, by rw [Nat.zero_add]; exact hs, e⟩) r z) t]

section AtForB
variable (c : LookupCCaller)

/-- **AT THE LOOKUP's OWN ROUNDS.** -/
theorem tail_doomed_forB {lt : ℕ} (hl : lt ≤ c.h.dT) (g : ℕ → Cb.Gl.E)
    (hg : ∃ t < 2 ^ lt, g t ≠ 0) (z : ℕ → Cb.Gl.E) :
    Doomed _ ((forBB Cb.Gl.E c.h c.L c.Ex).err fun k => tailDeg c.h lt (FoNums.v' c.h - k))
      fun τ => tailFn c.h lt g
        (fun j => (forBB Cb.Gl.E c.h c.L c.Ex).pt τ.rho z (FoNums.v' c.h - j)) ≠ 0 := by
  have C := forB_carries Cb.Gl.E c.h c.L c.Ex
  refine Blocks.doomed_rider (tailRev_degLE c.h hl g) _ C.inj z fun hv => ?_
  obtain ⟨t, ht, hne⟩ := hg
  exact hne (Blocks.vanishes_ext (g := lt) (v := g)
    (σ := fun t => FoNums.v' c.h - (c.h.dT - lt + t)) (tail_name_inj hl)
    (fun t _ => C.mem _ (Nat.sub_le _ _)) hv t ht)

/-- **That point is the output statement's**, at the lt places. -/
theorem tail_at_out {lt : ℕ} (hl : lt ≤ c.h.dT) (g : ℕ → Cb.Gl.E) (x : c.St₀) (y : c.Ex.Str)
    (τ : Tr (forB Cb.Gl.E c.h c.L V₀ V₀C (Ex := c.Ex)).R.shape)
    (x' : Cb.LdLkp.TX (c.St₀ × Cb.Gl.E) Cb.Gl.E (Option c.J₀)) (z : ℕ → Cb.Gl.E)
    (ho : (forB Cb.Gl.E c.h c.L V₀ V₀C (Ex := c.Ex)).R.out x y τ = some x') :
    tailFn c.h lt g (fun j => (forBB Cb.Gl.E c.h c.L c.Ex).pt τ.rho z (FoNums.v' c.h - j)) =
      tailFn c.h lt g x'.2.1.pt := by
  have C := forB_carries Cb.Gl.E c.h c.L c.Ex
  unfold tailFn
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [eqN_congr (a' := fun s => x'.2.1.pt (c.h.dT - lt + s)) (fun s hs => by
    have hs' : 0 + s < lt := by rw [Nat.zero_add]; exact hs
    have h1 := tail_place_le hl hs'
    show (forBB Cb.Gl.E c.h c.L c.Ex).pt τ.rho z (FoNums.v' c.h - (c.h.dT - lt + (0 + s))) = _
    rw [C.rd x y τ x' z ho _ (Nat.sub_le _ _)]
    show x'.2.1.pt (FoNums.v' c.h - (FoNums.v' c.h - (c.h.dT - lt + (0 + s)))) = _
    rw [show FoNums.v' c.h - (FoNums.v' c.h - (c.h.dT - lt + (0 + s))) = c.h.dT - lt + (0 + s) by
      omega]) t]

end AtForB

#print axioms tailId_val_fn
#print axioms tail_degLE
#print axioms tail_degLE_sharp
#print axioms tailDeg_sum
#print axioms tail_doomed
#print axioms tailRev_degLE
#print axioms tail_doomed_forB
#print axioms tail_at_out

end VerifiableInference.OnPublicFiles
