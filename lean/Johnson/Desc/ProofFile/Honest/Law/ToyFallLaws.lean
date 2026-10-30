-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/ToyFallLaws.lean: theorems about the toy example of
Honest/Law/ToyFall.lean: the fields `exact` and `fresh` of `Good` (Honest/Side.lean) at its eight
sides. The theorems are about that file's own made-up objects alone. None is one of the library's
goals.

  1  `ExactAt`, `FreshAt`   the two fields, letter for letter, each under one name
  2  `shear1`, `Cs.eq011u`, `spendE`, `cutAll_spendE`, `fresh_two`   an owner of two coins whose
     second coin is spent: the two distributions of `fresh` are one distribution
  3  `vmem_…`, `vshows_…`, `vtells_…`   what each part shows and each simulator returns, as an
     equation in the coins; the spender also where its stop stops it
  4  `vA_exact` … `vL_exact`   `exact` at the eight sides
  5  `vA_fresh` … `vL_fresh`   `fresh` at the eight sides

Limits.
  * A toy example.
  * None of the sixteen reads the verifier's state: each holds at every coin, also at those at which
    the description rejects.
  * The fields of `Good` on a whole list's run are not in this file.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.ToyFall
import Johnson.Desc.ProofFile.Honest.Law.ToyExact
import Johnson.Desc.ProofFile.Honest.Law.ToyStop

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.Toy
open VerifiableInference.Desc (Place Block FileDescription)
open VerifiableInference.Desc.BlockToy (St tree₃ drawD orc)
open OnBytes.Slice (toF toE ofF ofE)
open Prob

/-! ## 1 The two fields, each under one name -/

section
variable {S Cl V W X Pb : Type}

/-- The field `exact` of `Good`, letter for letter. -/
def ExactAt (φ : Face V W Pb) (σ : Side S Cl V W X Pb) (chain firstTree : Nat)
    (On : (u : Member V W X Pb) → CsAll u.part.carries → Mid W X → Before → Prop)
    (bud : Nat → List Fmt.Drawn → List (List (List Nat)) → Prop) : Prop :=
  ∀ u ∈ σ.members, ∀ ca m front ds asks, On u ca m front → m.seen = front.seen →
    drawsFit (u.rounds.map (·.1)) ds = true → bud u.number ds asks →
    front.holds chain firstTree (u.rounds.map (·.1)) ds = true →
    u.part.stopAt (φ.sees m.st.input) m.loc ds ≠ some .hid →
    (unif (Cs u.part.takes × CsAll u.part.spends)).map
        (fun c => σ.shows φ u (c.1, c.2, ca) m ds asks) =
      (unif (Cs u.sim.takes)).map fun c => u.tells φ c m.st.input front ds asks

/-- The field `fresh` of `Good`, letter for letter. -/
def FreshAt (φ : Face V W Pb) (σ : Side S Cl V W X Pb) (Bk : ProverCoinCounts) (ord : List Place)
    (bud : Nat → List Fmt.Drawn → List (List (List Nat)) → Prop) : Prop :=
  ∀ u ∈ σ.members, ∀ (p : Addr) sp ca m ds asks,
    drawsFit (u.rounds.map (·.1)) ds = true → bud u.number ds asks →
    u.part.stopAt (φ.sees m.st.input) m.loc ds ≠ some .hid →
    (unif (Cs u.part.takes)).map (fun c =>
        (cutAll c (Bk.spentBy ⟨σ.block.place, u.number⟩ p), σ.shows φ u (c, sp, ca) m ds asks,
          cutAll c (Bk.knownBy ord ⟨σ.block.place, u.number⟩ p))) =
      (unif (CsAll ((Bk.spentBy ⟨σ.block.place, u.number⟩ p).map Ahead.named) ×
          Cs u.part.takes)).map fun a =>
        (some a.1, σ.shows φ u (a.2, sp, ca) m ds asks,
          cutAll a.2 (Bk.knownBy ord ⟨σ.block.place, u.number⟩ p))

end

/-! ## 2 An owner of two coins whose second coin is spent -/

/-- (t, a) to (K + t + a, a). -/
def shear1 (K : Cb.Gl.F) : Cb.Gl.F × Cb.Gl.F ≃ Cb.Gl.F × Cb.Gl.F where
  toFun x := (K + x.1 + x.2, x.2)
  invFun y := (y.1 - y.2 - K, y.2)
  left_inv x := by
    refine Prod.ext ?_ rfl
    show K + x.1 + x.2 - x.2 - K = x.1
    ring
  right_inv y := by
    refine Prod.ext ?_ rfl
    show K + (y.1 - y.2 - K) + y.2 = y.1
    ring

/-- No coin, beside two blocks of one coin each. -/
def Cs.eq011u : Cs ⟨0, 0⟩ × (Cs ⟨1, 0⟩ × Cs ⟨1, 0⟩ × Unit) ≃ Cb.Gl.F × Cb.Gl.F where
  toFun c := (c.2.1.f ⟨0, by decide⟩, c.2.2.1.f ⟨0, by decide⟩)
  invFun x := (Cs.empty, (Cs.one x.1, Cs.one x.2, ()))
  left_inv c := Prod.ext (Cs.eq0.left_inv c.1)
    (Prod.ext (Cs.eq1.left_inv c.2.1) (Cs.eq1u.left_inv c.2.2))
  right_inv _ := rfl

/-- An entry by which the part at p spends the second coin of the part at o. -/
def spendE (n : String) (o p : Addr) : Ahead := ⟨n, o, ⟨1, 0⟩, ⟨1, 0⟩, p, true⟩

theorem cutAll_spendE (c : Cs ⟨2, 0⟩) (n : String) (o p : Addr) :
    cutAll c [spendE n o p] =
      (some (Cs.one (c.f ⟨1, by decide⟩), ()) :
        Option (CsAll ([spendE n o p].map Ahead.named))) := by
  show ((c.cut ⟨1, 0⟩ ⟨1, 0⟩).bind fun x => (cutAll c []).map fun y => (x, y)) = _
  rw [cut_u]
  rfl

/-- **The owner's condition for its spender**, where what the owner shows is a function g of K + t +
a: (a · g (K + t + a) · nothing) over (t, a), and the same with a drawn afresh. -/
theorem fresh_two {γ : Type} (K : Cb.Gl.F) (g : Cb.Gl.F → γ) (Sh : Cs ⟨2, 0⟩ → γ)
    (hS : ∀ c, Sh c = g (K + c.f ⟨0, by decide⟩ + c.f ⟨1, by decide⟩)) (n : String) (o p : Addr)
    (es ks : List Ahead) (hes : es = [spendE n o p]) (hks : ks = []) :
    (unif (Cs ⟨2, 0⟩)).map (fun c => (cutAll c es, Sh c, cutAll c ks)) =
      (unif (CsAll (es.map Ahead.named) × Cs ⟨2, 0⟩)).map fun a =>
        (some a.1, Sh a.2, cutAll a.2 ks) := by
  subst hes
  subst hks
  refine Eq.trans (map_unif_by_equiv (Cs.eq2.trans (shear1 K))
    (fun x : Cb.Gl.F × Cb.Gl.F =>
      ((some (Cs.one x.2, ()) : Option (CsAll ([spendE n o p].map Ahead.named))), g x.1,
        (some () : Option (CsAll (([] : List Ahead).map Ahead.named))))) _ fun c => ?_)
    (Eq.symm ?_)
  · exact Prod.ext (cutAll_spendE c n o p) (Prod.ext (hS c) rfl)
  · exact map_unif_fst_equiv ((Equiv.prodCongr Cs.eq1u (Cs.eq2.trans (shear1 K))).trans rot)
      (fun x : Cb.Gl.F × Cb.Gl.F =>
        ((some (Cs.one x.2, ()) : Option (CsAll ([spendE n o p].map Ahead.named))), g x.1,
          (some () : Option (CsAll (([] : List Ahead).map Ahead.named))))) _
      fun a => Prod.ext (congrArg some (Cs.eq1u.left_inv a.1).symm) (Prod.ext (hS a.2) rfl)

/-! ## 3 What each part shows -/

theorem vmem_A : vSideA.members = [vUA] := rfl
theorem vmem_B : vSideB.members = [vUB] := rfl
theorem vmem_S : vSideS.members = [vUS] := rfl
theorem vmem_D : vSideD.members = [vUD] := rfl
theorem vmem_M : vSideM.members = [vUM] := rfl
theorem vmem_W : vSideW.members = [vUW] := rfl
theorem vmem_L : vSideL.members = [vUL] := rfl
theorem vmem_E : vSideE.members = [vUE] := rfl

theorem vshows_A (c : Cs ⟨2, 0⟩) (sp ca : Unit) (m : Mid L Nat) (R : Fmt.Drawn)
    (asks : List (List (List Nat))) :
    vSideA.shows .own vUA (c, sp, ca) m [R] asks =
      eAt (toF m.st.input.w₀.ans + c.f ⟨0, by decide⟩ + c.f ⟨1, by decide⟩) := by
  have h : vSideA.shows .own vUA (c, sp, ca) m [R] asks =
      some [⟨[.e (ofF (toF m.st.input.w₀.ans + c.f ⟨0, by decide⟩ + c.f ⟨1, by decide⟩),
        ofF (toF 0), ofF (toF 0))], []⟩] := by with_unfolding_all rfl
  rw [h, ofF_toF_zero]
  rfl

theorem vshows_B (c : Cs ⟨2, 0⟩) (sp ca : Unit) (m : Mid L Nat) (R : Fmt.Drawn)
    (asks : List (List (List Nat))) :
    vSideB.shows .own vUB (c, sp, ca) m [R] asks =
      eAt (toF (m.st.input.w₀.a 0) + c.f ⟨0, by decide⟩ + c.f ⟨1, by decide⟩) := by
  have h : vSideB.shows .own vUB (c, sp, ca) m [R] asks =
      some [⟨[.e (ofF (toF (m.st.input.w₀.a 0) + c.f ⟨0, by decide⟩ + c.f ⟨1, by decide⟩),
        ofF (toF 0), ofF (toF 0))], []⟩] := by with_unfolding_all rfl
  rw [h, ofF_toF_zero]
  rfl

theorem vshows_D (c : Cs ⟨0, 0⟩) (sp ca : Unit) (m : Mid L Nat) (R : Fmt.Drawn)
    (asks : List (List (List Nat))) :
    vSideD.shows .own vUD (c, sp, ca) m [R] asks = some [⟨[], []⟩] := by
  with_unfolding_all rfl

theorem vshows_M (c : Cs ⟨1, 0⟩) (sp ca : Unit) (m : Mid L Nat) (R : Fmt.Drawn)
    (asks : List (List (List Nat))) :
    vSideM.shows .own vUM (c, sp, ca) m [R] asks =
      eAt (toF m.st.input.w₀.ans + c.f ⟨0, by decide⟩) := by
  have h : vSideM.shows .own vUM (c, sp, ca) m [R] asks =
      some [⟨[.e (ofF (toF m.st.input.w₀.ans + c.f ⟨0, by decide⟩), ofF (toF 0), ofF (toF 0))],
        []⟩] := by with_unfolding_all rfl
  rw [h, ofF_toF_zero]
  rfl

theorem vshows_W (c : Cs ⟨1, 0⟩) (sp ca : Unit) (m : Mid L Nat) (R : Fmt.Drawn)
    (asks : List (List (List Nat))) :
    vSideW.shows .own vUW (c, sp, ca) m [R] asks =
      eAt (toF (m.st.input.w₀.a 2) + c.f ⟨0, by decide⟩) := by
  have h : vSideW.shows .own vUW (c, sp, ca) m [R] asks =
      some [⟨[.e (ofF (toF (m.st.input.w₀.a 2) + c.f ⟨0, by decide⟩), ofF (toF 0), ofF (toF 0))],
        []⟩] := by with_unfolding_all rfl
  rw [h, ofF_toF_zero]
  rfl

theorem vshows_L (c : Cs ⟨1, 0⟩) (sp : Unit) (ca : Cs ⟨1, 0⟩ × Unit) (m : Mid L Nat)
    (R : Fmt.Drawn) (asks : List (List (List Nat))) :
    vSideL.shows .own vUL (c, sp, ca) m [R] asks =
      eAt (toF (m.st.input.w₀.a 1) + c.f ⟨0, by decide⟩ + ca.1.f ⟨0, by decide⟩) := by
  have h : vSideL.shows .own vUL (c, sp, ca) m [R] asks =
      some [⟨[.e (ofF (toF (m.st.input.w₀.a 1) + c.f ⟨0, by decide⟩ + ca.1.f ⟨0, by decide⟩),
        ofF (toF 0), ofF (toF 0))], []⟩] := by with_unfolding_all rfl
  rw [h, ofF_toF_zero]
  rfl

theorem vshows_E (c : Cs ⟨0, 0⟩) (sp : Unit) (ca : Cs ⟨1, 0⟩ × Cs ⟨1, 0⟩ × Unit) (m : Mid L Nat)
    (R : Fmt.Drawn) (asks : List (List (List Nat))) :
    vSideE.shows .own vUE (c, sp, ca) m [R] asks =
      eAt (toF (m.st.input.w₀.a 1) + ca.2.1.f ⟨0, by decide⟩ + ca.1.f ⟨0, by decide⟩) := by
  have h : vSideE.shows .own vUE (c, sp, ca) m [R] asks =
      some [⟨[.e (ofF (toF (m.st.input.w₀.a 1) + ca.2.1.f ⟨0, by decide⟩ + ca.1.f ⟨0, by decide⟩),
        ofF (toF 0), ofF (toF 0))], []⟩] := by with_unfolding_all rfl
  rw [h, ofF_toF_zero]
  rfl

theorem vtells_A (c : Cs ⟨1, 0⟩) (w : L) (front : Before) (ds : List Fmt.Drawn)
    (asks : List (List (List Nat))) :
    vUA.tells .own c w front ds asks = eAt (c.f ⟨0, by decide⟩) := rfl
theorem vtells_B (c : Cs ⟨1, 0⟩) (w : L) (front : Before) (ds : List Fmt.Drawn)
    (asks : List (List (List Nat))) :
    vUB.tells .own c w front ds asks = eAt (c.f ⟨0, by decide⟩) := rfl
theorem vtells_D (c : Cs ⟨0, 0⟩) (w : L) (front : Before) (ds : List Fmt.Drawn)
    (asks : List (List (List Nat))) : vUD.tells .own c w front ds asks = some [⟨[], []⟩] := rfl
theorem vtells_M (c : Cs ⟨1, 0⟩) (w : L) (front : Before) (ds : List Fmt.Drawn)
    (asks : List (List (List Nat))) :
    vUM.tells .own c w front ds asks = eAt (c.f ⟨0, by decide⟩) := rfl
theorem vtells_W (c : Cs ⟨1, 0⟩) (w : L) (front : Before) (ds : List Fmt.Drawn)
    (asks : List (List (List Nat))) :
    vUW.tells .own c w front ds asks = eAt (c.f ⟨0, by decide⟩) := rfl
theorem vtells_L (c : Cs ⟨1, 0⟩) (w : L) (front : Before) (ds : List Fmt.Drawn)
    (asks : List (List (List Nat))) :
    vUL.tells .own c w front ds asks = eAt (c.f ⟨0, by decide⟩) := rfl

/-! ### The spender -/

/-- The spender's round as `play` meets it, with the two spent coins put in. -/
def sS (m : Mid L Nat) (a b : Cb.Gl.F) : Step L Nat :=
  ⟨"spend", vaS, { entry := { name := "CS", msg := 32, roots := 1, drawE := 1 } }, [orc (2, 1)],
    vPS.bad, fun f o => (Face.own.sees m.st.input).bind fun w => vPS.hid w f o, 0, true,
    some ⟨fun _ _ s => .ok ⟨[], [⟨2, 1, fun p _ => toF (s.input.w₀.a p) + a + b⟩]⟩,
      fun s => s.own⟩⟩

theorem steps_S (c : Cs ⟨0, 0⟩) (sp : Cs ⟨1, 0⟩ × Cs ⟨1, 0⟩ × Unit) (ca : Unit) (m : Mid L Nat) :
    vUS.part.steps vSideS.block.name ⟨vSideS.block.place, vUS.number⟩ vUS.rounds
        (Face.own.sees m.st.input) (c, sp, ca) =
      [sS m (sp.1.f ⟨0, by decide⟩) (sp.2.1.f ⟨0, by decide⟩)] := rfl

theorem bad_13 (l : List Fmt.Drawn) : vPS.bad l [dE 13] = some "the challenge is 13" := rfl

theorem bad_else (l : List Fmt.Drawn) {R : Fmt.Drawn} (hR : R ≠ dE 13) : vPS.bad l [R] = none := by
  have hne : ([R].head? == some (dE 13)) = false :=
    beq_eq_false_iff_ne.2 fun h => hR (Option.some.inj h)
  show (if ([R].head? == some (dE 13)) = true then some "the challenge is 13" else none) = none
  exact if_neg (by rw [hne]; exact Bool.false_ne_true)

/-- Where the stop stops it the spender shows `none`, at every coin. -/
theorem vshows_S_13 (c : Cs ⟨0, 0⟩) (sp : Cs ⟨1, 0⟩ × Cs ⟨1, 0⟩ × Unit) (ca : Unit)
    (m : Mid L Nat) (asks : List (List (List Nat))) :
    vSideS.shows .own vUS (c, sp, ca) m [dE 13] asks = none := by
  have hb : (sS m (sp.1.f ⟨0, by decide⟩) (sp.2.1.f ⟨0, by decide⟩)).bad m.loc [dE 13] =
      some "the challenge is 13" := bad_13 m.loc
  have h := play_one_halt (s := sS m (sp.1.f ⟨0, by decide⟩) (sp.2.1.f ⟨0, by decide⟩))
    (d := dE 13) (m := m) (z := ⟨[], [⟨2, 1, fun p _ =>
      toF (m.st.input.w₀.a p) + sp.1.f ⟨0, by decide⟩ + sp.2.1.f ⟨0, by decide⟩⟩]⟩)
    (stop_front m.loc (fun _ => rfl) (fun _ => rfl)) rfl (stop_last_bad hb) rfl
    (by with_unfolding_all rfl) (by with_unfolding_all rfl)
  unfold Side.shows
  rw [steps_S, h]
  rfl

/-- Elsewhere it shows the one column that is asked. -/
theorem vshows_S (c : Cs ⟨0, 0⟩) (sp : Cs ⟨1, 0⟩ × Cs ⟨1, 0⟩ × Unit) (ca : Unit) (m : Mid L Nat)
    {R : Fmt.Drawn} (hR : R ≠ dE 13) (p : Nat) :
    vSideS.shows .own vUS (c, sp, ca) m [R] [[[p]]] =
      colAt p (toF (m.st.input.w₀.a p) + sp.1.f ⟨0, by decide⟩ + sp.2.1.f ⟨0, by decide⟩) := by
  unfold Side.shows
  rw [steps_S, play_one_go (s := sS m _ _) (z := ⟨[], [⟨2, 1, fun p _ =>
      toF (m.st.input.w₀.a p) + sp.1.f ⟨0, by decide⟩ + sp.2.1.f ⟨0, by decide⟩⟩]⟩)
    (stop_front m.loc (fun _ => rfl) (fun _ => rfl)) (stop_last_none (bad_else m.loc hR) rfl)
    rfl (by with_unfolding_all rfl) (by with_unfolding_all rfl)]
  rfl

theorem vtells_S_13 (c : Cs ⟨1, 0⟩) (w : L) (front : Before) (asks : List (List (List Nat))) :
    vUS.tells .own c w front [dE 13] asks = none := rfl

theorem vtells_S (c : Cs ⟨1, 0⟩) (w : L) (front : Before) {R : Fmt.Drawn} (hR : R ≠ dE 13)
    (p : Nat) : vUS.tells .own c w front [R] [[[p]]] = colAt p (c.f ⟨0, by decide⟩) := by
  have hne : ([R].head? == some (dE 13)) = false :=
    beq_eq_false_iff_ne.2 fun h => hR (Option.some.inj h)
  show (if ([R].head? == some (dE 13)) = true then none else
    some [(⟨[], [[(p, [ofF (c.f ⟨0, by decide⟩)])]]⟩ : Shown)]) = _
  exact if_neg (by rw [hne]; exact Bool.false_ne_true)

/-! ## 4 `exact` at the eight sides -/

theorem vA_exact : ExactAt .own vSideA 2 Fv.lastChainFirstTreeNumber onAny budAny := by
  intro u hu
  rw [vmem_A] at hu
  obtain rfl := List.mem_singleton.1 hu
  intro ca m front ds asks _ _ hd _ _ _
  have hd' : drawsFit [sayR] ds = true := hd
  obtain ⟨R, rfl, -⟩ := drawsFit_one hd'
  refine Eq.trans (map_unif_fst_equiv (Cs.eq2u.trans (shear1 (toF m.st.input.w₀.ans))) eAt _
    fun c => vshows_A c.1 c.2 ca m R asks) (Eq.symm ?_)
  exact map_unif_by_equiv Cs.eq1 eAt _ fun c => vtells_A c m.st.input front [R] asks

theorem vB_exact : ExactAt .own vSideB 2 Fv.lastChainFirstTreeNumber onAny budAny := by
  intro u hu
  rw [vmem_B] at hu
  obtain rfl := List.mem_singleton.1 hu
  intro ca m front ds asks _ _ hd _ _ _
  have hd' : drawsFit [sayR] ds = true := hd
  obtain ⟨R, rfl, -⟩ := drawsFit_one hd'
  refine Eq.trans (map_unif_fst_equiv (Cs.eq2u.trans (shear1 (toF (m.st.input.w₀.a 0)))) eAt _
    fun c => vshows_B c.1 c.2 ca m R asks) (Eq.symm ?_)
  exact map_unif_by_equiv Cs.eq1 eAt _ fun c => vtells_B c m.st.input front [R] asks

/-- The spender that sends: at the stop both distributions are always `none`; elsewhere the column
under the two spent coins has the distribution of the simulator's one coin. -/
theorem vS_exact : ExactAt .own vSideS 2 Fv.lastChainFirstTreeNumber onAny budOne := by
  intro u hu
  rw [vmem_S] at hu
  obtain rfl := List.mem_singleton.1 hu
  intro ca m front ds asks _ _ hd hb _ _
  have hd' : drawsFit [{ entry := { name := "CS", msg := 32, roots := 1, drawE := 1 } }] ds =
    true := hd
  obtain ⟨R, rfl, -⟩ := drawsFit_one hd'
  obtain ⟨p, rfl⟩ := onePos_elim (hb rfl)
  by_cases hR : R = dE 13
  · subst hR
    exact map_unif_point none _ _ (fun c => vshows_S_13 c.1 c.2 ca m [[[p]]])
      (fun c => vtells_S_13 c m.st.input front [[[p]]])
  · refine Eq.trans (map_unif_fst_equiv (Cs.eq011u.trans (shear1 (toF (m.st.input.w₀.a p))))
      (colAt p) _ fun c => vshows_S c.1 c.2 ca m hR p) (Eq.symm ?_)
    exact map_unif_by_equiv Cs.eq1 (colAt p) _ fun c => vtells_S c m.st.input front hR p

theorem vD_exact : ExactAt .own vSideD 2 Fv.lastChainFirstTreeNumber onAny budAny := by
  intro u hu
  rw [vmem_D] at hu
  obtain rfl := List.mem_singleton.1 hu
  intro ca m front ds asks _ _ hd _ _ _
  have hd' : drawsFit [{ entry := drawD }] ds = true := hd
  obtain ⟨R, rfl, -⟩ := drawsFit_one hd'
  exact map_unif_point (some [⟨[], []⟩]) _ _ (fun c => vshows_D c.1 c.2 ca m R asks)
    (fun c => vtells_D c m.st.input front [R] asks)

theorem vM_exact : ExactAt .own vSideM 2 Fv.lastChainFirstTreeNumber onAny budAny := by
  intro u hu
  rw [vmem_M] at hu
  obtain rfl := List.mem_singleton.1 hu
  intro ca m front ds asks _ _ hd _ _ _
  have hd' : drawsFit [{ entry := { name := "CS", msg := 24, poss := 1, logN := 3 }
                         opens := [(tree₃, .own 0)] }] ds = true := hd
  obtain ⟨R, rfl, -⟩ := drawsFit_one hd'
  refine Eq.trans (map_unif_by_equiv (Cs.eq1u.trans (Equiv.addLeft (toF m.st.input.w₀.ans))) eAt _
    fun c => vshows_M c.1 c.2 ca m R asks) (Eq.symm ?_)
  exact map_unif_by_equiv Cs.eq1 eAt _ fun c => vtells_M c m.st.input front [R] asks

theorem vW_exact : ExactAt .own vSideW 2 Fv.lastChainFirstTreeNumber onAny budAny := by
  intro u hu
  rw [vmem_W] at hu
  obtain rfl := List.mem_singleton.1 hu
  intro ca m front ds asks _ _ hd _ _ _
  have hd' : drawsFit [sayR] ds = true := hd
  obtain ⟨R, rfl, -⟩ := drawsFit_one hd'
  refine Eq.trans (map_unif_by_equiv (Cs.eq1u.trans (Equiv.addLeft (toF (m.st.input.w₀.a 2)))) eAt _
    fun c => vshows_W c.1 c.2 ca m R asks) (Eq.symm ?_)
  exact map_unif_by_equiv Cs.eq1 eAt _ fun c => vtells_W c m.st.input front [R] asks

theorem vL_exact : ExactAt .own vSideL 2 Fv.lastChainFirstTreeNumber onAny budAny := by
  intro u hu
  rw [vmem_L] at hu
  obtain rfl := List.mem_singleton.1 hu
  intro ca m front ds asks _ _ hd _ _ _
  have hd' : drawsFit [sayR] ds = true := hd
  obtain ⟨R, rfl, -⟩ := drawsFit_one hd'
  refine Eq.trans (map_unif_by_equiv
    (Cs.eq1u.trans ((Equiv.addLeft (toF (m.st.input.w₀.a 1))).trans
      (Equiv.addRight (ca.1.f ⟨0, by decide⟩)))) eAt _
    fun c => vshows_L c.1 c.2 ca m R asks) (Eq.symm ?_)
  exact map_unif_by_equiv Cs.eq1 eAt _ fun c => vtells_L c m.st.input front [R] asks

/-- The echo: both distributions are a single value, and the condition at the entry makes the two
values equal. -/
theorem vE_exact : ExactAt .own vSideE 2 Fv.lastChainFirstTreeNumber onEcho budAny := by
  intro u hu
  rw [vmem_E] at hu
  obtain rfl := List.mem_singleton.1 hu
  intro ca m front ds asks hOn _ hd _ _ _
  have hd' : drawsFit [sayR] ds = true := hd
  obtain ⟨R, rfl, -⟩ := drawsFit_one hd'
  have hOn' : (lastVals front == some [.e (ofF (toF (m.st.input.w₀.a 1) +
      ca.2.1.f ⟨0, by decide⟩ + ca.1.f ⟨0, by decide⟩), 0, 0)]) = true := hOn
  have hv := eq_of_beq hOn'
  refine map_unif_point
    (eAt (toF (m.st.input.w₀.a 1) + ca.2.1.f ⟨0, by decide⟩ + ca.1.f ⟨0, by decide⟩)) _ _
    (fun c => vshows_E c.1 c.2 ca m R asks) (fun c => ?_)
  show ((lastVals front).map fun v => [(⟨v, []⟩ : Shown)]) = _
  rw [hv]
  rfl

/-! ## 5 `fresh` at the eight sides -/

/-- The book's entries that spend: each is spent by the spender; its owner is one of the two. -/
theorem Bv_spent : ∀ e ∈ Bv.ahead, e.once = true →
    e.spender = vaS ∧ (e.owner.place = vpA ∨ e.owner.place = vpB) := by decide

theorem vA_fresh : FreshAt .own vSideA Bv (orderOf Fv) budAny := by
  intro u hu
  rw [vmem_A] at hu
  obtain rfl := List.mem_singleton.1 hu
  intro p sp ca m ds asks hd _ _
  have hd' : drawsFit [sayR] ds = true := hd
  obtain ⟨R, rfl, -⟩ := drawsFit_one hd'
  by_cases hp : p = vaS
  · subst hp
    exact fresh_two (toF m.st.input.w₀.ans) eAt _ (fun c => vshows_A c sp ca m R asks)
      "a to the spender" vaA vaS _ _ rfl rfl
  · exact fresh_of_nil _ (spentBy_nil Bv vaA p fun e he ho _ hs =>
      hp (hs.symm.trans (Bv_spent e he ho).1)) _ _

theorem vB_fresh : FreshAt .own vSideB Bv (orderOf Fv) budAny := by
  intro u hu
  rw [vmem_B] at hu
  obtain rfl := List.mem_singleton.1 hu
  intro p sp ca m ds asks hd _ _
  have hd' : drawsFit [sayR] ds = true := hd
  obtain ⟨R, rfl, -⟩ := drawsFit_one hd'
  by_cases hp : p = vaS
  · subst hp
    exact fresh_two (toF (m.st.input.w₀.a 0)) eAt _ (fun c => vshows_B c sp ca m R asks)
      "b to the spender" vaB vaS _ _ rfl rfl
  · exact fresh_of_nil _ (spentBy_nil Bv vaB p fun e he ho _ hs =>
      hp (hs.symm.trans (Bv_spent e he ho).1)) _ _

/-- No coin of a part at another place than the two owners' is spent. -/
theorem Bv_unspent {a : Place} (hA : vpA ≠ a) (hB : vpB ≠ a) :
    ∀ e ∈ Bv.ahead, e.once = true → e.owner.place ≠ a := fun e he ho hq =>
  (Bv_spent e he ho).2.elim (fun h => hA (h.symm.trans hq)) fun h => hB (h.symm.trans hq)

theorem vS_fresh : FreshAt .own vSideS Bv (orderOf Fv) budOne :=
  fresh_unspent .own vSideS Bv (orderOf Fv) budOne
    (Bv_unspent (a := vSideS.block.place) (by decide) (by decide))
theorem vD_fresh : FreshAt .own vSideD Bv (orderOf Fv) budAny :=
  fresh_unspent .own vSideD Bv (orderOf Fv) budAny
    (Bv_unspent (a := vSideD.block.place) (by decide) (by decide))
theorem vM_fresh : FreshAt .own vSideM Bv (orderOf Fv) budAny :=
  fresh_unspent .own vSideM Bv (orderOf Fv) budAny
    (Bv_unspent (a := vSideM.block.place) (by decide) (by decide))
theorem vW_fresh : FreshAt .own vSideW Bv (orderOf Fv) budAny :=
  fresh_unspent .own vSideW Bv (orderOf Fv) budAny
    (Bv_unspent (a := vSideW.block.place) (by decide) (by decide))
theorem vE_fresh : FreshAt .own vSideE Bv (orderOf Fv) budAny :=
  fresh_unspent .own vSideE Bv (orderOf Fv) budAny
    (Bv_unspent (a := vSideE.block.place) (by decide) (by decide))
theorem vL_fresh : FreshAt .own vSideL Bv (orderOf Fv) budAny :=
  fresh_unspent .own vSideL Bv (orderOf Fv) budAny
    (Bv_unspent (a := vSideL.block.place) (by decide) (by decide))

end ProofFile.Honest.Toy

#print axioms ProofFile.Honest.Toy.cutAll_spendE
#print axioms ProofFile.Honest.Toy.fresh_two
#print axioms ProofFile.Honest.Toy.vmem_A
#print axioms ProofFile.Honest.Toy.vmem_B
#print axioms ProofFile.Honest.Toy.vmem_S
#print axioms ProofFile.Honest.Toy.vmem_D
#print axioms ProofFile.Honest.Toy.vmem_M
#print axioms ProofFile.Honest.Toy.vmem_W
#print axioms ProofFile.Honest.Toy.vmem_L
#print axioms ProofFile.Honest.Toy.vmem_E
#print axioms ProofFile.Honest.Toy.vshows_A
#print axioms ProofFile.Honest.Toy.vshows_B
#print axioms ProofFile.Honest.Toy.vshows_D
#print axioms ProofFile.Honest.Toy.vshows_M
#print axioms ProofFile.Honest.Toy.vshows_W
#print axioms ProofFile.Honest.Toy.vshows_L
#print axioms ProofFile.Honest.Toy.vshows_E
#print axioms ProofFile.Honest.Toy.vtells_A
#print axioms ProofFile.Honest.Toy.vtells_B
#print axioms ProofFile.Honest.Toy.vtells_D
#print axioms ProofFile.Honest.Toy.vtells_M
#print axioms ProofFile.Honest.Toy.vtells_W
#print axioms ProofFile.Honest.Toy.vtells_L
#print axioms ProofFile.Honest.Toy.steps_S
#print axioms ProofFile.Honest.Toy.bad_13
#print axioms ProofFile.Honest.Toy.bad_else
#print axioms ProofFile.Honest.Toy.vshows_S_13
#print axioms ProofFile.Honest.Toy.vshows_S
#print axioms ProofFile.Honest.Toy.vtells_S_13
#print axioms ProofFile.Honest.Toy.vtells_S
#print axioms ProofFile.Honest.Toy.vA_exact
#print axioms ProofFile.Honest.Toy.vB_exact
#print axioms ProofFile.Honest.Toy.vS_exact
#print axioms ProofFile.Honest.Toy.vD_exact
#print axioms ProofFile.Honest.Toy.vM_exact
#print axioms ProofFile.Honest.Toy.vW_exact
#print axioms ProofFile.Honest.Toy.vL_exact
#print axioms ProofFile.Honest.Toy.vE_exact
#print axioms ProofFile.Honest.Toy.Bv_spent
#print axioms ProofFile.Honest.Toy.vA_fresh
#print axioms ProofFile.Honest.Toy.vB_fresh
#print axioms ProofFile.Honest.Toy.Bv_unspent
#print axioms ProofFile.Honest.Toy.vS_fresh
#print axioms ProofFile.Honest.Toy.vD_fresh
#print axioms ProofFile.Honest.Toy.vM_fresh
#print axioms ProofFile.Honest.Toy.vW_fresh
#print axioms ProofFile.Honest.Toy.vE_fresh
#print axioms ProofFile.Honest.Toy.vL_fresh
