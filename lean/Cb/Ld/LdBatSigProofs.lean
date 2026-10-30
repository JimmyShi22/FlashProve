-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdBatSigProofs.lean: the proofs of the statements of Cb/Ld/LdBatSig.lean (batching on
statements with samples: many claims into one; the bridge to the existential relaxation).

Named tools: `Grp.near_mem`, `cnt_comp_ge`. Nothing is defined here that a statement reads.

Main names (statements and hypotheses: Cb/Ld/LdBatSig.lean):
  `ldBat_sig`, `ldBat_sig_lin`: many claims into one, on statements with samples; the same for rows.
  `ldBat_ex_beside`: the batching inside the existential relaxation, beside any carried joint.
  `ldBat_atMem`: the value of a form that lives on one member.
  `ldBat_rows_iff`: what the rows of a group say.
  `ldBat_fits`: where "the joint radius implies each member's own" comes from.
  `ldBat_step`: the step without rounds, without error.
  `ldBat_bridge`: the bridge.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdBatSig
import Cb.Ld.LdBatProofs
import Cb.Ld.LdSigProofs
import Ior.TailProofs

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Cb.Ood IOR

theorem ldBat_sig : Spec.ldBat_sig := by
  intro E B Kc St₀ Wp _ _ S Sb v Z E₀ A₀ q hZ
  refine pieceTr_of_piece _ _ _ _ _ _ _ _ _ _ _ (fun _ _ w => w) _ q q
    (piece_draw Kc _ _ (E₀.prod S.ext) (S.Wit × Wp) Z.D (ldBatSigNx S Sb Z St₀)
      (S.over (claimRels (Vf.All v) A₀)) (S.over (claimRels (Vf.bat Z.ze v).Holds A₀)) Z.err q ?_
      (fun _ _ _ h => h) (fun _ => rfl) ?_)
  · intro x y w ρ h
    exact ⟨h.1, h.2.1, ldBat_fwd E _ B Z.D Sb Z.ze v x.1.1 (S.msgs w.1) ρ h.2.2.1, h.2.2.2⟩
  · intro x y _
    refine (cnt_mono fun ρ h => ?_).trans
      (ldBat_cnt_one E S.Msg B Sb Z v x.1.1 (fun m => ∀ i, S.decs x.2 y.2 i = some (m i)) hZ
        fun m m' h h' => funext fun i => Option.some.inj ((h i).symm.trans (h' i)))
    obtain ⟨w, hB, hA⟩ := h
    exact ⟨S.msgs w.1, hB.1, hB.2.1, fun hall => hA ⟨hB.1, hall, hB.2.2⟩⟩

theorem ldBat_sig_lin : Spec.ldBat_sig_lin := by
  intro E B Kc St₀ Wp _ _ S Sb sl Z E₀ A₀ q hZ
  have e : (fun (x : E × ((∀ b, Sb b) × Z.D)) (m : S.Msg) => (Slf.bat Z.ze sl).Holds x (S.ents m)) =
      (Vf.bat Z.ze fun b =>
        (fun st (m : S.Msg) => (sl b).val st (S.ents m) : Vf E (Sb b) S.Msg)).Holds := by
    funext x m
    have h := congrFun (congrFun (ldBat_slf E S.Ent B Z.D Sb Z.ze sl) x.2) (S.ents m)
    exact propext ⟨fun h1 => h.symm.trans h1, fun h1 => h.trans h1⟩
  rw [e]
  exact ldBat_sig E B Kc St₀ Wp S Sb
    (fun b => (fun st (m : S.Msg) => (sl b).val st (S.ents m) : Vf E (Sb b) S.Msg)) Z E₀ A₀ q hZ

theorem ldBat_ex_beside : Spec.ldBat_ex_beside := by
  intro E P B Kc Xc Wc _ _ _ _ C Sb sl Z e L Ec Bc q hZ hL
  have hval : ∀ (x : E × ((∀ b, Sb b) × Z.D)) (m : C.J → E),
      (Slf.bat Z.ze sl).Holds x m ↔ (Vf.bat Z.ze fun b => (sl b).val).Holds x m := by
    intro x m
    have h := congrFun (congrFun (ldBat_slf E C.J B Z.D Sb Z.ze sl) x.2) m
    exact ⟨fun h1 => h.symm.trans h1, fun h1 => h.trans h1⟩
  refine pieceTr_of_piece _ _ _ _ _ _ _ _ _ _ _ (fun _ _ w => w) _ q q
    (piece_draw Kc _ _ (C.ext.prod Ec) (C.N.Wit × Wc) Z.D _
      (IOR.Rels.beside (C.relsAll sl e fun _ => ()) Bc)
      (IOR.Rels.beside (C.rels (Slf.bat Z.ze sl) e fun _ => ()) Bc) (L * Z.err) q ?_
      (fun _ _ _ h => h) (fun _ => rfl) ?_)
  · intro x y w ρ h
    exact ⟨⟨h.1.1,
        (hval _ _).2 (ldBat_fwd E _ B Z.D Sb Z.ze (fun b => (sl b).val) x.1 w.1.1 ρ h.1.2)⟩,
      h.2⟩
  · intro x y _
    have hl : ListLE (fun w : C.N.Wit => C.Near e y.1 (C.enc w.1 w.2)) L :=
      ood_list_of_cnt _ _ L (hL y.1)
    refine (cnt_mono fun ρ h => ?_).trans
      (cnt_exists_list_le _ L Z.err hl
        (fun (w : C.N.Wit) ρ =>
          (Vf.bat Z.ze fun b => (sl b).val).Holds (batNx Z.ze x.1 ρ) w.1 ∧
          ¬ Vf.All (fun b => (sl b).val) x.1 w.1)
        fun w _ => cnt_bat_at Z hZ _ x.1 w.1)
    obtain ⟨w, hB, hA⟩ := h
    exact ⟨w.1, hB.1.1, (hval _ _).1 hB.1.2, fun hall => hA ⟨⟨hB.1.1, hall⟩, hB.2⟩⟩

theorem ldBat_atMem : Spec.ldBat_atMem := by
  intro E St A _ _ _ Jf _ a sl st m
  rw [Fintype.sum_sigma, Finset.sum_eq_single a]
  · exact Finset.sum_congr rfl fun j _ => by simp [Slf.atMem]
  · intro b _ hb
    exact Finset.sum_eq_zero fun j _ => by simp [Slf.atMem, hb]
  · exact fun h => absurd (Finset.mem_univ a) h

theorem ldBat_rows_iff : Spec.ldBat_rows_iff := by
  intro E B _ S G Sb sl x σ u
  have hrow : ∀ (a : G.A) (s : (S.om a.1).Z.S),
      (G.rows sl (.inr ⟨a, s⟩)).Holds
        ((G.claims x σ).1 (.inr ⟨a, s⟩), (G.claims x σ).2 (.inr ⟨a, s⟩)) u ↔
      (S.om a.1).Z.val (σ a.1).1 (fun j => u ⟨a, j⟩) s = (σ a.1).2 s := by
    intro a s
    have h := ldBat_atMem E (S.om a.1).Z.D G.A (fun a : G.A => (S.om a.1).C.J) a
      ((S.om a.1).row s) (σ a.1).1 u
    exact ⟨fun h1 => h.symm.trans h1, fun h1 => h.trans h1⟩
  constructor
  · intro h
    exact ⟨fun b => h (.inl b), fun a => funext fun s => (hrow a s).1 (h (.inr ⟨a, s⟩))⟩
  · rintro ⟨h1, h2⟩ (b | ⟨a, s⟩)
    · exact h1 b
    · exact (hrow a s).2 (congrFun (h2 a) s)

/-- A reading that visits every position at least μ times multiplies a count by at least μ. -/
theorem cnt_comp_ge {P P' : Type} [Fintype P] [Fintype P'] (pos : P' → P) (μ : ℕ)
    (hμ : ∀ p, μ ≤ cnt fun x => pos x = p) (Q : P → Prop) :
    μ * cnt Q ≤ cnt fun x => Q (pos x) := by
  classical
  rw [cnt_eq_card_filter, cnt_eq_card_filter]
  have h1 : (Finset.univ.filter fun x => Q (pos x)).card =
      ∑ p ∈ Finset.univ.filter Q,
        ((Finset.univ.filter fun x => Q (pos x)).filter fun x => pos x = p).card :=
    Finset.card_eq_sum_card_fiberwise fun x hx =>
      Finset.mem_coe.2
        (Finset.mem_filter.2 ⟨Finset.mem_univ _, (Finset.mem_filter.1 (Finset.mem_coe.1 hx)).2⟩)
  rw [h1, mul_comm, ← smul_eq_mul, ← Finset.sum_const]
  refine Finset.sum_le_sum fun p hp => ?_
  refine (hμ p).trans ?_
  rw [cnt_eq_card_filter]
  refine Finset.card_le_card fun x hx => ?_
  have hx' := (Finset.mem_filter.1 hx).2
  exact Finset.mem_filter.2
    ⟨Finset.mem_filter.2 ⟨Finset.mem_univ _, hx' ▸ (Finset.mem_filter.1 hp).2⟩, hx'⟩

theorem ldBat_fits : Spec.ldBat_fits := by
  intro E _ S G μ hμ he a f g hn
  by_contra hc
  have h1 := cnt_comp_ge (G.pos a) (μ a) (hμ a) (fun p => (S.om a.1).C.T f p ≠ (S.om a.1).C.T g p)
  have h2 : (S.om a.1).e + 1 ≤ cnt fun p => (S.om a.1).C.T f p ≠ (S.om a.1).C.T g p := not_le.1 hc
  have h3 : cnt (fun x => (S.om a.1).C.T f (G.pos a x) ≠ (S.om a.1).C.T g (G.pos a x)) ≤ G.e := hn
  exact absurd (he a) (not_lt.2 ((Nat.mul_le_mul_left _ h2).trans (h1.trans h3)))


section Bridge
variable {E : Type} {S : Sig E} (G : Grp S)

/-- Near in the complex of a group gives near in each member, at the common positions. -/
theorem Grp.near_mem [Field E] (k : ℕ) (f g : G.C.Word) (h : G.C.Near k f g) (a : G.A) :
    ((S.om a.1).C.atPos (G.pos a)).Near k (fun p => f ⟨a, p⟩) (fun p => g ⟨a, p⟩) := by
  have h' : cnt (fun x => G.C.T f x ≠ G.C.T g x) ≤ k := h
  show cnt (fun x =>
      (S.om a.1).C.T (fun p => f ⟨a, p⟩) (G.pos a x) ≠
        (S.om a.1).C.T (fun p => g ⟨a, p⟩) (G.pos a x)) ≤ k
  refine le_trans (cnt_mono (Q := fun x => G.C.T f x ≠ G.C.T g x) fun x hx hfg => hx ?_) h'
  funext α
  exact congrFun hfg ⟨a, α⟩

theorem Grp.toExt_isLocal : G.toExt.IsLocal := by
  classical
  intro y y' x h
  funext α
  have h1 := h ⟨α.1.1, G.pos α.1 x⟩ (Finset.mem_image.2 ⟨α.1, Finset.mem_univ _, rfl⟩)
  have h2 : (S.om α.1.1).C.T ((S.om α.1.1).upW (y α.1.1)) (G.pos α.1 x) =
      (S.om α.1.1).C.T ((S.om α.1.1).upW (y' α.1.1)) (G.pos α.1 x) :=
    eq_of_heq (Sigma.mk.inj h1).2
  exact congrFun h2 α.2

theorem Sig.subExt_isLocal (kp : S.O → Prop) [DecidablePred kp] : (S.subExt kp).IsLocal := by
  intro y y' q h
  have h1 := h ⟨q.1.1, q.2⟩ (Finset.mem_singleton_self _)
  have h2 : (S.om q.1.1).C.T ((S.om q.1.1).upW (y q.1.1)) q.2 =
      (S.om q.1.1).C.T ((S.om q.1.1).upW (y' q.1.1)) q.2 :=
    eq_of_heq (Sigma.mk.inj h1).2
  exact Sigma.ext rfl (heq_of_eq h2)

end Bridge

theorem ldBat_step : Spec.ldBat_step := by
  intro E B Kc St₀ Wp _ _ _ S G kp _ Sb sl E₀ A₀ hc hF
  obtain ⟨_, hfs, _, hcomp, hpair⟩ := extMap_isLocal
  refine ⟨?_, ?_, ?_, fun _ _ => rfl, ?_⟩
  · exact hpair _ _ _ _ _ (hcomp _ _ _ _ _ G.toExt_isLocal (hfs E₀ S.ext).2)
      (hpair _ _ _ _ _ (hfs E₀ S.ext).1 (hcomp _ _ _ _ _ (Sig.subExt_isLocal kp) (hfs E₀ S.ext).2))
  · rintro x y w ⟨hE, hA, hR, h0⟩
    refine ⟨rfl, ⟨?_, ?_⟩, fun a => hE a.1, fun a => hA a.1, h0⟩
    · funext p
      exact congrFun (hE p.1.1) p.2
    · exact (ldBat_rows_iff E B S G Sb sl x.1.1 x.2 (G.msg (S.msgs w.1))).2 ⟨hR, fun a => hA a.1⟩
  · rintro x y x' ⟨hcf, h0⟩ hx
    rw [← Option.some.inj hx]
    exact ⟨trivial, fun a => hcf a.1, h0⟩
  · rintro x y x' w' ⟨hcf, _⟩ hx hB
    rw [← Option.some.inj hx] at hB
    obtain ⟨⟨hnear, hrows⟩, hdec, h0⟩ := hB
    obtain ⟨hsl, hans⟩ := (ldBat_rows_iff E B S G Sb sl x.1.1 x.2 w'.1.1).1 hrows
    have hmem : ∀ (o : S.O) (h : G.mem o), S.decs x.2 y.2 o = some fun j => w'.1.1 ⟨⟨o, h⟩, j⟩ := by
      intro o h
      refine (sig_dec_good E (S.om o) (y.2 o) (x.2 o).1 (hcf o) (x.2 o).2 _).2
        ⟨⟨fun q => w'.1.2 ⟨⟨o, h⟩, q⟩, ?_⟩, hans ⟨o, h⟩⟩
      exact hF ⟨o, h⟩ _ _ (G.near_mem G.e _ _ hnear ⟨o, h⟩)
    have hb1 : ∀ (o : S.O) (h : G.mem o),
        ((ldBrBack G kp Wp hc w').1 o).1 = fun j => w'.1.1 ⟨⟨o, h⟩, j⟩ := by
      intro o h
      simp [ldBrBack, h]
    have hb2 : ∀ (o : S.O) (h : ¬ G.mem o),
        (ldBrBack G kp Wp hc w').1 o = w'.2.1 ⟨o, (hc o).resolve_left h⟩ := by
      intro o h
      simp [ldBrBack, h]
    have hall : ∀ o, S.decs x.2 y.2 o = some ((ldBrBack G kp Wp hc w').1 o).1 := by
      intro o
      by_cases h : G.mem o
      · rw [hb1 o h]
        exact hmem o h
      · rw [hb2 o h]
        exact hdec ⟨o, (hc o).resolve_left h⟩
    refine ⟨hall, ?_, ?_⟩
    · have e : G.msg (S.msgs (ldBrBack G kp Wp hc w').1) = w'.1.1 := by
        funext n
        exact congrFun (hb1 n.1.1 n.1.2) n.2
      show Slf.All sl x.1.1 (G.msg (S.msgs (ldBrBack G kp Wp hc w').1))
      rw [e]
      exact hsl
    · have e : S.res (T := OMsg.Msg) kp (S.msgs (ldBrBack G kp Wp hc w').1) =
          (S.sub kp).msgs w'.2.1 := by
        funext a
        exact Option.some.inj ((hall a.1).symm.trans (hdec a))
      show A₀.relR (x.1.2, y.1)
        (S.res (T := OMsg.Msg) kp (S.msgs (ldBrBack G kp Wp hc w').1), w'.2.2)
      rw [e]
      exact h0

open Classical in
theorem ldBat_bridge : Spec.ldBat_bridge := by
  intro E B Kc St₀ Wp _ _ _ S G kp _ Sb sl Z L E₀ A₀ hc qi qo hZ hL hF hq
  have hval : ∀ (x : E × ((∀ ν, G.RowSt Sb ν) × Z.D)) (m : G.C.J → E),
      (Slf.bat Z.ze (G.rows sl)).Holds x m ↔
      (Vf.bat Z.ze fun ν => (G.rows sl ν).val).Holds x m := by
    intro x m
    have h :=
      congrFun (congrFun (ldBat_slf E G.C.J (G.Row B) Z.D (G.RowSt Sb) Z.ze (G.rows sl)) x.2) m
    exact ⟨fun h1 => h.symm.trans h1, fun h1 => h.trans h1⟩
  have hp : Piece (IOR.draw Z.D (ldBrNx G kp Sb Z St₀) (LdBrE G kp E₀))
      (Honest.draw Z.D (ldBrNx G kp Sb Z St₀) (LdBrE G kp E₀) (LdBrW G kp Wp))
      (IOR.Rels.beside (G.C.relsAll (G.rows sl) G.e fun _ => ()) ((S.sub kp).over A₀))
      (IOR.Rels.beside (G.C.rels (Slf.bat Z.ze (G.rows sl)) G.e fun _ => ()) ((S.sub kp).over A₀))
      (fun _ _ w => w)
      (Nums.draw Kc Z.D (ldBrNx G kp Sb Z St₀) (LdBrE G kp E₀) (L * Z.err)) qo qo := by
    refine piece_draw Kc _ _ (LdBrE G kp E₀) (LdBrW G kp Wp) Z.D (ldBrNx G kp Sb Z St₀) _ _
      (L * Z.err) qo ?_ (fun _ _ _ h => h) (fun _ => rfl) ?_
    · intro x y w ρ h
      exact ⟨⟨h.1.1,
          (hval _ _).2
            (ldBat_fwd E _ (G.Row B) Z.D (G.RowSt Sb) Z.ze
              (fun ν => (G.rows sl ν).val) x.1 w.1.1 ρ h.1.2)⟩,
        h.2⟩
    · intro x y _
      have hl : ListLE (fun w : G.C.N.Wit => G.C.Near G.e y.1 (G.C.enc w.1 w.2)) L :=
        ood_list_of_cnt _ _ L (hL y.1)
      refine (cnt_mono fun ρ h => ?_).trans
        (cnt_exists_list_le _ L Z.err hl
          (fun (w : G.C.N.Wit) ρ =>
            (Vf.bat Z.ze fun ν => (G.rows sl ν).val).Holds (batNx Z.ze x.1 ρ) w.1 ∧
            ¬ Vf.All (fun ν => (G.rows sl ν).val) x.1 w.1)
          fun w _ => cnt_bat_at Z hZ _ x.1 w.1)
      obtain ⟨w, hB, hA⟩ := h
      exact ⟨w.1, hB.1.1, (hval _ _).1 hB.1.2, fun hall => hA ⟨⟨hB.1.1, hall⟩, hB.2⟩⟩
  exact pieceTr_of_piece _ _ _ _ _ _ _ _ _ _ _ (fun _ _ w => ldBrBack G kp Wp hc w) _ qi qo
    (piece_pre Kc _ _ _ _ _ _ _ _ _ _ _ _ _ _ (fun _ _ w => w) _ _ _ _
      (fun _ w => ldBrBack G kp Wp hc w) qo qi qo
      (ldBat_step E B Kc St₀ Wp S G kp Sb sl E₀ A₀ hc hF) hp fun U hU => by convert hq U hU)

end Cb
