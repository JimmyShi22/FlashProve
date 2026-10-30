-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdPscProofsIor.lean: proofs for Cb/Ld/LdPsc.lean, second part: the block as an IOR.

Strings (`psc_point`) and locality (`psc_local`); completeness; the main step of knowledge soundness
for the whole block; knowledge soundness in its two forms (for each fixed tuple of messages at the
base; with a carried part, where the relaxed relation determines the entries (`PscBase.Det`)); the
output rows.

Main names:
  `PscCopy`: what the rules below ask of an IOR that copies state and oracles: the main step, in the
    form "a claim that is false of m stays false of m".
  `PscCopy.know_at`, `PscCopy.know_det`, `psc_acc_keep`: from the main step to the two forms; from
    completeness at the base to completeness with a carried part.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdPscProofs
import Ior.FrameProofs
import Ior.SeqProofs

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop

/-! ## The rules, for any IOR that copies state and oracles -/

section Generic
variable {E J St X X' : Type} {Ex : ExtSpec}

/-- R copies the state of the claim and the oracles, and a claim that is false of m stays false of
m, but for the errors ε. -/
structure PscCopy (R : IOR X Ex X' Ex) (stOf : X → St) (stOf' : X' → St) (Φ : X → (J → E) → Prop)
    (Φ' : X' → (J → E) → Prop) (ε : Err R.shape) : Prop where
  st : ∀ x y τ o, R.out x y τ = some o → stOf' o = stOf x
  imp : ∀ y τ, R.imp y τ = y
  sound : ∀ x y m, ¬ Φ x m → Doomed R.shape ε fun τ => ∀ o, R.out x y τ = some o → ¬ Φ' o m

variable {R : IOR X Ex X' Ex} {stOf : X → St} {stOf' : X' → St} {Φ : X → (J → E) → Prop}
  {Φ' : X' → (J → E) → Prop} {ε : Err R.shape}

theorem PscCopy.red (h : PscCopy R stOf stOf' Φ Φ' ε) {a : X × Ex.Str} {τ : Tr R.shape}
    {b : X' × Ex.Str} (hb : R.red.out a τ = some b) :
    R.out a.1 a.2 τ = some b.1 ∧ stOf' b.1 = stOf a.1 ∧ b.2 = a.2 := by
  obtain ⟨h1, h2⟩ := IOR.red_out_eq_some.1 hb
  exact ⟨h1, h.st _ _ _ _ h1, h2.trans (h.imp _ _)⟩

theorem PscCopy.know_at (h : PscCopy R stOf stOf' Φ Φ' ε) {M Wp Kc : Type}
    (A0 : IOR.Rels Kc St Ex (M × Wp)) (msg : M → J → E) (m : M) :
    R.red.Know (fun a => A0.on (stOf a.1, a.2))
      (fun a wp => A0.relR (stOf a.1, a.2) (m, wp) ∧ Φ a.1 (msg m))
      (fun b wp => A0.relR (stOf' b.1, b.2) (m, wp) ∧ Φ' b.1 (msg m)) (fun _ _ wp => wp) ε := by
  intro a _
  by_cases hS : Φ a.1 (msg m)
  · refine Doomed.of_forall _ _ fun τ b wp hb hw => ⟨?_, hS⟩
    obtain ⟨_, h2, h3⟩ := h.red hb
    rw [← h2, ← h3]
    exact hw.1
  · refine Doomed.mono _ _ ?_ (h.sound a.1 a.2 (msg m) hS)
    intro τ hτ b wp hb hw
    exact absurd hw.2 (hτ b.1 (h.red hb).1)

theorem PscCopy.carry_base (h : PscCopy R stOf stOf' Φ Φ' ε) {Wt Kc : Type}
    (A0 : IOR.Rels Kc St Ex Wt) (a : X × Ex.Str) (τ : Tr R.shape) (b : X' × Ex.Str)
    (ha : A0.on (stOf a.1, a.2)) (hb : R.red.out a τ = some b) : A0.on (stOf' b.1, b.2) := by
  obtain ⟨_, h2, h3⟩ := h.red hb
  rw [h2, h3]
  exact ha

end Generic

section GenericKeep
variable {E J St X X' Cr : Type} {E₀ F : ExtSpec} {R : IOR X E₀ X' E₀} {stOf : X → St}
  {stOf' : X' → St} {Φ : X → (J → E) → Prop} {Φ' : X' → (J → E) → Prop}
  {ε : Err R.shape} {Wt : Type}

theorem PscCopy.red_keep (h : PscCopy R stOf stOf' Φ Φ' ε) {a : (X × Cr) × (E₀.prod F).Str}
    {τ : Tr R.shape} {b : (X' × Cr) × (E₀.prod F).Str} (hb : (R.keep Cr F).red.out a τ = some b) :
    R.out a.1.1 a.2.1 τ = some b.1.1 ∧
    ((stOf' b.1.1, b.1.2), b.2) = ((stOf a.1.1, a.1.2), a.2) := by
  obtain ⟨e1, h1⟩ := IOR.keepE_red_out (R.keepX Cr) F a τ b hb
  obtain ⟨e2, h2⟩ := IOR.keepX_red_out R Cr (a.1, a.2.1) τ (b.1, b.2.1) h1
  obtain ⟨h3, h4, h5⟩ := h.red h2
  exact ⟨h3, Prod.ext (Prod.ext h4 e2) (Prod.ext h5 e1)⟩

theorem PscCopy.know_det (h : PscCopy R stOf stOf' Φ Φ' ε)
    (Bs : PscBase E J St Cr (E₀.prod F) Wt) (hD : Bs.Det) :
    (R.keep Cr F).red.Know (Bs.rels stOf Φ fun _ => ()).on (Bs.rels stOf Φ fun _ => ()).relR
      (Bs.rels stOf' Φ' fun _ => ()).relR (fun _ _ w => w) ε := by
  intro a ha
  by_cases hS : ∃ w0, Bs.relR ((stOf a.1.1, a.1.2), a.2) w0 ∧ ¬ Φ a.1.1 (Bs.msg w0)
  · obtain ⟨w0, hw0, hn⟩ := hS
    refine Doomed.mono _ _ ?_ (h.sound a.1.1 a.2.1 (Bs.msg w0) hn)
    intro τ hτ b w hb hw
    obtain ⟨h1, h2⟩ := h.red_keep hb
    have hr : Bs.relR ((stOf a.1.1, a.1.2), a.2) w := h2 ▸ hw.1
    have hm : Bs.msg w = Bs.msg w0 := hD _ w w0 ha hr hw0
    exact absurd (hm ▸ hw.2) (hτ b.1.1 h1)
  · refine Doomed.of_forall _ _ fun τ b w hb hw => ?_
    obtain ⟨_, h2⟩ := h.red_keep hb
    have hr : Bs.relR ((stOf a.1.1, a.1.2), a.2) w := h2 ▸ hw.1
    exact ⟨hr, by_contra fun hn => hS ⟨w, hr, hn⟩⟩

theorem PscCopy.carry_keep (h : PscCopy R stOf stOf' Φ Φ' ε) (Bs : PscBase E J St Cr (E₀.prod F) Wt)
    (a : (X × Cr) × (E₀.prod F).Str) (τ : Tr R.shape) (b : (X' × Cr) × (E₀.prod F).Str)
    (ha : (Bs.rels stOf Φ fun _ => ()).on a) (hb : (R.keep Cr F).red.out a τ = some b) :
    (Bs.rels stOf' Φ' fun _ => ()).on b := by
  obtain ⟨_, h2⟩ := h.red_keep hb
  show Bs.on ((stOf' b.1.1, b.1.2), b.2)
  rw [h2]
  exact ha

/-- completeness at the base, whatever rides along, gives completeness with a carried part -/
theorem psc_acc_keep (H : R.Honest Wt Wt) (Bs : PscBase E J St Cr (E₀.prod F) Wt)
    (hacc : ∀ P : St → E₀.Str → Wt → Prop, H.Acc (fun x y w => P (stOf x) y w ∧ Φ x (Bs.msg w))
      (fun o y w => P (stOf' o) y w ∧ Φ' o (Bs.msg w))) :
    (H.keep Cr F).Acc (Bs.rels stOf Φ fun _ => ()).rel (Bs.rels stOf' Φ' fun _ => ()).rel := by
  intro x y w c ρ hR hρ
  obtain ⟨h1, h2⟩ := hacc (fun st y₀ w => Bs.rel (st, x.2) (y₀, y.2) w) x.1 y.1 w c ρ hR hρ
  have e := IOR.Honest.keepX_run H Cr w x c ρ
  show (R.keep Cr F).out x y (((H.keepX Cr).strat w x c).run ρ).1 =
      some (((H.keepX Cr).strat w x c).run ρ).2.1 ∧
    (Bs.rels stOf' Φ' fun _ => ()).rel (((H.keepX Cr).strat w x c).run ρ).2.1
      ((R.keep Cr F).imp y (((H.keepX Cr).strat w x c).run ρ).1)
      (((H.keepX Cr).strat w x c).run ρ).2.2
  rw [e]
  refine ⟨?_, h2⟩
  show (R.out x.1 y.1 ((H.strat w x.1 c).run ρ).1).map (fun xo => (xo, x.2)) = _
  rw [h1]
  rfl

end GenericKeep

/-! ## The claims -/

section Claims
variable (E : Type) [Field E]

theorem psc_out_iff : Spec.psc_out_iff E := by
  intro Y o m
  constructor
  · rintro ⟨hU, hE⟩
    refine ⟨?_, hE⟩
    have e : (fun a => Y.G o.st m a (Y.hp o.st o.pt)) = o.vals := funext hE
    unfold PscPar.UHolds at hU
    unfold PscPar.MidHolds PscPar.whole PscPar.sum
    simp only
    rw [e]
    linear_combination hU
  · rintro ⟨hM, hE⟩
    refine ⟨?_, hE⟩
    have e : (fun a => Y.G o.st m a (Y.hp o.st o.pt)) = o.vals := funext hE
    unfold PscPar.MidHolds PscPar.whole PscPar.sum at hM
    simp only at hM
    rw [e] at hM
    unfold PscPar.UHolds
    linear_combination hM

theorem psc_out_mid : Spec.psc_out_mid E := fun Y o m h => ((psc_out_iff E Y o m).1 h).1

theorem psc_mid_empty : Spec.psc_mid_empty E := fun Y _ z m =>
  ⟨fun h =>
      ((psc_out_iff E Y ⟨z.st, z.eps, z.pt, z.fin, isEmptyElim⟩ m).2 ⟨h, fun a => isEmptyElim a⟩).1,
    fun h =>
      ((psc_out_iff E Y ⟨z.st, z.eps, z.pt, z.fin, isEmptyElim⟩ m).1 ⟨h, fun a => isEmptyElim a⟩).1⟩

theorem psc_row_E : Spec.psc_row_E E := fun Y rowA hA o m a => by
  unfold PscPar.EHolds Slf.Holds PscPar.slE
  rw [hA]

theorem psc_row_U : Spec.psc_row_U E := by
  classical
  intro Y rowB hB o m
  have h1 : hU (Y.vars o.st) (Y.W o.st m) (Y.hp o.st o.pt) =
      ∑ j, (∑ i, if Y.wAt (pIx Y.fmt (Y.dat o.st) i) = j then hSl (Y.vars o.st) (Y.hp o.st o.pt) i
          else 0) * m j := by
    rw [hide_form E E]
    simp only [Finset.sum_mul, smul_eq_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rfl
  have hB' : ∀ b, Y.Gb o.st m b (Y.hp o.st o.pt) = ∑ j, rowB o.st b (Y.hp o.st o.pt) j * m j :=
    fun b => hB _ _ _ _
  have h2 : ∑ b, Y.S1 o.st (Y.hp o.st o.pt) o.vals b * Y.Gb o.st m b (Y.hp o.st o.pt) =
      ∑ j, (∑ b, Y.S1 o.st (Y.hp o.st o.pt) o.vals b * rowB o.st b (Y.hp o.st o.pt) j) * m j := by
    simp only [hB', Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun b _ => by ring
  have h3 : ∑ j, Y.slU rowB o j * m j =
      ∑ j, (∑ i, if Y.wAt (pIx Y.fmt (Y.dat o.st) i) = j then hSl (Y.vars o.st) (Y.hp o.st o.pt) i
            else 0) * m j +
        o.eps * hPsi (Y.vars o.st) (Y.hp o.st o.pt) * ∑ j, Y.slS o.st j * m j +
        o.eps * ∑ j,
            (∑ b, Y.S1 o.st (Y.hp o.st o.pt) o.vals b * rowB o.st b (Y.hp o.st o.pt) j) * m j := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    unfold PscPar.slU
    ring
  show _ ↔ ∑ j, Y.slU rowB o j * m j = Y.tU o
  rw [h3, ← h1, ← h2]
  exact Iff.rfl

end Claims

/-! ## The reduction itself: strings, the verifier's output, locality -/

section Term
variable {E : Type} [Field E]

def pRound_point (f : PFmt E) : (pRound f).IsPoint where
  finPos := inferInstanceAs (Fintype Empty)
  decPos := inferInstanceAs (DecidableEq Empty)
  ofSyms := fun _ => ()
  rd_ofSyms := fun _ p => p.elim
  ofSyms_rd := fun _ => rfl
  zero := fun _ => ()

def pRounds_point : (l : List (PFmt E)) → Shape.IsPoint (pRounds l)
  | [] => ()
  | f :: l => (pRound_point f, pRounds_point l)

variable [Fintype E]

def pRound0_point : (pRound0 E).IsPoint where
  finPos := inferInstanceAs (Fintype Empty)
  decPos := inferInstanceAs (DecidableEq Empty)
  ofSyms := fun _ => ()
  rd_ofSyms := fun _ p => p.elim
  ofSyms_rd := fun _ => rfl
  zero := fun _ => ()

omit [Fintype E] in
def pRoundV_point (A : Type) : (pRoundV E A).IsPoint where
  finPos := inferInstanceAs (Fintype Empty)
  decPos := inferInstanceAs (DecidableEq Empty)
  ofSyms := fun _ => ()
  rd_ofSyms := fun _ p => p.elim
  ofSyms_rd := fun _ => rfl
  zero := fun _ => ()

namespace PscPar
variable (Y : PscPar E)

theorem outC_congr (x : E × Y.St) (τ τ' : Tr Y.shapeC)
    (h1 : τ.rho = τ'.rho) (h2 : τ.plains = τ'.plains) : Y.outC x τ = Y.outC x τ' := by
  unfold outC mu eps pt qs
  rw [h1, h2]

theorem outC_st (x : E × Y.St) (τ : Tr Y.shapeC) (z : Y.Mid) (h : Y.outC x τ = some z) :
    z.st = x.2 := by
  unfold outC at h
  split at h
  · obtain rfl := Option.some.inj h
    rfl
  · exact absurd h (by simp)

theorem outC_eq (x : E × Y.St) (τ : Tr Y.shapeC) (μ ε : E) (γ : PPt Y.fmt)
    (q : RIdx (Y.vars x.2) → E) (h1 : Y.mu τ = μ) (h2 : Y.eps τ = ε) (h3 : Y.pt τ = γ)
    (h4 : Y.qs x.2 τ = q) (hC : HCons (Y.vars x.2) (μ + ε * x.1) q (Y.hp x.2 γ)) :
    Y.outC x τ = some ⟨x.2, ε, γ, hFin (Y.vars x.2) (μ + ε * x.1) q (Y.hp x.2 γ)⟩ := by
  unfold outC
  rw [h1, h2, h3, h4, if_pos hC]

theorem core_local (Ex : ExtSpec) : (Y.core Ex).IsLocal where
  out := fun x _ _ τ τ' h1 h2 _ _ => Y.outC_congr x τ τ' h1 h2
  imp := fun _ _ _ _ q _ _ h _ => h q (Finset.mem_singleton_self q)

omit [Fintype E] in
theorem ends_local (Ex : ExtSpec) : (Y.ends Ex).IsLocal where
  out := fun z _ _ τ τ' _ h2 _ _ => by
    show some (⟨z.st, z.eps, z.pt, z.fin, τ.plains.1⟩ : Y.Out) =
      some ⟨z.st, z.eps, z.pt, z.fin, τ'.plains.1⟩
    rw [h2]
  imp := fun _ _ _ _ q _ _ h _ => h q (Finset.mem_singleton_self q)

theorem psc_out_some (Ex : ExtSpec) (x : E × Y.St) (y : Ex.Str) (τ₁ : Tr (Y.core Ex).shape)
    (τ₂ : Tr (Y.ends Ex).shape) (o : Y.Out) (h : (Y.psc Ex).out x y (Tr.app τ₁ τ₂) = some o) :
    Y.outC x τ₁ = some ⟨o.st, o.eps, o.pt, o.fin⟩ := by
  have h' : ((Y.core Ex).seq (Y.ends Ex)).out x y (Tr.app τ₁ τ₂) = some o := h
  rw [IOR.seq_out_app] at h'
  obtain ⟨z, hz, ho⟩ := Option.bind_eq_some_iff.1 h'
  obtain rfl := Option.some.inj ho
  exact hz

end PscPar
end Term

section Main
variable (E : Type) [Field E] [Fintype E]

theorem psc_point : Spec.psc_point E := fun Y _ =>
  ⟨Shape.IsPoint.append (s := Y.shapeC) (t := [pRoundV E Y.A])
    (pRound0_point, pRounds_point Y.fmt) (pRoundV_point Y.A, ())⟩

theorem psc_local : Spec.psc_local E := fun Y Ex => (Y.core_local Ex).seq (Y.ends_local Ex)

theorem psc_len : Spec.psc_len E := fun Y Ex => by
  show (Y.shapeC ++ [pRoundV E Y.A]).length = _
  simp

/-- Completeness of `core` (round 0 and the rounds of the variables), whatever rides along. -/
theorem psc_core_acc_any (Y : PscPar E) (Ex : ExtSpec) (Wt : Type) (msg : Wt → Y.J → E)
    (hV : Y.VarsOK) (hD : Y.DegOK) (P : Y.St → Ex.Str → Wt → Prop) :
    (Y.honC Ex msg).Acc (fun x y w => P x.2 y w ∧ Y.SumHolds x (msg w))
      (fun z y w => P z.st y w ∧ Y.MidHolds z (msg w)) := by
  intro x y w c ρ hR _
  obtain ⟨h1, h2, h3, h4⟩ := psc_run E Y Ex Wt msg w x ρ
  obtain ⟨c1, c2⟩ :=
    hRounds_cons _ _ _ _ (Y.whole_rounds hV hD x.2 (msg w) ρ.1 (Y.hp x.2 (pG Y.fmt ρ.2)))
  have hs : hSumAll (Y.vars x.2) (Y.whole x.2 (msg w) ρ.1) =
      hMu (Y.vars x.2) (Y.W x.2 (msg w)) + ρ.1 * x.1 := by
    rw [Y.whole_sum hV, hR.2]
  rw [hs] at c1 c2
  have ho := Y.outC_eq x (((Y.honC Ex msg).strat w x ()).run ρ).1 _ ρ.1 (pG Y.fmt ρ.2) _ h1
    (congrArg (fun r : Rho Y.shapeC => r.1) h3)
    (congrArg (fun r : Rho Y.shapeC => pG Y.fmt r.2) h3) h2 c1
  rw [c2] at ho
  refine ⟨?_, ?_⟩
  · show Y.outC x (((Y.honC Ex msg).strat w x ()).run ρ).1 =
      some (((Y.honC Ex msg).strat w x ()).run ρ).2.1
    rw [ho, h4]
    rfl
  · show P (((Y.honC Ex msg).strat w x ()).run ρ).2.1.st y
        (((Y.honC Ex msg).strat w x ()).run ρ).2.2 ∧
      Y.MidHolds (((Y.honC Ex msg).strat w x ()).run ρ).2.1
        (msg (((Y.honC Ex msg).strat w x ()).run ρ).2.2)
    rw [h4]
    exact ⟨hR.1, rfl⟩

omit [Fintype E] in
theorem psc_ends_acc_any (Y : PscPar E) (Ex : ExtSpec) (Wt : Type)
    (msg : Wt → Y.J → E) (P : Y.St → Ex.Str → Wt → Prop) :
    (Y.honE Ex msg).Acc (fun z y w => P z.st y w ∧ Y.MidHolds z (msg w))
      (fun o y w => P o.st y w ∧ Y.OutHolds o (msg w)) := by
  intro z y w c ρ hR _
  exact ⟨rfl, hR.1, (psc_out_iff E Y (Y.honOut z (msg w)) (msg w)).2 ⟨hR.2, fun _ => rfl⟩⟩

theorem psc_acc_any (Y : PscPar E) (Ex : ExtSpec) (Wt : Type) (msg : Wt → Y.J → E) (hV : Y.VarsOK)
    (hD : Y.DegOK) (P : Y.St → Ex.Str → Wt → Prop) :
    (Y.hon Ex msg).Acc (fun x y w => P x.2 y w ∧ Y.SumHolds x (msg w))
      (fun o y w => P o.st y w ∧ Y.OutHolds o (msg w)) :=
  (psc_core_acc_any E Y Ex Wt msg hV hD P).seq (psc_ends_acc_any E Y Ex Wt msg P)

theorem psc_core_acc_base : Spec.psc_core_acc_base E := fun Y Ex Wt _ A0 msg hV hD =>
  psc_core_acc_any E Y Ex Wt msg hV hD A0.rel
theorem psc_acc_base : Spec.psc_acc_base E := fun Y Ex Wt _ A0 msg hV hD =>
  psc_acc_any E Y Ex Wt msg hV hD A0.rel

theorem psc_core_acc : Spec.psc_core_acc E := fun Y _ E₀ _ Wt Bs hV hD =>
  psc_acc_keep (stOf := Prod.snd) (stOf' := PscPar.Mid.st) (Φ := Y.SumHolds) (Φ' := Y.MidHolds)
    (Y.honC E₀ Bs.msg) Bs (psc_core_acc_any E Y E₀ Wt Bs.msg hV hD)
theorem psc_acc : Spec.psc_acc E := fun Y _ E₀ _ Wt Bs hV hD =>
  psc_acc_keep (stOf := Prod.snd) (stOf' := PscPar.Out.st) (Φ := Y.SumHolds) (Φ' := Y.OutHolds)
    (Y.hon E₀ Bs.msg) Bs (psc_acc_any E Y E₀ Wt Bs.msg hV hD)

theorem psc_keeps : Spec.psc_keeps E := by
  intro Y Ex Wt msg w x c ρ
  have e := IOR.Honest.run_seq (Y.honC Ex msg) (Y.honE Ex msg) w x c ρ
  have h4 := (psc_run E Y Ex Wt msg w x (Rho.fst ρ)).2.2.2
  show ((((Y.honC Ex msg).seq (Y.honE Ex msg)).strat w x c).run ρ).2.2 = w
  rw [e]
  show (((Y.honC Ex msg).strat w x ()).run (Rho.fst ρ)).2.2 = w
  rw [h4]

/-- The main step, for the whole block. -/
theorem psc_sound_at : Spec.psc_sound_at E := by
  intro Y Ex hV hD hI x y m hx
  refine Doomed.append (Y.core Ex).shape (Y.ends Ex).shape (Y.errC Ex) _ _
    (Doomed.mono _ _ ?_ (psc_core_sound_at E Y Ex hV hD hI x m hx))
  intro τ₁ h₁
  refine Doomed.of_forall _ _ fun τ₂ o ho hO => ?_
  exact h₁ _ (Y.psc_out_some Ex x y τ₁ τ₂ o ho) (psc_out_mid E Y o m hO)

theorem psc_copy_core (Y : PscPar E) (Ex : ExtSpec) (hV : Y.VarsOK) (hD : Y.DegOK) (hI : Y.ValInj) :
    PscCopy (Y.core Ex) Prod.snd PscPar.Mid.st Y.SumHolds Y.MidHolds (Y.errC Ex) where
  st := fun x _ τ z h => Y.outC_st x τ z h
  imp := fun _ _ => rfl
  sound := fun x _ m hx => psc_core_sound_at E Y Ex hV hD hI x m hx

theorem psc_copy (Y : PscPar E) (Ex : ExtSpec) (hV : Y.VarsOK) (hD : Y.DegOK) (hI : Y.ValInj) :
    PscCopy (Y.psc Ex) Prod.snd PscPar.Out.st Y.SumHolds Y.OutHolds (Y.err Ex) where
  st := fun x y τ o h => by
    have h' : (Y.psc Ex).out x y (Tr.app (Tr.fst τ) (Tr.snd (s := (Y.core Ex).shape) τ)) =
        some o := by
      rw [Tr.app_fst_snd]; exact h
    exact Y.outC_st x _ _ (Y.psc_out_some Ex x y _ _ o h')
  imp := fun _ _ => rfl
  sound := fun x y m hx => psc_sound_at E Y Ex hV hD hI x y m hx

theorem psc_know_at : Spec.psc_know_at E := fun Y Ex _ _ _ A0 msg hV hD hI m =>
  (psc_copy E Y Ex hV hD hI).know_at A0 msg m
theorem psc_core_know_at : Spec.psc_core_know_at E := fun Y Ex _ _ _ A0 msg hV hD hI m =>
  (psc_copy_core E Y Ex hV hD hI).know_at A0 msg m
theorem psc_know : Spec.psc_know E := fun Y _ E₀ _ _ Bs hV hD hI hDet =>
  (psc_copy E Y E₀ hV hD hI).know_det Bs hDet
theorem psc_core_know : Spec.psc_core_know E := fun Y _ E₀ _ _ Bs hV hD hI hDet =>
  (psc_copy_core E Y E₀ hV hD hI).know_det Bs hDet

theorem psc_carry : Spec.psc_carry E := by
  intro Y Cr E₀ F Wt Bs a τ b ha hb
  obtain ⟨e1, h1⟩ := IOR.keepE_red_out ((Y.psc E₀).keepX Cr) F a τ b hb
  obtain ⟨e2, h2⟩ := IOR.keepX_red_out (Y.psc E₀) Cr (a.1, a.2.1) τ (b.1, b.2.1) h1
  obtain ⟨h3, h4⟩ := IOR.red_out_eq_some.1 h2
  have h3' : (Y.psc E₀).out a.1.1 a.2.1 (Tr.app (Tr.fst τ) (Tr.snd (s := (Y.core E₀).shape) τ)) =
      some b.1.1 := by
    rw [Tr.app_fst_snd]; exact h3
  have h5 : b.1.1.st = a.1.1.2 := Y.outC_st a.1.1 _ _ (Y.psc_out_some E₀ a.1.1 a.2.1 _ _ b.1.1 h3')
  have e : ((b.1.1.st, b.1.2), b.2) = ((a.1.1.2, a.1.2), a.2) :=
    Prod.ext (Prod.ext h5 e2) (Prod.ext h4 e1)
  show Bs.on ((b.1.1.st, b.1.2), b.2)
  rw [e]
  exact ha

theorem psc_carry_base : Spec.psc_carry_base E := by
  intro Y Ex Wt Kc A0 msg a τ b ha hb
  obtain ⟨h3, h4⟩ := IOR.red_out_eq_some.1 hb
  have h3' : (Y.psc Ex).out a.1 a.2 (Tr.app (Tr.fst τ) (Tr.snd (s := (Y.core Ex).shape) τ)) =
      some b.1 := by
    rw [Tr.app_fst_snd]; exact h3
  have h5 : b.1.st = a.1.2 := Y.outC_st a.1 _ _ (Y.psc_out_some Ex a.1 a.2 _ _ b.1 h3')
  show A0.on (b.1.st, b.2)
  rw [h5, h4]
  exact ha

end Main
end Cb
