-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdFrontProofs.lean: the proofs of the statements of Cb/Ld/LdFront.lean.

Main names (statements and hypotheses: Cb/Ld/LdFront.lean):
  `front_carry`, `front_zk`, `front_okFrom`, `front_sides`, `prog_okFrom`: see their statements in
    Cb/Ld/LdFront.lean.
  `chain_append_assoc` (`append` is associative), `prog_onto_append`: brackets.
The lemmas `prog_step`, `quiet_step`, `zkOK_step`, `sd_step` and their like for `bat`, `split`
unfold `prog`, `Quiet`, `ZkOK`, `Sd` (Cb/Ld/LdFront.lean, under "Definitions.") at one kind of move.

Limits: what the head of Cb/Ld/LdFront.lean lists as not said is not said here either. `front_zk`
does not say that anything is zero knowledge: under the hypotheses of its statement it concludes the
condition `p.prog.Zk base` (`LdProg.Zk`, Cb/Req1/LdReq.lean) from the condition `p.ZkOK`
(Cb/Ld/LdFront.lean).
-/
import Cb.Ld.LdFront
import Cb.Req1.LdSegProofs
import Cb.Ld.LdBatSigProofs

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Cb.Ood IOR IOR.Chain

theorem chain_append_assoc : Spec.chain_append_assoc := by
  intro K A B C D c₁ c₂ c₃
  induction c₃ with
  | one l => rw [append_one, append_one, append_snoc]
  | snoc c l ih => rw [append_snoc, append_snoc, append_snoc, ih]

/-! ### The recursions, unfolded -/

namespace Front
variable {E : Type} [Field E] [Fintype E] {S : Sig E} {E₀ : ExtSpec}
  {Wp Kc : Type} {x y : FSt S E₀ Wp Kc}

/-- the data of the two blocks -/
@[reducible] def batD (B : Type) (iB : Fintype B) (Sb : B → Type) (sl : ∀ b, Slf E (Sb b) S.Ent)
    (Z : Evader E B) (St₀ : Type) (A₀ : IOR.Rels Kc St₀ E₀ (S.Msg × Wp)) : LdBatD E Kc :=
  ⟨S, B, Sb, sl, Z, St₀, Wp, E₀, A₀⟩
@[reducible] def splD (G₁ G₂ : Grp S) (k : SplitAt G₁ G₂) (St₁ St₂ : Type) (sl₁ : Slf E St₁ G₁.C.J)
    (sl₂ : Slf E St₂ G₂.C.J) (St₀ : Type) (A₀ : IOR.Rels Kc St₀ E₀ (S.Msg × Wp))
    (Rs : S.Ent → Prop) (dRs : DecidablePred Rs) : LdSplD E Kc :=
  ⟨S, G₁, G₂, k, St₁, St₂, sl₁, sl₂, St₀, Wp, E₀, A₀, Rs⟩

theorem prog_nil (x : FSt S E₀ Wp Kc) : (Front.nil x).prog = .nil x.stage := by rw [prog]
theorem prog_step (p : Front x y) (z : FSt S E₀ Wp Kc) f g m back :
    (p.step z f g m back).prog = .snoc p.prog (.step _ z.stage f g m back) := by rw [prog]
theorem prog_bat (B iB Sb sl Z St₀) (A₀ : IOR.Rels Kc St₀ E₀ (S.Msg × Wp)) (p : Front x _) :
    (Front.bat B iB Sb sl Z St₀ A₀ p).prog = .snoc p.prog (.bat (batD B iB Sb sl Z St₀ A₀)) := by
  rw [prog]
theorem prog_split (G₁ G₂ k St₁ St₂ sl₁ sl₂ St₀) (A₀ : IOR.Rels Kc St₀ E₀ (S.Msg × Wp))
    (Rs dRs) (p : Front x _) :
    (Front.split G₁ G₂ k St₁ St₂ sl₁ sl₂ St₀ A₀ Rs dRs p).prog =
      .snoc p.prog (.split (splD G₁ G₂ k St₁ St₂ sl₁ sl₂ St₀ A₀ Rs dRs)) := by rw [prog]

variable (Rd own : S.Ent → Prop) (Rr : S.O → Prop)

omit [Fintype E] in
theorem quiet_step (p : Front x y) (z : FSt S E₀ Wp Kc) f g m back :
    (p.step z f g m back).Quiet Rd own ↔
    p.Quiet Rd own ∧ (∀ a w, (m (a, w)).2 = w) ∧ ∀ a w w', (m (a, w')).1 = (m (a, w)).1 := by
  rw [Quiet]
omit [Fintype E] in
theorem quiet_bat (B iB Sb sl Z St₀) (A₀ : IOR.Rels Kc St₀ E₀ (S.Msg × Wp)) (p : Front x _) :
    (Front.bat B iB Sb sl Z St₀ A₀ p).Quiet Rd own ↔ p.Quiet Rd own := by rw [Quiet]
omit [Fintype E] in
theorem quiet_split (G₁ G₂ k St₁ St₂ sl₁ sl₂ St₀) (A₀ : IOR.Rels Kc St₀ E₀ (S.Msg × Wp))
    (Rs dRs) (p : Front x _) :
    (Front.split G₁ G₂ k St₁ St₂ sl₁ sl₂ St₀ A₀ Rs dRs p).Quiet Rd own ↔
    p.Quiet Rd own ∧ (∀ n, Rs n → Rd n) ∧
    (∀ st n, own (G₁.ent n) → sl₁ st n = 0) ∧ ¬ own ⟨k.o, k.j⟩ := by rw [Quiet]

variable (base : MaskFact x.stage.J.W → Prop)

theorem zkOK_step (p : Front x y) (z : FSt S E₀ Wp Kc) f g m back :
    (p.step z f g m back).ZkOK Rd Rr base ↔ p.ZkOK Rd Rr base := by rw [ZkOK]
theorem zkOK_bat (B iB Sb sl Z St₀) (A₀ : IOR.Rels Kc St₀ E₀ (S.Msg × Wp)) (p : Front x _) :
    (Front.bat B iB Sb sl Z St₀ A₀ p).ZkOK Rd Rr base ↔ p.ZkOK Rd Rr base := by rw [ZkOK]
theorem zkOK_split (G₁ G₂ k St₁ St₂ sl₁ sl₂ St₀) (A₀ : IOR.Rels Kc St₀ E₀ (S.Msg × Wp))
    (Rs dRs) (p : Front x _) :
    (Front.split G₁ G₂ k St₁ St₂ sl₁ sl₂ St₀ A₀ Rs dRs p).ZkOK Rd Rr base ↔
    p.ZkOK Rd Rr base ∧
    p.Quiet Rd (fun n => n = ⟨k.o, k.j⟩) ∧
    (∀ n, Rs n → Rd n) ∧
    base (x.stage.wideFact Rd Rr (fun n => n = ⟨k.o, k.j⟩) E fun u _ => u) := by rw [ZkOK]

variable (q : Finset (E₀.prod S.ext).Pos → Prop)

omit [Fintype E] in
theorem sd_step (p : Front x y) (z : FSt S E₀ Wp Kc) f g m back :
    (p.step z f g m back).Sd q ↔
    p.Sd q ∧ IOR.SideC (IOR.pure f g) (IOR.Honest.pure f g m) (IOR.Nums.pure Kc f g).bud q q := by
  rw [Sd]
omit [Fintype E] in
theorem sd_bat (B iB Sb sl Z St₀) (A₀ : IOR.Rels Kc St₀ E₀ (S.Msg × Wp)) (p : Front x _) :
    (Front.bat B iB Sb sl Z St₀ A₀ p).Sd q ↔ p.Sd q := by rw [Sd]
omit [Fintype E] in
theorem sd_split (G₁ G₂ k St₁ St₂ sl₁ sl₂ St₀) (A₀ : IOR.Rels Kc St₀ E₀ (S.Msg × Wp))
    (Rs dRs) (p : Front x _) :
    (Front.split G₁ G₂ k St₁ St₂ sl₁ sl₂ St₀ A₀ Rs dRs p).Sd q ↔ p.Sd q := by rw [Sd]

end Front

open Front

section
variable (E Kc : Type) [Field E] [Fintype E]

theorem prog_onto_append : Spec.prog_onto_append E Kc := by
  intro Z A a b c₀ c p
  induction p with
  | nil => rw [LdProg.onto_nil, LdProg.onto_nil]
  | snoc p m ih => rw [LdProg.onto_snoc, LdProg.onto_snoc, ih, chain_append_assoc]

theorem prog_okFrom : Spec.prog_okFrom E Kc := by
  intro Z A a b c₀ c p base h0 hc hb hH hZ
  have h1 : (c₀.append c).Ok := (ok_append Kc _ _ _ c₀ c).2 ⟨h0, hc⟩
  have h2 := ldReq_prog_ok E Kc Z a b (c₀.append c) p base h1 hb hH hZ
  rw [prog_onto_append] at h2
  exact ((ok_append Kc _ _ _ c₀ (p.onto c)).1 h2).2

theorem front_carry : Spec.front_carry E Kc := by
  intro S E₀ Wp x y p base Rd Rr own Mk _ _ val
  induction p with
  | nil =>
      intro _ _ hb
      rw [prog_nil, LdProg.after_nil]
      exact hb
  | step p z f g m back ih =>
      intro hH hQ hb
      rw [prog_step, LdProg.hyp_snoc] at hH
      rw [quiet_step] at hQ
      rw [prog_step, LdProg.after_snoc]
      refine segCarry_step _ z.stage f g m back _ _ _ _ _ (ih hH.1 hQ.1 hb) fun a w w' M h => ?_
      rw [hQ.2.1, hQ.2.1]
      exact ⟨hQ.2.2 a w w', h⟩
  | bat B iB Sb sl Z St₀ A₀ p ih =>
      intro hH hQ hb
      rw [prog_bat, LdProg.hyp_snoc] at hH
      rw [quiet_bat] at hQ
      rw [prog_bat, LdProg.after_snoc]
      exact segWide_bat (batD B iB Sb sl Z St₀ A₀) _ Rd Rr own Mk val (ih hH.1 hQ hb)
  | split G₁ G₂ k St₁ St₂ sl₁ sl₂ St₀ A₀ Rs dRs p ih =>
      intro hH hQ hb
      rw [prog_split, LdProg.hyp_snoc] at hH
      rw [quiet_split] at hQ
      rw [prog_split, LdProg.after_snoc]
      exact segWide_split (splD G₁ G₂ k St₁ St₂ sl₁ sl₂ St₀ A₀ Rs dRs) _ Rd Rr own Mk val hH.2
        hQ.2.1 hQ.2.2.1 hQ.2.2.2 (ih hH.1 hQ.1 hb)

/-- reading less, after a front -/
theorem front_after_ent {S : Sig E} {E₀ : ExtSpec} {Wp : Type} {x y : FSt S E₀ Wp Kc}
    (p : Front x y) (base : MaskFact x.stage.J.W → Prop) (Rd : S.Ent → Prop) (Rr : S.O → Prop)
    (hcl : ∀ (Rd' own : S.Ent → Prop) (Mk : Type) [Fintype Mk] [Nonempty Mk] (val : Mk → S.Ent → E),
      (∀ n, Rd' n → Rd n) → (∀ n, own n → Rd' n) →
      base (x.stage.wideFact Rd Rr own Mk val) → base (x.stage.entFact Rd' own Mk val))
    (Rd' own : S.Ent → Prop) (Mk : Type) [Fintype Mk] [Nonempty Mk] (val : Mk → S.Ent → E)
    (hR : ∀ n, Rd' n → Rd n) (ho : ∀ n, own n → Rd' n)
    (h : p.prog.After base (y.stage.wideFact Rd Rr own Mk val)) :
    p.prog.After base (y.stage.entFact Rd' own Mk val) := by
  cases p with
  | nil =>
      rw [prog_nil, LdProg.after_nil] at h ⊢
      exact hcl Rd' own Mk val hR ho h
  | step p f g m back =>
      rw [prog_step, LdProg.after_snoc] at h ⊢
      exact segWide_ent _ y.stage _ _ Rd Rd' Rr own Mk val hR ho h
  | bat B iB Sb sl Z St₀ A₀ p =>
      rw [prog_bat, LdProg.after_snoc] at h ⊢
      exact segWide_ent _ (batD B iB Sb sl Z St₀ A₀).tgt _ _ Rd Rd' Rr own Mk val hR ho h
  | split G₁ G₂ k St₁ St₂ sl₁ sl₂ St₀ A₀ Rs dRs p =>
      rw [prog_split, LdProg.after_snoc] at h ⊢
      exact segWide_ent _ (splD G₁ G₂ k St₁ St₂ sl₁ sl₂ St₀ A₀ Rs dRs).tgt
        _ _ Rd Rd' Rr own Mk val hR ho h

theorem front_zk : Spec.front_zk E Kc := by
  intro S E₀ Wp x y p base Rd Rr hcl
  induction p with
  | nil =>
      intro _ _
      rw [prog_nil, LdProg.zk_nil]
      trivial
  | step p z f g m back ih =>
      intro hH hZ
      rw [prog_step, LdProg.hyp_snoc] at hH
      rw [zkOK_step] at hZ
      rw [prog_step, LdProg.zk_snoc]
      exact ⟨ih hH.1 hZ, trivial⟩
  | bat B iB Sb sl Z St₀ A₀ p ih =>
      intro hH hZ
      rw [prog_bat, LdProg.hyp_snoc] at hH
      rw [zkOK_bat] at hZ
      rw [prog_bat, LdProg.zk_snoc]
      exact ⟨ih hH.1 hZ, trivial⟩
  | split G₁ G₂ k St₁ St₂ sl₁ sl₂ St₀ A₀ Rs dRs p ih =>
      intro hH hZ
      rw [prog_split, LdProg.hyp_snoc] at hH
      rw [zkOK_split] at hZ
      rw [prog_split, LdProg.zk_snoc]
      refine ⟨ih hH.1 hZ.1, ?_⟩
      show p.prog.After base (splD G₁ G₂ k St₁ St₂ sl₁ sl₂ St₀ A₀ Rs dRs).mask.fact
      rw [segWide_splitFact]
      have hD : (splD G₁ G₂ k St₁ St₂ sl₁ sl₂ St₀ A₀ Rs dRs).Hyp := hH.2
      refine front_after_ent E Kc p base Rd Rr hcl Rs _ E _ hZ.2.2.1 (fun n hn => ?_)
        (front_carry E Kc S E₀ Wp _ _ p base Rd Rr _ E _ hH.1 hZ.2.1 hZ.2.2.2)
      rw [hn]
      exact hD.rdK

theorem front_okFrom : Spec.front_okFrom E Kc := by
  intro S E₀ Wp x y p Z A c₀ c Rd Rr h0 hc hH hZ
  refine prog_okFrom E Kc Z A _ _ c₀ c p.prog _ h0 hc (fun _ h => h) hH
    (front_zk E Kc S E₀ Wp x y p _ Rd Rr ?_ hH hZ)
  intro Rd' own Mk _ _ val hR ho h
  exact (freshGiven_none Kc _ _ (c₀.append c) (x.stage.entFact Rd' own Mk val)).1
    (segWide_ent _ x.stage (c₀.append c) (fun _ => False) Rd Rd' Rr own Mk val hR ho
      ((freshGiven_none Kc _ _ (c₀.append c) (x.stage.wideFact Rd Rr own Mk val)).2 h))

omit [Field E] [Fintype E] in
/-- saying a value needs of the oracles what follows needs -/
theorem ldSay_need {X X' Pl : Type} (d : Pl) (nx : X → Pl → X') (Ex : ExtSpec)
    (ρ : Rho (ldSay d nx Ex).shape) (U : Finset Ex.Pos) :
    (ldSay d nx Ex).need ρ U = U := by
  classical
  simp [IOR.need, IOR.given, ldSay]

theorem front_sides : Spec.front_sides E Kc := by
  intro S E₀ Wp x y p A c qa q hc
  induction p with
  | nil =>
      intro _ _
      rw [prog_nil, LdProg.onto_nil]
      exact hc
  | step p z f g m back ih =>
      intro hH hS
      rw [prog_step, LdProg.hyp_snoc] at hH
      rw [sd_step] at hS
      rw [prog_step, LdProg.onto_snoc]
      have hl : (LdMv.step _ z.stage f g m back).chain.SidesC (K := Kc) q q := by
        refine (sidesC_one _ _ _).2 ?_
        exact hS.2
      exact sidesC_append Kc A _ _ (p.prog.onto c) (LdMv.step _ z.stage f g m back).chain
        qa q q (ih hH.1 hS.1) hl
  | bat B iB Sb sl Z St₀ A₀ p ih =>
      intro hH hS
      rw [prog_bat, LdProg.hyp_snoc] at hH
      rw [sd_bat] at hS
      rw [prog_bat, LdProg.onto_snoc]
      have pc := ldBat_sig_lin E B Kc St₀ Wp S Sb sl Z E₀ A₀ q hH.2
      have hl : (LdMv.bat (batD B iB Sb sl Z St₀ A₀)).chain.SidesC (K := Kc) q q :=
        (sidesC_one (batD B iB Sb sl Z St₀ A₀).link q q).2
          (sideC_of_side _ _ _ _ _ _ _ _ _ _ _ ⟨pc.noHid, pc.noTie, pc.bears⟩)
      exact sidesC_append Kc A _ _ (p.prog.onto c)
        (LdMv.bat (batD B iB Sb sl Z St₀ A₀)).chain qa q q (ih hH.1 hS) hl
  | split G₁ G₂ k St₁ St₂ sl₁ sl₂ St₀ A₀ Rs dRs p ih =>
      intro hH hS
      rw [prog_split, LdProg.hyp_snoc] at hH
      rw [sd_split] at hS
      rw [prog_split, LdProg.onto_snoc]
      have gm := ldSeg_split E Kc (splD G₁ G₂ k St₁ St₂ sl₁ sl₂ St₀ A₀ Rs dRs) hH.2
      have hl : (LdMv.split (splD G₁ G₂ k St₁ St₂ sl₁ sl₂ St₀ A₀ Rs dRs)).chain.SidesC
          (K := Kc) q q :=
        (sidesC_one (splD G₁ G₂ k St₁ St₂ sl₁ sl₂ St₀ A₀ Rs dRs).link q q).2
          (sideC_of_side _ _ _ _ _ _ _ _ _ _ _
          (side_of_mm _ _ _ _ _ _ _ _ _ _ q q gm.mm (fun _ => trivial) fun ρ U hU => by
            have e : (splD G₁ G₂ k St₁ St₂ sl₁ sl₂ St₀ A₀ Rs dRs).link.R.need ρ U = U :=
              ldSay_need _ _ _ ρ U
            rw [e]
            exact hU))
      exact sidesC_append Kc A _ _ (p.prog.onto c)
        (LdMv.split (splD G₁ G₂ k St₁ St₂ sl₁ sl₂ St₀ A₀ Rs dRs)).chain qa q q (ih hH.1 hS) hl

end
end Cb
