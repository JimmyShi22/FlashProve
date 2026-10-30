-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdBattVSegProofs.lean: the statements of Cb/Ld/LdBattVSeg.lean, proved.
The proofs for a batching step of an interactive oracle proof as it is placed inside the protocol
for one request.

The proofs combine: the block's theorems (the block: `BattVPar.battV`) from
Cb/Ld/LdBattVProofs.lean, the index-lifting rule from Cb/Ld/LdWfIdxProofs.lean, the two steps
without a round by the rule for a change of the base joint (Cb/Ld/LdBatPeelProofs.lean), the sums
(`ldBattVSeg_nums`) by Cb/Req1/LdSegProofs.lean, the two holders (`ldBattVSeg_two`) by
Cb/Req1/LdSegCarryJoinRead.lean (from a wide fact to a block's reading) and the block's own joining
rule.
The main theorems are `ldBattVSeg_hyp`, `ldBattV_good`, `ldBattVSeg_two` and `ldBattVSeg_zk`. What
they state, under which hypotheses, and the limits: the head of Cb/Ld/LdBattVSeg.lean.
  `ldBattVSeg_hyp`: all that the list of moves asks (`LdProg.Hyp`).
  `ldBattV_good`, `ldBattVSeg_two`, `ldBattVSeg_zk`: see their statements.
Many statements of this library are written twice: a definition in the namespace `Spec` states a
proposition, and a theorem of the same name outside that namespace proves it (lean/GLOSSARY.md).
Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdBattVSeg
import Cb.Ld.LdBattVProofs
import Cb.Ld.LdWfIdxProofs
import Cb.Req1.LdSegStep
import Cb.Req1.LdSegRefSupp
import Cb.Req1.LdSegRefKit
import Cb.Req1.LdSegCarryJoinRead
import Cb.Ld.LdRngProofs

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Cb.RngPk IOR IOR.Chain
open scoped ENNReal

theorem ldBattVSeg_own : Spec.ldBattVSeg_own := by
  intro E Kc _ _ X h
  refine ⟨fun i j e => h.inj (Sum.inr.inj e), fun i e => h.wc i (Sum.inr.inj e),
    fun i => h.own i, h.ownC, fun _ => trivial, ?_, fun i a e => Sum.inr_ne_inl e,
    fun a e => Sum.inr_ne_inl e, ?_, ?_⟩
  · rintro q st (a | n) hn
    · rfl
    · exact ldSegRef_placed0 _ _ E X.μAt _ n fun a e => hn (e ▸ h.rdM a)
  · intro q st i
    exact ldSegRef_placed0 _ _ E X.μAt _ (X.wAt i) fun a e => h.wM i a e.symm
  · intro q st
    exact ldSegRef_placed0 _ _ E X.μAt _ X.cAt fun a e => h.cM a e.symm

theorem ldBattVSeg_bat : Spec.ldBattVSeg_bat := fun _ _ _ _ _ _ _ _ _ => rfl

namespace LdTenVD
variable {E Kc : Type} [Field E] [Fintype E] (X : LdTenVD E Kc)

/-- a form on the entries of the messages, read on all entries of the block -/
theorem formJ (f : X.S.Ent → E) (um : X.C.Msg × X.S.Msg) :
    ∑ j, (Sum.elim (fun _ => 0) f : X.bt.J → E) j * X.msg um j = ∑ n, f n * X.S.ents um.2 n := by
  have h : ∑ j, (Sum.elim (fun _ => 0) f : X.bt.J → E) j * X.msg um j =
      ∑ a : X.Rw × (Fin X.k → Bool), (0 : E) * X.mat um.1 a + ∑ n, f n * X.S.ents um.2 n :=
    Fintype.sum_sum_type _
  rw [h, Finset.sum_eq_zero fun a _ => zero_mul _, zero_add]

theorem rowA_iff (z : X.Mid) (um : X.C.Msg × X.S.Msg) :
    X.slA.Holds (X.tA z, z) (X.S.ents um.2) ↔ X.bt.RowA z (X.msg um) := by
  have e1 : ∑ n, X.slA z n * X.S.ents um.2 n =
      ∑ i, hSl (X.bt.our.par.vars z.st) (X.bt.our.par.hp z.st z.pt) i *
          X.S.ents um.2 (X.wAt (pIx (X.bt.fmt ++ [pDummy E 1]) (X.bt.our.datD z.st) i)) +
        ∑ a, (z.eps * (∏ i, X.bt.outPt z i) * ∑ q, X.bt.chi z q * X.mf (X.stOf z).2 q a) *
          X.S.ents um.2 (X.μAt a) := by
    have p1 := ldRng_placed _ _ E
      (fun i => X.wAt (pIx (X.bt.fmt ++ [pDummy E 1]) (X.bt.our.datD z.st) i))
      (hSl (X.bt.our.par.vars z.st) (X.bt.our.par.hp z.st z.pt)) (X.S.ents um.2)
    have p2 := ldRng_placed _ _ E X.μAt
      (fun a => z.eps * (∏ i, X.bt.outPt z i) * ∑ q, X.bt.chi z q * X.mf (X.stOf z).2 q a)
      (X.S.ents um.2)
    refine Eq.trans ?_ (congrArg₂ (· + ·) p1 p2)
    refine Eq.trans ?_ Finset.sum_add_distrib
    exact Finset.sum_congr rfl fun n _ => add_mul _ _ _
  have e2 : ∑ q, X.bt.chi z q * ∑ j, X.bt.slM q (X.bt.stOf z) j * X.msg um j =
      ∑ q, X.bt.chi z q * ∑ a, X.mf (X.stOf z).2 q a * X.S.ents um.2 (X.μAt a) :=
    Finset.sum_congr rfl fun q _ => by
      have h := X.formJ (placed X.μAt (X.mf (X.stOf z).2 q)) um
      rw [ldRng_placed] at h
      rw [← h]
      rfl
  have e3 : ∑ a, (z.eps * (∏ i, X.bt.outPt z i) * ∑ q, X.bt.chi z q * X.mf (X.stOf z).2 q a) *
        X.S.ents um.2 (X.μAt a) =
      z.eps * (∏ i, X.bt.outPt z i) *
        ∑ q, X.bt.chi z q * ∑ a, X.mf (X.stOf z).2 q a * X.S.ents um.2 (X.μAt a) := by
    simp only [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun a _ => by ring
  show ∑ n, X.slA z n * X.S.ents um.2 n = X.tA z ↔ _
  unfold BattVPar.RowA
  rw [e1, e2, e3]
  exact Iff.rfl

theorem rowsO_iff (z : X.Mid) (um : X.C.Msg × X.S.Msg) :
    X.RowsOKO (X.rowsOf z) um.2 ↔ X.RowsOK (X.stOf z).1 um.2 ∧ X.bt.RowA z (X.msg um) :=
  ⟨fun h => ⟨fun b => h (.inl b), (X.rowA_iff z um).1 (h (.inr ()))⟩, fun h b => match b with
    | .inl b => h.1 b
    | .inr () => (X.rowA_iff z um).2 h.2⟩

/-- the block keeps the state -/
theorem battV_st (x : (X.bt.Q → E) × X.bt.St) (y : X.C.E0.Str) (τ : Tr (X.bt.battV X.C.E0).shape)
    (z : X.Mid) (h : (X.bt.battV X.C.E0).out x y τ = some z) : X.stOf z = x.2 := by
  obtain ⟨x₂, h1, h2⟩ := Option.bind_eq_some_iff.1 ((seq_out _ _ x y τ).symm.trans h)
  have h1 : some (X.bt.nx x (drawn (Tr.fst τ))) = some x₂ := h1
  obtain ⟨z₁, h3, h4⟩ := Option.bind_eq_some_iff.1
    ((seq_out (X.bt.our.par.core X.C.E0) (X.bt.our.par.ends X.C.E0) x₂ _ _).symm.trans h2)
  have h3 : X.bt.our.par.outC x₂ (Tr.fst (Tr.snd (s := [drawRound X.bt.Z.D]) τ)) = some z₁ := h3
  unfold PscPar.outC at h3
  split at h3
  · rw [← Option.some.inj h4, ← Option.some.inj h3, ← Option.some.inj h1]
    rfl
  · exact absurd h3 (by simp)

theorem goodAt (hn : 2 ≤ X.n) (hZ : X.Z.OK) :
    GoodAt (X.bt.battV X.C.E0)
      (idxH X.C (X.bt.hon X.C.E0 fun w : (X.C.Msg × X.S.Msg) × X.Wp => X.msg w.1)) X.m0.A X.m1.A
      (idxExt X.C fun _ _ _ wp => wp) (X.bt.nums X.C.E0 Kc) :=
  idxLift_goodAt X.C Kc _ _ X.S.Msg X.Wp X.Wp (X.bt.battV X.C.E0) _ _ _ (fun x => X.rc x.2.2)
    (fun z => X.rc (X.stOf z).2) (fun _ _ _ wp => wp) (X.bt.nums X.C.E0 Kc)
    (fun x y τ z hz => congrArg (fun s : X.Xr × X.St => X.rc s.2) (X.battV_st x y τ z hz))
    (fun _ _ => rfl) (battV_goodAt E X.bt X.C.E0 (X.C.Msg × X.S.Msg) X.Wp Kc X.A1 X.msg hn hZ)

theorem stepIn_hyp : X.stepIn.Hyp :=
  ldSeg_step E Kc X.src X.m0 _ _ _ _
    (ldPeel_base E Kc _ _ _ _ X.S X.C.E0 X.C.E0 X.src.A X.m0.A (fun x => (x.2.1, (x.1, x.2.2)))
      (ExtMap.id X.C.E0) (fun _ w => w.2) (fun _ w => w.2) (extMap_isLocal.1 _)
    (fun _ _ _ hw => ⟨hw.2.1, ⟨hw.1, hw.2.2.1⟩, hw.2.2.2⟩) (fun _ _ hh => hh) (fun _ _ => rfl)
    (fun _ _ _ _ hw => by
      obtain ⟨U, hU, ⟨hr, ha⟩, ht⟩ := hw
      exact ⟨hr, U, hU, ha, ht⟩))

theorem stepOut_hyp (St₁ : Type) (fz : X.Mid → St₁)
    (Az : Rels Kc St₁ X.C.E0 (X.S.Msg × (X.C.PIdx × X.Wp))) (hE : X.Ends St₁ fz Az) :
    (X.stepOut St₁ fz Az).Hyp :=
  ldSeg_step E Kc X.m1 (X.tgt St₁ Az) _ _ _ _
    (ldPeel_base E Kc _ _ _ _ X.S X.C.E0 X.C.E0 X.m1.A (X.tgt St₁ Az).A
      (fun z => (X.rowsOf z, fz z)) (ExtMap.id X.C.E0) (fun _ w => w.2)
      (fun _ w => w.2) (extMap_isLocal.1 _)
    (fun z y w hw =>
      ⟨(X.rowsO_iff z (w.2.1.1.1, w.1)).2 ⟨hw.2.1.1, hw.2.2.1⟩,
        hE.fw z y w ⟨hw.1, hw.2.1.2, hw.2.2.2⟩⟩)
    (fun z y hh => hE.on z y hh) (fun _ w => hE.core w)
    (fun z y w ho hw => by
      obtain ⟨U, hU, ha, hp⟩ := hE.bw z y w ho hw.1 hw.2
      have hr := (X.rowsO_iff z (U, w.1)).1 hw.1
      exact ⟨U, hU, ⟨hr.1, ha⟩, hr.2, hp⟩))

end LdTenVD

theorem ldBattVSeg_rowA : Spec.ldBattVSeg_rowA := fun _ _ _ _ X z um => X.rowA_iff z um

theorem ldBattVSeg_rowA_supp : Spec.ldBattVSeg_rowA_supp := by
  intro E Kc _ _ X z n h1 h2
  have a := ldSegRef_placed0 _ _ E
    (fun i => X.wAt (pIx (X.bt.fmt ++ [pDummy E 1]) (X.bt.our.datD z.st) i))
    (hSl (X.bt.our.par.vars z.st) (X.bt.our.par.hp z.st z.pt)) n fun i => h1 _
  have b := ldSegRef_placed0 _ _ E X.μAt
    (fun a => z.eps * (∏ i, X.bt.outPt z i) * ∑ q, X.bt.chi z q * X.mf (X.stOf z).2 q a) n h2
  show placed (fun i => X.wAt (pIx (X.bt.fmt ++ [pDummy E 1]) (X.bt.our.datD z.st) i))
        (hSl (X.bt.our.par.vars z.st) (X.bt.our.par.hp z.st z.pt)) n +
      placed X.μAt
        (fun a => z.eps * (∏ i, X.bt.outPt z i) * ∑ q, X.bt.chi z q * X.mf (X.stOf z).2 q a) n = 0
  rw [a, b, add_zero]

theorem ldBattVSeg_rowA_named : Spec.ldBattVSeg_rowA_named := fun E Kc _ _ X z n h =>
  ldBattVSeg_rowA_supp E Kc X z n (fun i e => h (Or.inl ⟨i, e⟩)) fun a e => h (Or.inr ⟨a, e⟩)

theorem ldBattVSeg_rowsO : Spec.ldBattVSeg_rowsO := fun _ _ _ _ X z um => X.rowsO_iff z um

theorem ldBattVSeg_pend : Spec.ldBattVSeg_pend := by
  intro E Kc _ _ X z um Nm' _ _ μAt' ν hν
  have e : ∑ j, (Sum.elim (fun _ => 0) (placed μAt' (Pi.single ν (X.bt.beta z))) : X.bt.J → E) j *
        X.msg um j =
      X.bt.beta z * X.msg um X.bt.cAt := by
    rw [X.formJ, ldRng_placed,
      Finset.sum_eq_single ν (fun x _ hx => by rw [Pi.single_eq_of_ne hx, zero_mul])
        (fun h => absurd (Finset.mem_univ ν) h),
      Pi.single_eq_same, hν]
    rfl
  rw [e]
  exact Iff.rfl

theorem ldBattVSeg_ends_left : Spec.ldBattVSeg_ends_left := fun _ _ _ _ _ =>
  ⟨fun _ _ _ h => h, fun _ _ _ _ _ h => h, fun _ _ h => h, fun _ => rfl⟩

theorem ldBattVSeg_hyp : Spec.ldBattVSeg_hyp := by
  intro E Kc _ _ X St₁ fz Az hn hZ hE
  unfold LdTenVD.prog
  rw [LdProg.hyp_snoc, LdProg.hyp_snoc, LdProg.hyp_snoc]
  exact ⟨⟨⟨LdProg.hyp_nilK _, X.stepIn_hyp⟩,
      (allB_one X.link).2 (ldSeg_lift E Kc X.m0 _ _ _ X.m1.A _ _ _ _ (X.goodAt hn hZ)).1⟩,
    X.stepOut_hyp St₁ fz Az hE⟩

open Classical in
theorem ldBattVSeg_goodM : Spec.ldBattVSeg_goodM := by
  intro E Kc _ _ X hn hZ hO
  have own := ldBattVSeg_own E Kc X hO
  have gM := idxLift_goodM E X.C X.S Kc _ _ X.Wp X.Wp (X.bt.battV X.C.E0)
    (X.bt.hon X.C.E0 fun w : (X.C.Msg × X.S.Msg) × X.Wp => X.msg w.1)
    (X.bt.baseIn X.C.E0 X.A1 fun w => X.msg w.1)
    (X.bt.baseOut X.C.E0 X.A1 fun w => X.msg w.1)
    (fun x => X.rc x.2.2) (fun z => X.rc (X.stOf z).2) (fun _ _ _ wp => wp) (X.bt.nums X.C.E0 Kc)
    (X.bt.maskData X.C.E0 (fun w : (X.C.Msg × X.S.Msg) × X.Wp => X.msg w.1) X.RdJ)
    (fun x y τ z hz => congrArg (fun s : X.Xr × X.St => X.rc s.2) (X.battV_st x y τ z hz))
    (fun _ _ => rfl) (battV_goodAt E X.bt X.C.E0 (X.C.Msg × X.S.Msg) X.Wp Kc X.A1 X.msg hn hZ)
    (battV_mm E X.bt X.C.E0 _ _ X.RdJ hn own)
    (fun x _ w hw q => by
      show X.bt.lhs x.2 q (fun j => if X.RdJ j then X.msg w.1 j else 0) = x.1 q
      rw [← hw.2 q]
      exact X.bt.lhs_congr (fun a => if_pos (own.rdM a)) fun j hj =>
        if_pos (by by_contra hr; exact hj (own.rdS q x.2 j hr)))
  exact ldSeg_sub_goodM E Kc X.m0 X.m1 X.link X.mask gM

theorem ldBattV_good : Spec.ldBattV_good := ldBattVSeg_goodM

open Classical in
theorem ldBattVSeg_two : Spec.ldBattVSeg_two := by
  intro E Kc _ _ X Y Rd₁ Rd₂ Rr₁ Rr₂ hO hR hW hC
  have own := ldBattVSeg_own E Kc X hO
  let msg' : X.m0.J.W → X.bt.J → E := fun w => X.msg (w.2.1.1.1, X.S.msgs w.1)
  have rd : ∀ (Rd : X.S.Ent → Prop)
          (ow : X.S.Ent → Prop) (m m' : X.S.Msg) (wp : X.C.PIdx × X.Wp) (j : X.bt.J),
        (∀ n, X.Rd n → Rd n) → X.RdJ j → (∀ n, j = Sum.inr n → ¬ ow n) →
        (∀ n : X.S.Ent, Rd n → ¬ ow n → m' n.1 n.2 = m n.1 n.2) →
        X.msg (wp.1.1.1, m') j = X.msg (wp.1.1.1, m) j := by
    intro Rd ow m m' wp j h0 hj hn h
    cases j with
    | inl a => rfl
    | inr n => exact h n (h0 n hj) (hn n rfl)
  have fW : MaskFact.JCl Y (X.bt.factW msg' X.RdJ) :=
    wideJ_readG E Kc X.m0 Y Rd₁ Rr₁ (fun n => ∃ i, X.wAt i = n) (X.bt.WIx → E)
      (fun M => Function.extend X.wAt M fun _ => 0) X.bt.J X.bt.WIx X.bt.wAt X.wAt (fun M => M)
      X.RdJ (fun mw => X.msg (mw.2.1.1.1, mw.1)) (fun w => X.bt.cut X.RdJ (msg' w))
      (fun M k => Function.extend X.bt.wAt M k) own.inj (fun _ _ _ => rfl)
      (fun m m' wp j hj hp h =>
        rd Rd₁ _ m m' wp j (fun n hn => (hR n hn).1) hj
          (fun n e ⟨i, hi⟩ => hp i (by rw [e, ← hi]; rfl)) h)
      (fun _ _ hj => if_pos hj) (fun _ _ hj => if_neg hj) (fun _ _ => rfl) (fun i => ⟨i, rfl⟩)
      (fun i => (hR _ (hO.own i)).1) (fun M i => hO.inj.extend_apply M _ i) own.own hW
  have fC : MaskFact.JCl Y (X.bt.factC msg' X.RdJ) :=
    wideJ_readG E Kc X.m0 Y Rd₂ Rr₂ (fun n => ∃ _u : Unit, X.cAt = n) (Unit → E)
      (fun M => Function.extend (fun _ : Unit => X.cAt) M fun _ => 0) X.bt.J Unit
      (fun _ => X.bt.cAt) (fun _ => X.cAt) (fun M => M) X.RdJ (fun mw => X.msg (mw.2.1.1.1, mw.1))
      (fun w => X.bt.cut X.RdJ (msg' w)) (fun M k => Function.extend (fun _ : Unit => X.bt.cAt) M k)
      (fun _ _ _ => rfl) (fun _ _ _ => rfl)
      (fun m m' wp j hj hp h =>
        rd Rd₂ _ m m' wp j (fun n hn => (hR n hn).2) hj
          (fun n e ⟨_, hi⟩ => hp () (by rw [e, ← hi]; rfl)) h)
      (fun _ _ hj => if_pos hj) (fun _ _ hj => if_neg hj) (fun _ _ => rfl)
      (fun _ => ⟨(), rfl⟩) (fun _ => (hR _ hO.ownC).2)
      (fun M i =>
        (show Function.Injective (fun _ : Unit => X.cAt) from fun _ _ _ => rfl).extend_apply M _ i)
      (fun _ => own.ownC) hC
  exact battV_join E X.bt X.C.E0 X.m0.J.W msg' X.RdJ Y own.inj own.wc fW fC

theorem ldBattVSeg_zk : Spec.ldBattVSeg_zk := by
  intro E Kc _ _ X St₁ fz Az base hn hZ hO hf
  unfold LdTenVD.prog
  rw [LdProg.zk_snoc, LdProg.zk_snoc, LdProg.zk_snoc, LdProg.after_snoc, LdProg.after_nil]
  refine ⟨⟨⟨(LdProg.zk_nil _ _).2 trivial, ?_⟩, ?_⟩, ?_⟩
  · unfold LdTenVD.stepIn
    rw [LdMv.Zk]
    trivial
  · rw [LdMv.Zk]
    exact (okGiven_one X.link _).2 (Or.inr ⟨X.mask, ldBattVSeg_goodM E Kc X hn hZ hO, hf⟩)
  · unfold LdTenVD.stepOut
    rw [LdMv.Zk]
    trivial

theorem ldBattVSeg_kinds : Spec.ldBattVSeg_kinds := by
  intro E Kc _ _ X St₁ fz Az
  unfold LdTenVD.prog
  rw [LdProg.all_snoc, LdProg.all_snoc, LdProg.all_snoc]
  exact ⟨⟨⟨LdProg.all_nilK _ _, Or.inr (Or.inr rfl)⟩, Or.inr (Or.inl rfl)⟩, Or.inr (Or.inr rfl)⟩

theorem ldBattVSeg_nums : Spec.ldBattVSeg_nums := by
  intro E Kc _ _ X St₁ fz Az
  obtain ⟨_, _, _, _, _, hp⟩ := ldSeg_rounds E Kc
  have a1 := hp X.src X.m0 (sideF X.S fun x => (x.2.1, (x.1, x.2.2))) (sideG X.S (ExtMap.id X.C.E0))
    (sideM X.S (fun x => (x.2.1, (x.1, x.2.2))) fun _ w => w.2) (sideB X.S fun _ w => w.2)
  have a3 := hp X.m1 (X.tgt St₁ Az) (sideF X.S fun z => (X.rowsOf z, fz z))
    (sideG X.S (ExtMap.id X.C.E0))
    (sideM X.S (fun z => (X.rowsOf z, fz z)) fun _ w => w.2) (sideB X.S fun _ w => w.2)
  have c2 : (LdMv.sub X.m0 X.m1 (.one X.link)).chain = .one X.link := by rw [LdMv.chain]
  have l2 : X.link.R.shape.nAll = X.k + 4 := battV_len E X.bt X.C.E0
  unfold LdTenVD.prog LdTenVD.stepIn LdTenVD.stepOut
  refine ⟨?_, ?_, ?_⟩
  · rw [LdProg.nAll_snoc, LdProg.nAll_snoc, LdProg.nAll_snoc, LdProg.nAll_nil,
      a1.1, a3.1, c2, nAll_one, l2]
    omega
  · rw [LdProg.pBad_snoc, LdProg.pBad_snoc, LdProg.pBad_snoc, LdProg.pBad_nil,
      a1.2.2.1, a3.2.2.1, c2, pBad_one]
    show (0 : ℝ≥0∞) + 0 + (0 + 0) + 0 = 0
    simp
  · rw [LdProg.pHid_snoc, LdProg.pHid_snoc, LdProg.pHid_snoc, LdProg.pHid_nil,
      a1.2.2.2, a3.2.2.2, c2, pHid_one]
    show (0 : ℝ≥0∞) + 0 + (0 + 0) + 0 = 0
    simp

end Cb
