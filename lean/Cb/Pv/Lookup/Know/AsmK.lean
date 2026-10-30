-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Lookup/Know/AsmK.lean.
Knowledge soundness of the assembled lookup, over a sumcheck that is a letter.

States: baseKS: the lookup's verifier, built from verifiers alone, with its list of errors; LtK:
knowledge soundness of the letter at the lookup's own sumchecks;
  asmK_base: knowledge soundness between the library's joints; asmI_know: the same with the five
    arguments of the library's Know (`Iop.Reduction.Know`, Ior/Know.lean) written out, for each
    fixed tuple of messages: from "every key is a row of the table" to "the masked claim on the keys
    and all linear rows of the read-out hold", each beside the relaxed relation of a joint R0 that
    rides along; the condition is R0's, the extractor the identity, the errors baseKS's;
  asmI_know_sig, asmI_know_sigT: over a signature of sampled messages, by the library's
    sigLift_know. asmK_libOK: the library's own sumcheck meets LtK.
Premises: LtK of the letter; p is the characteristic of E; the library's conditions on the sizes
(Adm p); padsOK; all planes count (n + 2 = 2^w; a plane: Cb/Pv/Lookup/Asm/AsmH.lean). None names an
honest prover; all but the first are conditions on public numbers.
Limits: baseKS is built anew on the record LkAsmH. That at the library's sumcheck it is the verifier
of LkAsmH.baseA (Cb/Pv/Lookup/Asm/AsmH.lean) is not stated. A statement for every letter says
nothing on what the verifier accepts. The errors as numbers:
OnBytes/Tie/Pv/Lookup/Lists/TwAsm.lean (asmK_eps).
Terms: lean/GLOSSARY.md.

-/
import Cb.Pv.Lookup.Asm.AsmH
import Cb.Pv.Lookup.Know.LtK

set_option autoImplicit false

namespace Cb.LdLkp
open Iop IOR Hiop Prob Cb.Lkp Finset Kn TWhole

noncomputable section
namespace LkAsmH
variable {E : Type} [Field E] [Fintype E] (A : LkAsmH E)

section
variable {Ex : ExtSpec} (SK : PscLtK E Ex)

variable (Ex) in
/-- the planes' point -/
def rootK : BkK A.R.D.St0 (E × (A.R.D.lv 0).T.St) Ex :=
  drawK A.R.toIn.ev.D A.R.toIn.nxX Ex A.R.toIn.ev.err

def forestK : (l : ℕ) → BkK A.XR (E × (A.D.lv l).T.St) Ex
  | 0 => (segKK A.IK A.v' (fun x => A.tK (A.oR x)) SK).postM A.enterT
  | l + 1 => (forestK l).seq (A.D.levK SK l)

def endK : BkK (E × (A.D.lv A.d).T.St) A.XE Ex := SK.core A.En.par
def bitK : BkK A.XE A.XB Ex := chainK A.Bt.zc.toIn SK

def chnK : BkK A.St A.XB Ex :=
  ((((A.H.headK SK).seq (A.rootK Ex)).seq (A.forestK SK A.d)).seq (A.endK SK)).seq (A.bitK SK)

/-- The lookup's verifier, and its errors. -/
def baseKS : BkK A.St (TX A.St E A.J) Ex := (A.chnK SK).postM A.rd

/-- What is asked of the letter: KnowAt at the lookup's own sumchecks, and nowhere else. -/
structure LtK {M : Type} (Wp Kc : Type) (msg : M → A.J → E) : Prop where
  tie  : A.H.tie.LtK SK Wp Kc msg A.n
  keys : (A.IK.setV (A.v' + 1)).DK.LtK SK Wp Kc msg A.v'
  tab  : ∀ l < A.d, SK.FullK M Wp Kc (A.D.lv l).T.par (A.D.msgAt M msg l)
  clo  : SK.CoreK M Wp Kc A.En.par msg
  bit  : SK.FullK M Wp Kc A.Bt.zc.next.par msg

end
end LkAsmH
end
end Cb.LdLkp

namespace Cb
open Iop IOR Hiop Prob Cb.LdLkp Cb.Lkp Cb.LdLkp.Kn TWhole Finset

section
variable (E : Type) [Field E] [Fintype E]

/-- the keys' side, the step into the forest, the levels below l -/
theorem LdLkp.LkAsmH.forestK_know (A : LkAsmH E) (Mu : A.St → (A.J → E) → Prop) (Ex : ExtSpec)
    (Kc M Wp : Type) (SK : PscLtK E Ex) (R0 : Rels Kc A.St Ex (M × Wp)) (msg : M → A.J → E)
    (hK : (A.IK.setV (A.v' + 1)).DK.LtK SK Wp Kc msg A.v') (l : ℕ) :
    (∀ l' < l, SK.FullK M Wp Kc (A.D.lv l').T.par (A.D.msgAt M msg l')) →
    (A.forestK SK l).Know
      (cj R0 msg (fun x => (A.b2 (A.oR x)).1)
        (fun x m =>
          A.ΨK Mu x m ∧
          keyProd (A.v' + 1) (A.IK.key (A.IK.st x) m) (A.IK.lam x) + ∑ j, A.IK.fK x j * m j =
            A.tK (A.oR x)) fun x m =>
              A.ΨK (fun _ _ => True) x m ∧
              keyProd (A.v' + 1) (A.IK.key (A.IK.st x) m) (A.IK.lam x) + ∑ j, A.IK.fK x j * m j =
                A.tK (A.oR x))
      (A.D.jtAt msg (A.A0 E R0 msg Mu) l) := by
  induction l with
  | zero =>
    intro _
    have g := segKK_know E A.IK A.v' (fun x => A.tK (A.oR x)) Ex Kc A.St M Wp SK R0 msg
      (fun x => (A.b2 (A.oR x)).1) (A.ΨK Mu) (A.ΨK fun _ _ => True) hK
    rw [show A.D.jtAt msg (A.A0 E R0 msg Mu) 0 = _
        from ldLkpK_tree E A.D Ex Kc A.St M Wp R0 msg (fun s => (A.b2 (A.oR (A.o4 s.1))).1)
          (fun s m => A.ΨT Mu s.1 m ∧ A.Bts m)
          (fun s m => A.ΨT (fun _ _ => True) s.1 m ∧ A.Bts m) 0]
    refine know_postM A.enterT g (fun _ _ h => h) ?_
    · intro x y w _ h
      obtain ⟨hR, ⟨⟨⟨⟨⟨hn, hP⟩, hr2⟩, hr4, hc⟩, hb⟩, _⟩, h1⟩ := h
      exact ⟨hR, ⟨⟨⟨⟨⟨hb, hn⟩, hP⟩, hr2⟩, (A.enter_iff x _).mp h1⟩, hr4⟩, hc⟩
  | succ l ih =>
    intro hT
    exact know_seq (ih fun l' h => hT l' (Nat.lt_succ_of_lt h))
      (ldLkpK_level' E A.D Ex M Wp Kc SK msg (A.A0 E R0 msg Mu) l (hT l (Nat.lt_succ_self l))
        (ldLkpInst2_step E A.IT (A.n + 1)))

/-- the chain before the read-out -/
theorem LdLkp.LkAsmH.chnK_know (p : ℕ) [CharP E p] (A : LkAsmH E) (Mu : A.St → (A.J → E) → Prop)
    (Ex : ExtSpec) (Kc M Wp : Type) (SK : PscLtK E Ex) (R0 : Rels Kc A.St Ex (M × Wp))
    (msg : M → A.J → E) (hL : A.LtK SK Wp Kc msg) (hA : A.H.lkb.Adm p)
    (hP : padsOK (A.v' + 1) A.d A.pads = true) (hF : A.n + 1 + 1 = 2 ^ A.w) :
    (A.chnK SK).Know (cj R0 msg id (A.lk.inP Mu) A.lk.inR)
      (cj R0 msg (fun o => (A.b2 (A.oR (A.o4 (A.oldT o)))).1)
        (fun o m => A.ΨT Mu (A.oldT o) m ∧ RowsHold (A.rowsB o) m)
        fun o m => A.ΨT (fun _ _ => True) (A.oldT o) m ∧ RowsHold (A.rowsB o) m) := by
  -- the head
  have g1 := headK_know E p A.H Mu Ex Kc M Wp SK R0 msg hL.tie hA hP
  -- the point
  let R1 : Rels Kc A.X2 Ex (M × Wp) :=
    cj R0 msg (fun x => (A.b2 x).1) (A.Φ1 Mu) (A.Φ1 fun _ _ => True)
  have g2 : (A.rootK Ex).Know
      ⟨fun st y w => R1.rel st y w ∧ A.R.Holds st (msg w.1),
        fun a w => R1.relR a w ∧ A.R.Holds a.1 (msg w.1),
        R1.on, R1.core⟩
      ((A.I1.DT2 (A.n + 1)).jtAt msg (A.R.toIn.ride R1) 0) :=
    know_of_good (b := A.R.rootA Ex M Wp Kc)
      (ldLkpRoot_good E A.R Ex M Wp Kc R1 msg (ldLkpInst2_step E A.I1 (A.n + 1)) fun _ _ _ => rfl)
  have e1 : cj R0 msg (fun x : A.X2 => (A.b2 x).1)
        (fun x m =>
          ((A.H.RestF (A.b2 x) m ∧ Mu (A.b2 x).1 m) ∧ A.H.tie.Done A.n x.2 m) ∧
          A.H.tie.claim (A.n + 1) x m)
        (fun x m =>
          (A.H.RestF (A.b2 x) m ∧ A.H.tie.Done A.n x.2 m) ∧ A.H.tie.claim (A.n + 1) x m) =
      (⟨fun st y w => R1.rel st y w ∧ A.R.Holds st (msg w.1),
        fun a w => R1.relR a w ∧ A.R.Holds a.1 (msg w.1),
        R1.on,
        R1.core⟩ : Rels Kc A.X2 Ex (M × Wp)) :=
    (ldLkpK_congr E Kc A.St M Wp A.J A.X2 Ex R0 msg (fun x => (A.b2 x).1) _ _
        (fun x m => A.Φ1 Mu x m ∧ A.R.Holds x m)
        (fun x m => A.Φ1 (fun _ _ => True) x m ∧ A.R.Holds x m) (fun x m => A.junction1 hA.1 Mu x m)
        (fun x m =>
          Iff.trans (by simp only [and_true]) (A.junction1 hA.1 (fun _ _ => True) x m))).trans
      (ldLkpK_and E Kc A.St M Wp A.J A.X2 Ex R0 msg (fun x => (A.b2 x).1) (A.Φ1 Mu)
        (A.Φ1 fun _ _ => True) (fun x m => A.R.Holds x m) fun x m => A.R.Holds x m).symm
  have e2 : (A.I1.DT2 (A.n + 1)).jtAt msg (A.R.toIn.ride R1) 0 =
      cj R0 msg (fun x : A.XR => (A.b2 (A.oR x)).1)
        (fun x m =>
          A.ΨK Mu x m ∧
          keyProd (A.v' + 1) (A.IK.key (A.IK.st x) m) (A.IK.lam x) + ∑ j, A.IK.fK x j * m j =
            A.tK (A.oR x)) fun x m =>
              A.ΨK (fun _ _ => True) x m ∧
              keyProd (A.v' + 1) (A.IK.key (A.IK.st x) m) (A.IK.lam x) + ∑ j, A.IK.fK x j * m j =
                A.tK (A.oR x) :=
    (ldLkpK_tree E (A.I1.DT2 (A.n + 1)) Ex Kc A.St M Wp R0 msg (fun s => (A.b2 s.1).1)
        (fun s m => A.Φ1 Mu s.1 m) (fun s m => A.Φ1 (fun _ _ => True) s.1 m) 0).trans
      (ldLkpK_congr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (fun x m => A.junction2 Mu x m)
        (fun x m => A.junction2 (fun _ _ => True) x m))
  -- the keys' side and the forest
  have g3 := A.forestK_know E Mu Ex Kc M Wp SK R0 msg hL.keys A.d hL.tab
  -- the closing
  let A1 : Rels Kc (A.D.lv A.d).T.St Ex (M × Wp) := A.D.ride msg (A.A0 E R0 msg Mu) A.d
  have g4 : (A.endK SK).Know
      (A.En.relsIn A1 fun w => msg w.1) (A.En.par.baseMid A1 fun w => msg w.1) :=
    endMK_know E A.En Ex M Wp Kc SK A1 msg hL.clo
  have e3 : A.D.jtAt msg (A.A0 E R0 msg Mu) A.d = A.En.relsIn A1 fun w => msg w.1 :=
    instM_top E A.IT (A.n + 1) A.oE A.wE hF Ex M Wp Kc msg (A.A0 E R0 msg Mu)
  -- the bit test
  let R2 : Rels Kc A.XE Ex (M × Wp) :=
    cj R0 msg (fun z : A.XE => (A.b2 (A.oR (A.o4 (A.D.root A.d z.st).1))).1)
      (fun z m =>
        (A.ΨT Mu (A.D.root A.d z.st).1 m ∧ RowsHold (A.D.rowsAt A.d z.st) m) ∧
        A.En.par.MidHolds z m) fun z m =>
          (A.ΨT (fun _ _ => True) (A.D.root A.d z.st).1 m ∧ RowsHold (A.D.rowsAt A.d z.st) m) ∧
          A.En.par.MidHolds z m
  have g5 : (A.bitK SK).Know
      ⟨fun st y w => R2.rel st y w ∧ A.Bt.AllBits (msg w.1),
        fun a w => R2.relR a w ∧ A.Bt.AllBits (msg w.1),
        R2.on, R2.core⟩
      (A.Bt.zc.next.par.baseOut (A.Bt.zc.toIn.ride R2) fun w => msg w.1) :=
    bitPK_know E A.Bt Ex M Wp Kc SK R2 msg hL.bit
  have hb : ∀ m, A.Bt.AllBits m ↔ A.Bts m := fun m => ldLkpInst_bitsP E A.IT _ A.oB A.wB A.cB m
  obtain ⟨r1, r2, r3, r4⟩ := ldLkpP_ride E A.D Ex M Wp Kc msg (A.A0 E R0 msg Mu) A.d
  have e4 : A.En.par.baseMid A1 (fun w => msg w.1) =
      (⟨fun st y w => R2.rel st y w ∧ A.Bt.AllBits (msg w.1),
        fun a w => R2.relR a w ∧ A.Bt.AllBits (msg w.1),
        R2.on,
        R2.core⟩ : Rels Kc A.XE Ex (M × Wp)) := by
    refine LdLkp.rels_ext (funext fun z => funext fun y => funext fun w => propext ?_)
      (funext fun a => funext fun w => propext ?_) (funext fun a => propext (r3 a.1.st a.2)) r4
    · show A1.rel z.st y w ∧ A.En.par.MidHolds z (msg w.1) ↔ _
      rw [r1]
      exact ⟨fun h => ⟨⟨h.1.1.1, ⟨h.1.1.2.1, h.1.2⟩, h.2⟩, (hb _).2 h.1.1.2.2⟩,
        fun h => ⟨⟨⟨h.1.1, h.1.2.1.1, (hb _).1 h.2⟩, h.1.2.1.2⟩, h.1.2.2⟩⟩
    · show A1.relR (a.1.st, a.2) w ∧ A.En.par.MidHolds a.1 (msg w.1) ↔ _
      rw [r2]
      exact ⟨fun h => ⟨⟨h.1.1.1, ⟨h.1.1.2.1, h.1.2⟩, h.2⟩, (hb _).2 h.1.1.2.2⟩,
        fun h => ⟨⟨⟨h.1.1, h.1.2.1.1, (hb _).1 h.2⟩, h.1.2.1.2⟩, h.1.2.2⟩⟩
  have e5 : A.Bt.zc.next.par.baseOut (A.Bt.zc.toIn.ride R2) (fun w => msg w.1) =
      cj R0 msg (fun o => (A.b2 (A.oR (A.o4 (A.oldT o)))).1)
        (fun o m => A.ΨT Mu (A.oldT o) m ∧ RowsHold (A.rowsB o) m)
        fun o m => A.ΨT (fun _ _ => True) (A.oldT o) m ∧ RowsHold (A.rowsB o) m := by
    refine LdLkp.rels_ext (funext fun o => funext fun y => funext fun w => propext ?_)
      (funext fun a => funext fun w => propext ?_) rfl rfl
    · show R2.rel (A.outE o) y w ∧ A.Bt.zc.next.par.OutHolds o (msg w.1) ↔
        R0.rel (A.b2 (A.oR (A.o4 (A.oldT o)))).1 y w ∧
        A.ΨT Mu (A.oldT o) (msg w.1) ∧
        RowsHold (A.rowsB o) (msg w.1)
      rw [A.rowsB_iff]
      exact ⟨fun h => ⟨h.1.1, h.1.2.1.1, h.2, h.1.2.2, h.1.2.1.2⟩,
        fun h => ⟨⟨h.1, ⟨h.2.1, h.2.2.2.2⟩, h.2.2.2.1⟩, h.2.2.1⟩⟩
    · show R2.relR (A.outE a.1, a.2) w ∧ A.Bt.zc.next.par.OutHolds a.1 (msg w.1) ↔
        R0.relR ((A.b2 (A.oR (A.o4 (A.oldT a.1)))).1, a.2) w ∧
        A.ΨT (fun _ _ => True) (A.oldT a.1) (msg w.1) ∧
        RowsHold (A.rowsB a.1) (msg w.1)
      rw [A.rowsB_iff]
      exact ⟨fun h => ⟨h.1.1, h.1.2.1.1, h.2, h.1.2.2, h.1.2.1.2⟩,
        fun h => ⟨⟨h.1, ⟨h.2.1, h.2.2.2.2⟩, h.2.2.2.1⟩, h.2.2.1⟩⟩
  rw [e2] at g2
  rw [e3] at g3
  rw [e4] at g4
  rw [e5] at g5
  exact know_seq (know_seq (know_seq (know_seq (e1 ▸ g1) g2) g3) g4) g5

/-- Knowledge soundness (`BkK.Know`) between the library's own joints. This is said under the
hypotheses that stand in the statement itself, which this comment does not list; it is no claim that
they hold. Mu stands in the exact relation alone, which Know does not read: it is any. -/
theorem asmK_base (p : ℕ) [CharP E p] (A : LkAsmH E) (Mu : A.St → (A.J → E) → Prop) (Ex : ExtSpec)
    (Kc M Wp : Type) (SK : PscLtK E Ex) (R0 : Rels Kc A.St Ex (M × Wp)) (msg : M → A.J → E)
    (hL : A.LtK SK Wp Kc msg) (hA : A.H.lkb.Adm p) (hP : padsOK (A.v' + 1) A.d A.pads = true)
    (hF : A.n + 1 + 1 = 2 ^ A.w) :
    (A.baseKS SK).Know
      (cj R0 msg id (A.lk.inP Mu) A.lk.inR) (cj R0 msg Prod.fst (A.lk.out id id) (A.lk.out id id))
          := by
  have g := A.chnK_know E p Mu Ex Kc M Wp SK R0 msg hL hA hP hF
  refine know_postM A.rd g (fun _ _ h => h) ?_
  intro o y w _ h
  exact ⟨h.1, (A.out_iff o _).mp h.2⟩

/-- `asmK_base` at each fixed tuple of messages m, with the five arguments of `Iop.Reduction.Know`
written out: condition, input relation, output relation, extractor, errors. -/
theorem asmI_know (p : ℕ) [CharP E p] (A : LkAsmH E) (Ex : ExtSpec)
    (Kc M Wp : Type) (SK : PscLtK E Ex) (R0 : Rels Kc A.St Ex (M × Wp)) (msg : M → A.J → E)
    (hL : A.LtK SK Wp Kc msg) (hA : A.H.lkb.Adm p) (hP : padsOK (A.v' + 1) A.d A.pads = true)
    (hF : A.n + 1 + 1 = 2 ^ A.w) (m : M) :
    (A.baseKS SK).R.red.Know
      (fun a => R0.on (a.1, a.2))
      (fun a wp => R0.relR (a.1, a.2) (m, wp) ∧ A.lk.inR a.1 (msg m))
      (fun b wp => R0.relR (b.1.1, b.2) (m, wp) ∧ A.lk.out id id b.1 (msg m))
      (fun _ _ wp => wp) (A.baseKS SK).e :=
  (asmK_base E p A (fun _ _ => True) Ex Kc M Wp SK R0 msg hL hA hP hF).know m

/-- Over a signature, by the library's sigLift_know. -/
theorem asmI_know_sig (p : ℕ) [CharP E p] (A : LkAsmH E) (Sg : Sig E) (E₀ : ExtSpec)
    (Kc Wp : Type) (SK : PscLtK E E₀) (R0 : Rels Kc A.St E₀ (Sg.Msg × Wp))
    (msg : Sg.Msg → A.J → E)
    (hL : A.LtK SK Wp Kc msg) (hA : A.H.lkb.Adm p) (hP : padsOK (A.v' + 1) A.d A.pads = true)
    (hF : A.n + 1 + 1 = 2 ^ A.w) :
    ((A.baseKS SK).R.keep Sg.Smp Sg.ext).red.Know
      (Sg.over (cj R0 msg id (A.lk.inP fun _ _ => True) A.lk.inR)).on
      (Sg.over (cj R0 msg id (A.lk.inP fun _ _ => True) A.lk.inR)).relR
      (Sg.over (cj R0 msg Prod.fst (A.lk.out id id) (A.lk.out id id))).relR
      (fun _ _ w => (w.1, w.2)) (A.baseKS SK).e :=
  sigLift_know E Sg Kc _ _ Wp Wp E₀ E₀ (A.baseKS SK).R _ _ (fun _ _ _ wp => wp) (A.baseKS SK).e
    (asmK_base E p A (fun _ _ => True) E₀ Kc Sg.Msg Wp SK R0 msg hL hA hP hF).know

/-- The same; the exact side of the two joints, which Know does not read, written away. -/
theorem asmI_know_sigT (p : ℕ) [CharP E p] (A : LkAsmH E) (Sg : Sig E) (E₀ : ExtSpec)
    (Kc Wp : Type) (SK : PscLtK E E₀) (R0 : Rels Kc A.St E₀ (Sg.Msg × Wp))
    (msg : Sg.Msg → A.J → E)
    (hL : A.LtK SK Wp Kc msg) (hA : A.H.lkb.Adm p) (hP : padsOK (A.v' + 1) A.d A.pads = true)
    (hF : A.n + 1 + 1 = 2 ^ A.w) :
    ((A.baseKS SK).R.keep Sg.Smp Sg.ext).red.Know
      (Sg.over (cj R0 msg id (fun _ _ => True) A.lk.inR)).on
      (Sg.over (cj R0 msg id (fun _ _ => True) A.lk.inR)).relR
      (Sg.over (cj R0 msg Prod.fst (fun _ _ => True) (A.lk.out id id))).relR
      (fun _ _ w => (w.1, w.2)) (A.baseKS SK).e :=
  asmI_know_sig E p A Sg E₀ Kc Wp SK R0 msg hL hA hP hF

theorem asmK_libOK (A : LkAsmH E) (Ex : ExtSpec) (M Wp Kc : Type) (msg : M → A.J → E) :
    A.LtK (PscLtK.lib E Ex) Wp Kc msg :=
  { tie := fun l _ =>
      have ok := tieF_ok E A.H.tie l
      PscLtK.lib_ourK M Wp Kc _ _ ok.1 ok.2.2.1 ok.2.2.2 ok.2.1
    keys := fun l _ =>
      have ok := ldLkpP_ok E (A.IK.setV (A.v' + 1)).DK l
      PscLtK.lib_ourK M Wp Kc _ _ ok.1 ok.2.2.1 ok.2.2.2 ok.2.1
    tab := fun l _ =>
      have ok := ldLkpP_ok E A.D l
      PscLtK.lib_ourK M Wp Kc _ _ ok.1 ok.2.2.1 ok.2.2.2 ok.2.1
    clo := PscLtK.lib_coreK M Wp Kc _ _ (endM_vars E A.En).1
      (endM_deg E A.En (instM_ok E A.IT (A.n + 1) A.oE A.wE)) (endM_vars E A.En).2
    bit := PscLtK.lib_ourK M Wp Kc _ _ (ldZeroP_vars E A.Bt.zc).1 (ldLkpBitP_degX E A.Bt)
      (ldLkpBitP_degY E A.Bt) (ldZeroP_vars E A.Bt.zc).2 }

end
end Cb
