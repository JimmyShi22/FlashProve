-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdBattVFmt.lean: the format of the batching with a value shown.

Book-keeping for composition. A batching step of an interactive oracle proof meets the library's
conditions of format on a step of a protocol: which further oracle it leaves alone, what it passes
on of the statement, what its honest prover hands on of the witness, and which bounds it bears.
Definitions, statements and proofs. Rules of the framework only. The batching is the list of moves
`X.prog` of Cb/Ld/LdBattVSeg.lean, with its link `X.link`; that a link has the format is `Link.Fmt`
(Cb/Req1/LdReqFormat.lean). The analogue of the batching's parts of Cb/Obj/LdObjectReqEndFmt.lean
and Cb/Req1/LdSegRefFmt.lean.

Main names:
  `X.bk`: the block with its honest side on (messages, (prover encoded index, further witness)), as
    a block at the base (`BkA`, Cb/Ld/LdLkpTreeP.lean); it sends no oracle.
  `Spec.ldBattVSeg_plain`: `X.bk` has the format at the base (`Plain`, Cb/Ld/LdLkpFormat.lean): it
    only copies its oracles; the honest prover ends with its witness; every budget, in this sense:
    `∀ ρ T, b.P.bud ρ T` (b: `X.bk`); nothing withheld, in this sense: `withheld w x = ∅` for all w,
    x.
  `Spec.ldBattVSeg_linkFmt`: `X.link` has the format, for every i, r, px, q: the index, wherever it
    sits among the further oracles (i), is left alone (`idx`); whatever r reads off the state
    (`X.stOf`) is handed on (`pass`); so is what any reader px reads off the further witness
    (`hands`, with its two conditions: `Honest.Hands`, Cb/Ld/LdWfPre.lean); every bound q is borne
    (`bears`).
  `Spec.ldBattVSeg_fmt`: the three moves (`X.src` → `X.m0` → `X.m1` → `X.tgt`: the head of
    Cb/Ld/LdBattVSeg.lean) have the format (`LdProg.Fmt`, Cb/Req1/LdSegFormat.lean), if r₁ reads off
    fz z what r reads off the state in z.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdBattVSegProofs
import Cb.Req1.LdSegRefFmt
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR IOR.Chain Cb.LdLkp

namespace LdTenVD
variable {E Kc : Type} [Field E] [Fintype E] (X : LdTenVD E Kc)

/-- the block, with the honest side that X.link lifts -/
def bk : BkA Kc X.S.Msg ((X.Q → E) × (X.Xr × X.St)) X.Mid X.C.E0 (X.C.PIdx × X.Wp) :=
  ⟨X.bt.battV X.C.E0,
    idxH X.C (X.bt.hon X.C.E0 fun w : (X.C.Msg × X.S.Msg) × X.Wp => X.msg w.1),
    X.bt.nums X.C.E0 Kc⟩

end LdTenVD

namespace Spec

def ldBattVSeg_plain : Prop := ∀ (E Kc : Type) [Field E] [Fintype E] (X : LdTenVD E Kc), X.bk.Plain

def ldBattVSeg_linkFmt : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (E0 : ExtSpec) (Rc Pw : Type)
      (X : LdTenVD E Kc) (i : IxAt E0 X.C.E0) (r : X.Xr × X.St → Rc)
      (px : X.C.PIdx × X.Wp → Pw) (q : Finset X.m0.Ex.Pos → Prop),
    X.link.Fmt (X.m0.fmt i (fun x => r x.2) px q) (X.m1.fmt i (fun z => r (X.stOf z)) px q)

def ldBattVSeg_fmt : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (E0 : ExtSpec) (Rc Pw : Type) (X : LdTenVD E Kc)
      (St₁ : Type) (fz : X.Mid → St₁) (Az : Rels Kc St₁ X.C.E0 (X.S.Msg × (X.C.PIdx × X.Wp)))
      (i : IxAt E0 X.C.E0) (r : X.St → Rc) (r₁ : St₁ → Rc) (px : X.C.PIdx × X.Wp → Pw)
      (q : Finset X.src.Ex.Pos → Prop),
    (∀ z, r₁ (fz z) = r (X.stOf z).2) →
    (X.prog St₁ fz Az).Fmt (X.src.fmt i (fun x => r x.2.2) px q)
      ((X.tgt St₁ Az).fmt i (fun x => r₁ x.2) px q)

end Spec

theorem ldBattVSeg_plain : Spec.ldBattVSeg_plain := by
  intro E Kc _ _ X
  have h0 : ((⟨IOR.draw X.bt.Z.D X.bt.nx X.C.E0,
        Honest.draw X.bt.Z.D X.bt.nx X.C.E0 ((X.C.Msg × X.S.Msg) × X.Wp),
        Nums.draw Kc X.bt.Z.D X.bt.nx X.C.E0 X.bt.Z.err⟩ :
        BkA Kc (X.C.Msg × X.S.Msg) _ _ X.C.E0 X.Wp).seq
      ⟨X.bt.our.par.psc X.C.E0,
        X.bt.our.par.hon X.C.E0 (fun w => X.msg w.1),
        X.bt.our.par.nums X.C.E0 Kc⟩).Plain :=
    plain_seq (plain_draw _ _ _) (plain_psc X.bt.our.par X.C.E0 Kc _ _ _)
  refine ⟨h0.copies, fun w x c ρ => ?_, h0.budAll, fun w x => h0.free (idxIn X.C w) x⟩
  have e := h0.keepsW (idxIn X.C w) x c ρ
  have e2 : ((X.bk.H.strat w x c).run ρ).2.2 =
      (w.1, (w.2.1,
          (((X.bt.hon X.C.E0 fun w : (X.C.Msg × X.S.Msg) × X.Wp => X.msg w.1).strat
              (idxIn X.C w) x c).run ρ).2.2.2)) :=
    congrArg (fun o : Tr X.bk.R.shape × (X.Mid × (X.S.Msg × (X.C.PIdx × X.Wp))) => o.2.2)
      (Strat.run_map
        (fun o : X.Mid × ((X.C.Msg × X.S.Msg) × X.Wp) =>
          (o.1, ((w.1, (w.2.1, o.2.2)) : X.S.Msg × (X.C.PIdx × X.Wp))))
        ((X.bt.hon X.C.E0 fun w : (X.C.Msg × X.S.Msg) × X.Wp => X.msg w.1).strat (idxIn X.C w) x c)
        ρ)
  rw [e2,
    show (((X.bt.hon X.C.E0 fun w : (X.C.Msg × X.S.Msg) × X.Wp => X.msg w.1).strat
        (idxIn X.C w) x c).run ρ).2.2 = idxIn X.C w from e]
  rfl

theorem ldBattVSeg_linkFmt : Spec.ldBattVSeg_linkFmt := by
  intro E Kc _ _ E0 Rc Pw X i r px q
  have hp := ldBattVSeg_plain E Kc X
  exact
    { idx := IdxLink.of_step (lift_idxStep X.S hp) i
      pass := (Passes.keepX (R := X.bk.R) (r₁ := fun x => r x.2) (r₂ := fun z => r (X.stOf z))
        (fun x y τ z hz => congrArg r (X.battV_st x y τ z hz)) X.S.Smp).keepE X.S.ext
      hands := lift_hands X.S hp _ fun w => px w.2
      bears := lift_bears X.S hp q }

theorem ldBattVSeg_fmt : Spec.ldBattVSeg_fmt := by
  intro E Kc _ _ E0 Rc Pw X St₁ fz Az i r r₁ px q hr
  obtain ⟨_, mU, _⟩ := ldFmt_mv E Kc E0 Rc Pw
  unfold LdTenVD.prog
  refine (LdProg.fmt_snoc _ _ _ _).2
    ⟨X.m1.fmt i (fun z => r (X.stOf z).2) px q,
      (LdProg.fmt_snoc _ _ _ _).2
        ⟨X.m0.fmt i (fun x => r x.2.2) px q,
          (LdProg.fmt_snoc _ _ _ _).2
            ⟨X.src.fmt i (fun x => r x.2.2) px q, (LdProg.fmt_nil _ _ _).2 rfl, ?_⟩,
          ?_⟩,
      ?_⟩
  · exact ldFmt_keep E Kc E0 Rc Pw X.S _ _ _ _ X.C.E0 X.src.A X.m0.A _ _ _ i (fun x => r x.2.2)
      (fun x => r x.2.2) px px q (fun x x' e => by cases e; rfl) fun _ => rfl
  · exact mU _ _ _ _ _
      ((Chain.fmt_one _ _ _).2 (ldBattVSeg_linkFmt E Kc E0 Rc Pw X i (fun x => r x.2) px q))
  · exact ldFmt_keep E Kc E0 Rc Pw X.S _ _ _ _ X.C.E0 X.m1.A (X.tgt St₁ Az).A _ _ _ i
      (fun z => r (X.stOf z).2) (fun x => r₁ x.2) px px q
      (fun x x' e => by cases e; exact hr _) fun _ => rfl

end Cb
