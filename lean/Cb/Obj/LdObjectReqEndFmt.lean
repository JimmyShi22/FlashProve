-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Obj/LdObjectReqEndFmt.lean: the format of the batching of tensor rows, and of the last three
moves of a request.

This file is book-keeping on a chain of interactive oracle reductions. A format (`JFmt`,
Cb/Req1/LdReqFormat.lean) says where the encoded index is among a joint's oracles, and where record
and prover encoded index are read; a link has the format (`Link.Fmt`) if, among other clauses, it
leaves the index alone and hands these on.
One definition, statements and proofs. Framework only; no place of a text is rendered.
The batching of tensor rows on the encoded index (`LdTenD`, Cb/Req1/LdSegRefTen.lean) sends scalars
only: it reads no oracle and ties none; its claims read the index through the statement's own
decoding.

Main names:
  `X.bk`: the block with its honest side on (messages, (prover encoded index, `X.Wp`)), as a block
    that sends no oracle (`BkA`, Cb/Ld/LdLkpTreeP.lean).
  `Spec.ldOREFmt_plain`: it has the format at the base (`Plain`, Cb/Ld/LdLkpFormat.lean): only
    copies; the honest prover ends with its witness; every budget; nothing withheld.
  `Spec.ldOREFmt_link`: `X.link` has the format: the index, wherever it sits among the further
    oracles, is left alone; whatever is read off the state (`X.stOf`) is handed on; any reader of
    the further witness; every bound is borne.
  `Spec.ldOREFmt_last`: `R.lastP` (Cb/Obj/LdObjectReqEnd.lean) has the format, from "rows on all
    entries, beside the pending tensor rows" to the last stage of a request in the object's form
    `R.O.fmtZAt` (record: the second component; prover encoded index: `Prod.fst` of the further
    witness).

Terms: lean/GLOSSARY.md.
-/
import Cb.Obj.LdObjectReqEndAt
import Cb.Req1.LdSegFrontFmt
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR IOR.Chain Cb.LdLkp

namespace LdTenD
variable {E Kc : Type} [Field E] [Fintype E] (X : LdTenD E Kc)

/-- The block, with the honest side that `X.link` lifts. -/
def bk :
    BkA Kc X.S.Msg ((X.Q → E) × (X.Xr × X.St)) X.bt.par.Mid X.C.E0 (X.C.PIdx × X.Wp) :=
  ⟨X.bt.batt X.C.E0,
    idxH X.C (X.bt.hon X.C.E0 fun w : (X.C.Msg × X.S.Msg) × X.Wp => X.msg w.1),
    X.bt.nums X.C.E0 Kc⟩

end LdTenD

namespace Spec

def ldOREFmt_plain : Prop := ∀ (E Kc : Type) [Field E] [Fintype E] (X : LdTenD E Kc), X.bk.Plain

def ldOREFmt_link : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (E0 : ExtSpec) (Rc Pw : Type)
      (X : LdTenD E Kc) (i : IxAt E0 X.C.E0) (r : X.Xr × X.St → Rc)
      (px : X.C.PIdx × X.Wp → Pw) (q : Finset X.m0.Ex.Pos → Prop),
    X.link.Fmt (X.m0.fmt i (fun x => r x.2) px q) (X.m1.fmt i (fun z => r (X.stOf z)) px q)

def ldOREFmt_last : Prop :=
  ∀ (F E Kc : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]
      (R : LdORE F E Kc) (q : Finset R.z.J.E.Pos → Prop),
    R.lastP.Fmt
      (R.X.src.fmt (⟨id, id⟩ : IxAt R.Cf.conf.E0 R.Cf.conf.E0) (fun x => R.rc x.2.2) Prod.fst q)
      (R.O.fmtZAt R.bEnd Prod.fst q)

end Spec

theorem ldOREFmt_plain : Spec.ldOREFmt_plain := by
  intro E Kc _ _ X
  have h0 : ((⟨IOR.draw X.bt.Z.D X.bt.nx X.C.E0,
        Honest.draw X.bt.Z.D X.bt.nx X.C.E0 ((X.C.Msg × X.S.Msg) × X.Wp),
        Nums.draw Kc X.bt.Z.D X.bt.nx X.C.E0 X.bt.Z.err⟩ :
        BkA Kc (X.C.Msg × X.S.Msg) _ _ X.C.E0 X.Wp).seq
      ⟨X.bt.par.core X.C.E0,
        X.bt.par.honC X.C.E0 (fun w => X.msg w.1),
        X.bt.par.numsC X.C.E0 Kc⟩).Plain :=
    plain_seq (plain_draw _ _ _) (plain_core X.bt.par X.C.E0 Kc _ _ _)
  refine ⟨h0.copies, fun w x c ρ => ?_, h0.budAll, fun w x => h0.free (idxIn X.C w) x⟩
  have e := h0.keepsW (idxIn X.C w) x c ρ
  have e2 : ((X.bk.H.strat w x c).run ρ).2.2 =
      (w.1, (w.2.1,
          (((X.bt.hon X.C.E0 fun w : (X.C.Msg × X.S.Msg) × X.Wp => X.msg w.1).strat
              (idxIn X.C w) x c).run ρ).2.2.2)) :=
    congrArg (fun o : Tr X.bk.R.shape × (X.bt.par.Mid × (X.S.Msg × (X.C.PIdx × X.Wp))) => o.2.2)
      (Strat.run_map
        (fun o : X.bt.par.Mid × ((X.C.Msg × X.S.Msg) × X.Wp) =>
          (o.1, ((w.1, (w.2.1, o.2.2)) : X.S.Msg × (X.C.PIdx × X.Wp))))
        ((X.bt.hon X.C.E0 fun w : (X.C.Msg × X.S.Msg) × X.Wp => X.msg w.1).strat (idxIn X.C w) x c)
        ρ)
  rw [e2,
    show (((X.bt.hon X.C.E0 fun w : (X.C.Msg × X.S.Msg) × X.Wp => X.msg w.1).strat
        (idxIn X.C w) x c).run ρ).2.2 = idxIn X.C w from e]
  rfl

theorem ldOREFmt_link : Spec.ldOREFmt_link := by
  intro E Kc _ _ E0 Rc Pw X i r px q
  have hp := ldOREFmt_plain E Kc X
  exact
    { idx := IdxLink.of_step (lift_idxStep X.S hp) i
      pass := (Passes.keepX (R := X.bk.R) (r₁ := fun x => r x.2) (r₂ := fun z => r (X.stOf z))
        (fun x y τ z hz => congrArg r (X.batt_st x y τ z hz)) X.S.Smp).keepE X.S.ext
      hands := lift_hands X.S hp _ fun w => px w.2
      bears := lift_bears X.S hp q }

theorem ldOREFmt_last : Spec.ldOREFmt_last := by
  intro F E Kc _ _ _ _ _ R q
  unfold LdORE.lastP
  refine (LdProg.fmt_snoc _ _ _ _).2
    ⟨R.X.m1.fmt ⟨id, id⟩ (fun z => R.rc (R.X.stOf z).2) Prod.fst q,
      (LdProg.fmt_snoc _ _ _ _).2
        ⟨R.X.m0.fmt ⟨id, id⟩ (fun x => R.rc x.2.2) Prod.fst q,
          (LdProg.fmt_snoc _ _ _ _).2 ⟨_, (LdProg.fmt_nil _ _ _).2 rfl, ?_⟩,
          ?_⟩,
      ?_⟩
  · exact ldStepF_fmt R.S R.X.src.A R.X.m0.A (fun x => (x.2.1, (x.1, x.2.2))) ⟨id, id⟩
      _ _ Prod.fst q (fun _ => rfl)
  · exact (fmt_one _ _ _).2 (ldOREFmt_link E Kc _ _ _ R.X ⟨id, id⟩ (fun s => R.rc s.2) Prod.fst q)
  · exact ldStepF_fmt R.S R.X.m1.A R.bEnd (fun z => (z, R.recOf z)) ⟨id, id⟩ _ (fun b => b.2)
      Prod.fst q (fun _ => rfl)

end Cb
