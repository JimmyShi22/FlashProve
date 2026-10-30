-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Obj/LdObjectReqEndIntoFmt.lean: for toys: the format of the block in which the prover says masked
values, and of the tail from the stage after a closing to the last three moves of a request.

This file is book-keeping on a chain of interactive oracle reductions. A format (`JFmt`,
Cb/Req1/LdReqFormat.lean) says where the encoded index is among a joint's oracles, and where record
and prover encoded index are read; a link has the format (`Link.Fmt`) if, among other clauses, it
leaves the index alone and hands these on.
A definition (`X.sayBk`), statements (all but `ldStepF_fmt_le` a `Prop` in `Cb.Spec`) and proofs.
Framework only; no place of a text is rendered.
The block of Cb/Ld/LdTenSay.lean sends scalars only: it reads no oracle and ties none. So, as for
the batching (Cb/Obj/LdObjectReqEndFmt.lean):

Main names:
  `X.sayBk`, `Spec.ldOREIF_plain`: it has the format at the base (`Plain`, Cb/Ld/LdLkpFormat.lean):
    only copies; the honest prover ends with its witness; every budget; nothing withheld.
  `Spec.ldOREIF_link`: `X.sayLink` has the format: the index is left alone; whatever is read off the
    state is handed on; any reader of the further witness; every bound is borne.
  `Spec.ldOREIF_tail`: `R.tailP` (Cb/Obj/LdObjectReqEndInto.lean) has the format, from the stage
    after a closing (record: `R.rc` of the second component; prover encoded index: `Prod.fst`) to
    `R.X.src` in the form in which the format of `R.lastP` starts. `Spec.ldOREIF_tail_le`: the
    demand (`JFmt.q`) after the tail may be smaller than the one in front of it.

Terms: lean/GLOSSARY.md.
-/
import Cb.Obj.LdObjectReqEndInto
import Cb.Obj.LdObjectReqEndFmt
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR IOR.Chain Cb.LdLkp

/-- The block, with the honest side that `X.sayLink` lifts. -/
def LdTenD.sayBk {E Kc : Type} [Field E] [Fintype E] (X : LdTenD E Kc) :
    BkA Kc X.S.Msg (X.Xr × X.St) ((X.Q → E) × (X.Xr × X.St)) X.C.E0 (X.C.PIdx × X.Wp) :=
  ⟨X.bt.say X.C.E0,
    idxH X.C (X.bt.sayH X.C.E0 fun w : (X.C.Msg × X.S.Msg) × X.Wp => X.msg w.1),
    X.bt.sayN X.C.E0 Kc⟩

namespace Spec

def ldOREIF_plain : Prop := ∀ (E Kc : Type) [Field E] [Fintype E] (X : LdTenD E Kc), X.sayBk.Plain

def ldOREIF_link : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (E0 : ExtSpec) (Rc Pw : Type)
      (X : LdTenD E Kc) (i : IxAt E0 X.C.E0) (r : X.Xr × X.St → Rc)
      (px : X.C.PIdx × X.Wp → Pw) (q : Finset X.p1.Ex.Pos → Prop),
    X.sayLink.Fmt (X.p1.fmt i r px q) (X.m0.fmt i (fun x => r x.2) px q)

def ldOREIF_tail : Prop :=
  ∀ (F E Kc : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]
      (R : LdORE F E Kc) (Xa : Type) (Φ : Xa → R.S.Msg → Prop)
      (A₁ : Rels Kc R.St R.Cf.conf.E0 (R.S.Msg × (R.Cf.conf.PIdx × R.G)))
      (rows : Xa → R.X.Xr) (q : Finset R.z.J.E.Pos → Prop),
    (R.tailP Xa Φ A₁ rows).Fmt
      ((R.pre Xa Φ A₁).fmt (⟨id, id⟩ : IxAt R.Cf.conf.E0 R.Cf.conf.E0)
        (fun x => R.rc x.2) Prod.fst q)
      (R.X.src.fmt (⟨id, id⟩ : IxAt R.Cf.conf.E0 R.Cf.conf.E0) (fun x => R.rc x.2.2) Prod.fst q)

/-- The same, with a smaller demand after the tail than in front of it. -/
def ldOREIF_tail_le : Prop :=
  ∀ (F E Kc : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]
      (R : LdORE F E Kc) (Xa : Type) (Φ : Xa → R.S.Msg → Prop)
      (A₁ : Rels Kc R.St R.Cf.conf.E0 (R.S.Msg × (R.Cf.conf.PIdx × R.G)))
      (rows : Xa → R.X.Xr) (q q' : Finset R.z.J.E.Pos → Prop),
    (∀ U, q' U → q U) →
    (R.tailP Xa Φ A₁ rows).Fmt
      ((R.pre Xa Φ A₁).fmt (⟨id, id⟩ : IxAt R.Cf.conf.E0 R.Cf.conf.E0)
        (fun x => R.rc x.2) Prod.fst q)
      (R.X.src.fmt (⟨id, id⟩ : IxAt R.Cf.conf.E0 R.Cf.conf.E0) (fun x => R.rc x.2.2) Prod.fst q')

end Spec

/-- A step without rounds over one signature, under the hypotheses below: the demand after it may be
smaller. -/
theorem ldStepF_fmt_le {E Kc : Type} [Field E] [Fintype E] (S : Sig E) {St St' Wp : Type}
    {E₀ E0 : ExtSpec} {Rc Pw : Type} (A : Rels Kc St E₀ (S.Msg × Wp))
    (A' : Rels Kc St' E₀ (S.Msg × Wp)) (f : St → St') (i : IxAt E0 E₀) (rc : St → Rc)
    (rc' : St' → Rc) (px : Wp → Pw) (q q' : Finset (E₀.prod S.ext).Pos → Prop)
    (h : ∀ x, rc' (f x) = rc x) (hq : ∀ U, q' U → q U) :
    (ldStepF S A A' f).Fmt ((⟨S, St, E₀, Wp, A⟩ : LdStage E Kc).fmt i rc px q)
      ((⟨S, St', E₀, Wp, A'⟩ : LdStage E Kc).fmt i rc' px q') := by
  refine ldFmt_step E Kc E0 Rc Pw _ _ _ _ _ _ _ _
    (ExtMap.Moves.pair_left (ExtMap.Moves.comp (ExtMap.Moves.id i) (ExtMap.Moves.fst i S.ext))
      (ExtMap.Avoids.snd i S.ext))
    ?_ (fun _ => rfl) ?_
  · intro x x' e
    obtain rfl := Option.some.inj e
    exact h x.1
  · intro U V hV hU
    have e : V = U :=
      Finset.ext fun x =>
        (hV x).trans ⟨fun ⟨u, hu, hx⟩ => ((sideG_id_mem S E₀ u x).1 hx) ▸ hu,
          fun hx => ⟨x, hx, (sideG_id_mem S E₀ x x).2 rfl⟩⟩
    rw [e]
    exact hq U hU

theorem ldOREIF_plain : Spec.ldOREIF_plain := fun _ _ _ _ X =>
  ⟨ldSay_copies (0 : X.bt.Q → _) (fun (st : X.bt.St) a => (a, st)) X.C.E0,
    fun _ _ _ _ => rfl, fun _ _ => trivial,
    fun _ _ => Set.union_self _⟩

theorem ldOREIF_link : Spec.ldOREIF_link := by
  intro E Kc _ _ E0 Rc Pw X i r px q
  have hp := ldOREIF_plain E Kc X
  exact
    { idx := IdxLink.of_step (lift_idxStep X.S hp) i
      pass := (Passes.keepX (R := X.sayBk.R) (r₁ := r) (r₂ := fun x => r x.2) (fun x y τ z hz => by
        obtain rfl := Option.some.inj hz
        rfl) X.S.Smp).keepE X.S.ext
      hands := lift_hands X.S hp _ fun w => px w.2
      bears := lift_bears X.S hp q }

theorem ldOREIF_tail : Spec.ldOREIF_tail := by
  intro F E Kc _ _ _ _ _ R Xa Φ A₁ rows q
  unfold LdORE.tailP LdTenD.sayT
  rw [LdProg.app_snoc, LdProg.app_snoc, LdProg.app_nil]
  refine (LdProg.fmt_snoc _ _ _ _).2
    ⟨R.X.m0.fmt ⟨id, id⟩ (fun x => R.rc x.2.2) Prod.fst q,
      (LdProg.fmt_snoc _ _ _ _).2
        ⟨R.X.p1.fmt ⟨id, id⟩ (fun x => R.rc x.2) Prod.fst q,
          (LdProg.fmt_snoc _ _ _ _).2 ⟨_, (LdProg.fmt_nil _ _ _).2 rfl, ?_⟩,
          ?_⟩,
      ?_⟩
  · exact ldStepF_fmt R.S (claimRels Φ A₁) R.X.p1.A (fun x => (rows x.1, x.2)) ⟨id, id⟩
      _ _ Prod.fst q (fun _ => rfl)
  · exact (fmt_one _ _ _).2 (ldOREIF_link E Kc _ _ _ R.X ⟨id, id⟩ (fun s => R.rc s.2) Prod.fst q)
  · exact ldStepF_fmt R.S R.X.m0.A R.X.src.A (fun x => (x.2.1, (x.1, x.2.2))) ⟨id, id⟩
      _ _ Prod.fst q (fun _ => rfl)

theorem ldOREIF_tail_le : Spec.ldOREIF_tail_le := by
  intro F E Kc _ _ _ _ _ R Xa Φ A₁ rows q q' hq
  unfold LdORE.tailP LdTenD.sayT
  rw [LdProg.app_snoc, LdProg.app_snoc, LdProg.app_nil]
  refine (LdProg.fmt_snoc _ _ _ _).2
    ⟨R.X.m0.fmt ⟨id, id⟩ (fun x => R.rc x.2.2) Prod.fst q',
      (LdProg.fmt_snoc _ _ _ _).2
        ⟨R.X.p1.fmt ⟨id, id⟩ (fun x => R.rc x.2) Prod.fst q',
          (LdProg.fmt_snoc _ _ _ _).2 ⟨_, (LdProg.fmt_nil _ _ _).2 rfl, ?_⟩,
          ?_⟩,
      ?_⟩
  · exact ldStepF_fmt_le R.S (claimRels Φ A₁) R.X.p1.A (fun x => (rows x.1, x.2)) ⟨id, id⟩
      _ _ Prod.fst q q' (fun _ => rfl) hq
  · exact (fmt_one _ _ _).2 (ldOREIF_link E Kc _ _ _ R.X ⟨id, id⟩ (fun s => R.rc s.2) Prod.fst q')
  · exact ldStepF_fmt R.S R.X.m0.A R.X.src.A (fun x => (x.2.1, (x.1, x.2.2))) ⟨id, id⟩
      _ _ Prod.fst q' (fun _ => rfl)

end Cb
