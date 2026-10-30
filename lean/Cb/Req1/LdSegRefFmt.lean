-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Req1/LdSegRefFmt.lean: the format of the body of the reference segment.

Book-keeping: this file is about a property of a sequence of reductions (its format), along the
body of a segment.
Definitions, statements and proofs. Rules of the framework only; nothing of a text is rendered
here.
Cb/Req1/LdSegFormat.lean says what the format of a list of moves is: where the encoded index is
among the further oracles (i), that the record (rc) and the prover encoded index (px) are handed
on, and that every link bears what follows (q: which sets of positions may still be asked for).
Here it is shown, under the hypotheses of each statement, for the lists of
Cb/Req1/LdSegRefRng.lean, Cb/Req1/LdSegRefDig.lean, Cb/Req1/LdSegRefRows.lean,
Cb/Req1/LdSegRefTen.lean, for the body (Cb/Req1/LdSegRefBody.lean) and for the closed body
(Cb/Req1/LdSegRefAll.lean).

Main names:
  `Spec.ldFmt_copies`: a reduction on claims about messages that only copies its oracles and bears
    every budget, lifted over the oracle messages of a stage; the further witness may change. It is
    asked that the verifier's output keeps the record and that the honest prover's new further
    witness keeps what px reads.
  `Spec.ldFmt_keep`: a step without rounds over one signature and the same further oracles, which
    may reject, and whose honest map makes a new further witness. It is asked that what it puts out
    keeps the record and that the new further witness keeps what px reads.
  In the lists below, "front" and "tensor" of `Spec.ldSegRef_body_fmt` apart (their formats are
    hypotheses), the demand q on positions changes at the two sendings only (`S.qSum`: the new
    oracle messages bear t positions each).
  `Spec.ldSegRef_rr_fmt`: read, then the range check, from `D.d1.Hyp`, `D.d3.Hyp`.
  `Spec.ldSegRef_dg_fmt`: step; shift; step; the digits' lookup (its chain's format: a hypothesis).
    `Spec.ldSegRef_asm_fmt`: the assembled lookup has it.
  `Spec.ldSegRef_ga_fmt`: the step that gathers the rows, if g₀ keeps the record.
  `Spec.ldSegRef_tn_fmt`: the batching's three moves, if fz keeps the record.
  `Spec.ldSegRef_body_fmt`: the body, from the formats of front, digits' lookup and tensor, the
    hypotheses of the two sendings, and: g₀ keeps the record.
  `Spec.ldSegRefAll_fmt`: the closed body: from `A.OK pp` (pp the characteristic of E) and: each
    map on explicit parts keeps what the reader of the record reads (`ρ.Laws`, and the like for
    fz).
Terms: lean/GLOSSARY.md.
-/
import Cb.Req1.LdSegRefAllProofs
import Cb.Req1.LdSegFrontFmt
import Cb.Obj.LdObjectReqEndFmt

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Cb.Rng Cb.RngPk Cb.Lkp Cb.LdLkp IOR IOR.Chain

/-- The readers of the record along the closed body. -/
structure LdRefR {E Kc : Type} [Field E] [Fintype E] {I : LdRefIx E}
    (A : LdRefD E Kc I) (Rc : Type) where
  rcV : A.V.Fp.St → Rc
  r0  : A.V.Fp.Z.St0 → Rc
  r   : ∀ j, (A.V.T j).St → Rc
  rz  : A.Xa.Q.D.St → Rc
  rT  : A.Stt → Rc

/-- Each map on explicit parts keeps what the reader of the record reads. -/
structure LdRefR.Laws {E Kc : Type} [Field E] [Fintype E] {I : LdRefIx E} {A : LdRefD E Kc I}
    {Rc : Type} (ρ : LdRefR A Rc) : Prop where
  e   : ∀ x, ρ.r0 (A.V.Fp.e x) = ρ.rcV x.1.1
  g0  : ∀ o, ρ.r 0 (A.V.g0 o).2 = ρ.r0 (A.V.Fp.Z.old o.st)
  g   : ∀ j o, ρ.r (j + 1) (A.V.g j o).2 = ρ.r j o.st
  gz  : ∀ o, ρ.rz (A.V.gz o) = ρ.r A.V.m o.st
  gT  : ∀ st, ρ.rT (A.g₀ st).2 = ρ.rz st

namespace Spec

/-- A lifted reduction that only copies its oracles. -/
def ldFmt_copies : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (E0 : ExtSpec) (Rc Pw : Type) (a : LdStage E Kc)
      (St' Wp' : Type) (B : Rels Kc St' a.E₀ (a.S.Msg × Wp')) (R : IOR a.St a.E₀ St' a.E₀)
      (H : R.Honest (a.S.Msg × a.Wp) (a.S.Msg × Wp'))
      (ext : a.S.Msg → a.St × a.E₀.Str → Tr R.shape → Wp' → a.Wp) (P : Nums Kc R)
      (i : IxAt E0 a.E₀) (rc : a.St → Rc) (rc' : St' → Rc) (px : a.Wp → Pw)
      (px' : Wp' → Pw) (q : Finset a.Ex.Pos → Prop),
    R.OnlyCopies → (∀ ρ T, P.bud ρ T) → R.Passes rc rc' →
    (∀ m wp x c ρ, px' ((H.strat (m, wp) x c).run ρ).2.2.2 = px wp) →
    (a.lift B R H ext P).Fmt (a.fmt i rc px q)
      ((⟨a.S, St', a.E₀, Wp', B⟩ : LdStage E Kc).fmt i rc' px' q)

/-- A step over one signature and the same further oracles. -/
def ldFmt_keep : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (E0 : ExtSpec) (Rc Pw : Type) (S : Sig E)
      (St St' Wp Wp' : Type) (E₀ : ExtSpec) (A : Rels Kc St E₀ (S.Msg × Wp))
      (A' : Rels Kc St' E₀ (S.Msg × Wp')) (f : St × S.Smp → Option (St' × S.Smp))
      (m : (St × S.Smp) × (S.Wit × Wp) → (St' × S.Smp) × (S.Wit × Wp'))
      (back : (St × S.Smp) × (E₀.prod S.ext).Str → S.Wit × Wp' → S.Wit × Wp) (i : IxAt E0 E₀)
      (rc : St → Rc) (rc' : St' → Rc) (px : Wp → Pw) (px' : Wp' → Pw)
      (q : Finset (E₀.prod S.ext).Pos → Prop),
    (∀ x x', f x = some x' → rc' x'.1 = rc x.1) → (∀ p, px' (m p).2.2 = px p.2.2) →
    (LdMv.step (⟨S, St, E₀, Wp, A⟩ : LdStage E Kc) ⟨S, St', E₀, Wp', A'⟩ f
        (sideG S (ExtMap.id E₀)) m back).Fmt
      ((⟨S, St, E₀, Wp, A⟩ : LdStage E Kc).fmt i rc px q)
      ((⟨S, St', E₀, Wp', A'⟩ : LdStage E Kc).fmt i rc' px' q)

def ldSegRef_rr_fmt : Prop :=
  ∀ (E Kc : Type) (E₀ : ExtSpec) (Wp : Type) [Field E] [Fintype E] (E0 : ExtSpec)
      (Rc Pw : Type) (D : LdRrD E Kc E₀ Wp) (i : IxAt E0 E₀) (rc : D.St → Rc)
      (px : Wp → Pw) (q : Finset D.s0.Ex.Pos → Prop),
    D.d1.Hyp → D.d3.Hyp →
    D.prog.Fmt (D.s0.fmt i rc px q)
      (D.s4.fmt i (fun x => rc x.1) px ((D.S.sum D.N).qSum D.N' (D.S.qSum D.N q D.t) D.t'))

def ldSegRef_dg_fmt : Prop :=
  ∀ (E Kc : Type) (E₀ : ExtSpec) (Wp : Type) [Field E] [Fintype E] (E0 : ExtSpec) (Rc Pw : Type)
      (Q : LdDgP E Kc E₀ Wp) (mult : Q.X₄ × E → Ms Q.T E₀ → Prop) (ent : Ms Q.T E₀ → Q.Nn → E)
      (n : ℕ) (lk : Chain Kc (Q.lkS mult).J (Q.lkT ent n).J) (i : IxAt E0 E₀) (rc : Q.X₄ → Rc)
      (px : Wp → Pw) (q : Finset Q.D.s4.Ex.Pos → Prop),
    lk.Fmt ((Q.lkS mult).fmt i (fun x => rc x.1) px q)
      ((Q.lkT ent n).fmt i (fun x => rc x.1.1) px q) →
    (Q.prog mult ent n lk).Fmt (Q.D.s4.fmt i rc px q) ((Q.lkT ent n).fmt i (fun x => rc x.1.1) px q)

def ldSegRef_asm_fmt : Prop :=
  ∀ (E Kc : Type) (E₀ : ExtSpec) (Wp : Type) [Field E] [Fintype E] (E0 : ExtSpec)
      (Rc Pw : Type) (X : LdDgA E Kc E₀ Wp) (i : IxAt E0 E₀) (rc : X.Q.X₄ → Rc)
      (px : Wp → Pw) (q : Finset X.Q.D.s4.Ex.Pos → Prop),
    X.lk.Fmt ((X.Q.lkS X.mult).fmt i (fun x => rc x.1) px q)
      ((X.Q.lkT X.ent X.A.nRows).fmt i (fun x => rc x.1.1) px q)

def ldSegRef_ga_fmt : Prop :=
  ∀ (E Kc : Type) (E₀ : ExtSpec) (Wp : Type) [Field E] [Fintype E] (E0 : ExtSpec) (Rc Pw : Type)
      (G : LdGaP E Kc E₀ Wp) (St₀ : Type) (g₀ : G.Q.D.St → St₀)
      (Ar : Rels Kc St₀ E₀ (G.Q.T.Msg × Wp)) (i : IxAt E0 E₀) (rc : G.Q.D.St → Rc) (r₀ : St₀ → Rc)
      (px : Wp → Pw) (q : Finset G.Q.D.s4.Ex.Pos → Prop),
    (∀ st, r₀ (g₀ st) = rc st) →
    (G.step St₀ g₀ Ar).Fmt ((G.Q.lkT G.ent G.n).fmt i (fun x => rc x.1.1.1) px q)
      ((G.tgt St₀ Ar).fmt i (fun x => r₀ x.2) px q)

def ldSegRef_tn_fmt : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (E0 : ExtSpec) (Rc Pw : Type) (X : LdTenD E Kc)
      (St₁ : Type) (fz : X.bt.par.Mid → St₁)
      (Az : Rels Kc St₁ X.C.E0 (X.S.Msg × (X.C.PIdx × X.Wp))) (i : IxAt E0 X.C.E0) (r : X.St → Rc)
      (r₁ : St₁ → Rc) (px : X.C.PIdx × X.Wp → Pw) (q : Finset X.src.Ex.Pos → Prop),
    (∀ z, r₁ (fz z) = r (X.stOf z).2) →
    (X.prog St₁ fz Az).Fmt (X.src.fmt i (fun x => r x.2.2) px q)
      ((X.tgt St₁ Az).fmt i (fun x => r₁ x.2) px q)

/-- The body. -/
def ldSegRef_body_fmt : Prop :=
  ∀ (E Kc : Type) (E₀ : ExtSpec) (Wp : Type) [Field E] [Fintype E] (E0 : ExtSpec) (Rc Pw : Type)
      (Y : LdBodyD E Kc E₀ Wp) (z : LdStage E Kc) (tensor : LdProg Y.tgt z) (i : IxAt E0 E₀)
      (rc : Y.G.Q.D.St → Rc) (r₀ : Y.St₀ → Rc) (px : Wp → Pw) (q : Finset Y.G.Q.D.s0.Ex.Pos → Prop)
      (φ : JFmt Kc E0 Rc Pw Y.a.J) (ψ : JFmt Kc E0 Rc Pw z.J),
    Y.G.Q.D.d1.Hyp → Y.G.Q.D.d3.Hyp → (∀ st, r₀ (Y.g₀ st) = rc st) →
    Y.front.Fmt φ (Y.G.Q.D.s0.fmt i rc px q) →
    Y.lk.Fmt ((Y.G.Q.lkS Y.mult).fmt i (fun x => rc x.1.1) px
        ((Y.G.Q.D.S.sum Y.G.Q.D.N).qSum
          Y.G.Q.D.N' (Y.G.Q.D.S.qSum Y.G.Q.D.N q Y.G.Q.D.t) Y.G.Q.D.t'))
      ((Y.G.Q.lkT Y.G.ent Y.G.n).fmt i (fun x => rc x.1.1.1) px
        ((Y.G.Q.D.S.sum Y.G.Q.D.N).qSum
          Y.G.Q.D.N' (Y.G.Q.D.S.qSum Y.G.Q.D.N q Y.G.Q.D.t) Y.G.Q.D.t')) →
    tensor.Fmt
      (Y.tgt.fmt i (fun x => r₀ x.2) px
        ((Y.G.Q.D.S.sum Y.G.Q.D.N).qSum
          Y.G.Q.D.N' (Y.G.Q.D.S.qSum Y.G.Q.D.N q Y.G.Q.D.t) Y.G.Q.D.t')) ψ →
    (Y.body z tensor).Fmt φ ψ

/-- The closed body. -/
def ldSegRefAll_fmt : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (pp : ℕ) [CharP E pp] (E0 : ExtSpec) (Rc Pw : Type)
      (I : LdRefIx E) (A : LdRefD E Kc I) (i : IxAt E0 I.C.E0) (ρ : LdRefR A Rc)
      (px : I.C.PIdx × (A.W₁ × A.Gh) → Pw) (q : Finset A.Xa.Q.D.s0.Ex.Pos → Prop) (St₁ : Type)
      (fz : A.X.bt.par.Mid → St₁)
      (Az : Rels Kc St₁ I.C.E0 (A.Xa.Q.T.Msg × (I.C.PIdx × (A.W₁ × A.Gh)))) (r₁ : St₁ → Rc),
    A.OK pp → ρ.Laws → (∀ z, r₁ (fz z) = ρ.rT (A.X.stOf z).2) →
    (A.body St₁ fz Az).Fmt (A.V.Fp.s0.fmt i ρ.rcV px q)
      ((A.X.tgt St₁ Az).fmt i (fun x => r₁ x.2) px
        ((A.Xa.Q.D.S.sum A.Xa.Q.D.N).qSum
          A.Xa.Q.D.N' (A.Xa.Q.D.S.qSum A.Xa.Q.D.N q A.Xa.Q.D.t) A.Xa.Q.D.t'))

end Spec

theorem ldFmt_copies : Spec.ldFmt_copies := by
  intro E Kc _ _ E0 Rc Pw a St' Wp' B R H ext P i rc rc' px px' q hc hb hr hh
  refine ⟨IdxLink.of_step (IdxStep.keep hc.noReads hc.noTie hc.copy hc.src a.S.Smp a.S.ext) i,
    (hr.keepX a.S.Smp).keepE a.S.ext,
    ?_, ?_⟩
  · intro x y w c ρ _ _
    have e : ((a.lift B R H ext P).H.strat w x c).run ρ = _ := Sig.liftH_run a.S H w x c ρ
    rw [e]
    exact hh _ _ _ _ _
  · intro ρ U hU
    refine ⟨hb _ _, ?_⟩
    have e : (a.lift B R H ext P).R.need ρ U = U := need_keep hc ρ U
    rw [e]
    exact hU

theorem ldFmt_keep : Spec.ldFmt_keep := by
  intro E Kc _ _ E0 Rc Pw S St St' Wp Wp' E₀ A A' f m back i rc rc' px px' q hr hp
  refine ldFmt_step E Kc E0 Rc Pw _ _ _ _ _ _ _ _
    (ExtMap.Moves.pair_left (ExtMap.Moves.comp (ExtMap.Moves.id i) (ExtMap.Moves.fst i S.ext))
      (ExtMap.Avoids.snd i S.ext))
    hr hp ?_
  intro U V hV hU
  have e : V = U :=
    Finset.ext fun x =>
      (hV x).trans ⟨fun ⟨u, hu, hx⟩ => ((sideG_id_mem S E₀ u x).1 hx) ▸ hu,
        fun hx => ⟨x, hx, (sideG_id_mem S E₀ x x).2 rfl⟩⟩
  rw [e]
  exact hU

/-- what a sender hands on, read through "back" -/
theorem LdSendD.rest_snd {E Kc : Type} [Field E] {a : LdStage E Kc} (d : LdSendD a)
    (h : d.D.Laws (a.S.backN d.N d.bk)) (w : a.W) :
    ∃ m, d.bk m (d.D.rest w).2 = w.2 :=
  ⟨_, congrArg Prod.snd (h.back w (Classical.arbitrary _))⟩

theorem ldSegRef_rr_fmt : Spec.ldSegRef_rr_fmt := by
  intro E Kc E₀ Wp _ _ E0 Rc Pw D i rc px q h1 h3
  obtain ⟨mS, mU, _⟩ := ldFmt_mv E Kc E0 Rc Pw
  unfold LdRrD.prog
  refine (LdProg.fmt_snoc _ _ _ _).2
    ⟨D.s3v.fmt i (fun x => rc x.1) (fun w => px w.1.1) (D.S.qSum D.N q D.t),
      (LdProg.fmt_snoc _ _ _ _).2
        ⟨D.s3.fmt i (fun x => rc x.1) (fun w => px w.1) (D.S.qSum D.N q D.t),
          (LdProg.fmt_snoc _ _ _ _).2
            ⟨D.s2.fmt i rc px (D.S.qSum D.N q D.t),
              (LdProg.fmt_snoc _ _ _ _).2
                ⟨D.s1.fmt i rc (fun w => px w.1) q,
                  (LdProg.fmt_snoc _ _ _ _).2
                    ⟨D.s0.fmt i rc px q, (LdProg.fmt_nil _ _ _).2 rfl, ?_⟩,
                  ?_⟩,
              ?_⟩,
          ?_⟩,
      ?_⟩
  · refine ldFmt_step E Kc E0 Rc Pw _ _ _ _ _ _ _ _ (ExtMap.Moves.id _)
      (fun x x' e => by cases e; rfl) (fun _ => rfl) ?_
    intro U V hV hU
    have e : V = U :=
      Finset.ext fun x =>
        (hV x).trans ⟨fun ⟨u, hu, hx⟩ => (Finset.mem_singleton.1 hx) ▸ hu,
          fun hx => ⟨x, hx, Finset.mem_singleton.2 rfl⟩⟩
    rw [e]
    exact hU
  · refine mS _ _ _ _
      (ldFmt_send E Kc E0 Rc Pw D.s1 D.d1 i rc (fun w => px w.1) px q h1 fun w => ?_)
    obtain ⟨m, hm⟩ := D.d1.rest_snd h1.sender w
    exact congrArg (fun v : Wp × D.p.Rds E => px v.1) hm
  · exact mU _ _ _ _ _
      ((Chain.fmt_one _ _ _).2
        (ldFmt_copies E Kc E0 Rc Pw D.s2 _ _ (rngOut D.p D.r D.A₁) (rngDraw D.p D.St E₀)
          (rngDrawH D.p D.r D.A₁) (fun _ _ _ w => w.1) (rngDrawN D.p D.r) i rc (fun x => rc x.1) px
          (fun w => px w.1) _ (OnlyCopies.draw _ _ _) (fun _ _ => trivial)
          (fun x y τ x' e => by cases e; rfl) fun _ _ _ _ _ => rfl))
  · exact ldFmt_keep E Kc E0 Rc Pw (D.S.sum D.N) _ _ _ _ E₀ D.s3.A D.s3v.A _ _ _ i
      (fun x => rc x.1) (fun x => rc x.1) (fun w => px w.1) (fun w => px w.1.1) _
      (fun x x' e => by cases e; rfl) fun _ => rfl
  · refine mS _ _ _ _
      (ldFmt_send E Kc E0 Rc Pw D.s3v D.d3 i (fun x => rc x.1)
        (fun w => px w.1.1) px _ h3 fun w => ?_)
    obtain ⟨m, hm⟩ := D.d3.rest_snd h3.sender w
    exact congrArg (fun v : (Wp × D.p.Dg E) × D.V => px v.1.1) hm

theorem ldSegRef_dg_fmt : Spec.ldSegRef_dg_fmt := by
  intro E Kc E₀ Wp _ _ E0 Rc Pw Q mult ent n lk i rc px q hl
  obtain ⟨_, mU, _⟩ := ldFmt_mv E Kc E0 Rc Pw
  unfold LdDgP.prog LdDgP.pre
  refine (LdProg.fmt_snoc _ _ _ _).2
    ⟨(Q.lkS mult).fmt i (fun x => rc x.1) px q,
      (LdProg.fmt_snoc _ _ _ _).2
        ⟨Q.u1.fmt i (fun x => rc x.1) px q,
          (LdProg.fmt_snoc _ _ _ _).2
            ⟨Q.u0.fmt i rc px q,
              (LdProg.fmt_snoc _ _ _ _).2 ⟨Q.D.s4.fmt i rc px q, (LdProg.fmt_nil _ _ _).2 rfl, ?_⟩,
              ?_⟩,
          ?_⟩,
      mU _ _ _ _ _ hl⟩
  · exact ldFmt_keep E Kc E0 Rc Pw Q.T _ _ _ _ E₀ Q.D.s4.A Q.u0.A _ _ _ i rc rc px px q
      (fun x x' e => by cases e; rfl) fun _ => rfl
  · exact mU _ _ _ _ _
      ((Chain.fmt_one _ _ _).2
        (ldFmt_copies E Kc E0 Rc Pw Q.u0 _ _ (Q.sh.jOut Q.R0) _ _ _ _ i rc (fun x => rc x.1)
          px px q (OnlyCopies.draw _ _ _) (fun _ _ => trivial)
          (fun x y τ x' e => by cases e; rfl) fun _ _ _ _ _ => rfl))
  · exact ldFmt_keep E Kc E0 Rc Pw Q.T _ _ _ _ E₀ Q.u1.A (Q.lkS mult).A _ _ _ i (fun x => rc x.1)
      (fun x => rc x.1) px px q (fun x x' e => by cases e; rfl) fun _ => rfl

theorem ldSegRef_asm_fmt : Spec.ldSegRef_asm_fmt := by
  intro E Kc E₀ Wp _ _ E0 Rc Pw X i rc px q
  have hp := ldLkpAsm2N_plain E X.A X.Q.Nn X.ι E₀ X.Q.T.Msg Wp Kc X.Q.T.ents
  exact (Chain.fmt_one _ _ _).2
    { idx := IdxLink.of_step (lift_idxStep X.Q.T hp) i
      pass := ((passes_map (X.A.passN E X.Q.Nn X.ι E₀ X.Q.T.Msg Wp Kc X.Q.T.ents)
          fun x : X.Q.X₄ × E => rc x.1).keepX
        X.Q.T.Smp).keepE X.Q.T.ext
      hands := lift_hands X.Q.T hp _ fun w => px w.2
      bears := lift_bears X.Q.T hp q }

theorem ldSegRef_ga_fmt : Spec.ldSegRef_ga_fmt := by
  intro E Kc E₀ Wp _ _ E0 Rc Pw G St₀ g₀ Ar i rc r₀ px q hr
  refine ldFmt_keep E Kc E0 Rc Pw G.Q.T _ _ _ _ E₀ (G.Q.lkT G.ent G.n).A (G.tgt St₀ Ar).A _ _ _ i
    (fun x => rc x.1.1.1) (fun x => r₀ x.2) px px q (fun x x' e => ?_) fun _ => rfl
  by_cases hl : x.1.2.2.length = G.n
  · rw [if_pos hl] at e
    cases e
    exact hr _
  · rw [if_neg hl] at e
    cases e

theorem ldSegRef_tn_fmt : Spec.ldSegRef_tn_fmt := by
  intro E Kc _ _ E0 Rc Pw X St₁ fz Az i r r₁ px q hr
  obtain ⟨_, mU, _⟩ := ldFmt_mv E Kc E0 Rc Pw
  unfold LdTenD.prog
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
      ((Chain.fmt_one _ _ _).2 (ldOREFmt_link E Kc E0 Rc Pw X i (fun x => r x.2) px q))
  · exact ldFmt_keep E Kc E0 Rc Pw X.S _ _ _ _ X.C.E0 X.m1.A (X.tgt St₁ Az).A _ _ _ i
      (fun z => r (X.stOf z).2) (fun x => r₁ x.2) px px q
      (fun x x' e => by cases e; exact hr _) fun _ => rfl

theorem ldSegRef_body_fmt : Spec.ldSegRef_body_fmt := by
  intro E Kc E₀ Wp _ _ E0 Rc Pw Y z tensor i rc r₀ px q φ ψ h1 h3 hr hf hl ht
  unfold LdBodyD.body
  refine ldProg_app_fmt E Kc E0 Rc Pw _ _ _ _ _ _ _ _
    ((LdProg.fmt_snoc _ _ _ _).2
      ⟨_, ldProg_app_fmt E Kc E0 Rc Pw _ _ _ _ _ _ _ _
          (ldProg_app_fmt E Kc E0 Rc Pw _ _ _ _ _ _ _ _ hf
            (ldSegRef_rr_fmt E Kc E₀ Wp E0 Rc Pw Y.G.Q.D i rc px q h1 h3))
          (ldSegRef_dg_fmt E Kc E₀ Wp E0 Rc Pw Y.G.Q Y.mult Y.G.ent Y.G.n Y.lk i
            (fun x => rc x.1) px _ hl),
        ldSegRef_ga_fmt E Kc E₀ Wp E0 Rc Pw Y.G Y.St₀ Y.g₀ Y.Ar i rc r₀ px _ hr⟩) ht

theorem ldSegRefAll_fmt :
    Spec.ldSegRefAll_fmt := fun E Kc _ _ _ _ E0 Rc Pw _ A i ρ px q St₁ fz Az r₁ h hρ hr =>
  ldSegRef_body_fmt E Kc _ _ E0 Rc Pw A.Y (A.X.tgt St₁ Az) (A.X.prog St₁ fz Az) i ρ.rz
    (fun x => ρ.rT x.2) px q _ _ h.send1 h.send3 hρ.gT
    (ldSegFrontFmt E Kc E0 Rc Pw A.Xa.Q.D.s0 A.V i ρ.rcV ρ.r0 ρ.r ρ.rz px q
      h.front.back hρ.e hρ.g0 hρ.g hρ.gz)
    (ldSegRef_asm_fmt E Kc _ _ E0 Rc Pw A.Xa i (fun x => ρ.rz x.1) px _)
    (ldSegRef_tn_fmt E Kc E0 Rc Pw A.X St₁ fz Az i ρ.rT r₁ px _ hr)

end Cb
