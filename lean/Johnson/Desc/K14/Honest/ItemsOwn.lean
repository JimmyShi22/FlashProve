-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Honest/ItemsOwn.lean: claims on an honest prover's tables behind the sub-protocols
of the linear claim's shared rounds, said AT THE STATE's OWN STATEMENT.

The library's forms for constraints and sample constraints (RowsUL, SmpSay:
Johnson/Desc/K14/Law/LedgerOne.lean) say "at some statement that has grown out of the state's": so
they go backwards along a run, as soundness reads it, and not forwards. An honest side's
sentences go forwards. So here the same claims are said at the state's own statement (RowsU;
SmpOwn). Each gives the library's form (rowsUL_of_own; SmpOwn.say).

Main names:
  SmpOwn, SmpOwn.say  a message's sample constraints hold, at the state's own statement
  SmpOwn.quiet, SmpOwn.zeta   **it goes forwards** over a step that leaves the messages (QuietStep),
                      and over "LIN zeta"
  Public8.sampleOwn2, sampleOwn5, recGOwn3, locOwn4   behind the two sendings, "(rec_gamma)" and
                      "LOC": with the premises of their namesakes in
                      Johnson/Desc/K14/Honest/ItemsHold.lean
  Steps.sampleOwn2, recGOwn3, locOwn4, sampleOwn5, Steps.order1, …, order8   the same, and the
                      statement's order, from a run of steps
                      (Johnson/Desc/K14/Honest/StepsBack.lean)

What is not claimed. What the namesakes do not claim. That a sample constraint goes forwards over a
sending. Nothing on soundness or on hiding. This is not completeness of the protocol or of a
program.

-/
import Johnson.Desc.K14.Honest.StepsTwins
import Johnson.Desc.K14.Honest.OrderNext

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Honest
open OnBytes OnBytes.Params Desc.Plain
open OnBytes.Means (Words InOrder)
open OnBytes.Slice (rdE)
open VerifiableInference.Desc (Grows)
open Desc.K14.Law (rowsOn parK1_sent parO RowsU SmpSay QuietStep on4_of_seatedUB
  onward_laysRec onward_loc laysLocW linZeta_inv)

/-- **A message's sample constraints hold, at the state's own statement**: the message number o is
there, and each of its sample constraints, as the state holds them, holds of the words. -/
def SmpOwn (o : Nat) (s : St) (m : Words Cb.Gl.E) : Prop :=
  ∃ x, s.st.oracles[o]? = some x ∧ Means.AllSay rdE s.st x.sampleRows.toList m

/-- It gives the library's form. -/
theorem SmpOwn.say {o : Nat} {s : St} {m : Words Cb.Gl.E} (h : SmpOwn o s m) : SmpSay o s m := by
  obtain ⟨x, hx, hs⟩ := h
  exact ⟨x, s.st, hx, Grows.refl _, hs⟩

/-- **It goes forwards over a step that leaves the messages.** -/
theorem SmpOwn.quiet {o : Nat} {a b : St} {m : Words Cb.Gl.E} (q : QuietStep a b)
    (h : SmpOwn o a m) : SmpOwn o b m := by
  obtain ⟨x, hx, hs⟩ := h
  have e := q.msgs.2 o
  rw [hx] at e
  obtain ⟨y, hy, e'⟩ := Option.map_eq_some_iff.1 e
  have e3 : y.sampleRows = x.sampleRows := (Prod.mk.inj (Prod.mk.inj e').2).2
  refine ⟨y, hy, fun r hr => ?_⟩
  rw [e3] at hr
  refine (Means.says_of_shapes rdE q.msgs.1 (fun j => ?_) r m).2 (hs r hr)
  have ej := congrArg (Option.map Prod.fst) (q.msgs.2 j)
  simpa [Option.map_map, Function.comp_def] using ej

/-- It goes forwards over "LIN zeta", which leaves the statement. -/
theorem SmpOwn.zeta {o : Nat} {a b : St} {r : Fmt.RoundView} {m : Words Cb.Gl.E}
    (k : linZeta a [r] = some b) (h : SmpOwn o a m) : SmpOwn o b m := by
  rw [linZeta_inv a b r k]
  exact h

variable {P : P14} {sentU : Array OracleNotice} {layO : TreeLay} {d0 : St} {V : View8}
  {D : States8} {H : Inputs}

/-- **Behind the sending of o_u its sample constraints hold of the honest words, at the state's own
statement**, where the OOD answers that this sending shows are the honest ones. -/
theorem Public8.sampleOwn2 (S : Public8 P sentU layO d0) (u : To2 P sentU d0 V D)
    (hU : ShownU P sentU d0 V D H) :
    SmpOwn d0.st.oracles.size D.d2 (words2 P sentU d0 V.r1 H) := by
  obtain ⟨⟨_, hsz, _⟩, _⟩ := sends_of S.facts d0.st.oracles.size
  obtain ⟨y, hy, hs⟩ := smp_new u.s2 H.w₀ (rowsU P d0 V.r1 H) hU 0 hsz (by omega)
  rw [(S.at1 u.front).size] at hy hs
  refine ⟨y, hy, fun r hr => ?_⟩
  exact (Means.says_of_words rdE D.d2.st r fun o ho part i =>
    words2_old P sentU d0 V.r1 H o (by rw [(S.at2 u).size] at ho; exact ho) part i).1 (hs r hr)

/-- **Behind the second sending o_omega's and o_sp's sample constraints hold of the honest words, at
the state's own statement**, where the OOD answers that this sending shows are the honest ones. -/
theorem Public8.sampleOwn5 (S : Public8 P sentU layO d0) (u : To5 P sentU d0 V D)
    (hO : ShownO P sentU d0 V D H) :
    SmpOwn (d0.st.oracles.size + 2) D.d5 (words2 P sentU d0 V.r1 H) ∧
      SmpOwn (d0.st.oracles.size + 3) D.d5 (words2 P sentU d0 V.r1 H) := by
  obtain ⟨w2, _, _⟩ := withOmega_two S.facts.two
  have sO : (parO P).sent.size = 2 := (congrArg Array.size (parK1_sent P 5 _ _)).trans w2
  obtain ⟨y, hy, hs⟩ := smp_new u.s5 (words1 P sentU d0 V.r1 H) (rowsO P d0 V.r1 H) hO 0
    (by rw [sO]; omega) (by omega)
  obtain ⟨z, hz, ht⟩ := smp_new u.s5 (words1 P sentU d0 V.r1 H) (rowsO P d0 V.r1 H) hO 1
    (by rw [sO]; omega) (by omega)
  rw [(S.at4 u.front).size] at hy hs hz ht
  exact ⟨⟨y, hy, hs⟩, ⟨z, hz, ht⟩⟩

/-- **Behind "(rec_gamma)" the constraints on o_u's group hold of the honest words, at the state's
own statement** (RowsU). -/
theorem Public8.recGOwn3 (S : Public8 P sentU layO d0) (u : To3 P sentU d0 V D)
    (hA : OwnAnswers P d0.loc.key H) :
    RowsU rdE 0 P.par.S.fold.index.answers D.d3 (words2 P sentU d0 V.r1 H) := by
  have A := S.at2 u.front
  obtain ⟨hi, hP2⟩ := on4_of_seatedUB P.par D.d2 (A.stands S.facts)
  obtain ⟨ho, hl⟩ := onward_laysRec P.par D.d2 D.d3 V.rs3 u.k3
  have h0 : rowsOn D.d2 D.d2.loc.gU = [] :=
    List.eq_nil_of_length_eq_zero (S.rows2 u.front (S.keyFits_of u))
  have k := rec_hold rdE P.par D.d2 D.d3 V.rs3 D.d3.st (words2 P sentU d0 V.r1 H) H.Rw u.k3 hi
    (hP2 _ ho.grows) (fold_at S.facts d0 V.r1 H A.notes) (by rw [A.carried.key]; exact hA)
    (by rw [h0]; intro r hr; cases hr)
  rw [← hl] at k
  exact stretch_say k _ _

/-- **Behind "LOC" the constraints that it has laid hold of the honest words, at the state's own
statement** (RowsU). -/
theorem Public8.locOwn4 (S : Public8 P sentU layO d0) (u : To4 P sentU d0 V D)
    (hC : OwnColumns P V H) :
    RowsU rdE P.par.S.fold.index.answers P.par.S.fold.columns D.d4
      (words2 P sentU d0 V.r1 H) := by
  have A := S.at3 u.front
  obtain ⟨hi, hP3⟩ := on4_of_seatedUB P.par D.d3 (A.stands S.facts)
  obtain ⟨ho, hl⟩ := onward_loc P.par D.d3 D.d4 V.r4 V.cols u.k4
  obtain ⟨_, rows, hrows, _, hU, _⟩ := laysLocW P.par D.d3 D.d4 V.r4 V.cols u.k4
  have hs := loc_say rdE P.par D.d3 V.r4 V.cols D.d4.st (words2 P sentU d0 V.r1 H) H.Rw rows hrows
    hi (hP3 _ ho.grows) (fold_at S.facts d0 V.r1 H A.notes)
    (weights_size P.par D.d3 A.carried.psi) hC
  intro r hr
  rw [hl, hU, List.drop_left' (S.rows3 u.front)] at hr
  exact hs r (List.mem_of_mem_take hr)

/-! ## The same, and the statement's order, from a run of steps -/

variable {B : Eight P} {ft : Nat} {W : Seen8}

/-- Behind "LIN point" the statement is in order, if the first one is: from
the steps up to there. -/
theorem Steps.order1 (S : Public8 P sentU layO d0) (u : StepTo1 B ft d0 W D)
    (h0 : InOrder d0.st) : InOrder D.d1.st :=
  S.order1 (S.to1 u) h0

/-- Behind the sending of o_u the statement is in order, if the first one is: from
the steps up to there. -/
theorem Steps.order2 (S : Public8 P sentU layO d0) (u : StepTo2 B ft d0 W D)
    (h0 : InOrder d0.st) : InOrder D.d2.st := by
  obtain ⟨x, ids, t⟩ := S.to2 u
  have k := S.order2 t h0
  exact k

/-- Behind "(rec_gamma)" the statement is in order, if the first one is: from
the steps up to there. -/
theorem Steps.order3 (S : Public8 P sentU layO d0) (u : StepTo3 B ft d0 W D)
    (h0 : InOrder d0.st) : InOrder D.d3.st := by
  obtain ⟨x, ids, t⟩ := S.to3 u
  have k := S.order3 t h0
  exact k

/-- Behind "LOC" the statement is in order, if the first one is: from
the steps up to there. -/
theorem Steps.order4 (S : Public8 P sentU layO d0) (u : StepTo4 B ft d0 W D)
    (h0 : InOrder d0.st) : InOrder D.d4.st := by
  obtain ⟨x, ids, t⟩ := S.to4 u
  have k := S.order4 t h0
  exact k

/-- Behind the sending of o_omega and o_sp the statement is in order, if the first one is: from the
steps up to there. -/
theorem Steps.order5 (S : Public8 P sentU layO d0) (u : StepTo5 B ft d0 W D)
    (h0 : InOrder d0.st) : InOrder D.d5.st := by
  obtain ⟨x, ids, x', ids', t⟩ := S.to5 u
  have k := S.order5 t h0
  exact k

/-- Behind the joinings the statement is in order, if the first one is: from
the steps up to there. -/
theorem Steps.order6 (S : Public8 P sentU layO d0) (u : StepTo6 B ft d0 W D)
    (h0 : InOrder d0.st) : InOrder D.d6.st := by
  obtain ⟨x, ids, x', ids', t⟩ := S.to6 u
  have k := S.order6 t h0
  exact k

/-- Behind "LIN zeta" the statement is in order, if the first one is: from
the steps up to there. -/
theorem Steps.order7 (S : Public8 P sentU layO d0) (u : StepTo7 B ft d0 W D)
    (h0 : InOrder d0.st) : InOrder D.d7.st := by
  obtain ⟨x, ids, x', ids', t⟩ := S.to7 u
  have k := S.order7 t h0
  exact k

/-- Behind "SPLIT" the statement is in order, if the first one is: from
the steps up to there. -/
theorem Steps.order8 (S : Public8 P sentU layO d0) (u : StepTo8 B ft d0 W D)
    (h0 : InOrder d0.st) : InOrder D.d8.st := by
  obtain ⟨x, ids, x', ids', t⟩ := S.to8 u
  have k := S.order8 t h0
  exact k

/-- Behind the sending of o_u: its sample constraints, from the steps up to there. -/
theorem Steps.sampleOwn2 (S : Public8 P sentU layO d0) (u : StepTo2 B ft d0 W D)
    (hU : ShownU P sentU d0 W.view D H) :
    SmpOwn d0.st.oracles.size D.d2 (words2 P sentU d0 W.view.r1 H) := by
  obtain ⟨x, ids, t⟩ := S.to2 u
  have k := S.sampleOwn2 t (H := H) hU
  exact k

/-- Behind "(rec_gamma)": the constraints on o_u's group, from the steps up to there. -/
theorem Steps.recGOwn3 (S : Public8 P sentU layO d0) (u : StepTo3 B ft d0 W D)
    (hA : OwnAnswers P d0.loc.key H) :
    RowsU rdE 0 P.par.S.fold.index.answers D.d3 (words2 P sentU d0 W.view.r1 H) := by
  obtain ⟨x, ids, t⟩ := S.to3 u
  have k := S.recGOwn3 t hA
  exact k

/-- Behind "LOC": the constraints that it has laid, from the steps up to there. -/
theorem Steps.locOwn4 (S : Public8 P sentU layO d0) (u : StepTo4 B ft d0 W D)
    (hC : OwnColumns P W.view H) :
    RowsU rdE P.par.S.fold.index.answers P.par.S.fold.columns D.d4
      (words2 P sentU d0 W.view.r1 H) := by
  obtain ⟨x, ids, t⟩ := S.to4 u
  have k := S.locOwn4 t hC
  exact k

/-- Behind the second sending: the new sample constraints, from the steps up to there. -/
theorem Steps.sampleOwn5 (S : Public8 P sentU layO d0) (u : StepTo5 B ft d0 W D)
    (hO : ShownO P sentU d0 W.view D H) :
    SmpOwn (d0.st.oracles.size + 2) D.d5 (words2 P sentU d0 W.view.r1 H) ∧
      SmpOwn (d0.st.oracles.size + 3) D.d5 (words2 P sentU d0 W.view.r1 H) := by
  obtain ⟨x, ids, x', ids', t⟩ := S.to5 u
  have k := S.sampleOwn5 t (H := H) hO
  exact k

end Desc.K14.Honest

#print axioms Desc.K14.Honest.SmpOwn.say
#print axioms Desc.K14.Honest.SmpOwn.quiet
#print axioms Desc.K14.Honest.SmpOwn.zeta
#print axioms Desc.K14.Honest.Public8.sampleOwn2
#print axioms Desc.K14.Honest.Public8.sampleOwn5
#print axioms Desc.K14.Honest.Public8.recGOwn3
#print axioms Desc.K14.Honest.Public8.locOwn4
#print axioms Desc.K14.Honest.Steps.order1
#print axioms Desc.K14.Honest.Steps.order2
#print axioms Desc.K14.Honest.Steps.order3
#print axioms Desc.K14.Honest.Steps.order4
#print axioms Desc.K14.Honest.Steps.order5
#print axioms Desc.K14.Honest.Steps.order6
#print axioms Desc.K14.Honest.Steps.order7
#print axioms Desc.K14.Honest.Steps.order8
#print axioms Desc.K14.Honest.Steps.sampleOwn2
#print axioms Desc.K14.Honest.Steps.recGOwn3
#print axioms Desc.K14.Honest.Steps.locOwn4
#print axioms Desc.K14.Honest.Steps.sampleOwn5
