-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Total/CallersPaid.lean: the kind "lookup" (K3): for the item
"totalB" at the batching. Conditional: the reverse of the library's clauses at "planes" and "join"
(Honest/K3/Law/Total/PlanesJoinBack.lean) without the caller's clauses: at the readers and keys with
which the attention's and the head's runs are stated, what the caller's forms are worth follows from
the library's promise Ok at what is fixed and the part there, by the library's own lemmas. Five
theorems: two are a call (`planes_back_att`, `planes_back_head`); the other three have proofs of
five to ten lines.

Terms. Honest/K3/GLOSSARY.md. In this file: an entry o is a pair of a piece's number and a run's
name. `At L o run` (Johnson/Desc/First/Link/Law/LinkJoinPay.lean) says that the link L states the
run at the entry o. What is fixed at a state s is `fixed9 φ s`
(Johnson/Desc/First/Batch/Law/FitsAtS.lean). The link's reader is `K9.readersOfLink H L`
(Johnson/Desc/First/Batch/ReadersOfLink.lean); H holds its holes (`K9.LinkHoles`, there), and the
second hole is the field silent. The table's item at the entry is `formsQ`
(Johnson/Desc/Sound/FormsQ.lean), its public test `K9.formsIn`. The lookups' promise at what is
fixed is `K3Ok` (Johnson/Top/H/Keep/RunsPlain.lean). Ok is a letter: a condition on what is fixed.
"The state goes on from what is fixed" is `Fx9` (FitsAtS.lean).

What is shown.
  `fx_self`: from Ok at what is fixed and the part there: the state goes on from what is fixed.
  `planes_back_fam`: "planes", general in the readers and in two families of forms that are read off
    the fixed part.
  `planes_back_att`: "planes" at an attention segment's readers, `P.readersOfO A`; the values
    `bvAtt A`, `pvAtt A`.
  `planes_back_head`: "planes" at the head's readers, `callerReaders (planesAt iU3)`
    (Johnson/Desc/Kinds/HeadCaller.lean; Johnson/Stored/HeadSeatAt.lean); the values `bvHead iU3`,
    `pvHead iU3`.
  `join_back_att`: "join" at an attention segment's keys, `P.keysOfO A`; the values `kvAtt A`.
The statements are sentences on the verifier's state and the library's terms: no prover, coin or
play is named.

Hypotheses that remain.
  `hn`, `hAt`: the entry's name is not "K8.equations"; the kind's own run stands at the entry.
  `ht`: the table of terms at the entry is `plainTm` of the run's values.
  `hb`, `hOk`: a part is there at s; Ok holds at what is fixed. Whether Ok can be met is not shown
    here.
  `hK`: Ok gives the lookups' promise `K3Ok` at the calls' seat.
  `hQ`: (at an attention segment) Ok gives the attention's promise on what it heard (`K5OkAt`,
    Johnson/Desc/First/Att/Claims/InAt.lean); at the library's `OkAtt`
    (Johnson/Desc/First/Link/Law/OkOne.lean) it is the field k5.
  `hsil`: the readers' second hole says nothing at the entry and the state.
  `hq`: the table's item holds at the entry.
  `rB`, `nB`, `rP`, `nP`: (in `planes_back_fam`) the readers' forms are the two families wherever
    the state goes on from what is fixed; the families name no slot.

How the proof goes. As the library's `item_planes_core` (Johnson/P1K9R/ItemPlanesAt.lean) and
`k3i_join_att_at` (Johnson/P1K9R/ItemJoinAt.lean) show these clauses: Ok at what is fixed and the
part make "the state goes on from what is fixed"; there the caller's forms are families read off the
fixed part, which name no slot; such a form has one worth at whatever ledger.

Limits. All statements are implications. No instance of these hypotheses is exhibited in this file.
Not reached: the entry "join" of the head's segment.
At the head's segment `hsil` cannot be had at the library's own holes (`K9.holesAt`,
Johnson/Desc/First/Batch/ReadersAt.lean) at a state at which the tables can be made and the run
answers: there the second hole is filled (`k6Silent`, Johnson/Desc/Kinds/Law/K6SilentCode.lean: the
run itself at the state with the tables laid), at every name of a run; where the tables cannot be
made at the state, or the run refuses there, that hole says nothing. There the lemma is meant at the
empty hole (`K9.withSmall K9.LinkHoles.none`, Johnson/Desc/First/Batch/SmallReader.lean: `hsil` by
`rfl`), and what it says is carried over to the library's holes by the library's `forms_of_run`
(Johnson/Desc/First/Link/Law/HitemsHead.lean), where the run's own reader answers at the state. That
carrying over is not made here, and that hypothesis of `forms_of_run` is not shown in this file. At
every other segment the library's second hole says nothing outright. This bears on
`planes_back_head`. By a count over the table's text, not by Lean: of
the nine entries of "totalB" at which a link states one of the lookup's runs (six "objects", two
"planes", attention's "join") three are the head's (two "objects", one "planes"): so at the
library's own holes the theorems of Honest/K3/Law/Total/ObjectsBack.lean and
Honest/K3/Law/Total/PlanesJoinBack.lean apply at six of the nine. The nine are written out, by the
link's sort, in the statements of `theta_at_layers`, `theta_at_attention` and `theta_at_head`
(Honest/K3/Law/ThetaKept.lean).
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.P1K9R.ItemPlanesAt
import Johnson.P1K9R.ItemJoinAt
import Johnson.Desc.ProofFile.Honest.K3.Law.Total.PlanesJoinBack

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K3.Law.Total
open OnBytes OnBytes.Model
open VerifiableInference VerifiableInference.Desc
open VerifiableInference.Desc.K9 (atS)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.LinkJoin
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.PhiAll
open VerifiableInference.Desc.EntryUnit (entUnit)
open VerifiableInference.Desc.K3 (seatCalls planesRun)
open VerifiableInference.Desc.Kinds.Head (callerReaders planesAt)
open VerifiableInference.OnPublicFiles (plVals jnVals K3Ok heard_at k03_atS2_calls fits_at bitOf pinOf
        refValQ bvAtt pvAtt kvAtt bvHead pvHead att_read_bits att_read_pin att_read_keys head_read_bits
        head_read_pin noSlots_bits_att noSlots_pin_att noSlots_bits_head noSlots_pin_head)
open K5Law

variable {L : Link S Claim} {u : HTailF2} {Ok : Q BetaAll → Prop} {lmC jC : ℕ}

/-- From Ok at what is fixed and the part there: the state goes on from what is fixed at it. -/
theorem fx_self (s : S) (b : K9.Part) (hb : atS.get? s = some b)
    (hOk : Ok (fixed9 (phiAll u psiAll) s)) :
    (fixed9 (phiAll u psiAll) s).2 = some (pubOf b) ∧
      Fx9 (phiAll u psiAll) Ok (fixed9 (phiAll u psiAll) s) s := by
  have hq2 : (fixed9 (phiAll u psiAll) s).2 = some (pubOf b) := by
    show (atS.get? s).map pubOf = _
    rw [hb]
    rfl
  exact ⟨hq2, hOk, rfl, pubOf b, b, hq2, hb, goesOn_refl b⟩

/-- **"planes" without the caller's clauses**, general in the readers and in two families of forms
off the fixed part. Conditional on what this file's head lists. -/
theorem planes_back_fam (H : K9.LinkHoles) {rr : K3.Readers S} {bQ : ℕ × ℕ → Q BetaAll → Aff}
    {pQ : ℕ → Q BetaAll → Aff}
    (rB : ∀ i q e, Fx9 (phiAll u psiAll) Ok q e → bitOf rr e i.1 i.2 = bQ i q)
    (nB : ∀ i q, (bQ i q).slots = #[])
    (rP : ∀ col q e, Fx9 (phiAll u psiAll) Ok q e → pinOf rr e col = pQ col q)
    (nP : ∀ col q, (pQ col q).slots = #[])
    (tmOf : ℕ × String → ℕ → Q BetaAll → Bound GE8 → List (ℕ × GE8))
    (own : List (ℕ × ℕ)) (rd : ℕ × ℕ → MsgQ) (o : ℕ × String)
    (hn : (o.2 == "K8.equations") = false)
    (hAt : At L o (planesRun (seatCalls K3Lot.ofForm) lmC rr))
    (ht : tmOf o = plainTm (plVals hdCalls lmC jC
      (fun q y k col => refValQ bQ entUnit (k, col) q y) fun q y col => refValQ pQ entUnit col q y))
    (s : S) (b : K9.Part) (hb : atS.get? s = some b) (hOk : Ok (fixed9 (phiAll u psiAll) s))
    (hK : ∀ q, Ok q → K3Ok hdCalls lmC jC q) (hsil : H.silent o.1 o.2 s = none)
    (hq : formsQ (K9.readersOfLink H L) own o.1 o.2 s rd) :
    ∀ n, ∀ c ∈ tmOf o n (fixed9 (phiAll u psiAll) s) (dataQ own b rd), c.2 = 0 := by
  obtain ⟨hq2, hfx⟩ := fx_self (u := u) (Ok := Ok) s b hb hOk
  exact planes_back H L (phiAll u psiAll) hdCalls lmC jC (seatCalls K3Lot.ofForm)
    k03_atS2_calls (fits_at false) (heard_at u false) rr _ _ own rd o hn hAt tmOf ht s b hb
    (hK _ hOk) hsil hq
    (fun G _ k col => by
      rw [rB (k, col) _ s hfx]
      exact caller_at_table bQ (k, col) _ (pubOf b) hq2 (nB _ _) G _)
    (fun G _ col => by
      rw [rP col _ s hfx]
      exact caller_at_table pQ col _ (pubOf b) hq2 (nP _ _) G _)

/-- **"planes" at an attention segment's readers.** The hypothesis `hQ`: Ok gives the attention's
promise on what it heard. Conditional on what this file's head lists. -/
theorem planes_back_att (H : K9.LinkHoles) (A : Attention.Plan)
    (hQ : ∀ q v g' h', Ok q → q.2 = some v → rdAll q.1 = some (g', h') →
      K5OkAt (P.parCOf A) g'.zk h' v.F)
    (tmOf : ℕ × String → ℕ → Q BetaAll → Bound GE8 → List (ℕ × GE8))
    (own : List (ℕ × ℕ)) (rd : ℕ × ℕ → MsgQ) (o : ℕ × String)
    (hn : (o.2 == "K8.equations") = false)
    (hAt : At L o (planesRun (seatCalls K3Lot.ofForm) lmC (P.readersOfO A)))
    (ht : tmOf o = plainTm (plVals hdCalls lmC jC (bvAtt A) (pvAtt A)))
    (s : S) (b : K9.Part) (hb : atS.get? s = some b) (hOk : Ok (fixed9 (phiAll u psiAll) s))
    (hK : ∀ q, Ok q → K3Ok hdCalls lmC jC q) (hsil : H.silent o.1 o.2 s = none)
    (hq : formsQ (K9.readersOfLink H L) own o.1 o.2 s rd) :
    ∀ n, ∀ c ∈ tmOf o n (fixed9 (phiAll u psiAll) s) (dataQ own b rd), c.2 = 0 :=
  planes_back_fam H (att_read_bits (phiAll u psiAll) Ok rdAll A (hrd_all u) hQ)
    (noSlots_bits_att rdAll (P.parCOf A))
    (att_read_pin (phiAll u psiAll) Ok rdAll A (hrd_all u) hQ)
    (noSlots_pin_att rdAll (P.parCOf A)) tmOf own rd o hn hAt ht s b hb hOk hK hsil hq

/-- **"planes" at the head's readers.** Conditional on what this file's head lists. -/
theorem planes_back_head (H : K9.LinkHoles) (iU3 : ℕ)
    (tmOf : ℕ × String → ℕ → Q BetaAll → Bound GE8 → List (ℕ × GE8))
    (own : List (ℕ × ℕ)) (rd : ℕ × ℕ → MsgQ) (o : ℕ × String)
    (hn : (o.2 == "K8.equations") = false)
    (hAt : At L o (planesRun (seatCalls K3Lot.ofForm) lmC (callerReaders (planesAt iU3))))
    (ht : tmOf o = plainTm (plVals hdCalls lmC jC (bvHead iU3) (pvHead iU3)))
    (s : S) (b : K9.Part) (hb : atS.get? s = some b) (hOk : Ok (fixed9 (phiAll u psiAll) s))
    (hK : ∀ q, Ok q → K3Ok hdCalls lmC jC q) (hsil : H.silent o.1 o.2 s = none)
    (hq : formsQ (K9.readersOfLink H L) own o.1 o.2 s rd) :
    ∀ n, ∀ c ∈ tmOf o n (fixed9 (phiAll u psiAll) s) (dataQ own b rd), c.2 = 0 :=
  planes_back_fam H (head_read_bits (phiAll u psiAll) Ok kapAll iU3 (hkap_all u))
    (noSlots_bits_head kapAll iU3)
    (head_read_pin (phiAll u psiAll) Ok kapAll iU3 (hkap_all u))
    (noSlots_pin_head kapAll iU3) tmOf own rd o hn hAt ht s b hb hOk hK hsil hq

/-- **"join" at an attention segment's keys.** The hypothesis `hQ`: Ok gives the attention's promise
on what it heard. Conditional on what this file's head lists. -/
theorem join_back_att (H : K9.LinkHoles) (A : Attention.Plan)
    (hQ : ∀ q v g' h', Ok q → q.2 = some v → rdAll q.1 = some (g', h') →
      K5OkAt (P.parCOf A) g'.zk h' v.F)
    (tmOf : ℕ × String → ℕ → Q BetaAll → Bound GE8 → List (ℕ × GE8))
    (own : List (ℕ × ℕ)) (rd : ℕ × ℕ → MsgQ) (o : ℕ × String)
    (hn : (o.2 == "K8.equations") = false)
    (hAt : At L o (K3.joinRun (seatCalls K3Lot.ofForm) (P.keysOfO A)))
    (ht : tmOf o = plainTm (jnVals hdCalls lmC jC (kvAtt A)))
    (s : S) (b : K9.Part) (hb : atS.get? s = some b) (hOk : Ok (fixed9 (phiAll u psiAll) s))
    (hK : ∀ q, Ok q → K3Ok hdCalls lmC jC q) (hsil : H.silent o.1 o.2 s = none)
    (hq : formsQ (K9.readersOfLink H L) own o.1 o.2 s rd) :
    ∀ n, ∀ c ∈ tmOf o n (fixed9 (phiAll u psiAll) s) (dataQ own b rd), c.2 = 0 := by
  obtain ⟨hq2, hfx⟩ := fx_self (u := u) (Ok := Ok) s b hb hOk
  refine join_back H L (phiAll u psiAll) hdCalls lmC jC (seatCalls K3Lot.ofForm)
    k03_atS2_calls (fits_at false) (heard_at u false) (P.keysOfO A) (kvAtt A) own rd o hn hAt tmOf
    ht s b hb (hK _ hOk) hsil hq fun k => ?_
  rw [att_read_keys (phiAll u psiAll) Ok rdAll A (hrd_all u) hQ k _ s hfx]
  unfold kvAtt refValQ
  rw [hq2]
  rfl

end ProofFile.Honest.K3.Law.Total

#print axioms ProofFile.Honest.K3.Law.Total.fx_self
#print axioms ProofFile.Honest.K3.Law.Total.planes_back_fam
#print axioms ProofFile.Honest.K3.Law.Total.planes_back_att
#print axioms ProofFile.Honest.K3.Law.Total.planes_back_head
#print axioms ProofFile.Honest.K3.Law.Total.join_back_att
