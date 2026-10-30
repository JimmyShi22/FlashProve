-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/- Johnson/LPFE1R/HrunAt347.lean: THE PREMISE hrun OF hitems AT THE HEAD's LINK (
Link/Law/HitemsHead.lean: hitems_head; LPFE1R/HitemsAtConst.lean: hitems_head_at): "AT EVERY STATE
OF THE CONDITION IN FRONT OF THE HEAD's BATCHING THE RUN's OWN READER ANSWERS AT EACH OF SIX
ENTRIES": AT THE CLOSED CONSTANT, FROM THE HEAD ALONE. Statements and proofs.

THE ROAD. At the head's link the readers have two arms: the run's own reader; where that is silent,
the same reader at the state with the reads' tables laid in thought (k6Silent). The table's promise
says that the readers answer (LPFE1R/HinAtConst.lean: hin_at, with reader_of_formsIn).
Where the tables that lie in the state are those that the second arm would lay, the two arms ask one
reader at one state (speaks_of_forms, Top/H0/MergeLaw/SpeaksOfTables.lean).
K11's files have "the tables lie" (TablesLaid) at border 346, in front of the merge
(K11R/TablesAt346.lean). The merge's accepting step turns neither the tables that lie nor what
tablesAt reads.

  tablesLaid_merge  a yes of the merge's decision keeps TablesLaid
  tablesLaid_347    so TablesLaid holds at every state reached at border 347: in scope, at an
                    opening
  hrun_at           (h : AtMgA secondHashFunction …) z (hlk : h.𝔇.lk 24 = some L) : ∀ a, on0At h z 24 a → ∀ e
                    ∈ sortItems .head, e ∈ ‹the six› → (K9.readerOf (K9.statesOfLink L) e.1 e.2
                    a.1).isSome = true: hitems_head_at's premise, to the letter

Limits. The head AtMgA is a premise: a member of it is proved at storedPublicFiles and zGap alone (at secondHashFunction;
side library AtFullSide/Top/). The full size alone. Evaluated beside
(no theorem): at the honest state at 347 all six answer, at both sizes. No soundness statement.

-/
import Johnson.LPFE1R.HitemsAtConst
import Johnson.K11R.TablesAt346
import Johnson.Top.H0.MergeLaw.SpeaksOfTables

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Maker OnBytes.Slice
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.MergeLaw (TablesLaid speaks_of_forms speaksAt)
open Johnson.Desc.First.ForkMerge (HeadMergeP headMergeDecide)
open Johnson.Desc.First.Walk.Tied (Reach)
open ProofFile (Cl)

/-- **A yes of the merge's decision keeps "the tables lie".** -/
theorem tablesLaid_merge {Q : K8.ReadsQuiet.PH} {P : HeadMergeP} {s s' : S} {rs : List Fmt.RoundView}
    (h : headMergeDecide P s rs = .ok s') (ht : TablesLaid Q s) : TablesLaid Q s' := by
  unfold headMergeDecide at h
  split at h
  · rename_i a ha
    obtain ⟨_, _, h⟩ := K9L.ok_bind h
    obtain ⟨_, _, h⟩ := K9L.ok_bind h
    obtain ⟨t, _, h⟩ := K9L.ok_bind h
    obtain ⟨claim, _, h⟩ := K9L.ok_bind h
    obtain ⟨x, _, h⟩ := K9L.ok_bind h
    obtain ⟨⟨wo, F, t'⟩, _, h⟩ := K9L.ok_bind h
    dsimp only at h
    obtain ⟨_, _, h⟩ := K9L.ok_bind h
    obtain ⟨_, _, h⟩ := K9L.ok_bind h
    obtain rfl := Except.ok.inj h
    intro o tb ho htb
    obtain rfl := First.Here.head.inj ho
    have h0 : Kinds.Head.Law.tablesAt Q s = some tb := by
      unfold Kinds.Head.Law.tablesAt at htb ⊢
      rw [ha]
      exact htb
    exact ht a tb ha h0
  · exact nomatch h

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **The tables lie at every state reached at the head's batching's number.** -/
theorem tablesLaid_347 (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {a : ProofFile.InstPub × S}
    (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) 347 a) : TablesLaid (K9.phAt Bs.G₀.W 24) a.2 := by
  have h' : Reach 0 c.blocksInOrder (ProofFile.startS Z) (346 + 1) a := h
  cases h' with
  | @succ _ z s s' b0 hr hb hy =>
    obtain ⟨R, cs, _, e⟩ := hy
    have hd := ((step_ok_iff 0 b0 s s' R cs cs.length).1 e).2.2.2
    obtain ⟨Lk, b, e1, e2, hla, _⟩ := IM.k11_of hS hR O
    have h3 := IM.hear_at_flat e1 e2
    rw [IM.flatIx_scope hS hR O (by decide) 8] at h3
    obtain rfl : b = b0 := Option.some.inj (h3.symm.trans hb)
    exact tablesLaid_merge ((IM.k11_yes hla _ _ _ _).1 hd).1 (K11.tablesLaid_346 hS hR O (z, s) hr)

end

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain P5J.TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **hrun, AT THE CLOSED CONSTANT.** -/
theorem hrun_at (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (z : ProofFile.InstPub)
    {L : Link S Claim} (hlk : h.𝔇.lk 24 = some L) :
    ∀ a, on0At h z 24 a → ∀ e ∈ sortItems .head, e ∈ [(2, "guests"), (3, "norm"),
      (3, "policy"), (3, "logits"), (7, "guests"), (8, "the merge")] →
      (K9.readerOf (K9.statesOfLink L) e.1 e.2 a.1).isSome = true := by
  intro a ha e he h6
  have h8 : (e.2 == "K8.equations") = false := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h6
    rcases h6 with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have hs : IM.subAt 24 = .head := by decide
  have hin := hin_at h (m := 24) (by omega) z _ a ha (hs ▸ he) h8
  obtain ⟨R, hR⟩ := reader_of_formsIn _ _ _ _ _ hin
  rw [readers_at24 h 24, K9.readersAt_some _ _ _ _ L hlk] at hR
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have hr := P5J.list_rchIs h z _ _ ha.2
  have hb : batchAt P5J.fullLinks P5J.At.ps 24 = 347 := by
    rw [LPFK9.batchAt_full 24 (by omega)]
    decide
  rw [hb] at hr
  have ht := tablesLaid_347 h.scope h.reads O hr
  rw [O.W] at ht
  have hsp := speaks_of_forms (K9.holesAt (P5J.At.X Zp) 24 24 L) L (K9.phAt (P5J.At.X Zp) 24) e.1
    h8 (by unfold K9.holesAt; rfl) ht (by rw [hR]; rfl)
  exact hsp

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.tablesLaid_merge
#print axioms VerifiableInference.Desc.LinkJoin.tablesLaid_347
#print axioms VerifiableInference.Desc.LinkJoin.hrun_at
