-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/Law/WtFwdAtHead.lean: THE KIND K1's SHARES AT THE ITEMS "forms m
piece run", AT THE 25 READS' MEMBERS, AT ProofFile's lettersHead: THE PREMISE WtFwdS OF exchangeAtS_forms
(Honest/K1/Law/FormsShare.lean: "weights" goes forward), PAID UNDER THE LIBRARY's HEAD ALONE. Two
theorems; no definition.

THIS LETTER IS FOR THE HONEST RUN's OWN FORMS ALONE: NO STATEMENT ON ANY OTHER PARTY MAY TAKE IT.
NEVER ON SOUNDNESS's ROAD. (A fence. WHY IT BINDS HERE:
both laws stand at "honest" (Honest/Thread/First.lean) of the library's meaning: the first TAKES
K1.InAt at it, the second calls wt_fwd_reads at it, with the promise in front from the thread's
invariant by our bridge inAt_head, Honest/K1/Law/InAtOfThr.lean.)

  - heard_honest_342   UNDER h (A HYPOTHESIS): in front of number 342, under the promise InAt AT
                  THE MEANING ADAPTED TO THE HONEST SIDE, the head's reader answers: the sealed
                  hheard_342 (Johnson/Desc/K1/Law/HeardAtSendings.lean), WHICH IS GENERAL IN THE
                  MEANING and asks of it one public item's Bool, which "honest" keeps; its three
                  other premises as the sealed hheard_paid (HeardPaid.lean) pays them from the
                  scope.
  - wtFwdS_head   UNDER h, l < 25: WtFwdS at lettersHead, at the member number K1.noL l false, the
                  segment l, at the library's own letter h.𝔇.wt: wt_fwd_reads
                  (Honest/K1/Law/WtFwdReads.lean) with the sealed hidle_atAll, hmono_atAll
                  (Johnson/Desc/Kinds/Law/WtK6Mono.lean) and hquiet_in_scope; the yes by
                  yesOf_reads_head (YesAtFifty.lean). exchangeAtS_forms asks it at the run
                  "weights" alone: at l = 24; off 24 the sentence says nothing (hidle).

WHAT IT READS OF A WITNESS: the witness v stands under "for all", in the premise and in the end, at
the one letter h.𝔇.wt. It is handed the tables as sent, whole (Env.strs): more than the positions
that a verifier reads (the sentence at WtFwdS).

Limits. IT PAYS A PREMISE's FORM, NOT A SHARE. ThrS and Stepped stand in WtFwdS as hypotheses: no
law says that the thread holds at any run. THE FULL SIZE, THE FORMAT's EARLIER HASH. Nothing on any
property.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.K1.Law.FormsShare
import Johnson.Desc.ProofFile.Honest.K1.Law.WtFwdReads
import Johnson.Desc.ProofFile.Honest.K1.Law.InAtOfThr
import Johnson.Desc.ProofFile.Honest.K1.Law.YesAtFifty
import Johnson.Desc.K1.Law.HeardPaid
import Johnson.Desc.K1.Law.QuietInScope
import Johnson.Desc.K1.Law.LinksQuietAtAll
import Johnson.Desc.Kinds.Law.WtK6Mono

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open VerifiableInference.Desc
open VerifiableInference.Desc (Block Chain Strs Place)
open VerifiableInference.Desc.First (flatPlacesOf)
open VerifiableInference.Desc.Sound (MsgT uBySort linksFull mgAll mgBase)
open VerifiableInference.OnPublicFiles (headLink)
open VerifiableInference.Desc.K9 (statesOfLink readersOfLink holesAt)
open VerifiableInference.Desc.Kinds.Head (seatAt)
open VerifiableInference.Desc.Kinds.Head.Law (k6Silent p8K6)
open VerifiableInference.Desc.Kinds.Head.Law.AtTable (hidle_atAll hmono_atAll)
open ProofFile.Honest.FirstThread
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

/-- **IN FRONT OF 342 THE HEAD's READER ANSWERS**, under the promise at the honest side's meaning.
-/
theorem heard_honest_342 (ans : Nat → Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) :
    ∀ a y, K1.InAt h.𝔇.N (honest (mgAll h.𝔇 mgBase) ans test) linksFull
        (flatPlacesOf linksFull true) (K1.noL 24 false) a y →
      ∃ Hh, (seatAt (P5J.At.X Zp).hS (Kinds.Head.Law.readsOf (P5J.At.X Zp))).heard a.2 =
        some Hh := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨lk, _, _, _, eL, -⟩ := IM.k6_of h.scope h.reads O
  have hX : headLink (P5J.At.X Zp) = 24 := by
    have e := K1.headLink_open h.scope h.reads O
    rw [O.W] at e
    exact e
  have hreaders : h.𝔇.Rd 24 = readersOfLink
      ⟨(holesAt (P5J.At.X Zp) 24 24 lk).small,
        k6Silent (p8K6 (P5J.At.X Zp) 24) (statesOfLink lk)⟩ lk := by
    rw [K1.rd24 h.𝔇 hX lk ((K1.hlk_atAll h 24 (by decide)).trans eL), ← K1.silent24 lk]
  have hown : h.𝔇.runs 24 4 "own" = [(3, "norm"), (3, "policy"), (3, "logits")] :=
    K1.own_runs_24
  have K := K1.k6States_seated h.scope h.reads O lk eL
  rw [O.W] at K
  exact K1.hheard_342 h.𝔇 mgBase hreaders hown K h.𝔇.N _ (fun _ => rfl)

/-- **WtFwdS AT lettersHead, UNDER THE HEAD ALONE.** -/
theorem wtFwdS_head (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop) {l : ℕ}
    (hl : l < 25) :
    WtFwdS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w) Said
      ⟨h.𝔇.pubD, h.𝔇.ms, h.𝔇.St, uBySort h.𝔇.uL h.𝔇.uA h.𝔇.uH, h.𝔇.after, h.𝔇.wt, h.𝔇.rw⟩
      (K1.noL l false) l := by
  intro blk hblk k s μ E ds y cols s' hT _ hS v hw
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have hb : cF.blocksInOrder[K1.noL l false]? = some blk := hblk
  obtain ⟨X', arrs, hX, hY⟩ :=
    yesOf_reads_head h O hl hb (yes_of_stepped _ hS) μ.st.input.x.pub
  have hw' : h.𝔇.wt l (μ.st.input.x.pub, s)
      ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.strs E) v := hw
  show h.𝔇.wt l (μ.st.input.x.pub, s')
    ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.strs (E.add y.1)) v
  exact wt_fwd_reads h.𝔇.N
    (honest (mgAll h.𝔇 mgBase) (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).ans test)
    h.𝔇.wt (P5J.At.X Zp) (hidle_atAll h) (hmono_atAll h)
    (heard_honest_342 h test _) (K1.hquiet_in_scope h.scope h.reads O) l hl X' arrs hX
    (μ.st.input.x.pub, s) (μ.st.input.x.pub, s')
    ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.strs E)
    ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.strs (E.add y.1)) v hY
    (inAt_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said hT _) hw'

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.heard_honest_342
#print axioms ProofFile.Honest.K1.wtFwdS_head
