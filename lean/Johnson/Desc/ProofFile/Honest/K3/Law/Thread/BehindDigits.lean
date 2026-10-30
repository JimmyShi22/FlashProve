-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Thread/BehindDigits.lean: the honest side of the kind "lookup"
(K3): THE THREAD'S CLAUSE ON THE FORM, ONE BORDER ON, BEHIND AN ACCEPTANCE BY THE STATED
SUB-PROTOCOL'S OWN STEP, at the sub-protocol of a link's lookup on the digits: `form_digits`
(Honest/K3/Law/Thread/Behind.lean) with three of its premises on the two states paid by
`step_digits` (Honest/K3/Law/Thread/BehindStep.lean): "the same but for what the lookup lays",
`DigLeft`, the library's promise behind.

  `form_digits_step`   CONDITIONAL, see below: `L.thread.Form (b + 1) k s' m'`

WHAT STAYS. Of the run: the thread in front; that the input stays. Of the states: the library's
promise in front (`k3OnIn`: Honest/K3/Law/Thread/SiteThr.lean's `onIn_thr` gets it out of the
thread); an acceptance by the stated sub-protocol's step; no mark behind. On public data: the
library's `K3At`; that the stated sub-protocol stands at the address and its test on the plan
accepts; where the sub-protocol stands; three tests on the table and the numbers. AND THE FOUR
PREMISES ON THE MEANING of `form_digits`: other layers', but for "formsIn" of this sub-protocol's
own run "objects", which is the lookups' own to pay and is not paid here. No instance of these
hypotheses is exhibited in this file.

Limits. On the verifier's side alone. The riders and what the step keeps are letters of the thread:
nothing is said of them here. Nothing on soundness, completeness or any other property
of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.Behind
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.BehindStep

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law.AtThr
open OnBytes.Model (Aff)
open VerifiableInference.Desc (Place Block OpenedColumn Oracle)
open VerifiableInference.Desc.K3 (theStated Readers k3OnIn pieceAt)
open VerifiableInference.Desc.First (ModelPart pubSets openSets start shift sameStand bookFit sampledIn
  pubStep pubRowM
  pubOfItems stepOpen rowOf)
open VerifiableInference.Desc.First.Look (P Sent lookAt)
open VerifiableInference.Desc.Sound (MsgT Frame)
open VerifiableInference.OnPublicFiles (K3At K3Letters digTableB k3Like)
open ProofFile.Honest.FirstThread (Letters)

local notation "FS" => VerifiableInference.Desc.First.S

variable {Bk : ProverCoinCounts} {Cl W₀ Rc Xi Tr Xo Pp Cells Tok : Type}
  (L : Letters Bk Cl W₀ Rc Xi Tr Xo Pp Cells Tok MsgT)
  {X : OnBytes.Model.Verify.Public} {D : Sent} {Lk : K3Letters Cells Tok}

/-- **CONDITIONAL ON what this file's head lists: behind an acceptance by the stated sub-protocol's
own step at the digits' address the thread's clause on the form holds one border on.** No instance
of these hypotheses is exhibited in this file. -/
theorem form_digits_step (hK : K3At X D Lk L.MgP) (Fr : Frame) (y₀ : Fr.E.Str) {Cl' : Type}
    (claim : Aff → Cl')
    (readers : Nat → Option (Readers FS)) (codes : OnBytes.Codes) (shape : OnBytes.Params.ReqShape)
    (a a' : Place) (B : Block FS Cl') (hB : theStated claim readers X codes shape a = some B)
    (hOk : B.planOk = true) {b : Nat} (hk : L.ps[b]? = some a) (hk1 : L.ps[b + 1]? = some a')
    (hfitS : sameStand L.links a a' = true) (i : Nat) (hi : a.link = some i) (sub : ModelPart)
    (hsub : L.links[i]? = some sub) (hpcT : a.piece = 7 + shift sub)
      (hpc : a.piece = pieceAt X i true)
    (hTab : digTableB L.MgP.more L.links L.ps b a i (shift sub) = true)
    {x : VerifiableInference.Desc.First.Look.Place} (hlook : lookAt X i true = some x)
      {k : Coins Bk}
    {s s' : FS} {m m' : Mid (Local W₀ Rc Xi Tr) Xo} {E : Env} (hA : Thr L.thread b k s m E)
    (hm : m'.st.input = m.st.input)
    (hOnIn : k3OnIn (P.ofPlace (OnBytes.Params.settingOf X.P.frame) true x) s = true) (ft n : Nat)
    (rs : List Fmt.RoundView) (cols : List OpenedColumn) (hst : B.step ft s rs cols = .ok (s', n))
      (hf : s'.failed = none)
    (hIn : L.mgP.inOrder (L.pubOf m.st.input.x, s) = true →
      L.mgP.inOrder (L.pubOf m.st.input.x, s') = true)
    (told : List (List Oracle)) (hbf : bookFit L.N L.ps told = true) (hn : told[b]? = some [])
    (hHeld : ∀ e ∈ sampledIn L.N ((openSets L.links L.ps (start L.links))[b]?.getD []),
      L.mgP.held e.1 e.2 (L.pubOf m.st.input.x, s) = true →
        L.mgP.held e.1 e.2 (L.pubOf m.st.input.x, s') = true)
    (othersPub : ∀ r ∈ pubStep ((pubSets L.mgP.more L.links L.ps)[b]?.getD [])
      (pubRowM L.mgP.more L.links a) ++
        pubOfItems (stepOpen ((openSets L.links L.ps (start L.links))[b]?.getD [])
          (rowOf L.links a)),
      k3Like r = false → L.mgP.pub r (L.pubOf m.st.input.x, s') = true)
    (othersP : ∀ r ∈ pubStep ((pubSets L.mgP.more L.links L.ps)[b]?.getD [])
      (pubRowM L.mgP.more L.links a),
      (∀ j, r ≠ .left j) → (∀ j, r ≠ .leftOn j) → L.mgP.pubP r (L.pubOf m.st.input.x, s')) :
    L.thread.Form (b + 1) k s' m' := by
  obtain ⟨hs, _, hsh, _⟩ := onIn_parts hOnIn
  obtain ⟨T, DL, hOut⟩ := step_digits claim readers X codes shape a B hB hOk i hi hpc hlook hsh ft s
    s' n rs
    cols hst
  exact form_digits L hK Fr y₀ a a' hk hk1 hfitS i hi sub hsub hpcT hpc hTab hlook hA hm hOnIn T
    (hOut hOnIn)
    DL hf hIn told hbf hn hHeld othersPub othersP

end ProofFile.Honest.K3.Law.AtThr

#print axioms ProofFile.Honest.K3.Law.AtThr.form_digits_step
