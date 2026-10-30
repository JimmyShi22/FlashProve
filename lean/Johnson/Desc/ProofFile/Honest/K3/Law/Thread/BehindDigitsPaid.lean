-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Thread/BehindDigitsPaid.lean: the honest side of the kind
"lookup" (K3): the thread's clause on the form, one border on, behind an accepting step of the
stated sub-protocol at the digits' address: `form_digits_step`
(Honest/K3/Law/Thread/BehindDigits.lean) with two of its four premises on the meaning paid, and the
third cut in two.

  `form_digits_paid`   CONDITIONAL, see below: `L.thread.Form (b + 1) k s' m'`

PAID HERE. "In order" rides and "held" rides: from the library's `InOrderReads` and `HeldReads` at
the letters' meaning of the promise (Honest/K3/Law/Thread/BehindLetters.lean).
CUT IN TWO. "Every public item behind that is of none of the constructors which the lookups' layer
fills holds": (1) the item "formsIn" of this sub-protocol's own run "objects": THE LOOKUPS' OWN;
Honest/K3/Law/Thread/BehindObjects.lean's `objects_behind` concludes it, under premises of its
own; (2) all the others: OTHER LAYERS'.

WHAT STAYS. Of the run: the thread in front; that the input stays. Of the states: the library's
promise in front; an accepting step of the stated sub-protocol; no mark of failure behind. On
public data: the library's `K3At`, `InOrderReads`, `HeldReads`; that the stated sub-protocol stands
at the address and passes its test on the plan; where it stands; three tests on the table and the
numbers. On the meaning: (1), (2), and what each open public item says beside its Bool. No instance
of these hypotheses is exhibited in this file.

Limits. On the verifier's side alone. The thread's letters "rides" and "keeps" are not spoken of.
Nothing on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.BehindDigits
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.BehindLetters
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.BehindObjects

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law.AtThr
open OnBytes.Model (Aff)
open VerifiableInference.Desc (Place Block OpenedColumn Oracle)
open VerifiableInference.Desc.K3 (theStated Readers k3OnIn pieceAt)
open VerifiableInference.Desc.First (ModelPart pubSets openSets start shift sameStand bookFit pubStep
  pubRowM pubOfItems stepOpen rowOf)
open VerifiableInference.Desc.First.Look (P Sent lookAt)
open VerifiableInference.Desc.Sound (MsgT Frame)
open VerifiableInference.OnPublicFiles (K3At K3Letters digTableB k3Like InOrderReads HeldReads)
open ProofFile.Honest.FirstThread (Letters)

local notation "FS" => VerifiableInference.Desc.First.S

variable {Bk : ProverCoinCounts} {Cl W₀ Rc Xi Tr Xo Pp Cells Tok : Type}
  (L : Letters Bk Cl W₀ Rc Xi Tr Xo Pp Cells Tok MsgT)
  {X : OnBytes.Model.Verify.Public} {D : Sent} {Lk : K3Letters Cells Tok}

/-- **CONDITIONAL ON what this file's head lists: behind an accepting step of the stated
sub-protocol at the digits' address the thread's clause on the form holds one border on.**
No instance of these hypotheses is exhibited in this file. -/
theorem form_digits_paid (hK : K3At X D Lk L.MgP) (hIO : InOrderReads L.MgP)
    (hHe : HeldReads L.MgP) (Fr : Frame) (y₀ : Fr.E.Str) {Cl' : Type} (claim : Aff → Cl')
    (readers : Nat → Option (Readers FS)) (codes : OnBytes.Codes)
    (shape : OnBytes.Params.ReqShape) (a a' : Place) (B : Block FS Cl')
    (hB : theStated claim readers X codes shape a = some B) (hOk : B.planOk = true) {b : Nat}
    (hk : L.ps[b]? = some a) (hk1 : L.ps[b + 1]? = some a')
    (hfitS : sameStand L.links a a' = true) (i : Nat) (hi : a.link = some i) (sub : ModelPart)
    (hsub : L.links[i]? = some sub) (hpcT : a.piece = 7 + shift sub)
    (hpc : a.piece = pieceAt X i true)
    (hTab : digTableB L.MgP.more L.links L.ps b a i (shift sub) = true)
    {x : VerifiableInference.Desc.First.Look.Place} (hlook : lookAt X i true = some x)
    {k : Coins Bk} {s s' : FS} {m m' : Mid (Local W₀ Rc Xi Tr) Xo} {E : Env}
    (hA : Thr L.thread b k s m E) (hm : m'.st.input = m.st.input)
    (hOnIn : k3OnIn (P.ofPlace (OnBytes.Params.settingOf X.P.frame) true x) s = true)
    (ft n : Nat) (rs : List Fmt.RoundView) (cols : List OpenedColumn)
    (hst : B.step ft s rs cols = .ok (s', n)) (hf : s'.failed = none)
    (told : List (List Oracle)) (hbf : bookFit L.N L.ps told = true) (hn : told[b]? = some [])
    (hObj : L.mgP.pub (.formsIn i (7 + shift sub) "objects") (L.pubOf m.st.input.x, s') = true)
    (hRest : ∀ r ∈ pubStep ((pubSets L.mgP.more L.links L.ps)[b]?.getD [])
          (pubRowM L.mgP.more L.links a) ++
        pubOfItems (stepOpen ((openSets L.links L.ps (start L.links))[b]?.getD [])
          (rowOf L.links a)),
      k3Like r = false → r ≠ .formsIn i (7 + shift sub) "objects" →
        L.mgP.pub r (L.pubOf m.st.input.x, s') = true)
    (othersP : ∀ r ∈ pubStep ((pubSets L.mgP.more L.links L.ps)[b]?.getD [])
        (pubRowM L.mgP.more L.links a),
      (∀ j, r ≠ .left j) → (∀ j, r ≠ .leftOn j) → L.mgP.pubP r (L.pubOf m.st.input.x, s')) :
    L.thread.Form (b + 1) k s' m' := by
  obtain ⟨hs, _, hsh, _⟩ := onIn_parts hOnIn
  obtain ⟨T, _, _⟩ := step_digits claim readers X codes shape a B hB hOk i hi hpc hlook hsh ft s
    s' n rs cols hst
  exact form_digits_step L hK Fr y₀ claim readers codes shape a a' B hB hOk hk hk1 hfitS i hi sub
    hsub hpcT hpc hTab hlook hA hm hOnIn ft n rs cols hst hf
    (inOrder_rides L.ans L.test hIO T _) told hbf hn
    (fun e _ h => held_rides L.ans L.test hHe T e.1 e.2 _ h)
    (others_split L.mgP _ k3Like _ _ hObj hRest) othersP

end ProofFile.Honest.K3.Law.AtThr

#print axioms ProofFile.Honest.K3.Law.AtThr.form_digits_paid
