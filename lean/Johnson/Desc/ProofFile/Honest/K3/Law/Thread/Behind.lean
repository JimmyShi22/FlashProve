-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Thread/Behind.lean: the honest side of the kind "lookup" (K3):
THE THREAD'S CLAUSE ON THE FORM, ONE BORDER ON: what the frame's sentence "behind its acceptance"
(`Behind`, Honest/Thread/Pays.lean) asks first, at the sub-protocol of a link's lookup on the
digits. A sorting and one call of the library's own rule for that sub-protocol
(`k3_digits_behind_at`, Johnson/Desc/First/Look/K3DigitsBehind.lean). General in the first
chain's letters.

  `onAt_strs`       at the frame's honest letters the table's promise reads no oracle: it holds at
                    all strings or at none
  `form_digits`     CONDITIONAL, see below: `L.thread.Form (b + 1) k s' m'`

WHAT `form_digits` ASKS. Of the run: the thread in front; that the input stays. Of the two states:
the library's promise in front and behind (`k3OnIn`, `k3OnOut`), "the same but for what the lookup
lays" (`SameBut`), `DigLeft`, no mark behind. On public data: the library's `K3At`; where the
sub-protocol stands; three tests on the table and the numbers. AND FOUR PREMISES ON THE MEANING, as
the library's rule names them: "in order" rides; "held" rides at the open pins' tenants; every
public item behind that is of none of the constructors which the lookups' layer fills holds; what
each says beside its Bool holds. THEY ARE OTHER LAYERS', BUT FOR ONE ITEM UNDER THE THIRD: "formsIn"
of this sub-protocol's own run "objects", whose maker the table names THIS sub-protocol: that one is
the lookups' own to pay, and is not paid here. No instance of these hypotheses is exhibited in this
file. The riders and what the step keeps (`rides`, `keeps`) are letters of the thread: nothing is
said of them here.

Limits. On the verifier's side alone. The sub-protocol of the lookup on the calls is not served by
this file. Nothing on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.First.Look.K3DigitsBehind
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.AtBorder

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law.AtThr
open VerifiableInference.Desc (Place Strs Wit Oracle)
open VerifiableInference.Desc.K3 (k3OnIn k3OnOut pieceAt)
open VerifiableInference.Desc.First (ModelPart Item Numbers Meaning onAt pubSets openSets start shift
  sameStand bookFit
  sampledIn pubStep pubRowM pubOfItems stepOpen rowOf)
open VerifiableInference.Desc.First.Look (P Sent lookAt)
open VerifiableInference.Desc.Sound (MsgT Frame strsOf onQ)
open VerifiableInference.OnPublicFiles (K3At K3Letters SameBut DigLeft digTableB k3Like
        k3_digits_behind_at)
open ProofFile.Honest.FirstThread (Letters honest noStrs)

local notation "FS" => VerifiableInference.Desc.First.S

/-- **At the frame's honest letters the table's promise reads no oracle.** -/
theorem onAt_strs {Pp Wt : Type} {N : Numbers} {Mg : Meaning Pp Wt}
    {ans : Nat → Nat → Pp × FS → Strs → Wt → Prop} {test : Nat → FS → Option String}
      {links : List ModelPart}
    {p : Option Place} {O : List Item} {Q : List VerifiableInference.Desc.First.Pub} {a : Pp × FS}
      {y : Strs}
    (y' : Strs) (h : onAt N (honest Mg ans test) links p O Q a y) :
    onAt N (honest Mg ans test) links p O Q a y' := by
  obtain ⟨_, h2⟩ := h
  refine ⟨trivial, ?_⟩
  rcases h2 with hm | ⟨h1, h3, _, h4⟩
  · exact Or.inl hm
  · exact Or.inr ⟨h1, h3, fun _ _ => ⟨trivial, trivial⟩, h4⟩

section
variable {Bk : ProverCoinCounts} {Cl W₀ Rc Xi Tr Xo Pp Cells Tok : Type}
  (L : Letters Bk Cl W₀ Rc Xi Tr Xo Pp Cells Tok MsgT)
  {X : OnBytes.Model.Verify.Public} {D : Sent} {Lk : K3Letters Cells Tok}

/-- **CONDITIONAL ON what this file's head lists: behind the sub-protocol of a link's lookup on the
digits the thread's clause on the form holds one border on.** Fr, y₀: any frame of the library's and
any of its strings: the promise reads none. No instance of these hypotheses is exhibited in this
file. -/
theorem form_digits (hK : K3At X D Lk L.MgP) (Fr : Frame) (y₀ : Fr.E.Str) {b : Nat} (a a' : Place)
    (hk : L.ps[b]? = some a) (hk1 : L.ps[b + 1]? = some a') (hfitS : sameStand L.links a a' = true)
      (i : Nat)
    (hi : a.link = some i) (sub : ModelPart) (hsub : L.links[i]? = some sub)
      (hpcT : a.piece = 7 + shift sub)
    (hpc : a.piece = pieceAt X i true) (hTab : digTableB L.MgP.more L.links L.ps b a i (shift sub) =
      true)
    {x : VerifiableInference.Desc.First.Look.Place} (hlook : lookAt X i true = some x)
      {k : Coins Bk}
    {s s' : FS} {m m' : Mid (Local W₀ Rc Xi Tr) Xo} {E : Env} (hA : Thr L.thread b k s m E)
    (hm : m'.st.input = m.st.input)
    (hOnIn : k3OnIn (P.ofPlace (OnBytes.Params.settingOf X.P.frame) true x) s = true)
      (T : SameBut s s')
    (hOut : k3OnOut (P.ofPlace (OnBytes.Params.settingOf X.P.frame) true x) s' = true)
      (DL : DigLeft s s')
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
  have hon : onQ (Fr := Fr) L.N L.mgP L.links L.ps (fun t => (L.pubOf m.st.input.x, t)) b (s, y₀) :=
    onAt_strs (strsOf Fr y₀) (onAt_of_thr L hA)
  have hnext := k3_digits_behind_at L.links X D Lk L.mgP (k3At_honest hK L.ans L.test) L.N L.ps b a
    a' hk hk1
    hfitS i hi sub hsub hpcT hpc hTab hlook (L.pubOf m.st.input.x) (s, y₀)
      (s', y₀) hon hOnIn T hOut trivial DL
    hIn told hbf hn hHeld (fun _ _ _ => trivial) (fun _ _ _ => trivial) othersPub othersP
  refine ⟨?_, ?_⟩
  · show s'.failed.isNone = true
    rw [hf]
    rfl
  · show onAt L.N L.mgP L.links L.ps[b + 1]?
      (((openSets L.links L.ps (start L.links))[b + 1]?).getD [])
      (((pubSets L.mgP.more L.links L.ps)[b + 1]?).getD []) (L.pubOf m'.st.input.x, s') noStrs
    rw [hm]
    exact onAt_strs noStrs hnext

end

end ProofFile.Honest.K3.Law.AtThr

#print axioms ProofFile.Honest.K3.Law.AtThr.onAt_strs
#print axioms ProofFile.Honest.K3.Law.AtThr.form_digits
