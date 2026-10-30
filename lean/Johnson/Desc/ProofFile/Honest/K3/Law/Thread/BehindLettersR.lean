-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Thread/BehindLettersR.lean: the honest side of the kind
"lookup" (K3): THE LIBRARY'S `BehindPartsR` (Johnson/Desc/First/Look/K3CallsBehindR.lean: twenty-two
fields: what the SECOND FORM of its rule for the sub-protocol of a link's lookup on the calls asks)
AT THE FRAME'S HONEST LETTERS. One theorem.

WHY THE SECOND FORM. The first form (`BehindParts`; BehindLetters.lean) has two fields more, on the
public item of the name "frame.liveIs", and is paid from `K3AtLive`. By the library's own words
(Johnson/Desc/Sound/MgAt/K3At.lean, Limits) `K3AtLive` DOES NOT HOLD AT ITS COMPOSED MEANING: the
name is struck from that meaning's list. The library itself spends the second form there
(`behindPartsR_mgAll`, Johnson/Desc/Sound/MgAt/K3Calls.lean). So what is to be spent at the proof
file's letters goes by this file.

After the library's own `behindParts_ofR` (Johnson/Desc/First/Look/K3CallsAtR.lean), which stands at
the full size and at a piece of the verifier's side; here: general in the list of links, the list of
places and the letters "Yes" and "Rc".

  `behindPartsR_honest`  **the twenty-two fields**

FIELD · WHOSE · PAID BY.
  here next stand fit tells askFresh   the table's and the numbers': handed through (public tests)
  quiet askIn askFree                  the table's: by the library's `calls_quiet`,
                                       `calls_asks_open`, from "the public sets fit" and where the
                                       sub-protocol stands
  pubIn fOut fFresh fLeft fLeftP       THE LOOKUPS' LAYER'S: by `K3At`
  fLedger fFree                        the ledger's items: by two equations on the meaning (hled,
                                       hfree, hns)
  bOrder bHeld                         other layers' fields: from `SameBut` and `InOrderReads`,
                                       `HeldReads`
  bShown bNoColl                       at the honest letters both say "true"
  bPub bPubP                           OTHER LAYERS' ITEMS THAT ARE CARRIED PAST THE SUB-PROTOCOL:
                                       HANDED THROUGH, NOT PAID HERE

WHICH OF THE PREMISES HOLD AT THE LIBRARY'S COMPOSED MEANING OVER ITS BASE MEANING (`mgAll Dm
mgBase`). The five on the meaning (`K3At`, `HeldReads`, `InOrderReads`, hled, hfree): SHOWN THERE,
by calls of the library's own lemmas, in BehindLettersAt.lean [not in this library; so here read:
not proved in this library] (`lettersR_mgAll`). hns, "the public sets fit", askFresh, bPub and bPubP
are premises of the library's own `behindPartsR_mgAll` too. Shown in this folder since, at
`lettersAt` under the head: "the public sets fit" (`hfit_at`, FormRestAtHead.lean), askFresh
(`askFresh_at`, FormRestAtHeadFacts.lean); and, in a file that is not in this library, bPubP at
every state (`bPubP_at`, FormRestAtHeadFill.lean [not in this library; so here read: not proved in
this library]). Of hns this folder
has no proof; of bPub: the library has `othersPub_att_mgAll`,
`othersPub_lay_mgAll` (Johnson/Desc/Sound/MgAt/K3CallsOthers.lean) and `head_bPub_mgAll`
(K3HeadBehindAt.lean), and Honest/K3/Law/Total/CallsBehindState.lean says the same of two states,
each under hypotheses of its own; no file of this folder calls them for the field.

Limits. No instance of these hypotheses is exhibited in this file. On the verifier's side alone.
Nothing on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.First.Look.K3CallsAtR
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.AtBorder

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law.AtThr
open VerifiableInference.Desc (Place Strs Wit Oracle)
open VerifiableInference.Desc.K3 (pieceAt)
open VerifiableInference.Desc.First (ModelPart Numbers Meaning openSets pubSets start sameStand bookFit
  pubFit pubStep pubRowM pubOfItems stepOpen shift)
open VerifiableInference.Desc.First.Look (P Sent lookAt placeAt k3LookIn_onIn)
open VerifiableInference.Desc.Sound (MsgT Frame onQ)
open VerifiableInference.OnPublicFiles
open ProofFile.Honest.FirstThread (honest)

local notation "FS" => VerifiableInference.Desc.First.S

variable {Pp Cells Tok : Type} {X : OnBytes.Model.Verify.Public} {D : Sent}
  {Lk : K3Letters Cells Tok} {Mg : Meaning Pp (Wit Cells Tok MsgT)}
  (ans : Nat → Nat → Pp × FS → Strs → Wit Cells Tok MsgT → Prop) (test : Nat → FS → Option String)

/-- **CONDITIONAL ON what this file's head lists as premises (no instance of them is exhibited in
this file): the library's `BehindPartsR` at the frame's honest letters.** Yes, Rc: any letters. -/
theorem behindPartsR_honest {Fr : Frame} {N : Numbers} {links : List ModelPart} {ps : List Place}
    {z : Pp} {k l : Nat} {x : VerifiableInference.Desc.First.Look.Place} {a a' : Place} {sub : ModelPart}
    {told : List (List Oracle)} {nsOf : Nat → Option Nat}
    (Yes : FS × Fr.E.Str → FS × Fr.E.Str → Prop) (Rc : FS × Fr.E.Str → Prop)
    (hK : K3At X D Lk Mg)
    (hled : ∀ m u, Mg.pub (.ledger m) u = VerifiableInference.Desc.First.ledgerB u.2)
    (hfree : ∀ m u, Mg.pub (.freeAbove m) u =
      (nsOf m).any fun n => VerifiableInference.Desc.First.freeAboveB n u.2)
    (hns : nsOf l = some (P.ofPlace (OnBytes.Params.settingOf X.P.frame) false x).ns)
    (hIn : InOrderReads Mg) (hHe : HeldReads Mg) (hlook : lookAt X l false = some x)
    (hpX : pieceAt X l false = 2 + shift sub) (here : ps[k]? = some a)
    (next : ps[k + 1]? = some a') (hl : a.link = some l) (hs : links[l]? = some sub)
    (hpc : a.piece = 2 + shift sub) (stand : sameStand links a a' = true)
    (fit : bookFit N ps told = true) (tells : told[k]? = some [])
    (hfit : pubFit Mg.more links ps = true)
    (askFresh : VerifiableInference.Desc.First.Pub.linkFresh l ∈
      (pubSets Mg.more links ps)[k]?.getD [])
    (bPub : ∀ u v : FS × Fr.E.Str,
      onQ N (honest Mg ans test) links ps (fun s => (z, s)) k u → Rc u → u.1.failed = none →
      Yes u v → SameBut u.1 v.1 →
      ∀ p ∈ pubStep ((pubSets Mg.more links ps)[k]?.getD []) (pubRowM Mg.more links a) ++
          pubOfItems (stepOpen ((openSets links ps (start links))[k]?.getD [])
            (VerifiableInference.Desc.First.rowOf links a)),
        p ∉ paidCallsR l (2 + shift sub) → Mg.pub p (z, v.1) = true)
    (bPubP : ∀ u v : FS × Fr.E.Str,
      onQ N (honest Mg ans test) links ps (fun s => (z, s)) k u → Rc u → u.1.failed = none →
      Yes u v → SameBut u.1 v.1 →
      ∀ p ∈ pubStep ((pubSets Mg.more links ps)[k]?.getD []) (pubRowM Mg.more links a),
        p ≠ .left l → Mg.pubP p (z, v.1)) :
    BehindPartsR (Fr := Fr) x (OnBytes.Params.settingOf X.P.frame) N (honest Mg ans test) links ps z
      k l (2 + shift sub) (D.arrayOf.getD l #[]) a a' told Yes Rc :=
  { here := here
    next := next
    quiet := calls_quiet hl hs hpc
    stand := stand
    fit := fit
    tells := tells
    askIn := calls_asks_open Mg.more links ps k a l sub hfit here hl hs hpc _ (by simp)
    askFree := calls_asks_open Mg.more links ps k a l sub hfit here hl hs hpc _ (by simp)
    askFresh := askFresh
    pubIn := fun s h => k3LookIn_onIn (fLook_at hK l false hlook z s (by rw [hpX]; exact h))
    fOut := fun s h => by
      rw [← hpX]
      exact fOut_at hK l false hlook z s h
    fLedger := fun s h => by
      show Mg.pub (.ledger l) (z, s) = true
      rw [hled, ledgerB_is]
      exact h
    fFree := fun s => by
      show Mg.pub (.freeAbove l) (z, s) = true ↔ _
      rw [hfree, hns, Option.any_some, freeAboveB_is]
    fFresh := fun s => by
      show Mg.pub (.linkFresh l) (z, s) = true ↔ _
      rw [hK.linkFresh]
    fLeft := fun s => hK.left l (z, s)
    fLeftP := fun s h => by
      show Mg.pubP (.left l) (z, s)
      rw [hK.pLeft]
      exact ⟨_, by unfold placeAt; rw [hlook]; rfl, h⟩
    bOrder := fun u v _ _ _ _ hsb h => inOrder_sameBut hIn hsb z h
    bPub := bPub
    bPubP := bPubP
    bHeld := fun u v _ _ _ _ hsb t _ h => held_sameBut hHe hsb t.1 t.2 z h
    bShown := fun _ _ _ _ _ _ _ _ _ _ => trivial
    bNoColl := fun _ _ _ _ _ _ _ _ _ _ => trivial }

end ProofFile.Honest.K3.Law.AtThr

#print axioms ProofFile.Honest.K3.Law.AtThr.behindPartsR_honest
