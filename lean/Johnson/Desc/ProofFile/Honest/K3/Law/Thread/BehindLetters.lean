-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Thread/BehindLetters.lean: the honest side of the kind "lookup"
(K3): THE LIBRARY'S `BehindParts` (Johnson/Desc/First/Look/K3CallsBehind.lean: twenty-four fields:
what its rule for the sub-protocol of a link's lookup on the calls asks) AT THE FRAME'S HONEST
LETTERS. SIX FIELDS ARE HANDED THROUGH AS THEY STAND (public tests on the table and the numbers);
SIXTEEN ARE MADE, of premises of another form, which the table below names; TWO (bPub, bPubP: other
layers' items that ride past the sub-protocol) ARE HANDED THROUGH AND STAY UNPAID HERE. Since this
was written: at the frame's letters `lettersAt`, under the head, bPubP is shown at every state
(`bPubP_at`, FormRestAtHeadFill.lean [not in this library]); of bPub: the library has
`othersPub_att_mgAll`, `othersPub_lay_mgAll` (Johnson/Desc/Sound/MgAt/K3CallsOthers.lean) and
`head_bPub_mgAll` (K3HeadBehindAt.lean), and Honest/K3/Law/Total/CallsBehindState.lean says the same
of two states, each under hypotheses of its own; no file of this folder calls them for the field.
After the library's own `behindParts_of`
(Johnson/Desc/First/Look/K3CallsAt.lean), which stands at the full size and at a piece of the
verifier's side; here: general in the list of links, the list of places and the letter "Yes".
Theorems.

`behindParts_honest` AND `k3AtLive_honest` ARE TRUE AND CANNOT BE SPENT AT THE PROOF FILE'S
LETTERS: they take `K3AtLive`, which by the library's own words
(Johnson/Desc/Sound/MgAt/K3At.lean, Limits) does not hold at its composed meaning. WHAT IS SPENT
THERE GOES BY BehindLettersR.lean (the second form of the library's rule). Nothing calls the two
any more. `inOrder_rides` and `held_rides` are not touched by this.

  `k3AtLive_honest`     the honest letters turn none of the fields of which `K3AtLive` speaks
  `behindParts_honest`  **the twenty-four fields**
  `inOrder_rides`, `held_rides`   at the digits' sub-protocol: "in order" and "held"
                              ride from `SameBut`

FIELD · WHOSE · PAID BY.
  here next stand fit tells askFresh     the table's and the numbers': premises (public tests)
  quiet askIn askFree askLive            the table's: by the library's `calls_quiet`,
                                         `calls_asks_open`, `calls_live_open`, from "the public sets
                                         fit" and where the sub-protocol stands
  pubIn fOut fFresh fLeft fLeftP         THE LOOKUPS' LAYER'S: by `K3At`
  fLive                                  THE LOOKUPS' LAYER'S: by `K3AtLive`
  fLedger fFree                          the ledger's items: by two equations on the meaning
                              (premises hled, hfree, hns)
  bOrder bHeld                           other layers' fields: from `SameBut` and "it reads the
                                         statement, the check, the request | the statement and the
                                         book alone" (`InOrderReads`, `HeldReads`: premises)
  bShown bNoColl                         at the honest letters both say "true"
  bPub bPubP                             OTHER LAYERS' ITEMS THAT RIDE PAST THE SUB-PROTOCOL:
                              PREMISES, NOT PAID HERE

Limits. No instance of these hypotheses is exhibited in this file. On the verifier's side alone.
Nothing on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.First.Look.K3CallsAt
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.AtBorder

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law.AtThr
open VerifiableInference.Desc (Place Strs Wit Oracle)
open VerifiableInference.Desc.K3 (pieceAt)
open VerifiableInference.Desc.First (ModelPart Pub Numbers Meaning openSets pubSets start sameStand
  bookFit pubFit
  pubStep pubRowM pubOfItems stepOpen rowOf shift)
open VerifiableInference.Desc.First.Look (P Sent lookAt placeAt k3LookIn_onIn)
open VerifiableInference.Desc.Sound (MsgT Frame onQ)
open VerifiableInference.OnPublicFiles
open ProofFile.Honest.FirstThread (honest)

local notation "FS" => VerifiableInference.Desc.First.S

section
variable {Pp Cells Tok : Type} {X : OnBytes.Model.Verify.Public} {D : Sent}
  {Lk : K3Letters Cells Tok} {Mg : Meaning Pp (Wit Cells Tok MsgT)}
  (ans : Nat → Nat → Pp × FS → Strs → Wit Cells Tok MsgT → Prop) (test : Nat → FS → Option String)

/-- **The frame's honest letters turn none of the fields of which `K3AtLive` speaks.** -/
theorem k3AtLive_honest (hV : K3AtLive D Mg) : K3AtLive D (honest Mg ans test) := ⟨hV.live, hV.asks⟩

/-- **CONDITIONAL ON what this file's head lists as premises (no instance of them is exhibited in
this file): the library's `BehindParts` at the frame's honest letters.** Yes: any letter. -/
theorem behindParts_honest {Fr : Frame} {N : Numbers} {links : List ModelPart} {ps : List Place} {z : Pp}
    {k l : Nat} {x : VerifiableInference.Desc.First.Look.Place} {a a' : Place} {sub : ModelPart}
    {told : List (List Oracle)} {nsOf : Nat → Option Nat}
    (Yes : FS × Fr.E.Str → FS × Fr.E.Str → Prop) (hK : K3At X D Lk Mg) (hV : K3AtLive D Mg)
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
    (askFresh : Pub.linkFresh l ∈ (pubSets Mg.more links ps)[k]?.getD [])
    (bPub : ∀ u v : FS × Fr.E.Str,
      onQ N (honest Mg ans test) links ps (fun s => (z, s)) k u → u.1.failed = none → Yes u v →
      SameBut u.1 v.1 →
      ∀ p ∈ pubStep ((pubSets Mg.more links ps)[k]?.getD []) (pubRowM Mg.more links a) ++
          pubOfItems (stepOpen ((openSets links ps (start links))[k]?.getD []) (rowOf links a)),
        p ∉ paidCalls l (2 + shift sub) → Mg.pub p (z, v.1) = true)
    (bPubP : ∀ u v : FS × Fr.E.Str,
      onQ N (honest Mg ans test) links ps (fun s => (z, s)) k u → u.1.failed = none → Yes u v →
      SameBut u.1 v.1 →
      ∀ p ∈ pubStep ((pubSets Mg.more links ps)[k]?.getD []) (pubRowM Mg.more links a),
        p ≠ .left l → Mg.pubP p (z, v.1)) :
    BehindParts (Fr := Fr) x D (OnBytes.Params.settingOf X.P.frame) N (honest Mg ans test) links ps
      z
      k l (2 + shift sub) (D.arrayOf.getD l #[]) a a' told Yes :=
  { here := here
    next := next
    quiet := calls_quiet hl hs hpc
    stand := stand
    fit := fit
    tells := tells
    askIn := calls_asks_open Mg.more links ps k a l sub hfit here hl hs hpc _ (by simp)
    askFree := calls_asks_open Mg.more links ps k a l sub hfit here hl hs hpc _ (by simp)
    askFresh := askFresh
    askLive := calls_live_open Mg.more links ps k a l hfit here
      (hV.asks links a l sub hl hs (Or.inl hpc))
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
    fLive := fLive_at hV l z
    fLeft := fun s => hK.left l (z, s)
    fLeftP := fun s h => by
      show Mg.pubP (.left l) (z, s)
      rw [hK.pLeft]
      exact ⟨_, by unfold placeAt; rw [hlook]; rfl, h⟩
    bOrder := fun u v _ _ _ hsb h => inOrder_sameBut hIn hsb z h
    bPub := bPub
    bPubP := bPubP
    bHeld := fun u v _ _ _ hsb t _ h => held_sameBut hHe hsb t.1 t.2 z h
    bShown := fun _ _ _ _ _ _ _ _ _ => trivial
    bNoColl := fun _ _ _ _ _ _ _ _ _ => trivial }

/-- "In order" rides past a lookup's sub-protocol. CONDITIONAL ON `InOrderReads` and `SameBut`. -/
theorem inOrder_rides (hIn : InOrderReads Mg) {s t : FS} (T : SameBut s t) (z : Pp)
    (h : (honest Mg ans test).inOrder (z, s) = true) : (honest Mg ans test).inOrder (z, t) = true :=
  inOrder_sameBut hIn T z h

/-- "Held" rides past a lookup's sub-protocol. CONDITIONAL ON `HeldReads` and `SameBut`. -/
theorem held_rides (hHe : HeldReads Mg) {s t : FS} (T : SameBut s t) (j k : Nat) (z : Pp)
    (h : (honest Mg ans test).held j k (z, s) = true) :
    (honest Mg ans test).held j k (z, t) = true :=
  held_sameBut hHe T j k z h

end

end ProofFile.Honest.K3.Law.AtThr

#print axioms ProofFile.Honest.K3.Law.AtThr.k3AtLive_honest
#print axioms ProofFile.Honest.K3.Law.AtThr.behindParts_honest
#print axioms ProofFile.Honest.K3.Law.AtThr.inOrder_rides
#print axioms ProofFile.Honest.K3.Law.AtThr.held_rides
