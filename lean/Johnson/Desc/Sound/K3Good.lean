-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/K3Good.lean: THE SKELETON OF THE LOOKUP'S LEMMA: from named premises to
`Piece.GoodIn` (Johnson/Desc/Sound/GoodIn.lean), the form that the rule of composition asks of a
block. One definition of type Prop and three theorems. NO RESULT ON THE PROTOCOL: one premise,
(HEAR), holds all the work, and it is not proved: IT COUNTS FOR NOTHING IN ANY COUNT OF LAWS
PAID.

Main names:
  `Hear p Kb G rd rw on on' RB`: **(HEAR)**, as one text: see its docstring. It speaks of the
    block's `decide` and `rounds`, through the fold; of no flat function; and, behind the block, of
    VALUES alone: of witnesses of RB and of the proved block's relation at whatever it puts out. No
    reader of the statement behind is asked.
  `goodIn_ofBK`: FROM ANY PROVED BARE BLOCK OF THE LIBRARY (`KObj.BK` with `Know` and a carried
    condition), a reading G whose errors the block's errors bear, readers rd and rw, and (HEAR), to
    `GoodIn` from the proved block's in-relation, pulled back, to RB. General in the proved block:
    so it serves every kind that carries one, and the lookup at a key file as at a proof file.
  `hear_ofReader`: the heavier form, with a reader of the statement behind, gives (HEAR).
  `k3_goodIn_of`: `goodIn_ofBK` at the library's lookup inside a sub-proof with riders
    (`kLookupCR`), lifted over its caller's signature: knowledge soundness, the carried condition,
    the reading and its `Fits` are the library's own, BY NAME.

The relations: in front, the proved block's in-joint at (rd a, rw w): every call's keys lie in that
call's table, with the caller's own joint and the riders' source. Behind: RB, a letter. THE FILLING
THAT IS MEANT IS THE BORDER'S ROW IN THE TABLE OF JOINTS (`k3Out`,
Johnson/Desc/First/Look/K3Borders.lean): the forms that the hearing left, and the kind's own
formulas on the planes and on the key vectors fed with the true values at the points heard, are all
worth 0; with what rides beside. NOT "the runs of claims return here and their claims hold"
(`ClaimsHoldBehind`): that can stand in front of the batching alone (not in this library: Johnson/
Desc/Sound/ClaimsLater.lean, Limits). (HEAR)'s last clause is then rows of the list of K3's laws in
the lookups' files (not in this library) by name together: (L2a), owed, with (L1).

WHAT OF THE LIBRARY IT CALLS BY NAME, so that it can be counted (the rule: no routine in a context
may be reached from a statement or a proof): `lookupCR_knowAt`,
`lookupCR_onOut_of`, `lookupC_onOut`, `kLookupCR` (Johnson/Top/H/LookupCRide.lean, LookupC.lean) ·
`BaseKind.know_toKind`, `onOut_toKind`, `know_of_knowAt` (Johnson/Top/Kind.lean, KindKnowAt.lean) ·
`Fo.Peel.lookCarryT`, `lookCarryT_fits`, `BearsT`, `Fo.specF` (OnBytes/Tie/Pv/Lookup/Forest/). A
walk over constants from lookupCR_good, kLookupCR, lookCarryT and its laws, know_carryS and
out_iff_claims, statement and proof apart, has reached no routine in a context (over another
state of the library); from this file's own two theorems the walk is owed. FoPeelT.lean is imported
whole; it also holds a tie to `verify-on-bytes` (look_yesT), which is not called here.

Limits. (1) (HEAR) IS NOT PROVED, of K3.block or of any block; p is any piece here: nothing ties p.b
to the kind's text. (2) rd and rw are letters: at a constant rd the relation in front says nothing
of the record. (3) Hollow uses, each true and empty: a block that refuses all meets (HEAR) emptily,
and `GoodIn` holds of it (the first example); `on` that no statement meets; an entry of p.err as
large as a round's number of challenges (`BearsT` does not forbid it); a caller's joint R0 that
gives the riders' source itself (LookupCRide.lean's own head). AND THE EASIEST: AN RB THAT NO
WITNESS MEETS: then a block that says yes to all meets (HEAR) wherever Kb puts out (HearToy.lean,
not in this library: `yesToAll_hears_nothing`): THE LEMMA IS WORTH WHAT ITS RB IS WORTH: so whoever
uses it lays the RB that is meant and shows it met behind an honest run. So whoever uses it states
the errors as numbers below the challenge count and shows `on` met by an honest run. (4) A block
that says yes to all is tried against (HEAR) in that file: it fails at the RB that is meant there.
(5) By report the proved block fits the proof file's lookups alone (`FoNums.ok`
asks v below 32); the key file's stand on another typed block: `goodIn_ofBK` at that. (6) The rule
asks the law of `below b` where a file's decision is meant (ChainRule.lean, section 7): not here.
(7) ONE PUBLIC QUANTITY BY TWO ROADS: p.ds are held against the lookup's spec (hM), p.b.rounds
against the view (`roundsFit`): nothing here ties p.ds to p.b.rounds: the rule's `Tiled` ties them
by two counts alone (`Piece.Owed`); a statement "the tests on the plan give Tiled" is owed by the
rule's files. (8) What `on` must hold so that the proved block's condition in front is met (hon) is
not said; that the first block's condition comes of the public tests is owed at the chain. (9) NO
CALLER r HAS BEEN SHOWN WITH hok, hsel, hM AND hB TOGETHER AT A REAL PLACE'S SHAPE: until one is,
`k3_goodIn_of` may be empty where it is meant. (10) Nothing on acceptance, nothing on hiding.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.KnowInProofs
import Johnson.Top.H.LookupCRide
import OnBytes.Tie.Pv.Lookup.Forest.FoPeelT

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open _root_.Iop (Reduction Err Shape IOR ExtSpec oneExternalString Doomed BadFam Tr)

/-- **(HEAR): THE ONE PREMISE THAT HOLDS THE WORK.** p: the block with its stretch. Kb: a bare block
of the library. G: the reading of the block's written rounds as Kb's typed rounds. rd: the statement
in front, read as Kb's. rw: the witness in front, read as Kb's. RB: the relation behind the block,
IN THE DESCRIPTION'S OWN WORDS (the border's row in the table of joints: for a kind that hears: the
forms that it has left are worth 0, and what its later claims will say of committed values at the
points heard holds). At every statement in front with `on` and every written transcript of the
stretch: WHERE THE FRAME'S OWN FOLD AT THE LIST OF THIS ONE BLOCK SAYS YES, the transcript has an
image under the reading; Kb puts out some statement y at the statement read in front and that image;
if y is inside Kb's condition behind, the statement behind the block is inside the block's promise;
and EVERY WITNESS OF RB BEHIND THE BLOCK GIVES A WITNESS w' OF Kb's RELATION AT y such that the
block's extractor's value, read, is what Kb's extractor makes of w'. -/
def Hear {S Cl W : Type} {C : CK} {F : Frame} (p : Piece C F S Cl W) {A B : JK} (Kb : BK A B)
    (G : S × F.E.Str → CarryS (uLT C p.ds) Kb.R.shape) (rd : S × F.E.Str → A.X × A.E.Str)
    (rw : W → A.W) (on on' : S × F.E.Str → Prop) (RB : S × F.E.Str → W → Prop) : Prop :=
  ∀ a τ a', on a → p.ior.red.out a τ = some a' →
    ∃ τ' y, (G a).tr τ = some τ' ∧ Kb.R.red.out (rd a) τ' = some y ∧ (B.on y → on' a') ∧
      ∀ w, RB a' w → ∃ w', B.relR y w' ∧ rw (p.ext a τ w) = Kb.ext (rd a) τ' w'

/-- **From a proved bare block of the library to a block of the description.** -/
theorem goodIn_ofBK {S Cl W : Type} {C : CK} {F : Frame} (p : Piece C F S Cl W) {A B : JK}
    (Kb : BK A B) (hK : Kb.R.red.Know A.on A.relR B.relR Kb.ext Kb.err)
    (hO : ∀ a τ b, A.on a → Kb.R.red.out a τ = some b → B.on b)
    (G : S × F.E.Str → CarryS (uLT C p.ds) Kb.R.shape) (hfit : ∀ a, (G a).Fits Kb.err p.err)
    (rd : S × F.E.Str → A.X × A.E.Str) (rw : W → A.W) (on on' : S × F.E.Str → Prop)
    (RB : S × F.E.Str → W → Prop) (hon : ∀ a, on a → A.on (rd a))
    (H : Hear p Kb G rd rw on on' RB) :
    p.GoodIn on on' (fun a w => A.relR (rd a) (rw w)) RB := by
  refine pieceGoodIn S Cl W C F p _ _ A.W B.W Kb.R.red G Kb.err rd on on' A.on B.on _ _ A.relR
    B.relR Kb.ext hfit hon ?_ (knowInOfCarry _ _ _ _ _ _ _ _ _ _ _ hO hK)
  intro a τ a' ha ho
  obtain ⟨τ', y, e₁, e₂, e₃, e₄⟩ := H a τ a' ha ho
  refine ⟨τ', y, e₁, e₂, e₃, fun w hw => ?_⟩
  obtain ⟨w', hw', e⟩ := e₄ w hw
  refine ⟨w', hw', fun h => ?_⟩
  show A.relR (rd a) (rw (p.ext a τ w))
  rw [e]
  exact h

/-- The heavier form, with a reader rd' of the statement behind: Kb puts out JUST what is read off
the record behind, and the relation behind is Kb's, pulled back. It asks an equation of statements
(for a lookup: of rows as functions of coefficients), where `Hear` asks values alone. -/
theorem hear_ofReader {S Cl W : Type} {C : CK} {F : Frame} (p : Piece C F S Cl W) {A B : JK}
    (Kb : BK A B) (G : S × F.E.Str → CarryS (uLT C p.ds) Kb.R.shape)
    (rd : S × F.E.Str → A.X × A.E.Str) (rd' : S × F.E.Str → B.X × B.E.Str)
    (rw : W → A.W) (rw' : W → B.W) (on on' : S × F.E.Str → Prop)
    (H : ∀ a τ a', on a → p.ior.red.out a τ = some a' →
      ∃ τ', (G a).tr τ = some τ' ∧ Kb.R.red.out (rd a) τ' = some (rd' a') ∧
        (B.on (rd' a') → on' a') ∧ ∀ w, rw (p.ext a τ w) = Kb.ext (rd a) τ' (rw' w)) :
    Hear p Kb G rd rw on on' fun a' w => B.relR (rd' a') (rw' w) := by
  intro a τ a' ha ho
  obtain ⟨τ', e₁, e₂, e₃, e₄⟩ := H a τ a' ha ho
  exact ⟨τ', rd' a', e₁, e₂, e₃, fun w hw => ⟨rw' w, hw, e₄ w⟩⟩

/-! ### (HEAR) against silly members: no to all, here; yes to all, in HearToy.lean -/

/-- A block that says no to all MEETS (HEAR), EMPTILY, and `GoodIn` holds of it: a sentence "where
the block says yes …" claims nothing of when it says yes. It is no fault of the form: a verifier
that refuses all is sound. That the kind's own block is no such member is shown by runs. -/
example {S Cl W : Type} {C : CK} {F : Frame} (p : Piece C F S Cl W) {A B : JK} (Kb : BK A B)
    (G : S × F.E.Str → CarryS (uLT C p.ds) Kb.R.shape) (rd : S × F.E.Str → A.X × A.E.Str)
    (rw : W → A.W) (on on' : S × F.E.Str → Prop) (RB : S × F.E.Str → W → Prop)
    (hno : ∀ a τ, p.ior.red.out a τ = none) : Hear p Kb G rd rw on on' RB :=
  fun a τ a' _ ho => by rw [hno] at ho; cases ho

/-- NO MEMBER, A REMARK: where the block says yes, RB has a witness behind, and Kb's relation has
none at whatever Kb puts out, (HEAR) fails. A block that says yes to all is laid in
Johnson/Desc/Sound/HearToy.lean. -/
example {S Cl W : Type} {C : CK} {F : Frame} (p : Piece C F S Cl W) {A B : JK} (Kb : BK A B)
    (G : S × F.E.Str → CarryS (uLT C p.ds) Kb.R.shape) (rd : S × F.E.Str → A.X × A.E.Str)
    (rw : W → A.W) (on on' : S × F.E.Str → Prop) (RB : S × F.E.Str → W → Prop)
    (a a' : S × F.E.Str) (τ : Tr (uLT C p.ds)) (w : W) (ha : on a)
    (ho : p.ior.red.out a τ = some a') (hw : RB a' w)
    (hne : ∀ τ' y, Kb.R.red.out (rd a) τ' = some y → ∀ w', ¬ B.relR y w') :
    ¬ Hear p Kb G rd rw on on' RB := by
  intro H
  obtain ⟨τ', y, -, e, -, h⟩ := H a τ a' ha ho
  obtain ⟨w', hw', -⟩ := h w hw
  exact hne τ' y e w' hw'

end VerifiableInference.Desc.Sound

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Flat KObj VerifiableInference.OnPublicFiles
open Iop IOR Prob Cb Cb.LdLkp TWhole TwV Tw Cb.Fo OnBytes OnBytes.Slice OnBytes.Model
open OnBytes.PscRun Run _root_.Fo _root_.Fo.Peel

/-- **The lookup's lemma, from its named premises.** r: the caller with riders. hok, hsel: the
library's two public tests on it. hM: the stretch's written rounds meet the lookup's spec. hB: the
block's errors bear the proved block's. RB: the relation behind, in the description's own words. H:
(HEAR). -/
theorem k3_goodIn_of {S Cl W : Type} {F : Frame} (p : Piece (ckP .two) F S Cl W)
    (r : LookupCRCaller) (hok : OkLookupC (callersCR [r])) (hsel : SelLookupCR [r])
    (hM : List.Forall₂ MeetsT p.ds (specF r.c.h))
    (hB : BearsT p.ds _ ((kLookupCR [r]).ε r) p.err)
    (rd : S × F.E.Str →
      ((kLookupCR [r]).toKind.src r).X × ((kLookupCR [r]).toKind.src r).E.Str)
    (rw : W → ((kLookupCR [r]).toKind.src r).W) (on on' : S × F.E.Str → Prop)
    (RB : S × F.E.Str → W → Prop)
    (hon : ∀ a, on a → ((kLookupCR [r]).toKind.src r).on (rd a))
    (H : Hear p ((kLookupCR [r]).toKind.block r)
      (fun _ => lookCarryT r.c.h r.c.L r.c.Ex p.ds hM.length_eq) rd rw on on' RB) :
    p.GoodIn on on' (fun a w => ((kLookupCR [r]).toKind.src r).relR (rd a) (rw w)) RB := by
  have hr : r ∈ (kLookupCR [r]).sizes := List.mem_singleton.2 rfl
  have hA := lookupCR_knowAt [r] hok hsel
  exact goodIn_ofBK p ((kLookupCR [r]).toKind.block r)
    (BaseKind.know_toKind (BaseKind.know_of_knowAt hA) r hr)
    (fun a τ b ha hb =>
      BaseKind.onOut_toKind (lookupCR_onOut_of [r] (lookupC_onOut _ hok)) r hr a τ b hb ha)
    (fun _ => lookCarryT r.c.h r.c.L r.c.Ex p.ds hM.length_eq)
    (fun _ => lookCarryT_fits r.c.h r.c.L r.c.Ex p.ds hM _ _ hB)
    rd rw on on' RB hon H

end VerifiableInference.Desc.Sound
