-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/K05AtTable.lean: THE KIND's LAW AT THE SEATED BLOCK (K05_law_one_guard,
Johnson/Desc/First/Att/K05LawGuard.lean) SET AT THE TABLE OF JOINTS' OWN PROMISE
(Johnson/Desc/First/Borders.lean; imported, not turned): the piece of the
block k5AtN is GoodIn FROM the table's promise in front of the kind's block TO the table's promise
behind it.

THE STATEMENT (`K05_at_table`). ⟨blk, base, ds, [], the identity, Err.cap 128⟩.GoodIn
  (onT … pl O Q) (onT … pl' (stepOpen O (rowOf links pl)) (pubStep Q (pubRowM Mg.more links pl)))
  (Todo …) R',
where onT … p O Q a := onAt N Mg links (some p) O Q (π, a.1) (strsOf Fr a.2) ∧ a.1.failed = none.

WHAT THE PROMISE IN FRONT GIVES. Two things that the law and the carrying want of the record in
front are clauses of the promise itself: "nothing is heard at the digits' seat, and the link's table
of arrays is the plan's" is the public item linkFresh m (spent inside k5_t2 under K5Fill.linkFresh);
"what the lookup on the calls left" is what the public item left m says beside its Bool
(Meaning.pubP), spent here under ONE premise on the filling:
  hleftIs: Mg.pubP (.left m) (π, a'.1) gives K3LeftOutIs … (x0 a') (gOf a') a'.1.
ON hleftIs. pubP sees the PUBLIC RECORD a'.1 ALONE. K3LeftOutIs names x0 a' (the lookup's typed
out-statement) and gOf a' (what the lookup has heard), letters of the law that may read the oracles
a'.2 as well. So hleftIs can be met only where x0 and gOf hang on the record alone, or are chosen
out of what pubP says "there is" (leftOut_chosen_room, Johnson/Desc/First/Att/K05LeftChosen.lean).
It binds these two letters; no filling is shown.
"THERE IS ONE" AGAINST "THE RUN's OWN". The item left m says: what was heard is the end values of
a hearing of SOME rounds from SOME ledger in front. An x0 that is chosen out of that is the
out-statement of SOME such hearing, not of the transcript's. So the conclusion's "Todo (x0 a')
(I.part w)" speaks of that one. Whether two hearings that end in one heard record give one
out-statement decides what the sentence is worth where the lookup's law hands its own out-statement
on: THE JOINT OF THE LOOKUP's BLOCK AND THIS ONE: NOT SHOWN HERE.

HOW THE LAW's LETTERS ARE FILLED, SO THAT NOBODY READS IT BRIGHTER:
  on := onT in front. So "the table's promise in front gives the law's «on»" (t1) holds by its own
    letter: t1's content is hleftIs, left m ∈ Q (in hQ) and hokI.
  Rd := ridesNothing (q := True). So K5AtOn.promise and the law's "∧ Rd.q" SAY NOTHING here: ALL OF
    t2's CONTENT SITS IN k5_t2_piece (Johnson/Desc/First/Att/K05T2Piece.lean) AND ITS NAMED
    PREMISES.
  The law's LaidBehind is thrown away behind: the promise behind is had from the a in hand and the
  yes. THE PROMISE BEHIND COSTS NO ERROR: it holds at EVERY transcript with a yes: a deterministic
    carrying. Err.cap 128 is spent on the other half alone (Todo in front from R' behind), which is
    K05_law_one_guard's, untouched.
  UNBOUND LETTERS: D and rad are bound by nothing here, as in the law · that the table's N : Numbers
    is Wv's is said nowhere · yOf is idle · NOTHING TIES the law's ns (in Room) to nsPlan (K5Plan,
    K5Fill) · x.F.next + elems x.fs to first · x.fs and hS · pC and pD to the place x that lookAt
    returns: whoever calls the theorem picks them alike.
IT STANDS OVER THE GUARD (Johnson/Desc/First/Att/GuardN.lean: seven tests; its law stands at the link
2 * g + 1 with Wv.p4 = true): ONE LETTER m FOR THE BLOCK's LINK AND THE TABLE's SEGMENT,
with hm : m = 2 * g + 1 and hp4 : Wv.p4 = true.
WHAT STAYS A PREMISE, EACH BY NAME:
  of the law: hleftIs · hokI (K5AtOn.ok: the pin's item) · Bh : K5Behind at onT (worth · item).
  of t2: K5Place · K5Book · K5Plan · K5Fill · hQ (what the kind's row asks is open) · keptForms ·
  madeForms ·
    madeMore (Johnson/Desc/First/Att/K05T2.lean's head).
  of the seated block: PlanIs Wv, the block's own test, the guard, the written rounds
    (Johnson/Desc/First/Att/K05LawGuard.lean's binders).
Limits. A RULE OVER LETTERS: NONE OF THESE PREMISES IS SHOWN AT ANY FILLING OF THE TABLE's MEANING.
The piece stands over the carried record alone (get s := (π, s)). Stated at onAt, not at onQ. EMPTY
AT: a promise in front that holds of nothing: then GoodIn holds for nothing.
No soundness of the protocol is claimed. Nothing is claimed on completeness or hiding.

-/
import Johnson.Desc.First.Att.K05LawGuard
import Johnson.Desc.First.Att.K05T2Piece

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Att.P
open Iop Prob Cb IOR TWhole Cb.Fo Cb.LdLkp Cb.Pv.Att Cb.Pv.Att.End Inst.Model Inst.Model.AttSeg
open OnBytes OnBytes.Model OnBytes.Model.Road
open OnBytes.Tie.Pv.Att (recOf)
open OnBytes.Road.L5 (dimOf)
open OnBytes.Slice OnBytes.Flat OnBytes.Maker Run Fo.Peel
open VerifiableInference.Desc.First.Look (Sent attCaller attSg JAtt AttOK enMask lookAt)
open VerifiableInference.Desc.Sound (Frame Piece strsOf)
open VerifiableInference.Desc (Claim RoundAsG Place)
open VerifiableInference.Desc.First (Item Pub Meaning Numbers ModelPart onAt stepOpen pubStep rowOf pubRowOf
  pubRowM moreItem tiesOf)

/-- The table's promise at a border, with "no mark", over the piece's statements. -/
def onT {Pp Wt : Type} (N : Numbers) (Mg : Meaning Pp Wt) (links : List ModelPart) (π : Pp) (Fr : Frame)
    (p : Place) (O : List Item) (Q : List Pub) (a : First.S × Fr.E.Str) : Prop :=
  onAt N Mg links (some p) O Q (π, a.1) (strsOf Fr a.2) ∧ a.1.failed = none

/-- The promise that says nothing. -/
def ridesNothing (Fr : Frame) (base : ℕ) : Rides Fr base :=
  ⟨Unit, fun _ => (), fun _ _ _ => rfl, fun _ _ => True, fun _ _ _ _ _ => trivial⟩

open Classical in
/-- **THE KIND's LAW AT THE SEATED BLOCK, FROM THE TABLE's PROMISE IN FRONT TO THE TABLE's PROMISE
BEHIND.** -/
theorem K05_at_table {W Cl Pp Wt : Type} {Fr : Frame} (claim : Aff → Cl) {Wv : Verify.Public}
    (hP : PlanIs Wv) (hp4 : Wv.p4 = true) (g m : ℕ) (hm : m = 2 * g + 1) (before : List (ℕ × ℕ))
    (blk : VerifiableInference.Desc.Block First.S Claim)
    (hblk : k5AtN Wv m g before = some blk) (hok : blk.planOk = true)
    (hG : k5GuardN Wv m g = true) {a : Attention.Plan} (ha : Wv.A[g]? = some a)
    {x : VerifiableInference.Desc.First.Look.Place} (hx : lookAt Wv m false = some x) (D : Sent)
    (rad : OracleShape → Nat) (Ex : Iop.ExtSpec) (Wp : Type)
    (α : TX (Unit × Cb.Gl.E) Cb.Gl.E (Option (JAtt x.ns a.seam.tl)) → Cb.Gl.E) (ns base : ℕ)
    (ds : List RDT) (hds : List.Forall₂ RoundAsG ds (rounds (parO Wv m a before)))
    (tj : OnBytes.K.Kc.Tape)
    (x0 : First.S × Fr.E.Str → TX (Unit × Cb.Gl.E) Cb.Gl.E (Option (JAtt x.ns a.seam.tl)))
    (yOf : First.S × Fr.E.Str → Ex.Str) (gOf : First.S × Fr.E.Str → Forest.Heard)
    (plJ : ℕ → ℕ → JAtt x.ns a.seam.tl)
    (I : PinItemP Fr seatSO base W (attSg x D rad).Msg) (R' : First.S × Fr.E.Str → W → Prop)
    (N : Numbers) (Mg : Meaning Pp Wt) (links : List ModelPart) (π : Pp) (pl pl' : Place)
    (O : List Item) (Q : List Pub) (pC pD : Look.P) (hS : Forest.Shape) (arr : Array (ℕ × String))
    (first kr nsPlan : ℕ) (Ix : K5Place links m pl pl') (Bk : K5Book N pl pl')
    (Pn : K5Plan (parO Wv m a before).own m pC pD hS first kr nsPlan)
    (Fi : K5Fill Mg N π Fr base m O Q (parO Wv m a before).own pC pD arr first nsPlan)
    (hQ : ∀ q ∈ (pubRowOf links pl).asks, q ∈ Q)
    (keptForms : ∀ (s : First.S) (y : Fr.E.Str) (att : First.AttOwn) (hd : Heard) (G : Fork)
      (rs : List Fmt.RoundView), onAt N Mg links (some pl) O Q (π, s) (strsOf Fr y) → s.failed = none →
      s.here = .att att → hear (parO Wv m a before).own (att.F, rs, 0) = some (hd, G, [], 0) →
      ∀ i ∈ O, (rowOf links pl).ins.contains i = false → i ≠ .pinI → ∀ q ∈ tiesOf i,
        Mg.pub q (π, s) = true → Mg.pub q (π, behind s att hd G) = true)
    (madeForms : ∀ (s : First.S) (y : Fr.E.Str) (att : First.AttOwn) (hd : Heard) (G : Fork)
      (rs : List Fmt.RoundView), onAt N Mg links (some pl) O Q (π, s) (strsOf Fr y) → s.failed = none →
      s.here = .att att → hear (parO Wv m a before).own (att.F, rs, 0) = some (hd, G, [], 0) →
      ∀ q ∈ [Pub.formsInT m 3 "own", Pub.formsInT m 2 "planes", Pub.formsInT m 2 "join"],
        Mg.pub q (π, behind s att hd G) = true)
    (madeMore : ∀ (s : First.S) (y : Fr.E.Str) (att : First.AttOwn) (hd : Heard) (G : Fork)
      (rs : List Fmt.RoundView), onAt N Mg links (some pl) O Q (π, s) (strsOf Fr y) → s.failed = none →
      s.here = .att att → hear (parO Wv m a before).own (att.F, rs, 0) = some (hd, G, [], 0) →
      ∀ x ∈ (Mg.more.rows links pl).makes, Mg.pub (moreItem x) (π, behind s att hd G) = true ∧
        Mg.pubP (moreItem x) (π, behind s att hd G))
    (hleftIs : ∀ a' : First.S × Fr.E.Str, Mg.pubP (.left m) (π, a'.1) →
      K3LeftOutIs (VerifiableInference.Desc.K3.seatCalls claim).fork
        (VerifiableInference.Desc.K3.seatCalls claim).heard x.fs x.lm x.F.next
        (Cb.Fo.NumsEq.placeOf (enMask x.ns a.seam.tl) plJ)
        (fun F => Room F ns x.F.next
          (Forest.elems x.fs + (slotsOf (script (parO Wv m a before).own) + 0))) (x0 a') (gOf a') a'.1)
    (hokI : ∀ a', onT N Mg links π Fr pl O Q a' → I.ok (I.rc a'.1) a'.2)
    (Bh : K5Behind x a.seam.tl D rad Ex Wp α a (parO Wv m a before) ns base a.nW (plannedK a)
      (padOfO a.fs) tj gOf (onT N Mg links π Fr pl O Q) I R') :
    (⟨blk, base, ds, [], fun _ _ w => w, Err.cap 128 (uLT (ckP .two) ds)⟩ :
        Piece (ckP .two) Fr First.S Claim W).GoodIn
      (onT N Mg links π Fr pl O Q)
      (onT N Mg links π Fr pl' (stepOpen O (rowOf links pl)) (pubStep Q (pubRowM Mg.more links pl)))
      (fun a' w => ((closedOf (attBase x a.S a.seam.tl D rad)
          (attLin x a.S a.seam.tl D rad Ex Wp α ns
            (numsPlan (parO Wv m a before).own (x.F.next + Forest.elems x.fs))) ns
          (numsPlan (parO Wv m a before).own (x.F.next + Forest.elems x.fs))).own
          (theMeans Cb.Gl.E _ _ _)).ch.Todo (x0 a') (I.part w)) R' := by
  subst hm
  have hleftQ : Pub.left (2 * g + 1) ∈ Q := by
    refine hQ _ ?_
    rw [(k5_pubRow Ix).1]
    simp
  have hlaw := K05_law_one_guard claim hP hp4 g before blk hblk hok hG ha hx D rad Ex Wp α ns base ds
    hds tj x0 yOf gOf plJ (onT N Mg links π Fr pl O Q) I (ridesNothing Fr base) R'
    ⟨fun a' hon => hleftIs a' (onAt_pubP hon.1 hon.2 _ hleftQ), hokI, fun _ _ => trivial⟩ Bh
  have hD : DecidesK5 (⟨blk, base, ds, [], fun _ _ w => w, Err.cap 128 (uLT (ckP .two) ds)⟩ :
      Piece (ckP .two) Fr First.S Claim W) (parO Wv (2 * g + 1) a before) := by
    obtain ⟨a', ha', rfl⟩ := k5AtN_is Wv (2 * g + 1) g before blk hblk
    obtain rfl : a' = a := Option.some.inj (ha'.symm.trans ha)
    exact decides_k5_ok _ _ _ _ _ _
  refine goodIn_on'_mono _ hlaw fun a' τ b hon hout _ => ⟨?_, ?_⟩
  · exact k5_t2_piece N Mg links π _ (parO Wv (2 * g + 1) a before) hD (2 * g + 1) pl pl' O Q pC pD hS arr first kr nsPlan
      Ix Bk Pn Fi hQ keptForms madeForms madeMore a' b τ hon.1 hon.2 hout
  · exact k5_unmarked_stays _ (parO Wv (2 * g + 1) a before) hD a' b τ hout hon.2

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.K05_at_table
