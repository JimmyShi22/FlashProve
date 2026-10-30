-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K2/Law/MembersAtWalk.lean: the kind "the code switch" (K2): WHERE AN
HONEST PROVER's CLOSING's WALK OVER THE WRITTEN SEGMENTS IN FRONT OF A SWITCH RETURNS: ITS LAST
STEP, AND THE MEMBERS OF THE ROWS MADE THERE, AT THE SWITCH's OWN FRONT, UNDER THE HEAD's PREMISE,
AT ALL THREE SORTS OF THE KIND's PLACES. One definition (a proposition); statements with their
proofs: joins.

  `LastStep` `LastStep table own heard k m y M`: there are Sg, y', W, kept with: Sg is the written
                    segment number m (`segsW`, Law/PlacesWritten.lean) · the walk over `segsW.take
                    m` from the start returns y' · y hands (W, kept) on · AT prev := `y'.1.map
                    (·.1)`, prevKept := `(y'.1.map (·.2)).getD []`, base := `y'.2`: `segmentLeft
                    table Sg prev prevKept (own (0 + m)) heard k base = .ok (W, kept)` · whatever R
                    `segmentGroupRows` returns at these terms has `R.members = M`
  `lastStep_of` m < 25 · the walk over `segsW.take (m + 1)` from the start returns y · a law that
                    gives `R.members = M` at the written segment m and at a fold in front just where
                    m is not 0 ⊢ `LastStep … m y M`
  `link_lastStep` the head `AtMgA` · m < 23 · a reached (`AtMg.rch`) at 14 (m + 1) + 2 · the front
                    fx that the switch's block takes off a's state · the walk over `segsW.take (m +
                    1)` returns y ⊢ `LastStep … m y (membersTrue fx.st fx.f.rows)`
  `head_lastStep` the same at 339, at the walk over `segsW.take (23 + 1)`
  `fin_lastStep` the same at 353, behind the quiet step in front, at the walk over `segsW.take (24 +
                    1)`

What it is for. `claimTrue_at_segmentLeft` (Law/ClaimAtClosing.lean) asks a return of `segmentLeft`
(its h) and, first in its hR, that the rows' members are `membersTrue`. `LastStep` at M :=
`membersTrue fx.st fx.f.rows` holds both, at one Sg and at prev, prevKept and base AS TERMS OF THE
SHORTER WALK's RETURN: so that a law on the rows' entries that names that return meets it at the
same call of `segmentGroupRows`.

By: `closingFrom_take` (Law/ClosingAtTake.lean) · `link_members_front`, `head_members_front`,
`fin_members_front` (Law/MembersJoin.lean) · the second clause of `fencesW` (Law/TiesWritten.lean):
there are 25 written segments.

Limits. THAT THE WALK RETURNS IS A PREMISE. That a place's closing calls the walk at just these
segments (`segs.take p.link`, with the segments the written ones and p.link = m + 1) is not typed
here. No run is given at which the head's premise and "reached" hold together. Nothing on the rows'
entries, nor on the challenges. The full size alone. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.MembersJoin
import Johnson.Desc.ProofFile.Honest.K2.Law.ClosingAtTake
import Johnson.Desc.ProofFile.Honest.K2.Law.TiesWritten

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K2.Law
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K2.Honest (GroupMember Left membersTrue)
open VerifiableInference.Desc.Sound (allOf EAll)
open OnBytes.Maker (WholeD)
open P5J (AtMgA F0T)

/-- **What is said of the walk's last step**: the walk over the first m written segments returns
some y'; the last step is `segmentLeft` at the written segment number m, at what y' hands on; the
walk hands on what that returned; and whatever rows `segmentGroupRows` makes there have the members M. -/
def LastStep (table : FreshTable) (own : Nat → Nat → Nat → Nat → Cb.Gl.E)
    (heard : List Fmt.Drawn) (k : Nat → Except String Stretch) (m : Nat)
    (y : Option (Left × List OnBytes.OracleShape) × Nat) (M : List GroupMember) : Prop :=
  ∃ (Sg : SegmentPub) (y' : Option (Left × List OnBytes.OracleShape) × Nat) (W : Left)
    (kept : List OnBytes.OracleShape),
    segsW[m]? = some Sg ∧ closingFrom table own heard k (segsW.take m) 0 0 none = .ok y' ∧
    y.1 = some (W, kept) ∧
    segmentLeft table Sg (y'.1.map (·.1)) ((y'.1.map (·.2)).getD []) (own (0 + m)) heard k y'.2 =
      .ok (W, kept) ∧
    ∀ R, segmentGroupRows table Sg (y'.1.map (·.1)) ((y'.1.map (·.2)).getD []) (own (0 + m)) k y'.2
      true = .ok R → R.members = M

/-- From a law on the rows' members at the written segment m to the walk's last step. -/
theorem lastStep_of {table : FreshTable} {own : Nat → Nat → Nat → Nat → Cb.Gl.E}
    {heard : List Fmt.Drawn} {k : Nat → Except String Stretch} {m : Nat} (hm : m < 25)
    {y : Option (Left × List OnBytes.OracleShape) × Nat} {M : List GroupMember}
    (hy : closingFrom table own heard k (segsW.take (m + 1)) 0 0 none = .ok y)
    (key : ∀ (Sg : SegmentPub) (prev : Option Left) (prevKept : List OnBytes.OracleShape)
      (base : Nat) (R : GroupRows), segsW[m]? = some Sg → prev.isSome = (m != 0) →
      segmentGroupRows table Sg prev prevKept (own (0 + m)) k base true = .ok R → R.members = M) :
    LastStep table own heard k m y M := by
  have hlt : m < segsW.length := by rw [fencesW.2.1]; exact hm
  obtain ⟨y', W, kept, -, hA, hx, hp, hW, -⟩ :=
    closingFrom_take (List.getElem?_eq_getElem hlt) hy
  exact ⟨_, y', W, kept, List.getElem?_eq_getElem hlt, hA, hx, hW,
    fun R hR => key _ _ _ _ R (List.getElem?_eq_getElem hlt)
      (by rw [Option.isSome_map]; exact hp) hR⟩

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **At a segment's first place**: under the head, at the front that the switch's block takes off a
state reached at 14 (m + 1) + 2, m < 23, and at a walk over the first m + 1 written segments that
returns. -/
theorem link_lastStep (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {m : Nat} (h23 : m < 23)
    (a : ((F0T OnBytes.secondHashFunction Zp Np cF).XiPub × (F0T OnBytes.secondHashFunction Zp Np cF).S₁) ×
      (EAll (D.at OnBytes.Slice.frS.P.T.a) (allOf (D.at OnBytes.Slice.frS.P.T.a))).Str)
    (hr : h.toAtMg.rch (14 * (m + 1) + 2) a) {p : VerifiableInference.Desc.First.K2.P2}
    (hq : p.stands = .link) {fx : _root_.Tw.K2.Front}
    (hfx : VerifiableInference.Desc.First.K2.frontAt p a.1.2 = some fx)
    {table : FreshTable} {own : Nat → Nat → Nat → Nat → Cb.Gl.E} {heard : List Fmt.Drawn}
    {k : Nat → Except String Stretch} {y : Option (Left × List OnBytes.OracleShape) × Nat}
    (hy : closingFrom table own heard k (segsW.take (m + 1)) 0 0 none = .ok y) :
    LastStep table own heard k m y (membersTrue fx.st fx.f.rows) :=
  lastStep_of (by omega) hy fun _ _ _ _ _ hSg hp hR =>
    link_members_front h h23 a hr hq hfx hSg hp hR

/-- **At the output head's front** (339): the walk over the first 24 written segments. -/
theorem head_lastStep (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (a : ((F0T OnBytes.secondHashFunction Zp Np cF).XiPub × (F0T OnBytes.secondHashFunction Zp Np cF).S₁) ×
      (EAll (D.at OnBytes.Slice.frS.P.T.a) (allOf (D.at OnBytes.Slice.frS.P.T.a))).Str)
    (hr : h.toAtMg.rch 339 a) {p : VerifiableInference.Desc.First.K2.P2}
    (hq : p.stands = .head) {fx : _root_.Tw.K2.Front}
    (hfx : VerifiableInference.Desc.First.K2.frontAt p a.1.2 = some fx)
    {table : FreshTable} {own : Nat → Nat → Nat → Nat → Cb.Gl.E} {heard : List Fmt.Drawn}
    {k : Nat → Except String Stretch} {y : Option (Left × List OnBytes.OracleShape) × Nat}
    (hy : closingFrom table own heard k (segsW.take (23 + 1)) 0 0 none = .ok y) :
    LastStep table own heard k 23 y (membersTrue fx.st fx.f.rows) :=
  lastStep_of (by omega) hy fun _ _ _ _ _ hSg hp hR =>
    head_members_front h a hr hq hfx hSg hp hR

/-- **At the front behind the last segment** (353): the walk over all 25 written segments. -/
theorem fin_lastStep (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (a : ((F0T OnBytes.secondHashFunction Zp Np cF).XiPub × (F0T OnBytes.secondHashFunction Zp Np cF).S₁) ×
      (EAll (D.at OnBytes.Slice.frS.P.T.a) (allOf (D.at OnBytes.Slice.frS.P.T.a))).Str)
    (hr : h.toAtMg.rch 353 a) {t : S}
    (he : VerifiableInference.Desc.First.K2.finishFrontQ a.1.2 = .ok t)
    {p : VerifiableInference.Desc.First.K2.P2} (hq : p.stands = .finish)
    {fx : _root_.Tw.K2.Front} (hfx : VerifiableInference.Desc.First.K2.frontAt p t = some fx)
    {table : FreshTable} {own : Nat → Nat → Nat → Nat → Cb.Gl.E} {heard : List Fmt.Drawn}
    {k : Nat → Except String Stretch} {y : Option (Left × List OnBytes.OracleShape) × Nat}
    (hy : closingFrom table own heard k (segsW.take (24 + 1)) 0 0 none = .ok y) :
    LastStep table own heard k 24 y (membersTrue fx.st fx.f.rows) :=
  lastStep_of (by omega) hy fun _ _ _ _ _ hSg hp hR =>
    fin_members_front h a hr he hq hfx hSg hp hR

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.LastStep
#print axioms ProofFile.Honest.K2.Law.lastStep_of
#print axioms ProofFile.Honest.K2.Law.link_lastStep
#print axioms ProofFile.Honest.K2.Law.head_lastStep
#print axioms ProofFile.Honest.K2.Law.fin_lastStep
