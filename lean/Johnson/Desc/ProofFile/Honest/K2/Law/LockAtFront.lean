-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K2/Law/LockAtFront.lean: the kind "the code switch" (K2): THE LAW THAT
TIES THE CLAIM AT `leftAt` OF THE WORDS TO THE CLAIM AT WHAT AN HONEST PROVER's CLOSING RETURNS
(`claimTrue_at_segmentLeft`, Law/ClaimAtClosing.lean), WITH TWELVE OF ITS FOURTEEN PREMISES AND THE
FIRST CLAUSE OF A THIRTEENTH LAID IN (NOT THE TIE ON THE CHALLENGES HEARD, NOR THE CLAUSES ON
ENTRIES), AT A SWITCH's OWN FRONT, UNDER THE HEAD's PREMISE, AT ALL THREE SORTS OF THE KIND's
PLACES. One definition (a proposition); statements with their proofs: an assembly of laws typed
elsewhere.

  `LockedAt` `LockedAt table own heard k m y fx`: there are Sg, y', W, kept with: Sg is the written
                    segment number m · the walk over `segsW.take m` from the start returns y' · y
                    hands (W, kept) on · `segmentLeft` at Sg, at what y' hands on, returned (W,
                    kept) · AND, at every target T and all words w: IF the challenges heard at Sg's
                    numbers are the carried rows' (`challengesOr0 heard Sg.gamma =
                    fx.f.rows.gamma.map readE`) AND, at whatever R `segmentGroupRows` returns there, the
                    rows' main and mask entries at real rows and the entries of the mask sent ahead
                    at every row below 2 ^ h are the words', THEN `ClaimTrue` at `leftAt fx.st
                    fx.f.rows w` ↔ `ClaimTrue` at W
  `lockedAt_of` AT LETTERS: an opening · `FrontTies Z fx` · the description's segments are the
                    written ones · `LastStep … m y (membersTrue fx.st fx.f.rows)` ⊢ `LockedAt … m y
                    fx`
  `link_lockedAt` the head `AtMgA` · m < 23 · a reached (`AtMg.rch`) at 14 (m + 1) + 2 · the front
                    fx that the switch's block takes off a's state · the walk over `segsW.take (m +
                    1)` returns y ⊢ `LockedAt … m y fx`
  `head_lockedAt` the same at 339, at the walk over `segsW.take (23 + 1)`
  `fin_lockedAt` the same at 353, behind the quiet step in front, at the walk over `segsW.take (24 +
                    1)`

Which of the law's fourteen premises comes whence. h and the first clause of hR: `LastStep`
(Law/MembersAtWalk.lean) · hc, hcode, hmask: `segmentsOf_at_front` (Law/SegmentsAtFront.lean), with
`segments_at_head` (Law/PlacesWritten.lean) · hm, hk, hs, l1 to l4, hp: `FrontTies`
(Johnson/Desc/K2/Honest/Returns/FrontTiesReached.lean: `link_frontTies`, `head_frontTies`,
`fin_frontTies`). LEFT, AS THE TWO "IF" IN `LockedAt`: hγ, and the three clauses of hR on entries.

Limits. AN "↔" BETWEEN TWO CLAIMS, UNDER TWO HYPOTHESES THAT THIS FILE DOES NOT PAY: NEITHER CLAIM
IS HAD HERE. The first hypothesis is had in Law/GammaAtFront.lean, at the list of the challenges of
a run's own rounds; the second, on the entries against a witness's words, was had in no file when
this was written. THAT THE WALK RETURNS IS A PREMISE. That a place's closing calls the walk at just
these segments is not typed here. No run is given at which the head's premise and "reached" hold
together: as far as this file goes, the three laws under the head could hold of nothing. The three
clauses on entries stand typed a second time here, at S := fx.st and old := fx.f.rows:
`lockedAt_of`'s proof hands them to the law as they are. The full size alone. Nothing on tails.
Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.MembersAtWalk
import Johnson.Desc.ProofFile.Honest.K2.Law.SegmentsAtFront
import Johnson.Desc.ProofFile.Honest.K2.Law.ClaimAtClosing

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K2.Law
open OnBytes
open OnBytes.Slice (GE readE)
open OnBytes.Means (Words)
open VerifiableInference.Desc (Block Chain FileDescription)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K2.Honest (Left ClaimTrue sizesAt leftAt membersTrue)
open VerifiableInference.Desc.K2.Honest.Returns (FrontTies link_frontTies head_frontTies
  fin_frontTies)
open VerifiableInference.Desc.Sound (allOf EAll)
open OnBytes.Maker (WholeD)
open P5J (AtMgA F0T)

/-- **THE LOCK WITH ITS TIES ON CODES, LAYOUT AND MEMBERS LAID IN**, at a front fx and at a walk
over the first m + 1 written segments that returned y: y hands on some (W, kept), which
`segmentLeft` returned at the written segment m; and, at every target T and all words w: IF the
challenges heard at that segment's numbers are the carried rows', AND the entries of whatever rows
`segmentGroupRows` makes there are the words', THEN the claim at `leftAt` of the words is the claim at W.
-/
def LockedAt (table : FreshTable) (own : Nat → Nat → Nat → Nat → Cb.Gl.E)
    (heard : List Fmt.Drawn) (k : Nat → Except String Stretch) (m : Nat)
    (y : Option (Left × List OracleShape) × Nat) (fx : _root_.Tw.K2.Front) : Prop :=
  ∃ (Sg : SegmentPub) (y' : Option (Left × List OracleShape) × Nat) (W : Left)
    (kept : List OracleShape),
    segsW[m]? = some Sg ∧ closingFrom table own heard k (segsW.take m) 0 0 none = .ok y' ∧
    y.1 = some (W, kept) ∧
    segmentLeft table Sg (y'.1.map (·.1)) ((y'.1.map (·.2)).getD []) (own (0 + m)) heard k y'.2 =
      .ok (W, kept) ∧
    ∀ (T : SwitchTarget) (w : Words GE),
      challengesOr0 heard Sg.gamma = fx.f.rows.gamma.map readE →
      (∀ R, segmentGroupRows table Sg (y'.1.map (·.1)) ((y'.1.map (·.2)).getD []) (own (0 + m)) k y'.2
          true = .ok R →
        (∀ i b j, i < fx.f.rows.layout.members.size →
          b < (fx.st.oracles.getD (fx.f.rows.layout.members.getD i noId) default).shape.mainRows →
          (R.rows.getD i zeroMessage).main
              ((fx.st.oracles.getD (fx.f.rows.layout.members.getD i noId) default).shape.mainDeg
                == 3) b j =
            w (fx.f.rows.layout.members.getD i noId) .main (b + j * 2 ^ ceilLog2
              (fx.st.oracles.getD (fx.f.rows.layout.members.getD i noId)
                default).shape.mainRows)) ∧
        (∀ i b j, i < fx.f.rows.layout.members.size →
          b < (fx.st.oracles.getD (fx.f.rows.layout.members.getD i noId) default).shape.maskRows →
          (R.rows.getD i zeroMessage).mask b j =
            w (fx.f.rows.layout.members.getD i noId) .mask (b + j * 2 ^ ceilLog2
              (fx.st.oracles.getD (fx.f.rows.layout.members.getD i noId)
                default).shape.maskRows)) ∧
        ∀ b j, b < 2 ^ fx.f.rows.layout.h →
          (R.fresh.getD zeroMessage).mask b j = w fx.f.rows.fresh .mask
            (b + j * 2 ^ ceilLog2 (fx.st.oracles.getD fx.f.rows.fresh default).shape.maskRows)) →
      (ClaimTrue (sizesAt fx.st fx.f.rows T) fx.f.rows (leftAt fx.st fx.f.rows w) ↔
        ClaimTrue (sizesAt fx.st fx.f.rows T) fx.f.rows W)

/-- **The assembly, at letters**: the front's public ties, the walk's last step with the members'
clause, and "the description's segments are the written ones" give `LockedAt`. -/
theorem lockedAt_of {o : SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription Inst} {Z : Pub}
    {Bs : PureBase} {base : List (Block S Cl)} {c : Chain S Cl} {A : SharedSeat} {B : SecondSeat}
    (O : IM.Open o pol lay KL F Z Bs base c A B) {fx : _root_.Tw.K2.Front} (Tf : FrontTies Z fx)
    (hseg : segmentsOf Z Bs.G₀ = segsW) {table : FreshTable}
    {own : Nat → Nat → Nat → Nat → Cb.Gl.E} {heard : List Fmt.Drawn}
    {k : Nat → Except String Stretch} {m : Nat} {y : Option (Left × List OracleShape) × Nat}
    (L : LastStep table own heard k m y (membersTrue fx.st fx.f.rows)) :
    LockedAt table own heard k m y fx := by
  obtain ⟨Sg, y', W, kept, hSg, hA, hy, hW, hM⟩ := L
  obtain ⟨G, HL⟩ := Tf.lay
  have hmem : Sg ∈ segmentsOf Z Bs.G₀ := by
    rw [hseg]
    exact List.mem_of_getElem? hSg
  obtain ⟨c1, c2, c3⟩ := segmentsOf_at_front O Tf hmem
  refine ⟨Sg, y', W, kept, hSg, hA, hy, hW, fun T w hγ hE => ?_⟩
  exact claimTrue_at_segmentLeft fx.st G fx.f.rows T w hW c1 c2 c3 hγ HL.members HL.kept HL.sizes
    HL.k HL.h HL.mainFirst HL.maskFirst Tf.pow fun R hR => ⟨hM R hR, hE R hR⟩

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **At a segment's first place** (14 (m + 1) + 2, m < 23). -/
theorem link_lockedAt (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {m : Nat} (h23 : m < 23)
    (a : ((F0T OnBytes.secondHashFunction Zp Np cF).XiPub × (F0T OnBytes.secondHashFunction Zp Np cF).S₁) ×
      (EAll (D.at OnBytes.Slice.frS.P.T.a) (allOf (D.at OnBytes.Slice.frS.P.T.a))).Str)
    (hr : h.toAtMg.rch (14 * (m + 1) + 2) a) {p : VerifiableInference.Desc.First.K2.P2}
    (hq : p.stands = .link) {fx : _root_.Tw.K2.Front}
    (hfx : VerifiableInference.Desc.First.K2.frontAt p a.1.2 = some fx)
    {table : FreshTable} {own : Nat → Nat → Nat → Nat → Cb.Gl.E} {heard : List Fmt.Drawn}
    {k : Nat → Except String Stretch} {y : Option (Left × List OracleShape) × Nat}
    (hy : closingFrom table own heard k (segsW.take (m + 1)) 0 0 none = .ok y) :
    LockedAt table own heard k m y fx := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  exact lockedAt_of O
    (link_frontTies h.scope h.reads O h23 (h.toAtMg.rch_is_reach _ a hr) hq hfx)
    (segments_at_head h.toAtMg O) (link_lastStep h h23 a hr hq hfx hy)

/-- **At the output head's front** (339). -/
theorem head_lockedAt (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (a : ((F0T OnBytes.secondHashFunction Zp Np cF).XiPub × (F0T OnBytes.secondHashFunction Zp Np cF).S₁) ×
      (EAll (D.at OnBytes.Slice.frS.P.T.a) (allOf (D.at OnBytes.Slice.frS.P.T.a))).Str)
    (hr : h.toAtMg.rch 339 a) {p : VerifiableInference.Desc.First.K2.P2}
    (hq : p.stands = .head) {fx : _root_.Tw.K2.Front}
    (hfx : VerifiableInference.Desc.First.K2.frontAt p a.1.2 = some fx)
    {table : FreshTable} {own : Nat → Nat → Nat → Nat → Cb.Gl.E} {heard : List Fmt.Drawn}
    {k : Nat → Except String Stretch} {y : Option (Left × List OracleShape) × Nat}
    (hy : closingFrom table own heard k (segsW.take (23 + 1)) 0 0 none = .ok y) :
    LockedAt table own heard k 23 y fx := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  exact lockedAt_of O (head_frontTies h.scope h.reads O (h.toAtMg.rch_is_reach _ a hr) hq hfx)
    (segments_at_head h.toAtMg O) (head_lastStep h a hr hq hfx hy)

/-- **At the front behind the last segment** (353). -/
theorem fin_lockedAt (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (a : ((F0T OnBytes.secondHashFunction Zp Np cF).XiPub × (F0T OnBytes.secondHashFunction Zp Np cF).S₁) ×
      (EAll (D.at OnBytes.Slice.frS.P.T.a) (allOf (D.at OnBytes.Slice.frS.P.T.a))).Str)
    (hr : h.toAtMg.rch 353 a) {t : S}
    (he : VerifiableInference.Desc.First.K2.finishFrontQ a.1.2 = .ok t)
    {p : VerifiableInference.Desc.First.K2.P2} (hq : p.stands = .finish)
    {fx : _root_.Tw.K2.Front} (hfx : VerifiableInference.Desc.First.K2.frontAt p t = some fx)
    {table : FreshTable} {own : Nat → Nat → Nat → Nat → Cb.Gl.E} {heard : List Fmt.Drawn}
    {k : Nat → Except String Stretch} {y : Option (Left × List OracleShape) × Nat}
    (hy : closingFrom table own heard k (segsW.take (24 + 1)) 0 0 none = .ok y) :
    LockedAt table own heard k 24 y fx := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  exact lockedAt_of O
    (fin_frontTies h.scope h.reads O (h.toAtMg.rch_is_reach _ a hr) he hq hfx)
    (segments_at_head h.toAtMg O) (fin_lastStep h a hr he hq hfx hy)

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.LockedAt
#print axioms ProofFile.Honest.K2.Law.lockedAt_of
#print axioms ProofFile.Honest.K2.Law.link_lockedAt
#print axioms ProofFile.Honest.K2.Law.head_lockedAt
#print axioms ProofFile.Honest.K2.Law.fin_lockedAt
