-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K2/Law/GammaAtFront.lean: the kind "the code switch" (K2): THE
CHALLENGES OF A RUN's ROUNDS AT A WRITTEN SEGMENT's NUMBERS ARE THE CHALLENGES IN THE CARRIED ROWS
AT THE SWITCH's OWN FRONT: under the head's premise, at a reached state that the fold over the
sub-protocols in front returns AT THESE ROUNDS, at all three sorts of the kind's places. Statements
with their proofs; no definition. Two of the eight are closed facts, by the kernel.

  `varsW` BY THE KERNEL: at each of the 25 written segments the layout of the group of the segment's
                    public members (`groupLayout`, Johnson/Desc/K2/Honest/FoldEnd.lean;
                    `membersOfSeg`, Law/GroupMembers.lean) has as many row variables as the fold has
                    numbers
  `varsW_can_fail` A NEGATIVE LINE: with the next segment's members in their stead it holds at none
                    of the first 24
  `gamma_heard_of` AT LETTERS: an opening · `FrontTies Z fx` · the description's segments are the
                    written ones · the chain's cut is the written one · m < 25 · Sg is the written
                    segment m · `membersTrue fx.st fx.f.rows = membersOfSeg Sg (m != 0)` · the
                    carried rows have as many challenges as row variables · they are what R's rounds
                    from number `roundsAhead c.blocksInOrder (ixK10 m) + 2` on drew ⊢ `challengesOr0 (R.map
                    (·.drawn)) Sg.gamma = fx.f.rows.gamma.map readE`
  `count_behind_laid` l < 24: where the fold over the first 14 (l + 1) + 2 returns t₀: t₀'s walk's
                    frame's carried rows have as many challenges as row variables
  `count_behind_cleared` the like at 353
  `link_gamma_heard` the head `AtMgA` · m < 23 · a reached (`AtMg.rch`) at 14 (m + 1) + 2 · the
                    front fx that the switch's block takes off a's state · the fold over the first
                    14 (m + 1) + 2, at the rounds R, returns a's state · Sg is the written segment m
                    ⊢ that equation
  `head_gamma_heard` the same at 339, at the written segment 23
  `fin_gamma_heard` the same at 353, behind the quiet step in front, at the written segment 24

What it is for. The equation is the premise hγ of `claimTrue_at_segmentLeft`
(Law/ClaimAtClosing.lean), and the first "if" in `LockedAt` (Law/LockAtFront.lean), at heard :=
`R.map (·.drawn)`. It is said at EVERY Sg that is the written segment m: so it meets `LockedAt`'s
own Sg. No return of a prover's text is spent.

How the count is had. gamma's length is the carried layout's k (`LayFits.challenges`) · that is the
k of the description's own layout of the group (`FrontTies.lay`) · that is `groupLayout`'s at the
members at their true shapes (`groupLayout_true`, Johnson/Desc/K2/Honest/Carry/LayoutSame.lean) ·
these are the written segment's public members, and the codes are its own (`segmentsOf_at_front`,
Law/SegmentsAtFront.lean) · `varsW`.

By, beside these: `gammaTie_of`, `roundsAhead_written`, `gammaNumbersW` (Law/GammaHeard.lean) ·
`link_gamma_front`, `head_gamma_front`, `fin_gamma_front`
(Johnson/Desc/K2/Honest/Returns/GammaReached.lean) · `link_membersTrue_front` and its two like
(Returns/TrueMembersAtHead.lean) · `membersOfSeg_written` (Law/MembersJoin.lean) · `link_frontTies`
and its two like (Returns/FrontTiesReached.lean) · `segments_at_head` (Law/PlacesWritten.lean) · the
library's `tests_at_head` (Returns/UnderHead.lean), `number_is`
(Johnson/Desc/K10/Honest/KeepsSeat.lean), `tail_frame`, `closing_behind_cleared`,
`layFits_of_close`, `front_pin_link`, `front_nums_head`, `front_nums_fin`. NEAR, NOT CALLED:
`link_lay_reached` (Returns/ClosedReached.lean), `head_lay_reached`, `fin_lay_reached`
(Returns/ClosedArms.lean): `LayFits`, whose first field is the count, at "reached", at other forms
of the front: the two `count_behind_…` say it at a fold's return.

Limits. TWO PREMISES SPEAK OF ONE STATE: that it is reached (by the sub-protocols in their wrapped
form, at rounds under "there are") and that the fold returns it at R: nothing here gives either, nor
both together; no run is given at which the head's premise holds with them: the three laws under the
head could hold of nothing. THAT A PROVER's LIST OF CHALLENGES HEARD IS `R.map (·.drawn)` IS SAID
NOWHERE HERE. The negative line turns one thing. The full size and the format's second hash function alone.
Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.GammaHeard
import Johnson.Desc.ProofFile.Honest.K2.Law.MembersJoin
import Johnson.Desc.ProofFile.Honest.K2.Law.SegmentsAtFront
import Johnson.Desc.K2.Honest.Returns.GammaReached
import Johnson.Desc.K2.Honest.Carry.LayoutSame
import Johnson.Desc.K10.Honest.KeepsSeat

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K2.Law
open OnBytes
open OnBytes.Slice (readE)
open VerifiableInference.Desc (Block Chain FileDescription Grows foldBlocks)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K2.Honest (groupLayout membersTrue groupLayout_true)
open VerifiableInference.Desc.K2.Honest.Returns (FrontTies link_frontTies head_frontTies
  fin_frontTies layFits_of_close closing_behind_cleared tests_at_head link_gamma_front
  head_gamma_front fin_gamma_front link_membersTrue_front head_membersTrue_front
  fin_membersTrue_front)
open VerifiableInference.Desc.K13.Honest (roundsAhead)
open VerifiableInference.Desc.LinkJoin (offW)
open VerifiableInference.Desc.Sound (allOf EAll)
open VerifiableInference.PlanWritten (cutOf cutFirstFull)
open Meaning.K2 (tail_frame fold_cut fold_back front_pin_link front_nums_head front_nums_fin)
open Johnson.Prover.Link (drawnOf)
open OnBytes.Maker (WholeD)
open P5J (AtMgA F0T)
open LPFK10 (ixK10)

set_option maxRecDepth 1000000 in
/-- **BY THE KERNEL**: at each of the 25 written segments the layout of the group of the segment's
public members has as many row variables as the fold has numbers. -/
theorem varsW : ((List.range 25).all fun l =>
    match segsW[l]? with
    | some Sg => (groupLayout Sg.sizes.codes Sg.sizes.code Sg.sizes.maskCode
        (membersOfSeg Sg (l != 0))).k == Sg.gamma.length
    | none => false) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- A NEGATIVE LINE: with the next segment's members it holds at none of the first 24. -/
theorem varsW_can_fail : ((List.range 24).any fun l =>
    match segsW[l]?, segsW[l + 1]? with
    | some Sg, some Sn => (groupLayout Sg.sizes.codes Sg.sizes.code Sg.sizes.maskCode
        (membersOfSeg Sn true)).k == Sg.gamma.length
    | _, _ => true) = false := by
  decide +kernel

/-- **THE TIE ON THE CHALLENGES, AT LETTERS.** -/
theorem gamma_heard_of {o : SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription Inst} {Z : Pub}
    {Bs : PureBase} {base : List (Block S Cl)} {c : Chain S Cl} {A : SharedSeat} {B : SecondSeat}
    (O : IM.Open o pol lay KL F Z Bs base c A B) {fx : _root_.Tw.K2.Front} (Tf : FrontTies Z fx)
    (hseg : segmentsOf Z Bs.G₀ = segsW) (hcut : cutOf c.blocksInOrder = cutFirstFull) {m : Nat}
    (hm : m < 25) {Sg : SegmentPub} (hSg : segsW[m]? = some Sg)
    (hmem : membersTrue fx.st fx.f.rows = membersOfSeg Sg (m != 0))
    (hch : fx.f.rows.gamma.length = fx.f.rows.layout.k) {R : List Fmt.RoundView}
    (hG : fx.f.rows.gamma =
      ((R.drop (roundsAhead c.blocksInOrder (ixK10 m) + 2)).take fx.f.rows.gamma.length).map drawnOf) :
    challengesOr0 (R.map (·.drawn)) Sg.gamma = fx.f.rows.gamma.map readE := by
  obtain ⟨G, HL⟩ := Tf.lay
  have hin : Sg ∈ segmentsOf Z Bs.G₀ := by
    rw [hseg]
    exact List.mem_of_getElem? hSg
  obtain ⟨c1, c2, c3⟩ := segmentsOf_at_front O Tf hin
  have hv : (groupLayout Sg.sizes.codes Sg.sizes.code Sg.sizes.maskCode
      (membersOfSeg Sg (m != 0))).k = Sg.gamma.length := by
    have t := (List.all_eq_true.1 varsW) m (List.mem_range.2 hm)
    simp only [hSg] at t
    exact eq_of_beq t
  have hn : Sg.gamma = List.range' (offW (ixK10 m) + 2) Sg.gamma.length := by
    have t := (List.all_eq_true.1 gammaNumbersW) m (List.mem_range.2 hm)
    simp only [hSg] at t
    exact eq_of_beq t
  have hlen : fx.f.rows.gamma.length = Sg.gamma.length := by
    rw [hch, HL.k, ← (groupLayout_true fx.st G fx.f.rows HL.members HL.kept HL.sizes).1, hmem,
      ← c1, ← c2, ← c3]
    exact hv
  rw [roundsAhead_written hcut] at hG
  exact gammaTie_of hn hlen hG

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- Behind "laid" of the next segment the carried rows have as many challenges as row variables. -/
theorem count_behind_laid (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : Nat} (h24 : l < 24)
    {p : ProofFile.InstPub} {R R₀ : List Fmt.RoundView} {C C₀ : List VerifiableInference.Desc.OpenedColumn} {t₀ : S}
    (f₀ : foldBlocks 0 (c.blocksInOrder.take (14 * (l + 1) + 2)) (ProofFile.startS Z p) R C = .ok (t₀, R₀, C₀)) :
    t₀.check.frame.rows.gamma.length = t₀.check.frame.rows.layout.k := by
  obtain ⟨s, R₃, C₃, g3⟩ := fold_cut (k := 14 * l + 12) 4
    (by rw [show 14 * l + 12 + 4 = 14 * (l + 1) + 2 by omega]; exact f₀)
  obtain ⟨L, Q, rs, y, -, -, hy, hf⟩ := tail_frame hS hR O h24 g3 f₀
  rw [hf]
  exact (layFits_of_close hy (Grows.refl _)).challenges

/-- The like behind "cleared" of the last segment. -/
theorem count_behind_cleared (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    {p : ProofFile.InstPub} {R R₀ : List Fmt.RoundView} {C C₀ : List VerifiableInference.Desc.OpenedColumn} {t₀ : S}
    (f₀ : foldBlocks 0 (c.blocksInOrder.take 353) (ProofFile.startS Z p) R C = .ok (t₀, R₀, C₀)) :
    t₀.check.frame.rows.gamma.length = t₀.check.frame.rows.layout.k := by
  obtain ⟨w, Rw, Cw, Lw, Q, rs, x, -, -, -, hx, hf, -⟩ := closing_behind_cleared hS hR O f₀
  rw [hf]
  exact (layFits_of_close hx (Grows.refl _)).challenges

end

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **AT A SEGMENT's FIRST PLACE** (14 (m + 1) + 2, m < 23): under the head, at a state that is
reached and that the fold over the sub-protocols in front returns AT THE ROUNDS R: the challenges of
R at the written segment m's numbers are the carried rows'. -/
theorem link_gamma_heard (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {m : Nat} (h23 : m < 23)
    (a : ((F0T OnBytes.secondHashFunction Zp Np cF).XiPub × (F0T OnBytes.secondHashFunction Zp Np cF).S₁) ×
      (EAll (D.at OnBytes.Slice.frS.P.T.a) (allOf (D.at OnBytes.Slice.frS.P.T.a))).Str)
    (hr : h.toAtMg.rch (14 * (m + 1) + 2) a) {p : VerifiableInference.Desc.First.K2.P2}
    (hq : p.stands = .link) {fx : _root_.Tw.K2.Front}
    (hfx : VerifiableInference.Desc.First.K2.frontAt p a.1.2 = some fx)
    {z : ProofFile.InstPub} {R R₀ : List Fmt.RoundView} {C C₀ : List VerifiableInference.Desc.OpenedColumn}
    (f₀ : foldBlocks 0 (cF.blocksInOrder.take (14 * (m + 1) + 2)) (ProofFile.startS Zp z) R C =
      .ok (a.1.2, R₀, C₀))
    {Sg : SegmentPub} (hSg : segsW[m]? = some Sg) :
    challengesOr0 (R.map (·.drawn)) Sg.gamma = fx.f.rows.gamma.map readE := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have e12 : ixK10 m = 14 * m + 12 := by
    rw [ProofFile.Honest.K10.YesFree.number_is m, if_neg (by omega)]
  refine gamma_heard_of O
    (link_frontTies h.scope h.reads O h23 (h.toAtMg.rch_is_reach _ a hr) hq hfx)
    (segments_at_head h.toAtMg O) (tests_at_head h.toAtMg O).2.1 (by omega) hSg ?_ ?_ ?_
  · exact (link_membersTrue_front h h23 a hr hq hfx).trans
      (membersOfSeg_written (by omega) hSg).symm
  · obtain ⟨-, -, -, -, -, a6, -⟩ :=
      front_pin_link h.scope h.reads O (l := m + 1) (by omega) (by omega) f₀ hq hfx
    rw [a6]
    exact count_behind_laid h.scope h.reads O (by omega) f₀
  · rw [e12]
    exact link_gamma_front h.scope h.reads O h23 f₀ hq hfx

/-- **At the output head's front** (339): the written segment 23. -/
theorem head_gamma_heard (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (a : ((F0T OnBytes.secondHashFunction Zp Np cF).XiPub × (F0T OnBytes.secondHashFunction Zp Np cF).S₁) ×
      (EAll (D.at OnBytes.Slice.frS.P.T.a) (allOf (D.at OnBytes.Slice.frS.P.T.a))).Str)
    (hr : h.toAtMg.rch 339 a) {p : VerifiableInference.Desc.First.K2.P2}
    (hq : p.stands = .head) {fx : _root_.Tw.K2.Front}
    (hfx : VerifiableInference.Desc.First.K2.frontAt p a.1.2 = some fx)
    {z : ProofFile.InstPub} {R R₀ : List Fmt.RoundView} {C C₀ : List VerifiableInference.Desc.OpenedColumn}
    (f₀ : foldBlocks 0 (cF.blocksInOrder.take 339) (ProofFile.startS Zp z) R C = .ok (a.1.2, R₀, C₀))
    {Sg : SegmentPub} (hSg : segsW[23]? = some Sg) :
    challengesOr0 (R.map (·.drawn)) Sg.gamma = fx.f.rows.gamma.map readE := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have e12 : ixK10 23 = 334 := by
    rw [ProofFile.Honest.K10.YesFree.number_is 23, if_neg (by omega)]
  refine gamma_heard_of O
    (head_frontTies h.scope h.reads O (h.toAtMg.rch_is_reach _ a hr) hq hfx)
    (segments_at_head h.toAtMg O) (tests_at_head h.toAtMg O).2.1 (m := 23) (by omega) hSg ?_ ?_ ?_
  · exact (head_membersTrue_front h a hr hq hfx).trans
      (membersOfSeg_written (l := 23) (by omega) hSg).symm
  · obtain ⟨tm, Rm, Cm, fm⟩ := fold_back (k := 338) f₀
    obtain ⟨-, -, a3, -⟩ := front_nums_head h.scope h.reads O fm f₀ hq hfx
    rw [a3]
    exact count_behind_laid h.scope h.reads O (l := 23) (by omega) fm
  · rw [e12]
    exact head_gamma_front h.scope h.reads O f₀ hq hfx

/-- **At the front behind the last segment** (353): the written segment 24. -/
theorem fin_gamma_heard (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (a : ((F0T OnBytes.secondHashFunction Zp Np cF).XiPub × (F0T OnBytes.secondHashFunction Zp Np cF).S₁) ×
      (EAll (D.at OnBytes.Slice.frS.P.T.a) (allOf (D.at OnBytes.Slice.frS.P.T.a))).Str)
    (hr : h.toAtMg.rch 353 a) {t : S}
    (he : VerifiableInference.Desc.First.K2.finishFrontQ a.1.2 = .ok t)
    {p : VerifiableInference.Desc.First.K2.P2} (hq : p.stands = .finish)
    {fx : _root_.Tw.K2.Front} (hfx : VerifiableInference.Desc.First.K2.frontAt p t = some fx)
    {z : ProofFile.InstPub} {R R₀ : List Fmt.RoundView} {C C₀ : List VerifiableInference.Desc.OpenedColumn}
    (f₀ : foldBlocks 0 (cF.blocksInOrder.take 353) (ProofFile.startS Zp z) R C = .ok (a.1.2, R₀, C₀))
    {Sg : SegmentPub} (hSg : segsW[24]? = some Sg) :
    challengesOr0 (R.map (·.drawn)) Sg.gamma = fx.f.rows.gamma.map readE := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have e12 : ixK10 24 = 350 := by
    rw [ProofFile.Honest.K10.YesFree.number_is 24, if_pos rfl]
  refine gamma_heard_of O
    (fin_frontTies h.scope h.reads O (h.toAtMg.rch_is_reach _ a hr) he hq hfx)
    (segments_at_head h.toAtMg O) (tests_at_head h.toAtMg O).2.1 (m := 24) (by omega) hSg ?_ ?_ ?_
  · exact (fin_membersTrue_front h a hr he hq hfx).trans
      (membersOfSeg_written (l := 24) (by omega) hSg).symm
  · obtain ⟨-, -, a3, -⟩ := front_nums_fin h.scope h.reads O f₀ he hq hfx
    rw [a3]
    exact count_behind_cleared h.scope h.reads O f₀
  · rw [e12]
    exact fin_gamma_front h.scope h.reads O f₀ he hq hfx

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.varsW
#print axioms ProofFile.Honest.K2.Law.varsW_can_fail
#print axioms ProofFile.Honest.K2.Law.gamma_heard_of
#print axioms ProofFile.Honest.K2.Law.count_behind_laid
#print axioms ProofFile.Honest.K2.Law.count_behind_cleared
#print axioms ProofFile.Honest.K2.Law.link_gamma_heard
#print axioms ProofFile.Honest.K2.Law.head_gamma_heard
#print axioms ProofFile.Honest.K2.Law.fin_gamma_heard
