-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/W/MaskEllHead.lean: CONDITIONAL. Statements with their proofs.

What is here. THE LENGTH OF THE MASK ROW OF THE SEGMENT OF THE FEED-FORWARD LAYERS' OWN ROUNDS
(sub-protocol K4) AS A NUMBER, AND A FENCE AGAINST ITS LAST PLACE, under the library's hypothesis h
on the public files. `maskEll_head`: at each of the twelve groups the library's `maskEllAt`
(Johnson/Road/K4/Rec/MaskEllB.lean) at the library's `P5J.At.sentAt Zp`, at any radii, at segment 2
g, IS 8192. `slotsSharp_head`: a group's plan's number of entries of the mask row, AND ONE MORE, is
at most 8192. So, under `MaskRowPub` (Law/W/MaskSixHead.lean): the mask code's length at the member
u's shape is 8192 (`maskRow_ell_is`), and the lookup's place's number of entries, and one more, is
within it (`maskRow_fence`): NO ENTRY BELOW xl.ns IS THE ROW's LAST PLACE, which is the pad's place
by the library's test `padB` (Johnson/Desc/SeatAt.lean: at one answer).
How. `maskEll_head`: under h five parts of the public parameters are the library's written values
(`written_of_head`, Johnson/Road/K4/K4HeadWritten.lean); the length reads the codes and the
request's shape alone (`maskEllP_pin0`, K4PinsAnyRad.lean; `maskEllP_free`, K4PinsClosed.lean); at
the written values it is a closed fact by Lean's kernel (`ell_written`, K4PinsWrittenMask.lean): the
step that stands inside the library's `closed_at` (K4PinsPaid.lean), by a name. `slotsSharp_head`:
proved here anew, as the library proves `slots_plain` and `slots_paid` (K4PinsSlots.lean), and ended
one step earlier: the maker of the built segments refuses unless a segment's entries AND THE
ANSWERS' PADS have room (`built_ns_le`, Rec/BuiltTests.lean); the library's two end in «at most
8192» and drop the answers; here the number of answers of the written request's shape (the field
answers of `ReqShape`, not that of a message's shape) is 1 (`answers_written`: a closed fact by
Lean's kernel).

Not shown here. THAT THE ENTRIES WHICH THE MEMBER's ROUNDS SPEND LIE BELOW xl.ns: so the fence is
one step, not the whole way, to «the rounds never read the pad»; Law/W/MaskBelowHead.lean has the
other step of the entries that the tie `K4MaskTieAt` asks, where the thread stands. h, the library's
hypothesis `P5J.AtMgA` on the public files, is the only hypothesis of `maskEll_head` beside g < 12,
and of `slotsSharp_head` beside g < 12 and that the group has a plan (hG). That h can hold: the side
library AtFullSide proves, with no hypothesis, that h has a member at one place
(AtFullSide.Top.headMember_zFull, AtFullSide/Top/HeadMemberAtFull.lean, whose own Limits say what it
is worth). `MaskRowPub`, hl and hns follow from h and `LaidK4` (`maskRow_laid`,
Law/W/MaskRowAtSeg.lean): in the last two h and `LaidK4` alone are open. THE FULL SIZE ALONE, and
the format's second hash function alone. Beneath the four stand closed facts by Lean's own kernel
(`decide +kernel`): `ell_written`, `maskEll_written`, `shape_one` in the library and
`answers_written` here; the written values rest on prints of Lean's evaluator (their files' heads);
no independent checker has replayed them. `slotsSharp_head` CALLS BY NAME A STATEMENT OF A FILE
UNDER Johnson/Goal/ (`Meaning.scope_plans`), as the library's `slots_paid` does. A program's walk
from import to import, which reads import lines alone and stops unopened at Johnson/Goal/,
ThirdParty/, Johnson/D/, Johnson/Bridge/ and Cb/Bridge*, stopped at 70 modules under Johnson/Goal/,
at 7 under Johnson/Bridge/ and at 1 that begins Cb.Bridge, and saw 46 whose names hold RecCompile:
floors. A LAW, NOT A PART: no file that defines a part of the proof file's description may import
this one. Nothing on soundness, on completeness or on any other property. No property is claimed.

  `maskEll_head`   **the length is 8192, at each group**
  `answers_written`   a closed fact: the written request's shape has one answer
  `slotsSharp_head`   **a plan's entries and one more are at most 8192**
  `maskRow_ell_is`, `maskRow_fence`   **at the member u and the place xl**
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.W.MaskRowAtSeg
import Johnson.Road.K4.K4HeadWritten
import Johnson.Road.K4.K4PinsSlots
import Johnson.Road.K4.K4PinsWrittenMask

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4.W
open OnBytes OnBytes.Model
open Johnson.Pack (pMask)
open Johnson.G (layoutFull)
open OnBytes.Desc.First.K4 (Par)
open OnBytes.Road.K4 (parOf written_of_head shape_one maskEll_written ell_written seatW pin0
  maskEllP_pin0 maskEllP_free)
open OnBytes.Road.K4.Rec (RecPlan maskEllAt maskEllP)
open OnBytes.Maker (WholeD)
open VerifiableInference.PlanWritten (proofSizedFull)
open VerifiableInference.Desc (Chain Block)
open VerifiableInference.Desc.First.Look (Sent)
open VerifiableInference.Desc.Sound (Mem)
open P5J (AtMgA TS)
open ProofFile.Honest.K4.SeatedHead (LaidK4)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place}

/-- CONDITIONAL on h and hg. **THE LENGTH OF THE SEGMENT's MASK ROW IS 8192**, at any radii. -/
theorem maskEll_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {g : ℕ} (hg : g < 12)
    (rad : OracleShape → ℕ) : maskEllAt (P5J.At.sentAt Zp) rad (2 * g) = 8192 := by
  have W := written_of_head h.toAtMg
  have d : P5J.At.sentAt Zp = ⟨proofSizedFull.codes, proofSizedFull.request, layoutFull,
      Zp.made.p.built.links.map (·.arrayOf)⟩ := by
    unfold P5J.At.sentAt P5J.At.cs P5J.At.shape P5J.At.layout
    rw [show Zp.made.p.chains.proof.first.codes = proofSizedFull.codes from W.codes,
      show Zp.made.p.chains.proof.first.shape = proofSizedFull.request from
        W.shape.trans shape_one,
      show Zp.made.p.chains.proof.first.layout = layoutFull from W.layout]
  rw [d]
  have e1 : maskEllAt (⟨proofSizedFull.codes, proofSizedFull.request, layoutFull,
        Zp.made.p.built.links.map (·.arrayOf)⟩ : Sent) rad (2 * g) =
      maskEllP (pin0 (⟨proofSizedFull.codes, proofSizedFull.request, layoutFull,
        Zp.made.p.built.links.map (·.arrayOf)⟩ : Sent) (seatW (2 * g)) (2 * g)) :=
    maskEllP_pin0 (C := Empty) _ rad (2 * g) (seatW (2 * g)) (fun e _ _ => e.elim)
      (fun _ => (false, 0, 0))
  rw [e1]
  exact (maskEllP_free _ _ _ _ #[] _ _ (seatW (2 * g))).trans
    (eq_of_beq (List.all_eq_true.1 ell_written g (List.mem_range.2 hg)))

/-- By the kernel: the written request's shape has one answer. -/
theorem answers_written : proofSizedFull.request.answers = 1 := by decide +kernel

/-- CONDITIONAL on h, hg and hG. **A GROUP's PLAN's NUMBER OF ENTRIES OF THE MASK ROW, AND ONE MORE,
IS AT MOST 8192.** -/
theorem slotsSharp_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {g : ℕ} (hg : g < 12)
    {hp : Layer.HPlan2} (hG : (P5J.At.X Zp).G[g]? = some hp) : hp.ns + 1 ≤ 8192 := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have W := written_of_head h.toAtMg
  have hpub : Verify.publicOf Z.pol Z.KL (some Z.lay) = .ok Zp.p.X := O.W ▸ O.public
  obtain ⟨k4, _, _, hA⟩ := _root_.Meaning.scope_plans h.scope h.reads hpub
  obtain ⟨a, ha, _⟩ := hA g hg
  obtain ⟨X, hX, e⟩ := Option.map_eq_some_iff.1
    (OnBytes.Road.K4.Riders.built_ns_plain O.pub k4 hG ha)
  obtain ⟨zk, hz, hle⟩ := OnBytes.Road.K4.Rec.built_ns_le O.pub hX
  rw [W.codes, W.shape, shape_one] at hz
  rw [W.shape, shape_one] at hle
  have h8 := maskEll_written
  rw [hz] at h8
  have e8 : zk.ell = 8192 := Option.some.inj h8
  have a1 := answers_written
  omega

variable {R : RecPlan} {n k m g : ℕ} {x : Bool × Par} {blk₀ : Block TS ProofFile.Cl}
  {xl : VerifiableInference.Desc.First.Look.Place} {o : ℕ} {u : Mem}

/-- CONDITIONAL on h, Lh, P and hl. **THE MASK CODE's LENGTH AT u's SHAPE IS 8192.** -/
theorem maskRow_ell_is (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh)
    (Lh : LaidK4 Zp cF k m g x blk₀) (P : MaskRowPub h R n m xl o u) (hl : xl.link = m) :
    (pMask h.𝔇.cs (u.1.l.get u.2).1).ell = 8192 := by
  rw [maskRow_ell_free P hl, Lh.seg]
  exact maskEll_head h Lh.lt _

/-- CONDITIONAL on h, Lh, P, hl and hns. **THE PLACE's NUMBER OF ENTRIES OF THE MASK ROW, AND ONE
MORE, IS WITHIN THE MASK CODE's LENGTH AT u's SHAPE.** -/
theorem maskRow_fence (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh)
    (Lh : LaidK4 Zp cF k m g x blk₀) (P : MaskRowPub h R n m xl o u) (hl : xl.link = m)
    (hns : xl.ns = (parOf x).hp.ns) : xl.ns + 1 ≤ (pMask h.𝔇.cs (u.1.l.get u.2).1).ell := by
  rw [maskRow_ell_is h Lh P hl, hns]
  exact slotsSharp_head h Lh.lt Lh.hp

end ProofFile.Honest.K4.W

#print axioms ProofFile.Honest.K4.W.maskEll_head
#print axioms ProofFile.Honest.K4.W.answers_written
#print axioms ProofFile.Honest.K4.W.slotsSharp_head
#print axioms ProofFile.Honest.K4.W.maskRow_ell_is
#print axioms ProofFile.Honest.K4.W.maskRow_fence
