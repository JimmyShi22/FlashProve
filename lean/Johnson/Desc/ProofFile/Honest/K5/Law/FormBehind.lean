-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/FormBehind.lean: CONDITIONAL: THE THREAD's FORM BEHIND THE STEP
OF THE MEMBER THAT HEARS AN ATTENTION SEGMENT's OWN ROUNDS (kind K5), at the first chain's thread at
the library's head (`lettersHead`, Honest/Thread/FirstHead.lean), AT EACH OF THE 12 GROUPS. THE
THREAD IN FRONT AND THE MEMBER's STEP ARE PREMISES. General in all letters of `lettersHead`.
Statements with their proofs; no definition.

Why. Whoever shows the thread along the first chain owes, at each member, the form one border on
from the thread in front and the member's step. This file pays that at the 12 members of the kind
K5: the numbers 14 (2 g + 1) + 2 + 2 for a group g below 12. `formP_behind`
(Honest/K5/Law/Behind.lean) has the promise behind at another thread's letters, and asks beside that
the member is seated with the honest prover's half (`K5Seated`) and that the challenges fit. The
form alone needs neither.

How. The form is "no mark" and the table's promise at the honest letters, at no strings.
  * The member, the group's plan, and that the member decides as the kind's own decision:
    `k5_member` (Honest/K5/Law/Member.lean), from the hypothesis alone.
  * The step's yes is the member's decision's (`step_ok_iff`), so the kind's, with no mark behind it
    (`DecidesAs`' field `decides`); so the state behind is the hearing's return at the step's own
    rounds (`k5_yes_is`, Johnson/Desc/K5/Honest/Law/Returns.lean). WHICH rounds these are is not
    asked: that they are the played ones is what `formP_behind` spends `K5Seated` and "the
    challenges fit" for.
  * The promise behind: `behind_at_head` (Johnson/Desc/K5/Honest/Law/BehindAtHead.lean), which takes
    every list of rounds, at the honest letters (`honestLike_at`, `atBorder_at`:
    Honest/K5/Law/Behind.lean), a made-up frame without a tree and one made-up value of its strings:
    at these letters the promise reads no string. "Reached" comes out of the thread
    (`reach_of_made`, Honest/Thread/MadeLaw.lean).
  * The table's sets one border on: `openSets_succ`, `pubSets_succ`
    (Johnson/Desc/First/BordersSucc.lean), at the two places `H2K5.Door.place_full`, `next_full` and
    the list of extra public tests `hm_all` (Johnson/Desc/First/Att/Door/Law/).
  * Closed facts that the kernel decides, right beneath: the two places (`k5Lists_places`), and what
    `atBorder_at` lays of the table's two lists at the border (`twenty_full`, `doors_full`,
    `ties_full`): all of Johnson/Desc/First/Att/Door/Law/K5ListsFull.lean.

Main names:
  `k5_form_at`   the form behind, at the number `borderOf` g (14 (2 g + 1) + 4)
  `k5_form_behind`   **the form behind at 14 (2 g + 1) + 2 + 2, for g below 12**: the same theorem:
      the two spellings of the number are one by unfolding

BOTH ARE CONDITIONAL on the hypothesis h on the public input (`P5J.AtMgA`,
Johnson/P5J/MgAtAll.lean); g is below 12; blk is the member at that number; the thread in front
(`Thr`); the member's step (`Stepped`).
ON h. It can be met: at the full-size public files as Ladder/Stored.lean spells them it has a member
with no premise (`headMember_zFull`, AtFullSide/Top/HeadMemberAtFull.lean). This file does not call
it. These files are tied to the package's files by no theorem.

Limits. AN IMPLICATION: that a thread and a step can be met together at one of these numbers is
shown nowhere here. The form alone: nothing on the thread's other clauses behind the step (what
rides, what is kept, what was made), nor on the items of the kind's row: for these the premises of
Honest/K5/Law/Behind.lean and of the files above it stay. At the library's full size and at the
format's second hash function alone: h is typed there. What lies deeper beneath the calls was not walked.
Through its imports the file stands above the files under ThirdParty/ (lean/LIMITS.md, L15). The
file sets `maxHeartbeats` to 1000000.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.Behind
import Johnson.Desc.ProofFile.Honest.Thread.FirstHead
import Johnson.Desc.ProofFile.Honest.Thread.Pays
import Johnson.Desc.ProofFile.Honest.Thread.MadeLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K5
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Place Strs Chain)
open VerifiableInference.Desc.First (onAt openSets pubSets start leavesName openSets_succ
  pubSets_succ)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.First.Att.P
open H2K5.Door (moreOver9)
open H2K5.Honest (behind_at_head k5_yes_is)
open ProofFile.Honest.FirstThread (Script WtF lettersHead honest noStrs)
open P5J (AtMgA mgAtAll TS CellsM)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

/-- **The form behind the step of the member at the kind's border of group g.** CONDITIONAL: the
hypothesis h; g is below 12; blk is the member at that number; the thread in front; the member's
step. -/
theorem k5_form_at {g : Nat} (hg : g < 12) :
    ∀ blk, cF.blocksInOrder[borderOf g]? = some blk → ∀ k s m E ds y cols s',
      Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread (borderOf g) k s m E →
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Stepped blk k s m E ds y cols
        s' →
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Form (borderOf g + 1) k s'
        y.2 := by
  intro blk hblk k s m E ds y cols s' hT hS
  -- the member decides as the kind's own decision
  obtain ⟨blk', a, hfl, Pl, Dc⟩ := k5_member h hg
  obtain rfl : blk' = blk := Option.some.inj (hfl.symm.trans hblk)
  -- its step's yes is the kind's, and leaves no mark
  have hd := ((VerifiableInference.Desc.Sound.step_ok_iff _ blk' s s' _ _ _).1 hS.2).2.2.2
  obtain ⟨hdec, h1, -⟩ := (Dc.decides s s' _ _).1 hd
  obtain ⟨att, hd5, G, e, hh, rfl⟩ := k5_yes_is _ hdec
  obtain ⟨L, hL⟩ := P5J.At.laid_some Zp h.opts.laid
  -- the table at the border
  have hpl : P5J.At.ps[borderOf g]? = some ⟨1, some (2 * g + 1), 3, .K5⟩ :=
    H2K5.Door.place_full hg
  have hnx : P5J.At.ps[borderOf g + 1]? = some ⟨1, some (2 * g + 1), 4, .K1⟩ :=
    H2K5.Door.next_full hg
  have hm : (honest (mgAtAll h) (ansJT (P5J.At.cs Zp) (P5J.At.arr Zp) (P5J.At.smp Zp)
        (P5J.At.ms Zp Z.lay)) test).more =
      (moreOver9 {}).strike leavesName := H2K5.Door.hm_all h
  -- in front: no mark, the promise, reached
  obtain ⟨hf0, hon0⟩ := hT.2.2.1
  have h0 : s.failed = none := Option.isNone_iff_eq_none.1 hf0
  have hon : onAt (P5J.At.N Zp cF)
      (honest (mgAtAll h) (ansJT (P5J.At.cs Zp) (P5J.At.arr Zp) (P5J.At.smp Zp)
        (P5J.At.ms Zp Z.lay)) test) P5J.At.links (P5J.At.ps[borderOf g]?)
      (((openSets P5J.At.links P5J.At.ps (start P5J.At.links))[borderOf g]?).getD [])
      (((pubSets (honest (mgAtAll h) (ansJT (P5J.At.cs Zp) (P5J.At.arr Zp) (P5J.At.smp Zp)
        (P5J.At.ms Zp Z.lay)) test).more P5J.At.links P5J.At.ps)[borderOf g]?).getD [])
      (m.st.input.x.pub, s) noStrs := hon0
  rw [hpl, hm] at hon
  have hr := reach_of_made (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
    (ProofFile.startS Zp) m.st.input.x.pub
    (Nat.le_of_lt (List.getElem?_eq_some_iff.1 hblk).1) (fun _ e => e) hT.2.2.2.2.1
  -- the promise behind, by the kind's own law
  have hb := behind_at_head h hL hg Pl.plan
    (honest (mgAtAll h) (ansJT (P5J.At.cs Zp) (P5J.At.arr Zp) (P5J.At.smp Zp)
        (P5J.At.ms Zp Z.lay)) test)
    (honestLike_at h _ test) _ _ (atBorder_at hg)
    (Fr := ⟨0, [], fun _ => 0, 0⟩) (bs := 0) (y := (fun _ => (0, []), fun _ => []))
    (y' := (fun _ => (0, []), fun _ => [])) ⟨rfl, fun _ _ _ => rfl⟩ hr h0 hon e hh
  rw [hm] at hb
  -- the input is as it was
  obtain ⟨⟨st, -, hy⟩, -⟩ := hS.1
  obtain ⟨ei, -, -⟩ := play_mid _ _ _ _ _ hy
  refine ⟨?_, ?_⟩
  · show (behind s att hd5 G).failed.isNone = true
    rw [h1]
    rfl
  · show onAt (P5J.At.N Zp cF)
      (honest (mgAtAll h) (ansJT (P5J.At.cs Zp) (P5J.At.arr Zp) (P5J.At.smp Zp)
        (P5J.At.ms Zp Z.lay)) test) P5J.At.links (P5J.At.ps[borderOf g + 1]?)
      (((openSets P5J.At.links P5J.At.ps (start P5J.At.links))[borderOf g + 1]?).getD [])
      (((pubSets (honest (mgAtAll h) (ansJT (P5J.At.cs Zp) (P5J.At.arr Zp) (P5J.At.smp Zp)
        (P5J.At.ms Zp Z.lay)) test).more P5J.At.links P5J.At.ps)[borderOf g + 1]?).getD [])
      (y.2.st.input.x.pub, behind s att hd5 G) noStrs
    rw [ei, hnx, hm, openSets_succ _ _ _ _ _ hpl, pubSets_succ _ _ _ _ _ hpl]
    exact hb

/-- **THE FORM BEHIND THE STEP OF THE MEMBER OF KIND K5, AT EACH OF THE 12 GROUPS.** CONDITIONAL:
the hypothesis h; g is below 12; blk is the member number 14 (2 g + 1) + 2 + 2 of the first chain's
flat list; the thread in front; the member's step. -/
theorem k5_form_behind {g : Nat} (hg : g < 12) :
    ∀ blk, cF.blocksInOrder[14 * (2 * g + 1) + 2 + 2]? = some blk → ∀ k s m E ds y cols s',
      Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
        (14 * (2 * g + 1) + 2 + 2) k s m E →
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Stepped blk k s m E ds y cols
        s' →
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Form
        (14 * (2 * g + 1) + 2 + 2 + 1) k s' y.2 :=
  k5_form_at h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hg

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.k5_form_at
#print axioms ProofFile.Honest.K5.k5_form_behind
