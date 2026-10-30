-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K8/Law/FormBehind.lean: CONDITIONAL: THE THREAD's FORM BEHIND THE STEP
OF THE MEMBER AT WHICH A SEGMENT's SMALLNESS TEST DRAWS ITS CHALLENGES (kind K8), at the first
chain's thread at the library's head (`lettersHead`, Honest/Thread/FirstHead.lean), AT EACH OF THE
25 SEGMENTS. THE THREAD IN FRONT AND THE MEMBER's STEP ARE PREMISES. General in all letters of
`lettersHead`. Statements with their proofs; no definition.

Why. Whoever shows the thread along the first chain owes, at each member, the form one border on
from the thread in front and the member's step. This file pays that at the 25 members of the kind
K8: the numbers 14 l + 4 + 2 for a segment l below 24, and 343.

How. The form is "no mark" and the table's promise at the honest letters, at no strings. The promise
rides past the draw by the table's own rule for a row that closes and opens no class of rows and no
pin (`onAt_step_quiet`, Johnson/Desc/First/PromiseRides.lean), on the road of the library's `k08_t2`
(Johnson/Desc/First/K8/TieRides.lean), which is not called: it asks the whole of `DrawBlind`. Of
that structure's eleven fields five are on letters that the honest letters turn: two speak of the
items' meanings (`rides`, `reads`) and are not needed here; three (`decodes`, `shown`, `noColl`)
become "True". The other six are taken. Clause by clause:
  * the member is the draw's own block, seated alone at the segment's built link (`k8_sits_head`, by
    `SitsAt`, Johnson/P1K8R/Sits.lean): so its yes is the draw's, and no mark stands behind it;
  * "decodes", "shown", "no collision": true at the honest letters by their text;
  * where the chain stands: `drawn_shape`; the statement's groups and the book: the draw leaves them
    (`hear_leaves_statement`, `hear_leaves_book`); the six facts on the list of places:
    `k8_step_full` (Johnson/P1K8R/TiedBlind.lean, by the kernel), typed anew at the thread's letters
    by unfolding (`P5J.ps_full` is `rfl`; `ixOf` and `drawAt` have one text);
  * "in order", "held", the public items' Bools and what they say beside, the plan's two counts:
    fields of `DrawBlind` at the closed meaning (`blind_at_const`, Johnson/P1K8R/BlindJoin.lean, at
    `blindOwes_of_fence`, WtBack.lean), which the honest letters do not turn. That law's letter for
    a base is laid above the finitely many sampled tenants (`below_some`);
  * the one public item that is new behind the draw: `makes_reach`
    (Johnson/Desc/K8/Honest/Law/MakesAtHead.lean), at the honest letters, a made-up frame without a
    tree and one made-up value of its strings: at these letters the promise reads no string.
    "Reached" comes out of the thread (`reach_of_made`, Honest/Thread/MadeLaw.lean).

Main names:
  `below_some`   finitely many numbers lie below one bound
  `k8_sits_head`   the member at the draw's number is the draw's own block, seated alone
  `k8_form_at`   the form behind, at the library's number `drawAt` l of a segment l up to 24
  `k8_form_behind`   **the form behind at 14 l + 4 + 2, for l below 24**
  `k8_form_behind_last`   **the form behind at 343**

ALL BUT THE FIRST ARE CONDITIONAL on the hypothesis h on the public input (`P5J.AtMgA`,
Johnson/P5J/MgAtAll.lean). The last three also: blk is the member at that number; the thread in
front (`Thr`); the member's step (`Stepped`).
ON h. It can be met: at the full-size public files as Ladder/Stored.lean spells them it has a member
with no premise (`headMember_zFull`, AtFullSide/Top/HeadMemberAtFull.lean). This file does not call
it. These files are tied to the package's files by no theorem.

Limits. AN IMPLICATION: that a thread and a step can be met together at one of these numbers is
shown nowhere here. The form alone: nothing on the thread's other clauses behind the step (what
rides, what is kept, what was made). At the library's full size and at the format's second hash function
alone: h is typed there. Of the closed facts by the kernel beneath, one is named above; what lies
deeper was not walked. The file sets `maxHeartbeats` to 1000000.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.Thread.FirstHead
import Johnson.Desc.ProofFile.Honest.Thread.Pays
import Johnson.Desc.ProofFile.Honest.Thread.MadeLaw
import Johnson.Desc.K8.Honest.Law.MakesAtHead
import Johnson.P1K8R.WtBack
import Johnson.P1K8R.Sits
import Johnson.P1K8R.TiedBlind
import Johnson.Desc.First.PromiseRides
import Johnson.Desc.First.BordersSucc
import Johnson.P5J.FoldJ3

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K8
open VerifiableInference.Desc (Block Chain Strs Place)
open VerifiableInference.Desc.Sound (MsgT linksFull)
open VerifiableInference.Desc.First (onAt openSets pubSets start rowOf shapeAt bookAt sampledIn
  flatPlacesOf onAt_step_quiet openSets_succ pubSets_succ)
open VerifiableInference.Desc.First.K8 (drawAt Drawn drawn_of_yes drawn_shape hear_leaves_statement
  hear_leaves_book)
open OnBytes.Maker (WholeD)
open ProofFile.Honest.FirstThread (Script WtF lettersHead honest noStrs)
open P5J (AtMgA CellsM TS mgAtAll fullLinks)

/-- Finitely many numbers lie below one bound. -/
theorem below_some : ∀ xs : List (Nat × Nat), ∃ B, ∀ y ∈ xs, y.1 < B
  | [] => ⟨0, fun _ hy => absurd hy List.not_mem_nil⟩
  | x :: xs => by
    obtain ⟨B, hB⟩ := below_some xs
    refine ⟨B + x.1 + 1, fun y hy => ?_⟩
    rcases List.mem_cons.1 hy with rfl | hy
    · omega
    · have := hB y hy
      omega

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)

include h in
/-- **The member at the draw's number of segment l is the draw's own block, seated alone, at the
segment's built link.** CONDITIONAL: the hypothesis h; O: the opening of the description's maker; l
is at most 24. -/
theorem k8_sits_head {Bs : ProofFile.PureBase} {base : List (Block TS ProofFile.Cl)}
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (Desc.K14.Law.seatZ Zp Np) (Desc.K14.Law.secondAt Zp Np)) {l : Nat} (hl : l ≤ 24) :
    P1K8S.SitsAt Zp Bs.G₀ cF l (if l = 24 then 5 else 4) := by
  rcases Nat.lt_or_ge l 24 with h24 | h24
  · rw [if_neg (by omega)]
    rcases Nat.even_or_odd' l with ⟨g, rfl | rfl⟩
    · obtain ⟨Lk, b, Xl, _, e1, e2, e3, hh, _⟩ := IM.k8_of_layers h.scope h.reads O g (by omega)
      exact P1K8S.sitsAt_of_alone e1 e2 (IM.flatIx_scope h.scope h.reads O (by omega) 4) e3 hh
    · obtain ⟨Lk, b, Xl, _, e1, e2, e3, hh, _⟩ :=
        IM.k8_of_attention h.scope h.reads O g (by omega)
      exact P1K8S.sitsAt_of_alone e1 e2 (IM.flatIx_scope h.scope h.reads O (by omega) 4) e3 hh
  · obtain rfl : l = 24 := by omega
    obtain ⟨Lk, b, Xl, e1, e2, e3, hh, _⟩ := IM.k8_of_head h.scope h.reads O
    exact P1K8S.sitsAt_of_alone e1 e2 (IM.flatIx_scope h.scope h.reads O (by omega) 5) e3 hh

variable {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

/-- **The form behind the step of the member at the draw's number of segment l.** CONDITIONAL: the
hypothesis h; l is at most 24; blk is the member at that number; the thread in front; the member's
step. -/
theorem k8_form_at {l : Nat} (hl : l ≤ 24) :
    ∀ blk, cF.blocksInOrder[drawAt l]? = some blk → ∀ k s m E ds y cols s',
      Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread (drawAt l) k s m E →
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Stepped blk k s m E ds y cols
        s' →
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Form (drawAt l + 1) k s'
        y.2 := by
  intro blk hblk k s m E ds y cols s' hT hS
  obtain ⟨Bs, base0, O⟩ := h.laid.opened
  -- the member is the draw's own block, seated alone
  obtain ⟨Lk, B, Xl, -, -, hB, e3, -, hSe, -, -⟩ := k8_sits_head h O hl
  have hB' : cF.blocksInOrder[drawAt l]? = some B := by
    rw [P1K8T.drawAt_place]
    exact hB
  obtain rfl : B = blk := Option.some.inj (hB'.symm.trans hblk)
  -- its step's yes is the draw's, and leaves no mark
  have hd := ((VerifiableInference.Desc.Sound.step_ok_iff _ B s s' _ _ _).1 hS.2).2.2.2
  obtain ⟨hdraw, h1⟩ := (hSe.2 s _ _ s').1 hd
  have hDr : Drawn s s' := drawn_of_yes _ s s' _ _ hdraw
  have hst : s'.st = s.st := hear_leaves_statement _ s _ _ s' hdraw
  have hbk : s'.book = s.book := hear_leaves_book _ s _ _ s' hdraw
  -- the table at the draw's number
  obtain ⟨pK, pN, hK, hN, hq, hlk, hsd, hw⟩ := P1K8T.k8_step_full hl
  have hK : P5J.At.ps[drawAt l]? = some pK := hK
  have hN : P5J.At.ps[drawAt l + 1]? = some pN := hN
  -- in front: no mark, the promise, reached
  obtain ⟨hf0, hon0⟩ := hT.2.2.1
  have h0 : s.failed = none := Option.isNone_iff_eq_none.1 hf0
  have hon : onAt (P5J.At.N Zp cF)
      (honest (mgAtAll h) (ansJT (P5J.At.cs Zp) (P5J.At.arr Zp) (P5J.At.smp Zp)
        (P5J.At.ms Zp Z.lay)) test) fullLinks P5J.At.ps[drawAt l]?
      (((openSets fullLinks P5J.At.ps (start fullLinks))[drawAt l]?).getD [])
      (((pubSets (mgAtAll h).more fullLinks P5J.At.ps)[drawAt l]?).getD [])
      (m.st.input.x.pub, s) noStrs := hon0
  have hr := reach_of_made (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
    (ProofFile.startS Zp) m.st.input.x.pub
    (Nat.le_of_lt (List.getElem?_eq_some_iff.1 hblk).1) (fun _ e => e) hT.2.2.2.2.1
  -- the kind's own condition behind the draw
  have hmk := H2K8.makes_reach h (Fr := ⟨0, [], fun _ => 0, 0⟩)
    (honest (mgAtAll h) (ansJT (P5J.At.cs Zp) (P5J.At.arr Zp) (P5J.At.smp Zp)
      (P5J.At.ms Zp Z.lay)) test) O hl e3 m.st.input.x.pub
    (s, (fun _ => (0, []), fun _ => [])) (s', (fun _ => (0, []), fun _ => [])) hon hr h0
    ⟨_, _, hdraw⟩
  -- what the closed filling owes for the draw
  obtain ⟨base, hbase⟩ := below_some (sampledIn (P5J.At.N Zp cF)
    ((openSets linksFull (flatPlacesOf linksFull true) (start linksFull))[P1K8T.ixOf l]?.getD []))
  have Db := P1K8T.blind_at_const h hl (P1K8T.blindOwes_of_fence h hl base hbase)
  have hsh : shapeAt fullLinks (some pK) s = true := by
    have c0 := hon
    unfold onAt at c0
    rcases c0.2 with c | c
    · exact absurd h0 c
    · have c2 := c.1
      simp only [Bool.and_eq_true] at c2
      rw [hK] at c2
      exact c2.1.1.1.1.1
  -- the input is as it was
  obtain ⟨⟨st, -, hy⟩, -⟩ := hS.1
  obtain ⟨ei, -, -⟩ := play_mid _ _ _ _ _ hy
  refine ⟨?_, ?_⟩
  · show s'.failed.isNone = true
    rw [h1]
    rfl
  · show onAt (P5J.At.N Zp cF)
      (honest (mgAtAll h) (ansJT (P5J.At.cs Zp) (P5J.At.arr Zp) (P5J.At.smp Zp)
        (P5J.At.ms Zp Z.lay)) test) fullLinks P5J.At.ps[drawAt l + 1]?
      (((openSets fullLinks P5J.At.ps (start fullLinks))[drawAt l + 1]?).getD [])
      (((pubSets (mgAtAll h).more fullLinks P5J.At.ps)[drawAt l + 1]?).getD [])
      (y.2.st.input.x.pub, s') noStrs
    rw [ei, openSets_succ _ _ _ _ _ hK, pubSets_succ _ _ _ _ _ hK]
    refine onAt_step_quiet (P5J.At.N Zp cF) _ fullLinks P5J.At.ps[drawAt l]?
      P5J.At.ps[drawAt l + 1]? _ _ _ (rowOf fullLinks pK) (m.st.input.x.pub, s)
      (m.st.input.x.pub, s') noStrs noStrs hq hon (fun c => absurd h0 c) (fun _ => trivial)
      (fun _ => ?_) (by show s'.st.groups = s.st.groups; rw [hst])
      (by show s'.book.place = s.book.place; rw [hbk])
      (Db.inOrder _ s s' hDr) (fun hf => Db.pub _ s s' noStrs pK hDr hK hf hmk) (fun _ hb => ?_)
      (fun hf => Db.pubP _ s s' noStrs pK hDr hK hf hmk) (Db.held _ s s' hDr)
      (fun _ _ _ => trivial) (fun _ _ _ => trivial)
    · rw [hN]
      exact drawn_shape fullLinks pK pN s s' hDr hlk hsd hw hsh
    · unfold bookAt at hb ⊢
      show (s'.book.trees.size == _ && s'.book.place.size == s'.st.oracles.size &&
        s'.st.oracles.size == _) = true
      have hTr : (P5J.At.N Zp cF).treesAt P5J.At.ps[drawAt l + 1]? =
          (P5J.At.N Zp cF).treesAt P5J.At.ps[drawAt l]? := Db.trees
      have hMs : (P5J.At.N Zp cF).msgsAt P5J.At.ps[drawAt l + 1]? =
          (P5J.At.N Zp cF).msgsAt P5J.At.ps[drawAt l]? := Db.msgs
      rw [hbk, hst, hTr, hMs]
      exact hb

/-- **THE FORM BEHIND THE STEP OF THE MEMBER OF KIND K8, AT EACH SEGMENT BELOW 24.** CONDITIONAL:
the hypothesis h; l is below 24; blk is the member number 14 l + 4 + 2 of the first chain's flat
list; the thread in front; the member's step. -/
theorem k8_form_behind {l : Nat} (hl : l < 24) :
    ∀ blk, cF.blocksInOrder[14 * l + 4 + 2]? = some blk → ∀ k s m E ds y cols s',
      Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread (14 * l + 4 + 2) k s m
        E →
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Stepped blk k s m E ds y cols
        s' →
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Form (14 * l + 4 + 2 + 1) k
        s' y.2 := by
  have e : drawAt l = 14 * l + 4 + 2 := by
    unfold drawAt
    rw [if_neg (by omega)]
  have A := k8_form_at h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w (l := l) (by omega)
  rw [e] at A
  exact A

/-- **THE SAME AT THE LAST SEGMENT: THE MEMBER NUMBER 343.** CONDITIONAL: the hypothesis h; blk is
the member number 343; the thread in front; the member's step. -/
theorem k8_form_behind_last :
    ∀ blk, cF.blocksInOrder[343]? = some blk → ∀ k s m E ds y cols s',
      Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread 343 k s m E →
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Stepped blk k s m E ds y cols
        s' →
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Form (343 + 1) k s' y.2 :=
  k8_form_at h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w (l := 24) (by omega)

end ProofFile.Honest.K8

#print axioms ProofFile.Honest.K8.below_some
#print axioms ProofFile.Honest.K8.k8_sits_head
#print axioms ProofFile.Honest.K8.k8_form_at
#print axioms ProofFile.Honest.K8.k8_form_behind
#print axioms ProofFile.Honest.K8.k8_form_behind_last
