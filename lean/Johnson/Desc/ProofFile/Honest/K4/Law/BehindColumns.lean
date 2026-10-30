-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K4/Law/BehindColumns.lean: CONDITIONAL.

Can the hypotheses be met together? Statement by statement. The two on hst ask nothing. The one on
the written list asks g < 12. The one on h₀ asks 28 g + 5 < b₀ alone: 339 meets it at each g < 12.
The one on the member's place, and those on hF, on `K4KeepsM` and on hl, ask h and g < 12. Of h: the
side library AtFullSide proves, with no hypothesis, that h has a member at one place
(AtFullSide.Top.headMember_zFull, AtFullSide/Top/HeadMemberAtFull.lean, whose own Limits say what it
is worth). The one on hK asks h, g < 12 and keepsGivesClause; `k4_behindS_at_border` asks these and
28 g + 5 < b₀. keepsGivesClause is a hypothesis on the family f: the family of the threads' writers'
one term for the first thread meets it (`k4_first_clause_of_keeps_and_form`,
Law/BehindAtFirstThread.lean). BUT hF, hK, h₀, hl AND `BehindS` ARE IMPLICATIONS: THEY SPEAK ONLY
WHERE THE THREAD STANDS IN FRONT OF THE MEMBER AND THE MEMBER's STEP ACCEPTS. NO STAND OF SUCH A
THREAD BEYOND BORDER 0 IS KNOWN TO ANYBODY, SO THEY ARE NOT KNOWN TO SPEAK AT ANY RUN.

What is here. FIVE OF THE EIGHT COLUMNS OF `owesS_head_form` (Honest/Thread/GatherHeadForm.lean) AT
THE TWELVE MEMBERS OF THE FEED-FORWARD LAYERS' OWN ROUNDS (kind K4), the members number 28 g + 4, g
< 12, of the first chain's thread at the library's own parameters (`lettersHead`); AND WHAT THE FIVE
GIVE TOGETHER: `BehindS`. That lemma asks eight hypotheses at every member's number b: hP, hF, hK,
h₀, hst, hl, hX, hR. Here stand hF, hK, h₀, hst and hl at b = 28 g + 4, each in the column's own
text but for the hypothesis b < the thread's length, which is not needed. OF THE FIVE, TWO SAY
SOMETHING OUTRIGHT (hF, hl), ONE UNDER keepsGivesClause (hK), AND TWO HOLD FOR NOTHING AT THESE
BORDERS (h₀, hst). No definition. The proofs are calls and arithmetic.

  `no_clause_spans_k4_border`   of the 55 clauses of `csHead` (Honest/Thread/CsHead.lean) none
      speaks both at the border 28 g + 4 and at the border 28 g + 5, at any number g. Arithmetic on
      that list's text.
  `k4_stays_column_at_border`   **hst**: FOR NOTHING, by the line above; at every thread.
  `k4_written_place_at_border`   the written list of places has K4's place of group g at the number
      28 g + 4. A public fact.
  `k4_member_place_at_border`   the thread's member number 28 g + 4 stands at that place.
  `k4_form_column_at_border`   **hF**: the thread's form at the border behind the member's step. It
      is `k4_form_behindS_at` (Law/FormBehindHead.lean) with the number spelt 28 * g + 4, as the
      other columns and the list of clauses spell it, and not 14 * (2 * g) + 2 + 2.
  `k4_keeps_after_step_at_border`   **wherever the member's step accepts from s to s': `K4KeepsM s
      s'`** (Law/KeepsStep.lean). Nothing is read of the thread in front.
  `k4_keeps_column_at_border`   **hK**: at a family f, under keepsGivesClause.
  `k4_reply_column_at_border`   **h₀**: FOR NOTHING: the column speaks from the border b₀ on, and 28
      g + 5 lies in front of it.
  `k4_lays_column_at_border`   **hl**: the one clause of `csHead` that begins at 28 g + 5 is "the
      segment's own rounds have returned something"; the member lays it (`k4_laysS_own`,
      Law/LaysOwn.lean).
  `k4_behindS_at_border`   **SO `BehindS` (Honest/Thread/PaysS.lean) AT b = 28 g + 4**: where the
      member's step accepts, the form and what rides hold at the border behind, and the step kept
      what keeps names. From h, g < 12, 28 g + 5 < b₀ and keepsGivesClause ALONE: none of the
      columns hP, hX, hR is asked. By the frame's `behindS_of_keeps_and`
      (Honest/Thread/RidersAnd.lean).

Limits. CONDITIONAL, as said at the top. keepsGivesClause: from `K4KeepsM s s'` and the thread's
form at the border behind, at any coins and any stand of the prover: f at the kind K4, at K4's place
of group g. It is so shaped because the family of the threads' writers' term (`firstClauses`,
Honest/Thread/TheFirstThread.lean) is at K4: `K4KeepsM s s'`, a clause `formsBehind` on s', and
"True" in each further layer; their `formsBehind_of_form` draws `formsBehind` from the form behind
and from what `k4_written_place_at_border` says (Law/BehindAtFirstThread.lean). A family that always
holds meets keepsGivesClause too: what shuts such a family out is the law that spends keeps, which
asks the way back. The columns hP, hX and hR are not here. If a clause is added to `csHead` whose
span holds 28 g + 4 and 28 g + 5, `no_clause_spans_k4_border` falls. No proof here opens the
prover's moves: that the member's step accepts (`Thread.Stepped`) is a hypothesis of hF, hK, h₀ and
hl, and inside `BehindS`: at a prover whose side stops at the member at all challenges, or to whom
the book lends no steps, they hold for nothing. Its imports reach files of ours that are no part of
the library yet: Law/FormBehindHead.lean, Law/LaidAtGroup.lean, Law/LaysOwn.lean. THE FULL SIZE
ALONE, AND THE FORMAT's EARLIER HASH ALONE. A LAW, NOT A PART: it rests, through
Law/ElevenHead.lean, on modules under Johnson/Goal/: no file that defines a part may build on it; it
states no goal. Nothing on soundness, on completeness or on any other property.
No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.FormBehindHead
import Johnson.Desc.ProofFile.Honest.K4.Law.LaidAtGroup
import Johnson.Desc.ProofFile.Honest.K4.Law.LaysOwn
import Johnson.Desc.ProofFile.Honest.Thread.CsHead
import Johnson.Desc.ProofFile.Honest.Thread.KeepsBy
import Johnson.Desc.ProofFile.Honest.Thread.RidersAnd
import Johnson.Desc.ProofFile.Honest.Thread.SteppedYes
import Johnson.Second.Seam.LinksOne

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4
open OnBytes.Road.K4 (atK4_full)
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Place Chain Strs KindName)
open VerifiableInference.Desc.Sound (MsgT linksFull)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (Script WtF lettersHead head_rides_and head_keeps_kind)
open ProofFile.Honest.K4.SeatedHead (laid_at member_head k4Sits_head k4NoMark_head)

/-! ## 1 On the written lists: at every thread -/

/-- **No clause of `csHead` speaks both at the border 28 g + 4 and at the border 28 g + 5**, at any
number g. -/
theorem no_clause_spans_k4_border {W : Type} {ν : Nat} {st : Nat → TS → Prop}
    {R : Nat → Option OnBytes.Model.Forest.Heard → Prop} {g : ℕ}
    {c : RiderCl W TS} (hc : c ∈ csHead ν st R) (hlo : c.lo ≤ 28 * g + 4)
    (hhi : 28 * g + 4 + 1 ≤ c.hi) : False := by
  rcases csHead_span hc with ⟨a, b⟩ | ⟨l, _, a, b⟩ | ⟨g', _, a, b⟩ | ⟨g', _, a, b⟩ <;> omega

/-- **The column hst at K4's border**: for nothing: no clause is asked. At every thread and every
number g. -/
theorem k4_stays_column_at_border {Bk : ProverCoinCounts} {Cl V W X Pb : Type} (T : Thread Bk TS Cl V W X Pb)
    (ν : Nat) (st : Nat → TS → Prop) (R : Nat → Option OnBytes.Model.Forest.Heard → Prop)
    (g : ℕ) :
    ∀ c ∈ csHead ν st R, c.lo ≤ 28 * g + 4 → 28 * g + 4 + 1 ≤ c.hi → StaysBy T (28 * g + 4) c :=
  fun _ hc hlo hhi => (no_clause_spans_k4_border hc hlo hhi).elim

/-- **The written list of places has K4's place of group g at the number 28 g + 4.** A public fact:
the library's `atK4_full`, at the other of the library's two names for the list of segments. -/
theorem k4_written_place_at_border {g : ℕ} (hg : g < 12) :
    P5J.At.ps[28 * g + 4]? = some (IM.k4Place g) := by
  have e : P5J.At.ps = VerifiableInference.Desc.First.flatPlacesOf linksFull true := by
    unfold P5J.At.ps
    rw [Second.Seam.links_one.1]
  rw [e]
  exact (atK4_full g hg).here

/-! ## 2 At the first chain's thread -/

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X' : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X')
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)
  (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X' → Prop)

/-- CONDITIONAL: on h and hg. **The member number 28 g + 4 stands at K4's place of group g.** -/
theorem k4_member_place_at_border {g : ℕ} (hg : g < 12) :
    ∀ blk, (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.bs[28 * g + 4]? =
      some blk → blk.place = IM.k4Place g := by
  intro blk hb
  obtain ⟨x, blk₀, Lh⟩ := laid_at h hg
  obtain rfl : blk₀ = blk := Option.some.inj
    ((member_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Lh).symm.trans hb)
  exact IM.alone_place Lh.laid

/-- CONDITIONAL: on h and hg. **THE COLUMN hF AT K4's BORDER**: the form behind the member's step.
-/
theorem k4_form_column_at_border {g : ℕ} (hg : g < 12) :
    ∀ blk, (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.bs[28 * g + 4]? =
      some blk → ∀ k s m E ds y cols s',
      ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said (28 * g + 4) k s m
        E →
      drawsFit blk.rounds ds = true →
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Stepped blk k s m E ds y cols
        s' →
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Form (28 * g + 4 + 1) k s'
        y.2 :=
  fun blk hb k s m E ds y cols s' hT hd hS =>
    k4_form_behind h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w (atK4_full g hg) blk hb k s m E ds y
      cols s' hT.1 hd hS

/-- CONDITIONAL: on h and hg. **WHEREVER THE MEMBER's STEP ACCEPTS FROM s TO s': K4's CLAUSE OF
keeps.** -/
theorem k4_keeps_after_step_at_border {g : ℕ} (hg : g < 12) :
    ∀ blk, (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.bs[28 * g + 4]? =
      some blk → ∀ k s m E ds y cols s',
      drawsFit blk.rounds ds = true →
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Stepped blk k s m E ds y cols
        s' →
      K4KeepsM s s' := by
  intro blk hb k s m E ds y cols s' hd hS
  obtain ⟨x, blk₀, Lh⟩ := laid_at h hg
  exact k4_keepsM_step (k4Sits_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Lh)
    (k4NoMark_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Lh) blk hb s s'
    (stepYes_of_stepped _ hd hS)

/-- CONDITIONAL: on h, hg and keepsGivesClause. **THE COLUMN hK AT K4's BORDER**, at a family f of
clauses of keeps. keepsGivesClause: K4's clause and the form behind give f at the kind K4, at K4's
place of group g. -/
theorem k4_keeps_column_at_border (f : KindName → Place → TS → TS → Prop) {g : ℕ} (hg : g < 12)
    (keepsGivesClause : ∀ k s s' m', K4KeepsM s s' →
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w).thread.Form (28 * g + 4 + 1) k
        s' m' →
      f KindName.K4 (IM.k4Place g) s s') :
    ∀ blk, (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w).thread.bs[28 * g + 4]? =
      some blk → ∀ k s m E ds y cols s',
      ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w).thread Said (28 * g + 4) k
        s m E →
      drawsFit blk.rounds ds = true →
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w).thread.Stepped blk k s m E ds y
        cols s' →
      f blk.place.kind blk.place s s' := by
  intro blk hb k s m E ds y cols s' hT hd hS
  rw [k4_member_place_at_border h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w hg blk hb]
  exact keepsGivesClause k s s' y.2
    (k4_keeps_after_step_at_border h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w hg blk hb k s m
      E ds y cols s' hd hS)
    (k4_form_column_at_border h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w Said hg blk hb k s m
      E ds y cols s' hT hd hS)

/-- CONDITIONAL: on hb₀. **THE COLUMN h₀ AT K4's BORDER**: for nothing: the border behind the member
lies in front of b₀. -/
theorem k4_reply_column_at_border {g : ℕ} (hb₀ : 28 * g + 4 + 1 < b₀) :
    ∀ blk, (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.bs[28 * g + 4]? =
      some blk → ∀ k s m E ds y cols s',
      ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said (28 * g + 4) k s m
        E →
      drawsFit blk.rounds ds = true →
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Stepped blk k s m E ds y cols
        s' →
      b₀ ≤ 28 * g + 4 + 1 → s'.out.reply = some m.st.input.x.asked :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ hle => absurd hle (by omega)

/-- CONDITIONAL: on h and hg. **THE COLUMN hl AT K4's BORDER**: the one clause of `csHead` that
begins at the border 28 g + 5 is laid by the member. -/
theorem k4_lays_column_at_border (ν : Nat) (st : Nat → TS → Prop)
    (R : Nat → Option OnBytes.Model.Forest.Heard → Prop) {g : ℕ} (hg : g < 12) :
    ∀ c ∈ csHead ν st R, c.lo = 28 * g + 4 + 1 →
      LaysAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said (28 * g + 4)
        c := by
  intro c hc hlo
  obtain ⟨x, blk₀, Lh⟩ := laid_at h hg
  rcases (csHead_mem ν st R c).1 hc with
    ((((rfl | rfl | rfl | rfl | rfl | rfl | rfl) | ⟨l, _, rfl⟩) | ⟨g', _, rfl⟩) | ⟨g', _, rfl⟩)
  · exact absurd (show 342 = 28 * g + 4 + 1 from hlo) (by omega)
  · exact absurd (show 343 = 28 * g + 4 + 1 from hlo) (by omega)
  · exact absurd (show 347 = 28 * g + 4 + 1 from hlo) (by omega)
  · exact absurd (show 346 = 28 * g + 4 + 1 from hlo) (by omega)
  · exact absurd (show 344 = 28 * g + 4 + 1 from hlo) (by omega)
  · exact absurd (show 346 = 28 * g + 4 + 1 from hlo) (by omega)
  · exact absurd (show 346 = 28 * g + 4 + 1 from hlo) (by omega)
  · exact absurd (show 14 * l + 9 = 28 * g + 4 + 1 from hlo) (by omega)
  · exact absurd (show 14 * (2 * g' + 1) + 4 = 28 * g + 4 + 1 from hlo) (by omega)
  · exact k4_laysS_own Said (k4Sits_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Lh) _ _

/-- CONDITIONAL: on h, hg, hb₀ and keepsGivesClause. **`BehindS` AT K4's BORDER**, with the threads'
own list of clauses laid for what rides and keeps by the place's kind at a family f. None of the
columns hP, hX, hR is asked. An implication from the thread's stand in front of the member and the
member's accepting step; no such stand is known. -/
theorem k4_behindS_at_border (f : KindName → Place → TS → TS → Prop) (ν : Nat)
    (st : Nat → TS → Prop) (R : Nat → Option OnBytes.Model.Forest.Heard → Prop) {g : ℕ}
    (hg : g < 12) (hb₀ : 28 * g + 4 + 1 < b₀)
    (keepsGivesClause : ∀ k s s' m', K4KeepsM s s' →
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd (ridersOf (csHead ν st R)) (kpBy f)
        w).thread.Form (28 * g + 4 + 1) k s' m' →
      f KindName.K4 (IM.k4Place g) s s') :
    BehindS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd (ridersOf (csHead ν st R)) (kpBy f)
      w).thread Said (28 * g + 4) :=
  behindS_of_keeps_and _ Said (R₀ := fun c v s => b₀ ≤ c → s.out.reply = some v.x.asked)
    (head_rides_and h H Q test carryX item n₁ n₂ b₀ Vd (csHead ν st R) (kpBy f) w)
    (fun blk hblk k s m E ds y cols s' hA hd hS =>
      ⟨k4_form_column_at_border h H Q test carryX item n₁ n₂ b₀ Vd (ridersOf (csHead ν st R))
          (kpBy f) w Said hg blk hblk k s m E ds y cols s' hA hd hS,
        (head_keeps_kind h H Q test carryX item n₁ n₂ b₀ Vd (ridersOf (csHead ν st R)) f w hblk rfl
          s s').2
          (k4_keeps_column_at_border h H Q test carryX item n₁ n₂ b₀ Vd (ridersOf (csHead ν st R))
            w Said f hg keepsGivesClause blk hblk k s m E ds y cols s' hA hd hS)⟩)
    (k4_reply_column_at_border h H Q test carryX item n₁ n₂ b₀ Vd (ridersOf (csHead ν st R))
      (kpBy f) w Said hb₀)
    (k4_stays_column_at_border _ ν st R g)
    (k4_lays_column_at_border h H Q test carryX item n₁ n₂ b₀ Vd (ridersOf (csHead ν st R))
      (kpBy f) w Said ν st R hg)

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.no_clause_spans_k4_border
#print axioms ProofFile.Honest.K4.k4_stays_column_at_border
#print axioms ProofFile.Honest.K4.k4_member_place_at_border
#print axioms ProofFile.Honest.K4.k4_written_place_at_border
#print axioms ProofFile.Honest.K4.k4_form_column_at_border
#print axioms ProofFile.Honest.K4.k4_keeps_after_step_at_border
#print axioms ProofFile.Honest.K4.k4_keeps_column_at_border
#print axioms ProofFile.Honest.K4.k4_reply_column_at_border
#print axioms ProofFile.Honest.K4.k4_lays_column_at_border
#print axioms ProofFile.Honest.K4.k4_behindS_at_border
