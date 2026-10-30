-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/MergeLaw/MaskReached.lean: the test `maskMsgB` (MaskFront.lean) accepts at every
state that the chain's own sub-protocols hand on to a border behind the opening of the output head's
segment; and with it the test `maskAtB` (MaskRow.lean), at the form in which the law of the merge of
the claims on the committed table takes it. One definition with code, and theorems with their
proofs.

How. "Reached" (Johnson/Top/H0/Walk/Reach.lean) is inductive: a state at border k + 1 comes by an
accepting step of sub-protocol number k from a state that is reached at border k. So no induction
over the whole chain is wanted: from the border in question the steps are taken back one by one: n
sub-protocols that leave what the test reads (`SegStays`, MaskKeeps.lean), the one that opens the
segment (`OpenedAt`, MaskMaker.lean), and the one in front of it, behind which the state stands in
the output head's segment with a fresh frame at rest (`HeadFresh`). No step asks that the state
bears no mark.

The number O is counted back from the number of the statement's oracle messages at the border in
question, which the table's condition says there: behind the segment's first messages its first
sending holds one message more, and the n sub-protocols add `total d n`.

Main names:
  `reach_pred`: "reached" at border j + 1, taken back one step.
  `total d n`: d 0 + ... + d (n - 1). With code.
  `reach_back`: n steps back over sub-protocols that have `SegStays`.
  `maskMsgB_reached`: THE TEST AT A REACHED STATE. The sub-protocols are any with these three
    premises: number k0 makes `HeadFresh`, number k0 + 1 makes `OpenedAt l` of it, the n behind have
    `SegStays`. sh is the shape in the open segment's frame at the state in question, N its
    statement's number of messages; by sh the first of segment l's messages with mask rows has a
    number m below the number of the segment's first messages.
  `maskAtB_reached`: THE TEST OF MaskRow.lean AT BORDER k0 + 2 + n, for every statement that meets
    the table's condition there, bears no mark and lies in a family Rch all of whose members are
    reached. That the segment is the output head's is said by `HeadFresh` alone: the sort sub and
    the number l are free, and neither is held against the place p.

Limits. Where one of the sub-protocols number k0 to k0 + 1 + n never accepts from a reached state,
nothing is reached at border k0 + 2 + n, and both theorems speak of no state there; no reached state
is exhibited here. That the IOP as written in Lean holds such sub-protocols at these numbers is a
premise, and so is that the family's members are reached. Three more premises on the family, at that
one border and at unmarked states: `atFirstSeats` and `atFirstShapes` (Johnson/Desc/K12/Door)
accept, and the copy in use of the state of the calls has the shape sh. The premise m < `firstCount`
does not say that message m of the shape is of the first moment: `maskNoOf` counts among all the
segment's messages in the shape's order, `firstCount` counts those of the first moment wherever they
stand; the theorems hold all the same, for `maskOracle` itself reads the frame's list at m. No
example at the release's own values is given: that the premises on numbers can be met there is not
shown. Nothing on soundness.

-/
import Johnson.Top.H0.MergeLaw.MaskKeeps
import Johnson.Top.H0.MergeLaw.MaskMaker
import Johnson.Top.H0.Walk.ReachInv

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.MergeLaw
open OnBytes
open OnBytes.Model (LinkCtx)
open OnBytes.Params (ReqShape)
open VerifiableInference.Desc.Keeps (Decides)
open Johnson.Desc.First.Walk.Tied (Reach StepYes stepYes_decide)

section
variable {T Cl P : Type} {ft : ℕ} {bs : List (Block T Cl)} {start : P → T}

/-- "Reached" at border j + 1, taken back one step. -/
theorem reach_pred {k : ℕ} {a : P × T} (h : Reach ft bs start k a) : ∀ j, k = j + 1 →
    ∃ s b, Reach ft bs start j (a.1, s) ∧ bs[j]? = some b ∧ StepYes ft b s a.2 := by
  cases h with
  | zero z =>
    intro j e
    exact absurd e.symm (Nat.succ_ne_zero j)
  | succ hr hb hy =>
    intro j e
    obtain rfl := Nat.add_right_cancel e
    exact ⟨_, _, hr, hb, hy⟩

end

/-- d 0 + ... + d (n - 1). -/
def total (d : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => total d n + d n

section
variable {Cl P : Type} {ft : ℕ} {bs : List (Block S Cl)} {start : P → S}

/-- **n steps back** over sub-protocols that leave what the test reads. -/
theorem reach_back {k : ℕ} (d : ℕ → ℕ) : ∀ n : ℕ,
    (∀ i, i < n → ∃ b, bs[k + i]? = some b ∧ Decides (SegStays (d i)) b) →
    ∀ (z : P) (s' : S), Reach ft bs start (k + n) (z, s') →
      ∃ s, Reach ft bs start k (z, s) ∧ SegStays (total d n) s s'
  | 0, _, _, s', h => ⟨s', h, segStays_refl s'⟩
  | n + 1, hk, z, s', h => by
    obtain ⟨t, b, hr, hb, hy⟩ := reach_pred h (k + n) rfl
    obtain ⟨b', hb', hd⟩ := hk n (Nat.lt_succ_self n)
    obtain rfl : b = b' := Option.some.inj (hb.symm.trans hb')
    obtain ⟨rs, gs, hyes⟩ := stepYes_decide hy
    obtain ⟨s, hs, hst⟩ := reach_back d n (fun i hi => hk i (Nat.lt_succ_of_lt hi)) z t hr
    exact ⟨s, hs, hst.trans (hd t rs gs s' hyes)⟩

/-- **`maskMsgB O` accepts at a state that is reached at border k0 + 2 + n**: where sub-protocol
number k0 makes "fresh", number k0 + 1 makes "opened" of it, and the n behind leave what the test
reads and add `total d n` messages; the open segment's frame has the shape sh, by which the first of
segment l's messages with mask rows has a number m below the number of the segment's first messages;
and O is counted back from the statement's number N of messages. -/
theorem maskMsgB_reached {k0 n l : ℕ} {b1 b2 : Block S Cl} (d : ℕ → ℕ)
    (h1 : bs[k0]? = some b1) (hb1 : Decides (fun _ s' => HeadFresh s') b1)
    (h2 : bs[k0 + 1]? = some b2) (hb2 : Decides (fun s s' => HeadFresh s → OpenedAt l s') b2)
    (hk : ∀ i, i < n → ∃ b, bs[k0 + 2 + i]? = some b ∧ Decides (SegStays (d i)) b)
    {sh : ReqShape} {m O N : ℕ} (hm : maskNoOf sh l = some m) (hlt : m < firstCount sh l)
    (hO : O + (firstCount sh l + 1) + total d n = N + m) {z : P} {s : S}
    (hr : Reach ft bs start (k0 + 2 + n) (z, s)) (hsh : s.live.frame.shape = sh)
    (hN : s.st.oracles.size = N) : maskMsgB O s = true := by
  obtain ⟨s2, hr2, hst⟩ := reach_back d n hk z s hr
  obtain ⟨s1, c2, hr1, hc2, hy2⟩ := reach_pred hr2 (k0 + 1) rfl
  obtain rfl : c2 = b2 := Option.some.inj (hc2.symm.trans h2)
  obtain ⟨s0, c1, _, hc1, hy1⟩ := reach_pred hr1 k0 rfl
  obtain rfl : c1 = b1 := Option.some.inj (hc1.symm.trans h1)
  obtain ⟨rs1, gs1, y1⟩ := stepYes_decide hy1
  obtain ⟨rs2, gs2, y2⟩ := stepYes_decide hy2
  have hop : OpenedAt l s2 := hb2 s1 rs2 gs2 s2 y2 (hb1 s0 rs1 gs1 s1 y1)
  refine hst.mask (hop.mask (sh := sh) (fun L hL => ?_) hm hlt ?_)
  · obtain ⟨L', hL', _, _, _, e, _⟩ := hst.2 L hL
    rw [← e, ← hsh]
    unfold S.live
    rewrite [hL']
    rfl
  · have e := hst.1
    omega

end

/-- **`maskAtB` accepts at border k0 + 2 + n**, at every statement that meets the table's condition
there, lies in the family Rch and bears no mark. Every member of the family is reached (hR). p: the
place of the sub-protocol behind the border. The premises on the sub-protocols and on sh, m, O are
those of `maskMsgB_reached`, at N := the table's number of messages at p. -/
theorem maskAtB_reached {Pp W Cl : Type} {Fr : Sound.Frame} {ft : ℕ} {bs : List (Block S Cl)}
    {start : Pp → S} (Rch : ℕ → (Pp × S) × Fr.E.Str → Prop) (Nn : Numbers) (Mg : Meaning Pp W)
    (links : List ModelPart) (ps : List Place) (own : List (ℕ × ℕ)) (x : ℕ × ℕ) (R O k0 n l : ℕ)
    (L : K12.Door.Laid) (M : List OracleShape) (p : Place) (sub : ModelPart) {b1 b2 : Block S Cl}
    (d : ℕ → ℕ) (sh : ReqShape) (m : ℕ)
    (hR : ∀ a, Rch (k0 + 2 + n) a → Reach ft bs start (k0 + 2 + n) a.1)
    (h1 : bs[k0]? = some b1) (hb1 : Decides (fun _ s' => HeadFresh s') b1)
    (h2 : bs[k0 + 1]? = some b2) (hb2 : Decides (fun s s' => HeadFresh s → OpenedAt l s') b2)
    (hk : ∀ i, i < n → ∃ b, bs[k0 + 2 + i]? = some b ∧ Decides (SegStays (d i)) b)
    (hm : maskNoOf sh l = some m) (hlt : m < firstCount sh l)
    (hnum : O + (firstCount sh l + 1) + total d n = Nn.msgsAt (some p) + m)
    (hp : ps[k0 + 2 + n]? = some p) (hstand : standAt links p = .link sub)
    (hx : L.places[O]? = some x) (hown : x ∈ own)
    (hRb : (M[O]?).map (fun y => ceilLog2 y.maskRows) = some R)
    (hseats : ∀ a, Rch (k0 + 2 + n) a → a.1.2.failed = none →
      K12.Door.atFirstSeats L a.1.2 = true)
    (hshapes : ∀ a, Rch (k0 + 2 + n) a → a.1.2.failed = none →
      K12.Door.atFirstShapes M a.1.2 = true)
    (hlive : ∀ a, Rch (k0 + 2 + n) a → a.1.2.failed = none → a.1.2.live.frame.shape = sh) :
    ∀ (z : Pp) (a : S × Fr.E.Str),
      Sound.onQ Nn Mg links ps (fun s => (z, s)) (k0 + 2 + n) a →
      Rch (k0 + 2 + n) ((z, a.1), a.2) → a.1.failed = none → maskAtB own x R a.1 = true :=
  maskAtB_at_border Rch Nn Mg links ps own x R O (k0 + 2 + n) L M p sub hp hstand (by omega) hx
    hown hRb hseats hshapes fun a ha hf hN =>
      maskMsgB_reached (z := a.1.1) (s := a.1.2) d h1 hb1 h2 hb2 hk hm hlt hnum (hR a ha)
        (hlive a ha hf) hN

end VerifiableInference.Desc.First.MergeLaw

#print axioms VerifiableInference.Desc.First.MergeLaw.reach_pred
#print axioms VerifiableInference.Desc.First.MergeLaw.reach_back
#print axioms VerifiableInference.Desc.First.MergeLaw.maskMsgB_reached
#print axioms VerifiableInference.Desc.First.MergeLaw.maskAtB_reached
