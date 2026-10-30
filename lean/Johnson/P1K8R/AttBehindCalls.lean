-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K8R/AttBehindCalls.lean: THE FIRST CHAIN, AT AN ATTENTION SEGMENT: (1) BEHIND THE OWN STEP
OF THE LOOKUP ON THE SEGMENT's CALLS WHATEVER THE OPEN SEGMENT's FIELD g HOLDS IS WHAT THE STATE
HOLDS AS HEARD; (2) IN FRONT OF THE BATCHING THE STATE's LIST OF MATRICES AND THEIR NUMBER ARE THE
PLAN's. UNDER THE SCOPE, THE FILES READ, IM.Open (AND, FOR (1), THE DESCRIPTION's TEST ON ITS PLAN).
Lemmas; NONE OF THE LIBRARY's GOALS. No prover stands in them. Nothing on completeness, soundness or
hiding.
Why. An open attention segment has two fields for what the lookup on its calls returned: g, which
the segment's own rounds and the step that lays the tables read, and lookHeard, which the state
answers by. A sentence on the one is wanted of the other.

  `g_of_hearLook`, `g_behind_calls`   the lines of LinkJoin.fo_of_hearLook, padNames_behind_calls
      (Johnson/Desc/First/Link/Law/K4AtFront.lean), A SECOND TIME, at the other sort of segment;
      theStated_yes_calls (the same file), OnPublicFiles.decide_named: called
  **`att_g_behind`**   as `own_behind_calls` (Johnson/P1K8R/OwnBetween.lean) comes to that
      lookup's decision: its lines a second time
  **`sizes_at_att`**   LinkJoin.planned_at_batch (Johnson/Desc/First/Link/Law/PlannedAtDraw.lean)
      at `planned_sizes` (Johnson/P1K8R/TiesAtBatch.lean)
Kin. THE NEAREST: Johnson/Desc/ProofFile/Honest/K3/Law/Thread/PutG.lean: put_g is `g_of_hearLook`'s
sentence at the seat's writer; member_back_g, and back_g_link (AtLink.lean) under the description's
head, and att_back_head (AttBackHead.lean: at the number 14 (2 g + 1) + 3, under that head) are
`att_g_behind`'s NEAR TWINS: behind the member's accepting step the open attention segment's field g
holds what the hearing returned. NOT CALLED: this file imports none of these three files, and the
library may hold none of them; they name the value as the hearing's return; here it is what the
STATE answers as heard, at the number 14 l + 3. Besides: Att.hearLook_lays, LookIsHeard
(Johnson/Desc/First/Att/Claims/Premises.lean): behind the hearing both fields are laid and are one:
on the bare function; lookAtt_opens (Att/Door/LookGives.lean): from a test with code on the state.
`sizes_at_att` IS `mats_at_att` (Johnson/P1K8R/LiveTablesOfMark.lean) WITH THE NUMBER OF MATRICES
BESIDE THE LIST: its lines a second time; that file stands over the honest side's frame, this one
does not, and the library may not hold it. Also: seatReads_of_look
(Johnson/Desc/First/Att/K05SeatReadsTie.lean): from the same test with code: four equations between
the two fields, not the whole. tlOpen_head (Johnson/Desc/K5/Honest/Law/TlOpen.lean): under the head,
at a state reached at 14 (2 g + 1) + 4: the open segment's own list has the plan's number of
matrices: `sizes_at_att`'s clause on the number, five members earlier.
Limits. In scope alone. Nothing says that any step says yes or that any state is reached. (1) says
nothing where no attention segment is open, nor where the open segment's field g is empty: that it
holds something is `g_behind_calls`', at the lookup's decision.
Terms: lean/GLOSSARY.md.
-/
import Johnson.P1K8R.OwnBetween
import Johnson.P1K8R.TiesAtBatch

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K8
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open OnBytes.Model.Stages (LinkH)
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.First.K8 VerifiableInference.Desc.First.K8.Ready
open Johnson.Desc.First.Walk.Tied (Reach)

/-- Where nothing was heard yet, the hearing of the lookup on the calls lays its value in the field
g of an open attention segment. `LinkJoin.fo_of_hearLook`
(Johnson/Desc/First/Link/Law/K4AtFront.lean) at the other sort of segment: its lines, the arms
turned. -/
theorem g_of_hearLook (s : S) (g : Forest.Heard) (hn : s.lookHeard? = none) {a : First.AttOwn}
    (ha : (s.hearLook g).here = .att a) : a.g = some g := by
  have hm : ∀ n, (s.mark n).here = s.here := fun n => by
    unfold S.mark
    split <;> rfl
  cases hh : s.here with
  | att a0 =>
    have h0 : a0.lookHeard = none := by simpa [S.lookHeard?, hh] using hn
    have e : s.hearLook g =
        { s with here := .att { a0 with g := some g, lookHeard := some g } } := by
      simp [S.hearLook, hh, h0]
    rw [e] at ha
    obtain rfl := First.Here.att.inj ha
    rfl
  | lay a0 =>
    exfalso
    simp only [S.hearLook, hh] at ha
    split at ha
    · rw [hm, hh] at ha
      cases ha
    · cases ha
  | head a0 =>
    exfalso
    simp only [S.hearLook, hh] at ha
    split at ha
    · rw [hm, hh] at ha
      cases ha
    · split at ha
      · rw [hm, hh] at ha
        cases ha
      · cases ha
  | between =>
    exfalso
    simp only [S.hearLook, hh] at ha
    rw [hm, hh] at ha
    cases ha
  | fin _ =>
    exfalso
    simp only [S.hearLook, hh] at ha
    rw [hm, hh] at ha
    cases ha
  | mem _ =>
    exfalso
    simp only [S.hearLook, hh] at ha
    rw [hm, hh] at ha
    cases ha

/-- **BEHIND A YES OF THE SEATED LOOKUP ON THE CALLS: WHAT THE STATE HOLDS AS HEARD IS WHAT AN OPEN
ATTENTION SEGMENT's FIELD g HOLDS.** `LinkJoin.padNames_behind_calls` (the same file) at the other
sort of segment, without its clause on the names and so without its two premises on the ledger. -/
theorem g_behind_calls {Cl : Type} (claim : Aff → Cl) (readers : ℕ → Option (K3.Readers S))
    (X : Verify.Public) (codes : Codes) (shape : Params.ReqShape) (a : Place) (B : Block S Cl)
    (h : K3.theStated claim readers X codes shape a = some B) (hOk : B.planOk = true) (i : ℕ)
    (hi : a.link = some i) (hpc : a.piece = K3.pieceAt X i false) (s c : S) (rs : List Fmt.RoundView)
    (gs : List (List (ℕ × List UInt64))) (hd : B.decide s rs gs = .ok c) :
    ∃ fo, c.lookHeard? = some fo ∧ ∀ a, c.here = .att a → a.g = some fo := by
  obtain ⟨P', sent, laid, n, gs', -, hyes⟩ :=
    LinkJoin.theStated_yes_calls claim readers X codes shape a B h hOk i hi hpc s c rs gs hd
  obtain ⟨F, y, hF, hn, e, -⟩ :=
    OnPublicFiles.decide_named (K3.seatCalls claim) a.piece laid sent P' [] s c _ gs' hyes
  have hsome : ((K3.seatCalls claim).fork s).isSome = true := by
    rw [hF]
    rfl
  refine ⟨y.1, ?_, fun a ha => ?_⟩
  · rw [e]
    exact K3.seatCalls_reads claim _ _ _ hsome hn
  · rw [e] at ha
    exact g_of_hearLook (s.putFork y.2) y.1 ((S.look_putFork s y.2).trans hn) ha

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Claim)} {c : Chain S Claim}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **AT THE FIRST CHAIN, BEHIND THE OWN STEP OF THE LOOKUP ON A SEGMENT's CALLS** (l < 24): where
an attention segment is open behind it, whatever its field g holds is what the state holds as heard.
-/
theorem att_g_behind (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true)
    {l : ℕ} (hl : l < 24) {blk : Block S Claim} (hblk : c.blocksInOrder[14 * l + 3]? = some blk)
    {sj sk : S} {R : List Fmt.RoundView} {cs : List Desc.OpenedColumn}
    (hst : blk.step 0 sj R cs = .ok (sk, cs.length)) {gH : Forest.Heard}
    (hgH : sk.lookHeard? = some gH) :
    ∀ att G, sk.here = .att att → att.g = some G → G = gH := by
  have n24 : ¬ l = 24 := by omega
  obtain ⟨Lk', b₃, b', f1, f2, f3, f4⟩ := IM.k3_of hS hR O l (by omega) false
  have i3 : IM.k3Ix l false = 1 := by
    show (if false = true then 6 else 1) + (if l = 24 then 1 else 0) = 1
    rw [if_neg n24]
    rfl
  have hf3 : c.blocksInOrder[14 * l + 3]? = some b₃ := by
    have k := IM.hear_at_flat f1 f2
    rw [IM.flatIx_scope hS hR O (by omega : l ≤ 24) (IM.k3Ix l false), i3] at k
    exact k
  obtain rfl : b₃ = blk := Option.some.inj (hf3.symm.trans hblk)
  obtain ⟨b'', f3', hk⟩ := OnPublicFiles.k03_const_ok hS hR O hOk l (by omega) false
  obtain rfl : b' = b'' := Option.some.inj (f3.symm.trans f3')
  have hd3 := ((Sound.step_ok_iff 0 b₃ sj sk R cs cs.length).1 hst).2.2.2
  have hd3' := ((IM.yes_alone f4 (fun q => nomatch q) sj sk _ _).1 hd3).1
  have hp3 : (IM.k3Place l false).piece ≤ 3 := by
    show (if false = true then 6 else 1) + (if l = 24 then 1 else 0) + 1 ≤ 3
    rw [if_neg n24]
    decide
  obtain ⟨fo', hlk, hatt⟩ := g_behind_calls _ _ _ _ _ _ b' f3 hk l rfl
    (LinkJoin.piece_at_calls _ _ _ _ _ _ b' f3 l rfl hp3) sj sk _ _ hd3'
  obtain rfl : fo' = gH := Option.some.inj (hlk.symm.trans hgH)
  intro att G ha hG
  exact Option.some.inj (hG.symm.trans (hatt att ha))

/-- **IN FRONT OF AN ATTENTION SEGMENT's BATCHING, AT A REACHED STATE: THE LIST OF MATRICES AND
THEIR NUMBER ARE THE PLAN's.** -/
theorem sizes_at_att (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {g : ℕ} (hg : g < 12)
    {z : ProofFile.InstPub} {s : S}
    (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * (2 * g + 1) + 9) (z, s)) :
    ∃ q tl, Bs.G₀.W.A[g]? = some q ∧ s.tl? = some tl ∧ tl.NM = q.seam.tl.NM ∧
      tl.mats = q.seam.tl.mats := by
  obtain ⟨hN, -⟩ := IM.ground_named hS hR O.pub O.blank
  obtain ⟨-, X, -, -, -, -, e3, -⟩ := hN g hg
  obtain ⟨hT, -⟩ := IM.ground_tails hS hR O.pub O.blank
  obtain ⟨-, q, -, X', -, eq, -, -, -, -, -, -, e3', htl, -⟩ := hT g hg
  obtain rfl : X = X' := Option.some.inj (e3.symm.trans e3')
  have hv := LinkJoin.planned_at_batch planned_sizes hS hR O (x := (2 * g + 1, 4, 2))
    (List.mem_map.2 ⟨2 * g + 1, List.mem_range.2 (by omega), by
      rw [if_neg (by omega : ¬ 2 * g + 1 = 24), if_neg (by omega : ¬ 2 * g + 1 = 24)]⟩)
    e3 (z, s) h
  rw [htl] at hv
  unfold readTl at hv
  cases hts : s.tl? with
  | none =>
    rw [hts] at hv
    exact absurd hv (by simp)
  | some tl =>
    rw [hts] at hv
    have e := Option.some.inj hv
    simp only [sizesView, Prod.mk.injEq] at e
    exact ⟨q, tl, eq, rfl, e.1, e.2.2.1⟩

end

end P1K8

#print axioms P1K8.g_of_hearLook
#print axioms P1K8.g_behind_calls
#print axioms P1K8.att_g_behind
#print axioms P1K8.sizes_at_att
