-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Law/NoHouse/BackLeaves.lean: what the clauses of `keeps` at the
sub-protocols from a segment's batching to its shutting leave of the verifier's state, in the forms
that the rider clauses of the first chain's invariant need (Thread/CsHead.lean,
Thread/GatherStays.lean). The clauses are those of the authors of each kind's lemmas: `k9KeepsAt`
with `K9Keeps`, `EqKeeps`, `ShutKeeps` (Johnson/Desc/ProofFile/Honest/K9/), `K10Keeps`
(Johnson/Desc/K10/Honest/Keeps.lean), and `keepsFrame` with `keepsBehind` (KeepsFrame.lean,
BehindKeeps.lean). No definition.

  1  `k9Keeps_rest9`   the clause of the batching leaves the library's `rest9`
     (Johnson/Desc/First/Link/Law/Rest9.lean), if every run of claims that the batching calls does
  2  `rest9_lay_own`, `rest9_head3`   from "`rest9` is the same at every blank": in a feed-forward
     segment the field `own` is the same; in the output head's segment the fields `x`, `t`, `wo`
  3  `k10_head3`   the same three fields after the closing
  4  `bat_rest9_at`   under the library's `AtMgA`, at the batching of each of the 25 segments:
     `k9KeepsAt` at the place of the sub-protocol at that number leaves `rest9`
  5  `eq_at`, `shut_at`   at the numbers of the one equation and of the shutting: `k9KeepsAt` at the
     place there gives `EqKeeps`, `ShutKeeps`
  6  `behind_arm`   at the number of the frame's step after the batching: `keepsFrame` at the place
     there is `keepsBehind`

`rest9 L₀ F₀ t₀ s` is the state `s` with no count of rows owed and, in the open segment's part, the
link's context, the ledger and the range proof's state replaced by `L₀`, `F₀`, `t₀`.

For the one equation and the shutting the same three fields are in `EqKeeps.head` and
`ShutKeeps.head` (K9/CloseLeaves.lean). `beside_headOf`, which `k10_head3` calls, is from
K9/KeepsDecide.lean. Both files are by the authors of K9's lemmas.

Limits.
  * Nothing shows that any clause holds at any step.
  * The one equation changes the statement, so it does not leave `rest9`.
  * Items 4 to 6: full size only, under `AtMgA` at the hash function `secondHashFunction`.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.NoHouse.BehindLeft
import Johnson.Desc.ProofFile.Honest.Law.NoHouse.BehindAll
import Johnson.Desc.ProofFile.Honest.Law.NoHouse.KeepsFrame
import Johnson.Desc.ProofFile.Honest.Thread.HeadKeepsAt
import Johnson.Desc.ProofFile.Honest.K9.KeepsAtPlace
import Johnson.Desc.ProofFile.Honest.K9.SeatTied
import Johnson.Desc.ProofFile.Honest.K9.KeepsDecide
import Johnson.Desc.K10.Honest.Keeps
import Johnson.Desc.First.Link.Law.Rest9
import Johnson.LPFK9R.HtinAtConstant
import Johnson.P5J.K09List

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Chain Place KindName Block Claim claimsInBy)
open VerifiableInference.Desc.First (S HeadOwn LayOwn Here)
open VerifiableInference.Desc.LinkJoin (rest9 here9 rests_rest9 rest_set rest_putLink hearN)
open ProofFile.Honest.K9 (K9Keeps EqKeeps ShutKeeps k9KeepsAt claimsRunOf)
open ProofFile.Honest.K10.YesFree (K10Keeps)
open OnBytes.Maker (WholeD)
open P5J (AtMgA TS fullLinks)

/-! ## 1 The batching's clause and `rest9` -/

/-- The clause of the batching leaves `rest9`, if every run of claims that the order names does. -/
theorem k9Keeps_rest9 (L₀ : OnBytes.Model.LinkCtx) (F₀ : OnBytes.Model.Fork)
    (t₀ : OnBytes.Model.HTailF2) {p : VerifiableInference.Desc.K9.Where}
    {each : Nat × String → List Claim → S → Except String Unit} {bs : List (Block S Claim)}
    {order : List (Nat × String)} {s s' : S} (H : K9Keeps p (claimsInBy each bs order) s s')
    (hrun : ∀ o ∈ order, ∀ run, claimsRunOf bs o = some run → ∀ n e c e₁,
      run n e = .ok (c, e₁) → rest9 L₀ F₀ t₀ e₁ = rest9 L₀ F₀ t₀ e) :
    rest9 L₀ F₀ t₀ s' = rest9 L₀ F₀ t₀ s :=
  H.left (fun v z => rest9 L₀ F₀ t₀ z = rest9 L₀ F₀ t₀ v) (fun _ => rfl)
    (fun _ _ _ h h' => h'.trans h)
    (fun v a q ha hq => rest_set L₀ F₀ t₀ v a q ha (by rw [hq]))
    fun o ho run hr n v z hz => hrun o ho run hr n v z.1 z.2 hz

/-! ## 2 From "`rest9` is the same at every blank" -/

/-- In a feed-forward segment: the chain is still there, and the field `own` is the same. -/
theorem rest9_lay_own {s s' : S} (h : ∀ L₀ F₀ t₀, rest9 L₀ F₀ t₀ s' = rest9 L₀ F₀ t₀ s) :
    ∀ a, s.here = .lay a → ∃ a', s'.here = .lay a' ∧ a'.own = a.own := by
  intro a ha
  have e := h a.L a.F a.tl
  have e' : (rest9 a.L a.F a.tl s').here = (rest9 a.L a.F a.tl s).here :=
    congrArg (fun z : S => z.here) e
  have e'' : here9 a.L a.F a.tl s'.here = here9 a.L a.F a.tl s.here := e'
  rw [ha] at e''
  cases hs : s'.here with
  | lay a' =>
    rw [hs] at e''
    have e3 : ({ a' with L := a.L, F := a.F, tl := a.tl } : LayOwn) =
        { a with L := a.L, F := a.F, tl := a.tl } := Here.lay.inj e''
    have e4 := congrArg (fun z : LayOwn => z.own) e3
    exact ⟨a', rfl, e4⟩
  | between => rw [hs] at e''; cases e''
  | att _ => rw [hs] at e''; cases e''
  | head _ => rw [hs] at e''; cases e''
  | fin _ => rw [hs] at e''; cases e''
  | mem _ => rw [hs] at e''; cases e''

/-- In the output head's segment: the chain is still there, and three fields are the same. -/
theorem rest9_head3 {s s' : S} (h : ∀ L₀ F₀ t₀, rest9 L₀ F₀ t₀ s' = rest9 L₀ F₀ t₀ s) :
    ∀ a, s.here = .head a →
      ∃ a', s'.here = .head a' ∧ a'.x = a.x ∧ a'.t = a.t ∧ a'.wo = a.wo := by
  intro a ha
  obtain ⟨L, F, tl, e⟩ := rest9_head h a ha
  exact ⟨_, e, rfl, rfl, rfl⟩

/-! ## 3 The closing -/

theorem k10_head3 {s s' : S} (h : K10Keeps s s') :
    ∀ a, s.here = .head a →
      ∃ a', s'.here = .head a' ∧ a'.x = a.x ∧ a'.t = a.t ∧ a'.wo = a.wo :=
  ProofFile.Honest.K9.head_form
    (ProofFile.Honest.K10.YesFree.keeps_beside ProofFile.Honest.K9.beside_headOf h)

/-! ## 4 to 6 At the numbers of the first chain -/

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)

include h

/-- At the batching of segment `l`: the clause by the place leaves `rest9`. -/
theorem bat_rest9_at {l : Nat} (hl : l < 25) :
    ∀ blk, cF.blocksInOrder[14 * l + IM.nAt l + 2]? = some blk → ∀ s s',
      k9KeepsAt cF Zp blk.place s s' →
      ∀ L₀ F₀ t₀, rest9 L₀ F₀ t₀ s' = rest9 L₀ F₀ t₀ s := by
  intro blk hb s s' K L₀ F₀ t₀
  obtain ⟨Lk, p, w, Q, bE, bS, Sd, -⟩ := ProofFile.Honest.K9.seats_at_head h hl
  obtain rfl := Option.some.inj (hb.symm.trans Sd.batching)
  have hK9 := ProofFile.Honest.K9.bat_of_k9KeepsAt Sd K
  obtain ⟨hlk, seg, drawB, kp⟩ := ProofFile.Honest.K9.tied_of_seated h hl Sd
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  refine k9Keeps_rest9 L₀ F₀ t₀ hK9 ?_
  obtain ⟨g, hg⟩ : ∃ g, l = 2 * g ∨ l = 2 * g + 1 := ⟨l / 2, by omega⟩
  by_cases h24 : l = 24
  · subst h24
    exact fun o ho run hr => ProofFile.Honest.K9.fieldRun_head_at h O rfl Lk p hlk seg drawB kp {}
      (rests_rest9 L₀ F₀ t₀) o ho run hr
  · rcases hg with rfl | rfl
    · exact fun o ho run hr => ProofFile.Honest.K9.fieldRun_lay_at h O (2 * g) hl
        (lay_sub g (by omega)) Lk p hlk seg drawB kp {} (rests_rest9 L₀ F₀ t₀) o ho run hr
    · exact fun o ho run hr => ProofFile.Honest.K9.fieldRun_att_at h O (g := g) (by omega)
        (ProofFile.Honest.K9.sub_odd g (by omega)) Lk p hlk seg drawB kp {} (rests_rest9 L₀ F₀ t₀) o ho
        run hr

/-- At the one equation of segment `l`: the clause by the place gives `EqKeeps`. -/
theorem eq_at {l : Nat} (hl : l < 25) :
    ∀ blk, cF.blocksInOrder[14 * l + IM.nAt l + 4]? = some blk → ∀ s s',
      k9KeepsAt cF Zp blk.place s s' → EqKeeps s s' := by
  intro blk hb s s' K
  obtain ⟨Lk, p, w, Q, bE, bS, Sd, H⟩ := ProofFile.Honest.K9.seats_at_head h hl
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have e := H.atE
  rw [Sd.hears] at e
  obtain rfl := Option.some.inj (hb.symm.trans e)
  obtain ⟨-, -, e3⟩ := IM.k9Where_fields H.numbers
  have e1 := ProofFile.Honest.K9.piece_at_seat h.scope h.reads O hl H.numbers
  exact ProofFile.Honest.K9.eq_of_k9KeepsAt H (by show _ + 3 + 0 = p.pieceEq; omega) K

/-- At the shutting of segment `l`: the clause by the place gives `ShutKeeps`. -/
theorem shut_at {l : Nat} (hl : l < 25) :
    ∀ blk, cF.blocksInOrder[14 * l + IM.nAt l + 6]? = some blk → ∀ s s',
      k9KeepsAt cF Zp blk.place s s' → ShutKeeps s s' := by
  intro blk hb s s' K
  obtain ⟨Lk, p, w, Q, bE, bS, Sd, H⟩ := ProofFile.Honest.K9.seats_at_head h hl
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have e := H.atS
  rw [Sd.hears] at e
  obtain rfl := Option.some.inj (hb.symm.trans e)
  obtain ⟨-, -, e3⟩ := IM.k9Where_fields H.numbers
  have e1 := ProofFile.Honest.K9.piece_at_seat h.scope h.reads O hl H.numbers
  exact ProofFile.Honest.K9.shut_of_k9KeepsAt H (by show _ + 3 + 2 = p.pieceEq + 2; omega) K

/-- At the frame's step after the batching of segment `l`: the clause by the place is
`keepsBehind`. -/
theorem behind_arm (take : Nat → Bool) {l : Nat} (hl : l < 25) :
    ∀ blk, cF.blocksInOrder[14 * l + IM.nAt l + 3]? = some blk → ∀ s s',
      (keepsFrame P5J.At.links take blk.place s s' ↔ keepsBehind s s') := by
  intro blk hb s s'
  obtain ⟨Lk, p9, Q9, b₃, b₅, St⟩ := P5J.sits_at h l hl
  have hs := behind_seat h St
  rw [LPFK9.batch_nAt l hl] at hs
  obtain rfl : blk = Lk.behindB := Option.some.inj (hb.symm.trans hs)
  refine keepsFrame_behind P5J.At.links take (l := l) ?_ ?_ s s'
  · show some Lk.number = some l
    rw [behind_num_head h hl St.lk]
  · show Lk.hear.length + 2 = hearN fullLinks l + 2
    unfold hearN
    rw [St.sort, St.seg.hear]
    rfl

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.k9Keeps_rest9
#print axioms ProofFile.Honest.FirstThread.rest9_lay_own
#print axioms ProofFile.Honest.FirstThread.rest9_head3
#print axioms ProofFile.Honest.FirstThread.k10_head3
#print axioms ProofFile.Honest.FirstThread.bat_rest9_at
#print axioms ProofFile.Honest.FirstThread.eq_at
#print axioms ProofFile.Honest.FirstThread.shut_at
#print axioms ProofFile.Honest.FirstThread.behind_arm
