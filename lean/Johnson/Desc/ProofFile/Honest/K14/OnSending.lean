-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K14/OnSending.lean: kind K14: THE SENTENCE AT ENTRY OF THE TWO
SENDINGS' ROWS (pointApart, Honest/K14/ExactDefs.lean: the number of "LIN point" is not the number
of challenges heard) FOLLOWS FROM THE FRAME's SENTENCE ON WHERE A RUN STANDS: in the form OnFrom
(Honest/Thread/OnFrom.lean), which the frame's rules for rows take beside the field exact, at the
same sentence. Statements with their proofs: on lengths of lists; no distribution occurs; no
definition.

  inside_fit      in front of a member's first round the run has heard just the challenges of the
                  rounds in front: as many
  onFrom_sending  **OnFrom at a row of one part whose sentence at entry follows from pointApart**,
                  where the number of "LIN point" is not the number of rounds in front: general in
                  the frame's sentence T, the row and the bound on positions
  heard_in_front  at a list that begins as the shared rounds' blocksInOrder list does: at least one round
                  stands in front of every member at the place of "send o_u" or "send o_omega"
  onFrom_rows     **so OnFrom holds at both rows of sendingRows** (Honest/K14/ExactRows.lean) with
                  "LIN point" as round number 0, at every such list, at every member at the row's
                  place, WHATEVER WAS HEARD IN FRONT OF THE LIST

What is assumed. In onFrom_rows: that the frame's sentence T speaks of a list of the form FlatOf
(Johnson/Desc/K14/Honest/FlatForm.lean) at eight sub-protocols that the library makes; that the laid
row has the place, the parts and the sentence at entry of a row of sendingRows.
What is not claimed. That a frame's sentence T can be entered or holds along a run. That a filling
lays these rows. Anything on the bound on positions. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K14.ExactRows
import Johnson.Desc.ProofFile.Honest.K14.DataMade
import Johnson.Desc.ProofFile.Honest.K14.FreshShows
import Johnson.Desc.ProofFile.Honest.Thread.OnFrom

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open VerifiableInference.Desc (Block)
open Desc.K14 (P14 St blocks)
open Desc.K14.Honest (FlatOf)

variable {Bk : ProverCoinCounts} {S Cl X Pb W₀ Rc Ky : Type}

/-- **In front of a member's first round the run has heard as many challenges as there are rounds in
front.** -/
theorem inside_fit (T : Thread Bk S Cl Empty (Common W₀ Rc Ky) X Pb) {b : Nat} {k : Coins Bk}
    {m : Mid (Common W₀ Rc Ky) X} {E : Env} (h : Inside T b 0 k m E) :
    m.st.heard.length = (T.ahead ++ declsTo T.bs b).length := by
  unfold Inside at h
  obtain ⟨blk, s, m₀, E₀, l, ds, y, -, hT, -, hd, hy, rfl, -⟩ := h
  have hd0 : ds = [] := by
    have e := drawsFit_length _ _ hd
    rw [List.take_zero] at e
    exact List.eq_nil_of_length_eq_zero e
  subst hd0
  rw [List.take_zero] at hy
  have ey : (([], m₀) : List Played × Mid (Common W₀ Rc Ky) X) = y := Except.ok.inj hy
  rw [← ey]
  exact drawsFit_length _ _ hT.2.1

/-- **The sentence at entry of a sending's row follows from the frame's sentence.** -/
theorem onFrom_sending (T : Thread Bk S Cl Empty (Common W₀ Rc Ky) X Pb)
    (L : Lettered Bk S Cl Empty (Common W₀ Rc Ky) X Pb) (A : SendPub)
    (p : Part Empty (Common W₀ Rc Ky) X) (sim : Sim Pb) (hrow : L.row = [(p, sim)])
    (hOn : ∀ u ca m front, pointApart A m.st.heard → L.On u ca m front) (b : Nat)
    (hb : A.atPoint ≠ (T.ahead ++ declsTo T.bs b).length) (len : Nat → Nat → Nat) :
    OnFrom T L b len := by
  intro σ hσ u hu k m E ca front hI _ _
  have hr : σ.row = [(p, sim)] := by
    unfold Lettered.side Side.seated at hσ
    obtain ⟨blk, -, rfl⟩ := Option.map_eq_some_iff.1 hσ
    exact hrow
  rw [members_send σ p sim hr, List.mem_singleton] at hu
  subst hu
  refine hOn _ ca m front ?_
  have h0 : Inside T b 0 k m E := hI
  show A.atPoint ≠ m.st.heard.length
  rw [inside_fit T h0]
  exact hb

/-- **At least one round stands in front of either sending.** -/
theorem heard_in_front {xs : List (Block St Cl)} {c : OnBytes.Model.Verify.Chains} {P : P14}
    {b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit} (F : FlatOf xs c b1 b2 b3 b4 b5 b6 b7 b8)
    (hb : blocks P = some [b1, b2, b3, b4, b5, b6, b7, b8]) (b : Nat) (blk : Block St Cl)
    (hx : xs[b]? = some blk) (hp : blk.place = sendPlace 2 ∨ blk.place = sendPlace 5) :
    0 < (declsTo xs b).length := by
  obtain ⟨x0, x1, x2, x3, x4, x5, x6, x7, x8, tl, rfl, l0, l1, -⟩ := F
  obtain ⟨p1, -⟩ := places4 P b1 b2 b3 b4 b5 b6 b7 b8 hb
  obtain ⟨-, -, -, r1, -⟩ := declares3 P b1 b2 b3 b4 b5 b6 b7 b8 hb
  have q0 : x0.place = ⟨2, none, 0, .frame⟩ := l0.place
  have q1 : x1.place = place 1 := l1.place.trans p1
  match b, hx with
  | 0, hx =>
    obtain rfl : x0 = blk := Option.some.inj hx
    rw [q0] at hp
    simp [sendPlace] at hp
  | 1, hx =>
    obtain rfl : x1 = blk := Option.some.inj hx
    rw [q1] at hp
    simp [sendPlace, place] at hp
  | b + 2, _ =>
    unfold declsTo
    simp [List.take_succ_cons, List.flatMap_cons, l1.rounds, r1]

/-- **OnFrom at both rows of sendingRows, with "LIN point" as round number 0.** L: the row as a
filling lays it: its place, parts and sentence at entry are the row's. -/
theorem onFrom_rows (T : Thread Bk St Cl Empty (Common W₀ Rc Ky) X Pb)
    {c : OnBytes.Model.Verify.Chains} {P : P14} {b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit}
    (F : FlatOf T.bs c b1 b2 b3 b4 b5 b6 b7 b8)
    (hb : blocks P = some [b1, b2, b3, b4, b5, b6, b7, b8]) (weights : W₀ → Weights)
    (rand : Rc → TableRand) (r : Unlettered Empty (Common W₀ Rc Ky) X Pb)
    (hr : r ∈ sendingRows ⟨P, 0⟩ weights rand)
    (L : Lettered Bk St Cl Empty (Common W₀ Rc Ky) X Pb) (hplace : L.place = r.place)
    (hrow : L.row = r.row) (hOn : L.On = r.On) (b : Nat) (blk : Block St Cl)
    (hx : T.bs[b]? = some blk) (hp : blk.place = L.place) (len : Nat → Nat → Nat) :
    OnFrom T L b len := by
  have hne : ∀ hq : blk.place = sendPlace 2 ∨ blk.place = sendPlace 5,
      (⟨P, 0⟩ : SendPub).atPoint ≠ (T.ahead ++ declsTo T.bs b).length := fun hq => by
    have h1 := heard_in_front F hb b blk hx hq
    rw [List.length_append]
    show 0 ≠ _
    omega
  unfold sendingRows at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact onFrom_sending T L ⟨P, 0⟩ _ _ hrow (fun u ca m front h => by rw [hOn]; exact h) b
      (hne (Or.inl (hp.trans hplace))) len
  · exact onFrom_sending T L ⟨P, 0⟩ _ _ hrow (fun u ca m front h => by rw [hOn]; exact h) b
      (hne (Or.inr (hp.trans hplace))) len

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.inside_fit
#print axioms ProofFile.Honest.K14.onFrom_sending
#print axioms ProofFile.Honest.K14.heard_in_front
#print axioms ProofFile.Honest.K14.onFrom_rows
