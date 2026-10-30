-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P1K8R/ZeroSeat.lean: AT EVERY STATE THAT THE FIRST CHAIN's OWN SUB-PROTOCOLS REACH AT A
BORDER UP TO 353, EVERY VIRTUAL ROW OF EVERY ARRAY OF AN OPEN LEDGER BEGINS AT COLUMN 0 (`ZeroInv`,
Johnson/P1K8R/ZeroFrame.lean): IN THE GOALS' SCOPE, UNDER AN OPENING OF THE DESCRIPTION. By the
library's generic walk (Meaning.K2.SeatKeeps, Johnson/IMR/SeatKeeps.lean; open_fold,
Johnson/IMR/OpenWalk.lean), as its looks_at_open (Johnson/Desc/First/Link/Law/AtBatchOpen.lean) has
the arrays' looks. Lemmas; none of the library's goals. No prover stands in them; nothing on
completeness, soundness or hiding.

  **`seatKeeps_zero`**   every maker of the seat stands in `KeepsZero`: the term of the library's
      seatKeeps_looks (Johnson/LPFK9R/LooksSeat.lean), field for field
  `links_size`, **`okZero_at`**, **`okHeadZ_at`**   the two premises on the plan, paid by
      `built_allZero` (Johnson/P1K8R/AllZeroAtPlans.lean)
  **`zero_at_reach`**   the sentence at every reached state
  **`l0_at_batch`**   so, in front of a segment's batching: the upper virtual rows of the digits'
      array begin at column 0: the last clause of `digitsLaid`
      (Johnson/Desc/K8/Honest/DigitsFew.lean)
By: views_in_scope (Johnson/AtFull/Desc/Lots/LinksInScope.lean) · P1K8T.built_at ·
K9Asks.built_tl_Fp (Johnson/Desc/First/Link/Law/K9PosAskLaw.lean) · IM.ground_gets
(Johnson/IMR/PureJoin.lean) · reach_fold (Johnson/Top/H0/Walk/Reach.lean) · Meaning.Carry.front_len
· start_none (Johnson/LPFK9R/LooksSeat.lean).
Limits. The first chain, up to border 353: what stands behind the last link is not walked. The full
size; the earlier hash. An opening of the description is a premise.

-/
import Johnson.P1K8R.ZeroEnds
import Johnson.Desc.First.Link.Law.AtBatchOpen
import Johnson.AtFull.Desc.Lots.LinksInScope
import Johnson.Desc.First.Link.Law.K9PosAskLaw
import Johnson.P1K8R.Tied

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Keeps (Whole Decides Fn FnCl)
open Meaning.K2 (SeatKeeps frontOf)
open Johnson.Desc.First.Walk.Tied (Reach)
open P1K8 (l0At AllZero l0s ZeroInv KeepsZero allZero_map allZero_trees allZero_frame l0s_of_frame
  l0s_of_sums l0s_rows_map l0s_rows_modify allZero_laid allZero_start fill_l0s allZero_fill
  allZero_rests kz_refl kz_trans kz_of_cases kz_same kz_none zeroInv_none kz_trees)

/-- **EVERY MAKER OF THE SEAT.** -/
theorem seatKeeps_zero : SeatKeeps KeepsZero okZero (fun Q => AllZero Q.X.Fp) where
  refl := kz_refl
  trans := kz_trans
  frames := fun hB h => frames_kz hB h
  k1First := fun q gp _ => k1First_wholeZ q gp
  k1Later := fun q gp l p m a _ => k1Later_wholeZ q gp l p m a
  reads := fun h => readsQuietAt_wholeZ h
  k3 := fun c r X cs sh a _ h => theStated_wholeZ c r X cs sh a h
  k4 := k4C_wholeZ
  k5 := fun W l g bf _ h => k5N_wholeZ W l g bf h
  k6 := fun h => k6S_wholeZ h
  k7 := k7Of_wholeZ
  k8 := k8W_wholeZ
  k11 := k11_wholeZ
  closeOf := closeOf_wholeZ
  batch := fun p _ hf => batch_wholeZ p hf
  k2 := fun p _ => k2_wholeZ p
  front := headFront_kz
  openQ := fun P hP => headOpen_makesZ P hP
  finFront := finFront_kz
  finBehind := finBehind_kz

variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)} {c : Chain S ProofFile.Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- In scope the public part's own list of built links has 25 entries. -/
theorem links_size (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (hZ : ProofFile.pubPlain OnBytes.secondHashFunction P.pol lay P.KL = .ok Z) : Z.p.built.links.size = 25 := by
  have e := congrArg List.length (Johnson.AtFull.Lots.LinksScope.views_in_scope hS hR hZ)
  rw [List.length_map, Array.length_toList] at e
  exact e

/-- **The premise on the plan, paid.** -/
theorem okZero_at (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) : okZero Z.p.built.links := by
  intro m X hX
  obtain ⟨hlt, -⟩ := Array.getElem?_eq_some_iff.1 hX
  rw [links_size hS hR O.pub] at hlt
  obtain ⟨Xl, e3⟩ := P1K8T.built_at hS hR O (by omega : m ≤ 24)
  obtain ⟨X', x1, -, x3⟩ := K9Asks.built_tl_Fp O.blank e3
  obtain rfl : X' = X := Option.some.inj (x1.symm.trans hX)
  rw [← x3]
  exact P1K8.built_allZero hS hR O hlt e3

/-- **The premise on the head's link's letters, paid.** -/
theorem okHeadZ_at (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) :
    ∀ l Q, P1K2.pureLetters Bs.G₀ l = some Q → AllZero Q.X.Fp := by
  intro l Q hQ
  unfold P1K2.pureLetters at hQ
  obtain ⟨X', hX', rfl⟩ := Option.map_eq_some_iff.1 hQ
  obtain ⟨hlt, -⟩ := Array.getElem?_eq_some_iff.1 hX'
  rw [(IM.ground_gets hS hR O.pub O.blank).1] at hlt
  exact P1K8.built_allZero hS hR O hlt hX'

/-- **AT EVERY STATE THAT THE FIRST CHAIN's OWN SUB-PROTOCOLS REACH AT A BORDER UP TO 353.** -/
theorem zero_at_reach (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {k : ℕ} (hk : k ≤ 353)
    {z : ProofFile.InstPub} {s : S} (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) k (z, s)) : ZeroInv s := by
  obtain ⟨-, rs, cols, f⟩ := Johnson.Desc.First.Walk.Tied.reach_fold.1 h
  have hk' : k ≤ (frontOf c).length := by
    rw [Meaning.Carry.front_len hS hR O]
    exact hk
  exact Meaning.K2.open_fold seatKeeps_zero O (okZero_at hS hR O) (okHeadZ_at hS hR O) hk' f
    (zeroInv_none (start_none O.pub z))

/-- **In front of a segment's batching the upper virtual rows of the digits' array begin at
column 0.** -/
theorem l0_at_batch (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : ℕ} (hl : l < 25)
    {z : ProofFile.InstPub} {s : S}
    (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * l + (if l = 24 then 11 else 9)) (z, s))
    {tl : HTailF2} {G : Fork} (hG : s.fork? = some G) :
    ∀ b, b < tl.zzBlocks →
      ((G.trees.getD tl.ix.ZZ {}).rows.getD (tl.zzBlocks + b) {}).L0 = 0 :=
  fun b _ => zero_at_reach hS hR O (by split_ifs <;> omega) h G hG tl.ix.ZZ (tl.zzBlocks + b)

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.seatKeeps_zero
#print axioms VerifiableInference.Desc.LinkJoin.links_size
#print axioms VerifiableInference.Desc.LinkJoin.okZero_at
#print axioms VerifiableInference.Desc.LinkJoin.okHeadZ_at
#print axioms VerifiableInference.Desc.LinkJoin.zero_at_reach
#print axioms VerifiableInference.Desc.LinkJoin.l0_at_batch
