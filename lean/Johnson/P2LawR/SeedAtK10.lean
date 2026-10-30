-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P2LawR/SeedAtK10.lean: "seed" (a premise of onS_of_rowAsks: the sendings'
  invariant K1.SeedIs at every place of the l-th written list, at the reader of samples' own number)
  IN FRONT OF K10's PLACE OF EVERY LINK l < 25, AS ONE CALL: from the one head (P5J.AtMgA) at o :=
  OnBytes.secondHashFunction, the table's promise at ixK10 l, "reached" there, no mark, and K1.Tie at the
  place's own shape. A joining.


THE NAMES.
ten_is_ix: a closed fact, by Lean's kernel: at l < 25 the number tenAt l
  (Johnson/LPFE1R/BelowAtK10.lean) of the place of the kind K10 is ixK10 l.
place_tie: so the place at which hB_at_k10 speaks is the place at which the table's
  promise speaks.
seed_gen, book_at_ten: the call of seedIs_at_seat, and the promise's clause on the book
  at the spelling tenAt l of the place, each AT LETTERS: no written value stands in them. (A
  form with the written lists in the goal while a "there is" was opened ran Lean into its limits:
  recursion depth, then heartbeats.)
seed_at_K10: **the head · l < 25 · the promise at ixK10 l · reached there · no mark · a place i of
  the l-th written list · K1.Tie at its shape ⊢ ∃ ρ y, K1.SeedIs (At.cs Zp) … a.1.2.st (Sound.numAt
  (At.seats Zp) …) ρ y.** One call of seedIs_at_seat (what seed_field calls, a
  place at a time: so K1.Tie is asked at that place alone): its premises on the state by seed_state
  (Johnson/P2LawR/SeedStateAtK10.lean); its public premises by seed_public_laid,
  ld_at_laid and hB_at_k10.

Limits. The promise and K1.Tie are premises.
  NO MEMBER. At l = 0: the six-list, not the five-list.
  The full size alone. At OnBytes.secondHashFunction alone. It leans on the door's asksAt2. A raised limit
  stands in this file (maxRecDepth 100000). Nothing on soundness.
-/
import Johnson.P2LawR.SeedStateAtK10
import Johnson.LPFE1R.BelowAtK10

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.P2Notices
open OnBytes OnBytes.Slice
open OnBytes.Maker (WholeD)
open Johnson.G (linksFullLit)
open VerifiableInference.Desc (Chain Place smpHeld)
open VerifiableInference.Desc.First (flatPlacesOf)
open VerifiableInference.Desc.First.Close (seatK10)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.LinkJoin (tenAt seedIs_at_seat seed_public_laid ld_at_laid hB_at_k10)
open LPFK10 (ixK10)
open P5J

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- The two numbers of K10's place, tenAt l and ixK10 l, are one: by Lean's kernel. -/
theorem ten_is_ix : ((List.range 25).all fun l => tenAt l == ixK10 l) = true := by decide +kernel

/-- The place at which hB_at_k10 speaks is the place at which the promise speaks. -/
theorem place_tie {l : ℕ} (hl : l < 25) :
    (flatPlacesOf Sound.linksFull true)[tenAt l]? = At.ps[ixK10 l]? := by
  rw [eq_of_beq (List.all_eq_true.1 ten_is_ix l (List.mem_range.2 hl))]
  rfl

/-- The call, at letters: no written value stands in it, so that Lean unfolds none. -/
theorem seed_gen (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {k : ℕ} {z : ProofFile.InstPub} {s : TS}
    (hk : k ≤ (Meaning.K2.frontOf cF).length)
    (e : _root_.Johnson.Desc.First.Walk.Tied.Reach 0 (cF.blocksInOrder.map below) (ProofFile.startS Zp) k (z, s))
    {cs : Codes} {N : First.Numbers} {p : Option Place} {Ld : K12.Door.Laid}
    {M : List OracleShape} (hc : s.st.codes = cs) (hbook : First.bookAt N p s = true)
    (hseats : K12.Door.atFirstSeats Ld s = true) (hshapes : K12.Door.atFirstShapes M s = true)
    (hnd : Ld.places.Nodup) (seats : List (ℕ × ℕ)) (lo : List (OracleShape × ℕ))
    (seat : Fin lo.length → ℕ × ℕ) (i : Fin lo.length)
    (hB : seats.idxOf (seat i) < N.msgsAt p ∧ Ld.places[seats.idxOf (seat i)]? = some (seat i) ∧
      M[seats.idxOf (seat i)]? = some (lo.get i).1)
    (hh : smpHeld s.st s.book (seat i).1 (seat i).2 = true) (hT : K1.Tie cs (lo.get i).1) :
    ∃ ρ y, K1.SeedIs cs (lo.get i).1 s.st (Sound.numAt seats ⟨⟨lo, seat⟩, i⟩) ρ y := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  exact seedIs_at_seat O h.laid.value h.laid.planOk hk e hc hbook hseats hshapes hnd hB.1 hB.2.1
    hB.2.2 hh hT

/-- The promise's clause on the book, at the spelling tenAt l of the place. -/
theorem book_at_ten {N : First.Numbers} {s : TS} {l : ℕ} (hl : l < 25)
    (hb : First.bookAt N At.ps[ixK10 l]? s = true) :
    First.bookAt N (flatPlacesOf Sound.linksFull true)[tenAt l]? s = true := by
  rw [place_tie hl]
  exact hb

/-- **"seed", IN FRONT OF K10's PLACE OF EVERY LINK, AS ONE CALL.** -/
theorem seed_at_K10 (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {l : ℕ} (hl : l < 25)
    {a : (ProofFile.InstPub × TS) ×
      (Frame.E (frameAt (D.at frS.P.T.a) (allOf (D.at frS.P.T.a)) (D.at frS.P.T.a).key₁ 0)).Str}
    (ha : onQ (At.N Zp cF) (mgAtAll h) fullLinks At.ps (fun a => a) (ixK10 l) a)
    (hr : h.toAtMg.rch (ixK10 l) a) (hm : ¬ a.1.2.failed ≠ none)
    (i : Fin (linksFullLit.getD l []).length)
    (hT : K1.Tie (At.cs Zp) ((linksFullLit.getD l []).get i).1) :
    ∃ ρ y, K1.SeedIs (At.cs Zp) ((linksFullLit.getD l []).get i).1 a.1.2.st
      (Sound.numAt (At.seats Zp)
        ⟨⟨linksFullLit.getD l [], seatK10 (linksFullLit.getD l []) (At.pseats Zp) l⟩, i⟩) ρ y :=
  have S := seed_state h hl ha hr hm
  have hLd := ld_at_laid h.scope h.laid
  seed_gen h S.2.1 S.1 S.2.2.1 (book_at_ten hl S.2.2.2.1) (S.2.2.2.2.1 _ hLd) S.2.2.2.2.2.1
    (seed_public_laid h.scope h.laid hLd).1 (At.seats Zp) (linksFullLit.getD l [])
    (seatK10 (linksFullLit.getD l []) (At.pseats Zp) l) i (hB_at_k10 h.scope h.laid hLd hl i)
    (S.2.2.2.2.2.2 i) hT

end VerifiableInference.Desc.P2Notices

#print axioms VerifiableInference.Desc.P2Notices.ten_is_ix
#print axioms VerifiableInference.Desc.P2Notices.place_tie
#print axioms VerifiableInference.Desc.P2Notices.seed_gen
#print axioms VerifiableInference.Desc.P2Notices.book_at_ten
#print axioms VerifiableInference.Desc.P2Notices.seed_at_K10
