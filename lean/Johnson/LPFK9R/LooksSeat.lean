-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/LPFK9R/LooksSeat.lean: THE LAST JOIN OF A WALK FOR e₁: AT THE PROOF FILE's SEAT (ProofFile.onlineDescription)
EVERY SUB-PROTOCOL THAT THE IOP AS WRITTEN IN LEAN LAYS IN FRONT OF WHAT STANDS BEHIND THE LAST LINK
HANDS ON «the open ledger's arrays have the plan's looks».

  seatKeeps_looks B₀: **Meaning.K2.SeatKeeps (KeepsLooks (shOfBuilt B₀)) (· = B₀) okP**: every field
    by a theorem of Johnson/Desc/First/Link/Law/Looks*.lean. okP P: shOfBuilt B₀ P.l is the looks of
    P.X.Fp's arrays (the head's link's letters).
  descPure_looks: so, by descPure_keepsP: every sub-protocol of frontOf c is
    Decides (KeepsLooks (shOfBuilt Z.p.built.links)).
  okHead_at: the premise on the head's letters, PAID at the seat's own (P1K2.pureLetters off the
    blank letters). start_none: at the chain's first state no ledger is open.
  looks_at_reached: **ProofFile.onlineDescription o pol lay KL = .ok F ⊢ at every state reached (Reach, at
    c.blocksInOrder from ProofFile.startS Z) at a border k ≤ (frontOf c).length: LooksInv (shOfBuilt
    Z.p.built.links): NO OTHER PREMISE.**
Limits. It speaks of REACHED states alone. The borders behind the last link are not covered. Nothing
on soundness.
-/
import Johnson.IMR.SeatKeeps
import Johnson.IMR.RecRun
import Johnson.IMR.OwnSeat
import Johnson.Top.H0.Walk.ReachAt
import Johnson.Desc.First.Link.Law.LooksEnds

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Keeps (Whole Decides Fn FnCl)
open Meaning.K2 (SeatKeeps descPure_keepsP frontOf backOf flat_eq blank_built pub_start)
open Johnson.Desc.First.Walk.Tied (Reach RchAt)

/-- The premise on the head's link's letters. -/
def okHead (B₀ : Array Stages.LinkH) (P : First.K2.HeadPar) : Prop :=
  shOfBuilt B₀ P.l = P.X.Fp.trees.toList.map look

/-- **EVERY MAKER OF THE SEAT.** -/
theorem seatKeeps_looks (B₀ : Array Stages.LinkH) :
    SeatKeeps (KeepsLooks (shOfBuilt B₀)) (fun built => built = B₀) (okHead B₀) where
  refl := keeps_refl _
  trans := keeps_trans _
  frames := fun hB h => by
    subst hB
    exact frames_keep h
  k1First := fun q gp _ => k1First_whole _ q gp
  k1Later := fun q gp l p m a _ => k1Later_whole _ q gp l p m a
  reads := fun h => readsQuietAt_whole _ h
  k3 := fun c r X cs sh a _ h => theStated_whole _ c r X cs sh a h
  k4 := k4C_whole _
  k5 := fun W l g bf _ h => k5N_whole _ W l g bf h
  k6 := fun h => k6S_whole _ h
  k7 := k7Of_whole _
  k8 := k8W_whole _
  k11 := k11_whole _
  closeOf := closeOf_whole _
  batch := fun p _ hf => batch_whole _ p hf
  k2 := fun p _ => k2_whole _ p
  front := headFront_keeps _
  openQ := fun P hP => headOpen_makes _ P hP
  finFront := finFront_keeps _
  finBehind := finBehind_keeps _

/-- **AT THE PROOF FILE's SEAT.** -/
theorem descPure_looks {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst}
    {Z : ProofFile.Pub} (hZ : ProofFile.pureRoad.pub o pol lay KL = .ok Z)
    (hP : ∀ G, ProofFile.blankBy ProofFile.pureRoad.links Z = some G → ∀ l P,
      P1K2.pureLetters G l = some P → okHead Z.p.built.links P)
    (h : ProofFile.onlineDescription o pol lay KL = .ok F) :
    ∃ (A : ProofFile.SharedSeat) (B : ProofFile.SecondSeat) (c : Chain S ProofFile.Cl),
      F = ProofFile.fileDescBy o ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c ∧ c.front = [] ∧
        ∀ b ∈ frontOf c, Decides (KeepsLooks (shOfBuilt Z.p.built.links)) b := by
  obtain ⟨Z', A, B, c, hZ', e, k0, k⟩ := descPure_keepsP (seatKeeps_looks Z.p.built.links)
    (fun Z' hZ' => by rw [Except.ok.inj (hZ.symm.trans hZ')])
    (fun Z' hZ' G hG l P hl => by
      obtain rfl : Z = Z' := Except.ok.inj (hZ.symm.trans hZ')
      exact hP G hG l P hl) h
  obtain rfl : Z = Z' := Except.ok.inj (hZ.symm.trans hZ')
  exact ⟨A, B, c, e, k0, k⟩

/-- **The head's link's letters, off the blank letters, bear the built link's planned arrays**
(letters_arr, Johnson/IMR/OwnSeat.lean, at another field). -/
theorem okHead_at {mk : ProofFile.LinksBy} {Z : ProofFile.Pub} {G : ProofFile.Ground}
    (h : ProofFile.blankBy mk Z = some G) {l : ℕ} {P : First.K2.HeadPar}
    (hP : P1K2.pureLetters G l = some P) : okHead Z.p.built.links P := by
  obtain ⟨links, e⟩ := blank_built h
  unfold P1K2.pureLetters at hP
  obtain ⟨X', hX', rfl⟩ := Option.map_eq_some_iff.1 hP
  show shOfBuilt Z.p.built.links l = X'.Fp.trees.toList.map look
  rw [e] at hX'
  obtain ⟨hl, e'⟩ := Array.getElem?_eq_some_iff.1 hX'
  have hl1 : l < Z.p.built.links.size := by
    rw [Array.size_zipWith] at hl
    omega
  rw [Array.getElem_zipWith] at e'
  rw [← e']
  exact shOfBuilt_at (X := Z.p.built.links[l]'hl1) (Array.getElem?_eq_getElem hl1)

/-- The first chain's first state stands in front of the first link: no ledger is open. -/
theorem start_none {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {Z : ProofFile.Pub}
    (hZ : ProofFile.pureRoad.pub o pol lay KL = .ok Z) (p : ProofFile.InstPub) :
    (ProofFile.startS Z p).fork? = none := by
  refine fork_none_between ?_
  have e : Z.s₀.atBetween = true := by
    have k := pub_start hZ
    unfold S.startP at k
    split at k
    · rw [← Option.some.inj k]
      rfl
    · cases k
  unfold ProofFile.startS
  dsimp only
  split
  · exact e
  · rfl

/-- The induction along "reached", over a front stretch of the list. -/
theorem looks_reach_front {Cl P : Type} (shOf : ℕ → List Look) (ft : ℕ)
    (fr bk : List (Block S Cl)) (start : P → S) (h0 : ∀ z, LooksInv shOf (start z))
    (hs : ∀ b ∈ fr, Decides (KeepsLooks shOf) b) {k : ℕ} {a : P × S}
    (h : Reach ft (fr ++ bk) start k a) (hk : k ≤ fr.length) : LooksInv shOf a.2 := by
  induction h with
  | zero z => exact h0 z
  | @succ k z s s' b _ hb hy ih =>
    obtain ⟨R, c, _, e⟩ := hy
    have hk' : k < fr.length := hk
    rw [List.getElem?_append_left hk'] at hb
    exact hs b (List.mem_of_getElem? hb) _ _ _ _
      ((Sound.step_ok_iff ft b s s' R c c.length).1 e).2.2.2 (ih (Nat.le_of_lt hk'))

/-- **AT EVERY STATE THAT IS REACHED IN FRONT OF WHAT STANDS BEHIND THE LAST LINK: where a ledger
and a link of the number m are open, the ledger's arrays have the looks of the plan's arrays of link
m. NO PREMISE IS LEFT BUT THAT THE IOP IS MADE.** -/
theorem looks_at_reached {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst}
    {Z : ProofFile.Pub} (hZ : ProofFile.pureRoad.pub o pol lay KL = .ok Z)
    (h : ProofFile.onlineDescription o pol lay KL = .ok F) :
    ∃ (A : ProofFile.SharedSeat) (B : ProofFile.SecondSeat) (c : Chain S ProofFile.Cl),
      F = ProofFile.fileDescBy o ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c ∧
      ∀ (k : ℕ) (a : ProofFile.InstPub × S), Reach 0 c.blocksInOrder (ProofFile.startS Z) k a →
        k ≤ (frontOf c).length → LooksInv (shOfBuilt Z.p.built.links) a.2 := by
  obtain ⟨A, B, c, e, k0, hk⟩ := descPure_looks hZ (fun G hG l P hl => okHead_at hG hl) h
  refine ⟨A, B, c, e, fun k a hr hle => ?_⟩
  rw [flat_eq k0] at hr
  exact looks_reach_front _ 0 (frontOf c) (backOf c) (ProofFile.startS Z)
    (fun z => looksInv_none _ (start_none hZ z)) hk hr hle

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.okHead_at
#print axioms VerifiableInference.Desc.LinkJoin.start_none
#print axioms VerifiableInference.Desc.LinkJoin.looks_at_reached
#print axioms VerifiableInference.Desc.LinkJoin.seatKeeps_looks
#print axioms VerifiableInference.Desc.LinkJoin.descPure_looks
