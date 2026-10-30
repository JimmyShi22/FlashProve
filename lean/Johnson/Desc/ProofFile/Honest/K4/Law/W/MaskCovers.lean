-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/W/MaskCovers.lean: CONDITIONAL. Four statements with
their proofs; no definition.

What is here. THE FORM `Covers` (Honest/Small/Covers.lean, of other writers) AT THE TWO TEXTS THAT
THE MEMBER OF THE FEED-FORWARD LAYERS' OWN ROUNDS (sub-protocol K4) HAS OVER MESSAGES THAT ANOTHER
MEMBER SENDS: `k4MaskLotG` (its segment's mask row) and `k4IndexLotG` (its entry of the index masks'
message). THE SENDER's LOT Ls IS A LETTER: no kind of sender is named. `k4Mask_covers`: from hP
(`k4PubG` returns), J (the lock at the sender's letters o and base: a test on the book), hn (Ls
bears the message's number), hA (Ls's text answers at the places that K4 reads), hE (what it answers
at place ν of the mask row 0 is o's element number base + ν of the run's coins) and hL. Of `Covers`'
two clauses hn is the one on the number; J, hA, hE and hL give the other. `k4Index_covers`: the like
for the one entry. `k4MaskOwn_ofLots`, `k4IndexOwn_ofLots`: so, at a Script that is laid from a list
of lots in which Ls lies and with which the other lots of its number agree, `OwnMsgs` holds at K4's
text (`ofLots_ownMsgs_of_covers`, the same file).

Not shown here. THAT hn, hA OR hE HOLDS OF ANY SENDER's TEXT; that J holds of any book (under the
library's hypothesis on the public files: Law/W/LockAtHead.lean); that any list holds a lot Ls or
that the other lots agree with it. WHERE K4's TEXT ANSWERS AT NO ENTRY THE FORM ASKS hn ALONE. Each
statement is an equation at every run's coins, entry by entry: nothing is said on how an element of
the coins is sampled. hE lays the sender's entry number ν at (mask row 0, place ν): that is one
entry of the format only where the message has one mask row. Nothing on soundness, on completeness
or on any other property.
No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.W.MaskLockAt
import Johnson.Desc.ProofFile.Honest.K4.Law.W.IndexLockAt
import Johnson.Desc.ProofFile.Honest.Small.Covers

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no standing table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4.W
open OnBytes OnBytes.Model
open OnBytes.Desc.First.K4.Honest
open OnBytes.Desc.First.K4.Rt (k4Takes)
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.Sound (MsgT)
open ProofFile.Honest.FirstThread (Script OwnMsgs MsgLot PadLot TreeLot LotsAgree Covers
  ofLots_ownMsgs_of_covers)
open ProofFile.Honest.K4.Lot (k4MaskLotG k4MaskNum k4PubG k4IndexLotG k4IndexTextG k4IndexNum k4IndexRow
  k4IndexPlace)

/-- CONDITIONAL on hP, J, hn, hA, hE and hL. **THE SENDER's LOT COVERS K4's TEXT FOR THE MASK ROW.**
Ls: the sender's lot for the whole message: a letter. -/
theorem k4Mask_covers {Bk : ProverCoinCounts} {W₀ Rc Xi Tr X : Type} {cells : Tr → Cells}
    {weights : W₀ → Weights} {tokens : Xi → Array Nat}
    {look : K4Pub → List Fmt.Drawn → Forest.Heard} {Zp : ProofFile.Pub} {g : ℕ} {Qp : K4Pub}
    {o : Addr} {base : ℕ} (hP : k4PubG Zp g = some Qp)
    (J : K4MaskLockAt Bk Qp (Forest.elems (P5J.At.X Zp).y.fo) o base)
    (Ls : MsgLot Bk (Local W₀ Rc Xi Tr)) (hn : Ls.n = k4MaskNum Zp (2 * g))
    {Vq : Local W₀ Rc Xi Tr → Prop} {N : ℕ}
    (hA : ∀ k w (hd : List Fmt.Drawn) ν, Vq w → N ≤ hd.length →
      Forest.elems (P5J.At.X Zp).y.fo ≤ ν →
      ν + 1 < Forest.elems (P5J.At.X Zp).y.fo + k4Takes Qp.P Qp.hp Qp.g →
      (Ls.txt k w (hd.take Ls.fx) true 0 ν).isSome = true)
    {L : ℕ}
    (hE : ∀ k w hd ν y', ν < L → Ls.txt k w hd true 0 ν = some y' →
      (k.look 0 o).2.eAt (base + ν) = .ok y')
    (hL : Forest.elems (P5J.At.X Zp).y.fo + k4Takes Qp.P Qp.hp Qp.g ≤ L + 1) :
    Covers Vq N Ls (k4MaskLotG (Bk := Bk) (Rc := Rc) X cells weights tokens look Zp g) := by
  obtain ⟨_, _, cnt, K⟩ := J
  have hc := k4Cnt_of_lock K
  refine ⟨hn, fun k w hd hV hN mask row place y hy => ?_⟩
  have hy1 : ((k4PubG Zp g).bind fun Qp => Lot.k4MaskTextG X cells weights tokens look Qp
      (Forest.elems (P5J.At.X Zp).y.fo) k w (hd.take 0) mask row place) = some y := hy
  rw [hP] at hy1
  have hy' : Lot.k4MaskTextG X cells weights tokens look Qp (Forest.elems (P5J.At.X Zp).y.fo) k w
      (hd.take 0) mask row place = some y := hy1
  obtain ⟨hm, hr0, f1, f2⟩ := (k4MaskTextG_val cells weights tokens look Qp hy').1
  subst hm
  subst hr0
  have c0 := k4MaskTextG_coin cells weights tokens look Qp hy'
  have hj : place - Forest.elems (P5J.At.X Zp).y.fo < cnt := by omega
  obtain ⟨y1, m1, a1⟩ := k4Lock_member K k hj
  rw [c0] at m1
  have e1 : y = y1 := Option.some.inj m1
  have hpl : base + Forest.elems (P5J.At.X Zp).y.fo + (place - Forest.elems (P5J.At.X Zp).y.fo) =
      base + place := by omega
  rw [hpl, ← e1] at a1
  obtain ⟨y', hs⟩ := Option.isSome_iff_exists.1 (hA k w hd place hV hN f1 (by omega))
  have a2 := hE k w (hd.take Ls.fx) place y' (by omega) hs
  rw [a1] at a2
  have e2 : y = y' := Except.ok.inj a2
  rw [hs, e2]

/-- CONDITIONAL on hP, J, hn, hA and hE. **THE SENDER's LOT COVERS K4's TEXT FOR ITS ENTRY OF THE
INDEX MASKS' MESSAGE.** Ls: the sender's lot for the whole message: a letter. -/
theorem k4Index_covers {Bk : ProverCoinCounts} {W₀ Rc Xi Tr X : Type} (cells : Tr → Cells)
    (weights : W₀ → Weights) (tokens : Xi → Array Nat)
    (look : K4Pub → List Fmt.Drawn → Forest.Heard) {Zp : ProofFile.Pub} {g : ℕ} {Qp : K4Pub}
    (hP : k4PubG Zp g = some Qp) {o : Addr} {s₀ : ℕ} (J : K4LastEntryAt Bk Qp o s₀)
    (Ls : MsgLot Bk (Local W₀ Rc Xi Tr)) (hn : Ls.n = k4IndexNum Zp)
    {Vq : Local W₀ Rc Xi Tr → Prop} {N : ℕ}
    (hA : ∀ k w (hd : List Fmt.Drawn), Vq w → N ≤ hd.length →
      (Ls.txt k w (hd.take Ls.fx) true (k4IndexRow Zp g) (k4IndexPlace Zp g)).isSome = true)
    (hE : ∀ k w hd y', Ls.txt k w hd true (k4IndexRow Zp g) (k4IndexPlace Zp g) = some y' →
      (k.look 0 o).2.eAt s₀ = .ok y') :
    Covers Vq N Ls (k4IndexLotG (Bk := Bk) (Rc := Rc) X cells weights tokens look Zp g) := by
  obtain ⟨es₁, eL, K, rfl, rfl⟩ := J
  refine ⟨hn, fun k w hd hv hN mask r p y ht => ?_⟩
  rw [k4IndexLotG_txt cells weights tokens look hP] at ht
  have hs := k4IndexTextG_isSome (X := X) cells weights tokens look Qp (k4IndexRow Zp g)
    (k4IndexPlace Zp g) k w
    (hd.take (k4IndexLotG (Bk := Bk) (Rc := Rc) X cells weights tokens look Zp g).fx)
    mask r p
  rw [ht] at hs
  have hfence : mask = true ∧ r = k4IndexRow Zp g ∧ p = k4IndexPlace Zp g := by
    by_cases hc : mask = true ∧ r = k4IndexRow Zp g ∧ p = k4IndexPlace Zp g
    · exact hc
    · rw [decide_eq_false hc, Bool.false_and] at hs
      cases hs
  obtain ⟨rfl, rfl, rfl⟩ := hfence
  have hy := k4_last_of_member K k
    (k4IndexTextG_coin cells weights tokens look Qp ht)
  obtain ⟨y', hy'⟩ := Option.isSome_iff_exists.1 (hA k w hd hv hN)
  have e2 := hE k w (hd.take Ls.fx) y' hy'
  rw [hy] at e2
  obtain rfl := Except.ok.inj e2
  exact hy'

/-- CONDITIONAL on hLs, hagree and the six hypotheses of `k4Mask_covers`. **AT A SCRIPT THAT IS LAID
FROM LOTS: `OwnMsgs` AT K4's TEXT FOR THE MASK ROW**, which is in no list. -/
theorem k4MaskOwn_ofLots {Bk : ProverCoinCounts} {W₀ Rc Xi Tr X S Cl CellsT Tok : Type} {cells : Tr → Cells}
    {weights : W₀ → Weights} {tokens : Xi → Array Nat}
    {look : K4Pub → List Fmt.Drawn → Forest.Heard} {Zp : ProofFile.Pub} {g : ℕ} {Qp : K4Pub}
    {o : Addr} {base : ℕ} (bs : List (Block S Cl)) (front : ℕ)
    (cellsQ : Local W₀ Rc Xi Tr → CellsT) (tok : Local W₀ Rc Xi Tr → Tok)
    (pl : List (PadLot Bk (Local W₀ Rc Xi Tr))) (tl : ℕ → TreeLot Bk (Local W₀ Rc Xi Tr))
    (ml : List (MsgLot Bk (Local W₀ Rc Xi Tr))) {Ls : MsgLot Bk (Local W₀ Rc Xi Tr)}
    (hLs : Ls ∈ ml) (hagree : LotsAgree ml Ls) (hP : k4PubG Zp g = some Qp)
    (J : K4MaskLockAt Bk Qp (Forest.elems (P5J.At.X Zp).y.fo) o base)
    (hn : Ls.n = k4MaskNum Zp (2 * g)) {Vq : Local W₀ Rc Xi Tr → Prop} {N : ℕ}
    (hA : ∀ k w (hd : List Fmt.Drawn) ν, Vq w → N ≤ hd.length →
      Forest.elems (P5J.At.X Zp).y.fo ≤ ν →
      ν + 1 < Forest.elems (P5J.At.X Zp).y.fo + k4Takes Qp.P Qp.hp Qp.g →
      (Ls.txt k w (hd.take Ls.fx) true 0 ν).isSome = true)
    {L : ℕ}
    (hE : ∀ k w hd ν y', ν < L → Ls.txt k w hd true 0 ν = some y' →
      (k.look 0 o).2.eAt (base + ν) = .ok y')
    (hL : Forest.elems (P5J.At.X Zp).y.fo + k4Takes Qp.P Qp.hp Qp.g ≤ L + 1) :
    OwnMsgs (Script.ofLots bs front cellsQ tok pl tl ml) Vq N
      (k4MaskLotG (Bk := Bk) (Rc := Rc) X cells weights tokens look Zp g).n
      (k4MaskLotG (Bk := Bk) (Rc := Rc) X cells weights tokens look Zp g).fx
      (k4MaskLotG (Bk := Bk) (Rc := Rc) X cells weights tokens look Zp g).txt :=
  ofLots_ownMsgs_of_covers bs front cellsQ tok pl tl ml hLs hagree
    (k4Mask_covers hP J Ls hn hA hE hL)

/-- CONDITIONAL on hLs, hagree and the five hypotheses of `k4Index_covers`. **AT A SCRIPT THAT IS
LAID FROM LOTS: `OwnMsgs` AT K4's TEXT FOR ITS ENTRY OF THE INDEX MASKS' MESSAGE.** -/
theorem k4IndexOwn_ofLots {Bk : ProverCoinCounts} {W₀ Rc Xi Tr X S Cl CellsT Tok : Type} (cells : Tr → Cells)
    (weights : W₀ → Weights) (tokens : Xi → Array Nat)
    (look : K4Pub → List Fmt.Drawn → Forest.Heard) {Zp : ProofFile.Pub} {g : ℕ} {Qp : K4Pub}
    (bs : List (Block S Cl)) (front : ℕ)
    (cellsQ : Local W₀ Rc Xi Tr → CellsT) (tok : Local W₀ Rc Xi Tr → Tok)
    (pl : List (PadLot Bk (Local W₀ Rc Xi Tr))) (tl : ℕ → TreeLot Bk (Local W₀ Rc Xi Tr))
    (ml : List (MsgLot Bk (Local W₀ Rc Xi Tr))) {Ls : MsgLot Bk (Local W₀ Rc Xi Tr)}
    (hLs : Ls ∈ ml) (hagree : LotsAgree ml Ls) (hP : k4PubG Zp g = some Qp) {o : Addr} {s₀ : ℕ}
    (J : K4LastEntryAt Bk Qp o s₀) (hn : Ls.n = k4IndexNum Zp)
    {Vq : Local W₀ Rc Xi Tr → Prop} {N : ℕ}
    (hA : ∀ k w (hd : List Fmt.Drawn), Vq w → N ≤ hd.length →
      (Ls.txt k w (hd.take Ls.fx) true (k4IndexRow Zp g) (k4IndexPlace Zp g)).isSome = true)
    (hE : ∀ k w hd y', Ls.txt k w hd true (k4IndexRow Zp g) (k4IndexPlace Zp g) = some y' →
      (k.look 0 o).2.eAt s₀ = .ok y') :
    OwnMsgs (Script.ofLots bs front cellsQ tok pl tl ml) Vq N
      (k4IndexLotG (Bk := Bk) (Rc := Rc) X cells weights tokens look Zp g).n
      (k4IndexLotG (Bk := Bk) (Rc := Rc) X cells weights tokens look Zp g).fx
      (k4IndexLotG (Bk := Bk) (Rc := Rc) X cells weights tokens look Zp g).txt :=
  ofLots_ownMsgs_of_covers bs front cellsQ tok pl tl ml hLs hagree
    (k4Index_covers cells weights tokens look hP J Ls hn hA hE)

end ProofFile.Honest.K4.W

#print axioms ProofFile.Honest.K4.W.k4Mask_covers
#print axioms ProofFile.Honest.K4.W.k4Index_covers
#print axioms ProofFile.Honest.K4.W.k4MaskOwn_ofLots
#print axioms ProofFile.Honest.K4.W.k4IndexOwn_ofLots
