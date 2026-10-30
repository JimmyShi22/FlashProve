-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/Law/BookAt32.lean: THEOREMS. IN FRONT OF THE KEY FILE's LAST
PROXIMITY TEST (the last chain, border 2) THE BOOK's TREES OF THE INDEX MASKS, OF W AND OF OMEGA HAVE THE SHAPES THAT THE KEY FILE's IOP
AS WRITTEN IN LEAN (Key.descriptionFromSource X N P) TELLS OF THE FILE's TREES 0 · 5 · 7: OFF THE HISTORY, IN THE GOALS' SCOPE.
It names ShapeIs (Johnson/Desc/K12/Coin/FramesTie.lean).

Words: a "book" is the verifier state's table of trees (TreeBook); a "sending" is a prover's message of oracle messages (the kind K1); a
"layout" is what layTrees, the routine that places a sending's oracle messages in trees, returns; a "border" k lies in front of
sub-protocol k of a chain.

Main names:
  (treeShape · treeShape_keeps · keeps_of_seated · treeShape_made · omega_tree: Johnson/RunOne/Law/BookShapeStays.lean.)
  seat_seated                  an accepting run of a sending's seat gives K1.SeatedBy.
  omega_alone_full | _no       by the kernel: the three numbers of the shape of the layout of Omega alone, at the written key; a negative test.
  idx_one · keeps_1_17 · w_18 · seal_19    the first chain, border by border.
  told_w | nums_seven          in scope: from the file's tree 5 on is told what W's sending tells; what is told of tree 7, by its numbers.
  first_end                    at the first chain's end: six roots; the book's trees 0 and 5 fit what is told of the file's trees 0 and 5.
  book_32_of | book_32         the sentence above; book_32 at the premises in the form that a caller holds.
  there_32 | shapeIs_32        the same at the seats 0 · 2 · 4 of the six (atSix), by the tree's index z in the book with
                               (atSix k).1 = off₃N z (Johnson/Top/Fire/Code/KeyAtOff.lean); the three indices are there.

Premises of book_32: the scope's equations; the IOP as written in Lean passes its tests planOk and wantedOk; its data are the written data;
the numbers of the ranges' test's place are the maker's (spent for two counts: five trees stand at border 17; six roots at the chain's end).
IS IT EMPTY? book_32 GIVES the three trees at every state that the last chain reaches at border 2. The scope's premises are shown together
of nothing in Lean. That an honest key file reaches border 2 of the last chain is not shown here.
What is not claimed. Nothing on a tree's number, source, parts or root; nothing on places. NOT that Omega's tree here has the shape of the
shared chain's book's tree: the shape is computed anew from the codes and the plan. One size. Nothing on soundness.

-/
import Johnson.RunOne.Law.BookShapeStays
import Johnson.RunOne.Law.BookPlace
import Johnson.Desc.K1.Law.SeatedAtRecord
import Johnson.Desc.Book.BookFitsGround
import Johnson.Desc.Third.Law.StartBook
import Johnson.RunOne.Law.K12Shape15
import Johnson.RunOne.Law.K12Facts15
import Johnson.Desc.Key.KeyBattSays
import Johnson.RunOne.KeyYes
import Johnson.RunOne.KeyWYes
import Johnson.RunOne.KeyWShape
import Johnson.Desc.K13.KeepsCore
import Johnson.RunOne.KeySeatScopeW2
import Johnson.RunOne.KeySeatScope23
import Johnson.RunOne.KeyTenInScope
import Johnson.Top.Fire.Code.KeyASideAll
import Johnson.Top.Fire.Code.KeyAtOff
import Johnson.Desc.K12.Coin.FramesTie

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.Law.BookAt32
open OnBytes OnBytes.Params OnBytes.Maker
open OnBytes.Slice (BookKeeps)
open VerifiableInference.Desc VerifiableInference.Desc.Key VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open VerifiableInference.Desc.Key (FirstState Claim Xi Lookup)
open VerifiableInference.Desc.Ground (coreStill_same)
open VerifiableInference.Desc.K3.KeyLaw (bindX)
open VerifiableInference.Desc.K12 (T12 P12)
open VerifiableInference.Desc.K12.Coin (ShapeIs)
open VerifiableInference.Desc.Third (S₃ P₁₄ batchLinearConstraintsSecondPart)
open Johnson.RunOne.KeyRows1 (parW' w_yes takeMasksP_gnd dec_seal)
open Johnson.RunOne.KeyRows23 (Fk oneAt St₂ St₃)
open Johnson.RunOne.Sound (fk_idx_at fk_msg_at fk_rng_at)
open Johnson.RunOne.Law.FrontSteps (sent_par)
open Johnson.RunOne.Law.AllAtO (fk_two₀ fk_two₁)
open Johnson.RunOne.Law.BookStays (book_back)
open Johnson.RunOne.Law.BookAt2 (seat_core open_book)
open Lk6.AtPlan (keyFull)
open LPFD (Hist₁ Hist₂ Hist₃ Reached)
open Johnson.RunOne.Law.BookShapeStays

/-! ## 1 A sending's seat -/

/-- **An accepting run of a sending's seat**: what it lays into the book. -/
theorem seat_seated {β Cl : Type} {name : String} {P : K1.Par} {s t : ChainState β} {r₁ r₂ : Fmt.RoundView}
    {gs : List (List (ℕ × List UInt64))}
    (h : (sendingSeat (Cl := Cl) name P).decide s [r₁, r₂] gs = .ok t) :
    K1.SeatedBy P s.d.book s.d.st.oracles.size s.d.roots t.d.book t.d.st.oracles.size t.d.roots := by
  obtain ⟨ids, d', hd, e1, e2, e3⟩ := seat_core h
  rw [e1, e2, e3]
  exact K1.decideSend_seated P s.debt (withLoc s.d (#[] : Array ℕ)) d' r₁ r₂ ids hd

/-! ## 2 Omega's tree at the written key -/

/-- **By the kernel: the three numbers of that shape at the written key.** -/
theorem omega_alone_full :
    ((layTrees keyFull.codes #[{ shape := keyFull.once.shape.omega, leafClass := keyFull.once.shape.omegaLeafClass }]).map fun l =>
      ((l.shapes.getD 0 {}).logN, (l.shapes.getD 0 {}).mainSymbols.toList, (l.shapes.getD 0 {}).maskSymbols.toList)) =
      some (22, [36], [0]) := by decide +kernel

/-- A negative test. -/
theorem omega_alone_no :
    ((layTrees keyFull.codes #[{ shape := keyFull.once.shape.omega, leafClass := keyFull.once.shape.omegaLeafClass }]).map fun l =>
      ((l.shapes.getD 0 {}).logN, (l.shapes.getD 0 {}).mainSymbols.toList, (l.shapes.getD 0 {}).maskSymbols.toList)) ≠
      some (22, [37], [0]) := by decide +kernel

/-! ## 3 The first chain's sub-protocols and the book -/

/-- The index masks' sending, from the chain's start: tree τ has the layout's shape. -/
theorem idx_sent {one : OneTime} {Np : Pieces} {gI : List (List ℕ)} {s1 : FirstState} {q₁ q₂ : Fmt.RoundView}
    {gs0 : List (List (ℕ × List UInt64))}
    (h0 : (sendIndexMasks (Cl := Claim) one Np gI).decide (chainStart one.codes {}) [q₁, q₂] gs0 = .ok s1) :
    ∃ layI, layTrees one.codes #[one.indexMasks] = some layI ∧
      ∀ τ, τ < layI.shapes.size → treeShape s1.d.book τ = some (layI.shapes.getD τ {}) := by
  obtain ⟨m0, hk0, hq0⟩ := bindX h0
  obtain ⟨i0, -, hq0⟩ := bindX hq0
  cases hq0
  obtain ⟨hl, hS, -, -⟩ := seat_seated hk0
  rw [sent_par] at hl
  refine ⟨_, hl, fun τ hτ => ?_⟩
  have e : treeShape m0.d.book (0 + τ) = _ := treeShape_made hS hτ
  rwa [Nat.zero_add] at e

/-- The own message's sending keeps the book's older trees. -/
theorem own_keeps {one : OneTime} {Np : Pieces} {gB : List (List ℕ)} {s1 s2 : FirstState} {p₁ p₂ : Fmt.RoundView}
    {gs1 : List (List (ℕ × List UInt64))}
    (h1 : (sendOwnMessage (Cl := Claim) one Np gB).decide s1 [p₁, p₂] gs1 = .ok s2) :
    BookKeeps s1.d.book s2.d.book := by
  obtain ⟨m1, hk1, hq1⟩ := bindX h1
  rw [open_book (show openRangesGroup one m1 = .ok s2 from hq1)]
  exact keeps_of_seated (seat_seated hk1).seated

/-- The ranges' proximity test keeps them. -/
theorem rng_keeps {one : OneTime} {N : H2U.PlaceNums} {s s' : FirstState} {rs : List Fmt.RoundView}
    {gs : List (List (ℕ × List UInt64))}
    (hp : (rangesTest (enterRanges one) leaveRanges N : Block FirstState Claim).planOk = true)
    (h : (rangesTest (enterRanges one) leaveRanges N : Block FirstState Claim).decide s rs gs = .ok s') :
    BookKeeps s.d.book s'.d.book := by
  obtain ⟨tE, G, e, -, k1, -⟩ := Johnson.RunOne.Law.K12Shape15.out_of_yes hp h
  subst e
  exact k1.book

/-- The batching leaves the book. -/
theorem batt_book {one : OneTime} {Np : Pieces} {sent : ℕ} {s s' : FirstState} {rs : List Fmt.RoundView}
    {gs : List (List (ℕ × List UInt64))}
    (h : (batchTableRows (Cl := Claim) (fun x : LookupRecord => x.keys) one Np sent).decide s rs gs = .ok s') :
    s'.d.book = s.d.book := by
  obtain ⟨rows, out, msg, rs', -, -, hbt, rfl⟩ :=
    seat_says (Cl := Claim) (fun x : LookupRecord => x.keys) one Np sent s s' rs gs h
  obtain ⟨r, htk⟩ := batt_takes _ _ _ _ _ _ _ _ hbt
  exact (takeMasksP_gnd htk).2

/-- **W's sending**: what it lays into the book. -/
theorem w_seated {one : OneTime} {Np : Pieces} {sent : ℕ} {groups : List (List ℕ)} {bw : Block FirstState Claim}
    (hb : sendW one Np sent groups = some bw) {s s' : FirstState} {r₁ r₂ : Fmt.RoundView} {gs : List (List (ℕ × List UInt64))}
    (h : bw.decide s [r₁, r₂] gs = .ok s') :
    ∃ msg, linMessageW one.lin = some msg ∧
      layTrees (parW' one Np groups msg).codes (parW' one Np groups msg).sent = some (K1.layOf (parW' one Np groups msg)) ∧
      Book.Seated s.d.book s'.d.book (parW' one Np groups msg).sent.size s.d.st.oracles.size (K1.layOf (parW' one Np groups msg))
        (fun τ => (parW' one Np groups msg).gp.firstTree + (s.d.roots + τ)) (fun τ => .own (s.d.roots + τ)) := by
  obtain ⟨msg, s₁, gs', l, o, hm, -, hs, -, -, ho, rfl⟩ := w_yes one Np sent groups bw hb s s' r₁ r₂ gs h
  have S := seat_seated hs
  have eb : o.2.book = s₁.d.book := (K13.RelCore.rows_keeps coreStill_same one.lin l.claim s₁.sent s₁.d o ho).1
  refine ⟨msg, hm, S.lay, ?_⟩
  show Book.Seated s.d.book o.2.book _ _ _ _ _
  rw [eb]
  exact S.seated

/-! ## 4 Along the first chain's history -/


section
variable {X : Source} {N : H2U.PlaceNums} {P : LaterPlaces}

/-- One step back along the first chain's history. -/
theorem back_one (D : WholeD) (k : ℕ) (a : (descriptionFromSource X N P).XiPub × (descriptionFromSource X N P).S₁) (h : Hist₁ (descriptionFromSource X N P) D (k + 1) a) :
    ∃ (a' : (descriptionFromSource X N P).XiPub × (descriptionFromSource X N P).S₁) (b : Block FirstState Claim) (rs : List Fmt.RoundView)
      (gs : List (List (ℕ × List UInt64))),
      Hist₁ (descriptionFromSource X N P) D k a' ∧ (descriptionFromSource X N P).first.blocksInOrder[k]? = some b ∧ a.1 = a'.1 ∧
      b.decide a'.2 (rs.map noDigest) gs = .ok a.2 ∧ roundsFit b.rounds rs = true := by
  obtain ⟨a', b, rs, cols, hr, hb, hd, hf⟩ := Reached.last (k := k) h
  rw [List.getElem?_map] at hb
  obtain ⟨b₀, hb₀, rfl⟩ := Option.map_eq_some_iff.1 hb
  obtain ⟨e1, hd'⟩ := held_decide b₀ a' _ _ a hd
  exact ⟨a', b₀, rs, _, hr, hb₀, e1, hd', hf⟩

/-- **Behind the index masks' sending** tree τ of the book has the layout's shape. -/
theorem idx_one (D : WholeD) (a : (descriptionFromSource X N P).XiPub × (descriptionFromSource X N P).S₁) (h : Hist₁ (descriptionFromSource X N P) D 1 a) :
    ∃ layI, layTrees X.Y.k.oneTime.codes #[X.Y.k.oneTime.indexMasks] = some layI ∧
      ∀ τ, τ < layI.shapes.size →
        treeShape (show FirstState from a.2).d.book τ = some (layI.shapes.getD τ {}) := by
  obtain ⟨a0, b, rs, gs, hr, hb, -, hd, hf⟩ := back_one D 0 a h
  obtain ⟨q₁, q₂, rfl⟩ := fk_two₀ X N P b hb hf
  obtain ⟨gI, hgI⟩ := fk_idx_at X N P
  obtain rfl := Option.some.inj (hgI.symm.trans hb)
  have hs0 : a0.2 = chainStart X.Y.k.oneTime.codes {} := hr
  rw [hs0] at hd
  exact idx_sent hd

variable {x₀ x₁ : Lookup} {bw : Block FirstState Claim}

/-- **From border 1 to border 17 the book keeps its trees.** -/
theorem keeps_1_17 (hp : (descriptionFromSource X N P).planOk = true) (hl : lookupsOf X.Y.k.oneTime = [x₀, x₁]) (D : WholeD)
    (a : (descriptionFromSource X N P).XiPub × (descriptionFromSource X N P).S₁) (h : Hist₁ (descriptionFromSource X N P) D 17 a) :
    ∃ a₁ : (descriptionFromSource X N P).XiPub × (descriptionFromSource X N P).S₁, Hist₁ (descriptionFromSource X N P) D 1 a₁ ∧
      BookKeeps (show FirstState from a₁.2).d.book (show FirstState from a.2).d.book := by
  have hn : (lookupsOf X.Y.k.oneTime).length = 2 := by rw [hl]; rfl
  obtain ⟨a16, b16, rs16, gs16, h16, hb16, -, hd16, -⟩ := back_one D 16 a h
  obtain rfl := LPFD.block16 X.Y.k.oneTime X.Y.D.1 X.Y.told.1 X.set N x₀ x₁ hl b16 hb16
  have e16 : (show FirstState from a.2).d.book = (show FirstState from a16.2).d.book := batt_book hd16
  obtain ⟨a15, b15, rs15, gs15, h15, hb15, -, hd15, -⟩ := back_one D 15 a16 h16
  have hat := fk_rng_at X N P
  rw [hn] at hat
  obtain rfl := Option.some.inj (hat.symm.trans hb15)
  have k15 : BookKeeps (show FirstState from a15.2).d.book (show FirstState from a16.2).d.book :=
    rng_keeps (Johnson.RunOne.Law.K12Facts15.rng_plan X N P hp) hd15
  obtain ⟨a2, h2, -, e2⟩ := book_back D 13 (by rw [hn]) a15 h15
  obtain ⟨a1, b1, rs1, gs1, h1, hb1, -, hd1, hf1⟩ := back_one D 1 a2 h2
  obtain ⟨p₁, p₂, rfl⟩ := fk_two₁ X N P b1 hb1 hf1
  obtain ⟨gB, hgB⟩ := fk_msg_at X N P
  obtain rfl := Option.some.inj (hgB.symm.trans hb1)
  have k1 : BookKeeps (show FirstState from a1.2).d.book (show FirstState from a2.2).d.book := own_keeps hd1
  exact ⟨a1, h1, keeps_right e16 (k1.trans (keeps_left e2 k15))⟩

/-- **W's sending, at border 18.** -/
theorem w_18 (hl : lookupsOf X.Y.k.oneTime = [x₀, x₁])
    (hw : sendW X.Y.k.oneTime pieces (LPFD.sent17 X) (LPFD.g17 X) = some bw) (D : WholeD)
    (a : (descriptionFromSource X N P).XiPub × (descriptionFromSource X N P).S₁) (h : Hist₁ (descriptionFromSource X N P) D 18 a) :
    ∃ (a₁₇ : (descriptionFromSource X N P).XiPub × (descriptionFromSource X N P).S₁) (msg : Array OracleNotice) (num : ℕ → ℕ) (src : ℕ → Fmt.Src),
      Hist₁ (descriptionFromSource X N P) D 17 a₁₇ ∧ linMessageW X.Y.k.oneTime.lin = some msg ∧
      layTrees (parW' X.Y.k.oneTime pieces (LPFD.g17 X) msg).codes (parW' X.Y.k.oneTime pieces (LPFD.g17 X) msg).sent =
        some (K1.layOf (parW' X.Y.k.oneTime pieces (LPFD.g17 X) msg)) ∧
      Book.Seated (show FirstState from a₁₇.2).d.book (show FirstState from a.2).d.book
        (parW' X.Y.k.oneTime pieces (LPFD.g17 X) msg).sent.size (show FirstState from a₁₇.2).d.st.oracles.size
        (K1.layOf (parW' X.Y.k.oneTime pieces (LPFD.g17 X) msg)) num src := by
  obtain ⟨a17, b, rs, gs, h17, hb, -, hd, hf⟩ := back_one D 17 a h
  obtain rfl := LPFD.block17 X.Y.k.oneTime X.Y.D.1 X.Y.told.1 X.set N x₀ x₁ hl bw hw b hb
  obtain ⟨msg0, hm0⟩ : ∃ msg, linMessageW X.Y.k.oneTime.lin = some msg := by
    have hw' := hw
    unfold sendW at hw'
    obtain ⟨m, hm, -⟩ := Option.map_eq_some_iff.1 hw'
    exact ⟨m, hm⟩
  have hf' : roundsFit (K1.rounds (Johnson.RunOne.KeySendGood.parW X msg0)) rs = true := by
    rw [← Johnson.RunOne.KeySendGood.rounds_w hm0 hw]
    exact hf
  have hlen := roundsFit_length _ _ hf'
  obtain ⟨r₁, r₂, rfl⟩ : ∃ r₁ r₂, rs = [r₁, r₂] := by
    match rs, hlen with
    | [c, d], _ => exact ⟨c, d, rfl⟩
  obtain ⟨msg, hm, hlay, hS⟩ := w_seated hw hd
  exact ⟨a17, msg, _, _, h17, hm, hlay, hS⟩

/-- **The first chain's last sub-protocol hands the state on.** -/
theorem seal_19 (hl : lookupsOf X.Y.k.oneTime = [x₀, x₁])
    (hw : sendW X.Y.k.oneTime pieces (LPFD.sent17 X) (LPFD.g17 X) = some bw) (D : WholeD)
    (a : (descriptionFromSource X N P).XiPub × (descriptionFromSource X N P).S₁) (h : Hist₁ (descriptionFromSource X N P) D 19 a) : Hist₁ (descriptionFromSource X N P) D 18 a := by
  obtain ⟨a18, b, rs, gs, h18, hb, e1, hd, -⟩ := back_one D 18 a h
  obtain ⟨asks, ha⟩ := dec_seal X.Y.k.oneTime X.Y.D.1 X.Y.told.1 X.set N x₀ x₁ hl bw hw b hb
  rw [ha] at hd
  have e2 : a18.2 = a.2 := by
    cases hq : ChainEnd.refuse (asks a18.2) with
    | error e => rw [hq] at hd; cases hd
    | ok u => rw [hq] at hd; exact Except.ok.inj hd
  have e : a18 = a := Prod.ext e1.symm e2
  exact e ▸ h18

end

/-! ## 5 What is told of the file's trees 5 and 7, in scope -/

section
open Johnson.RunOne.KeyLetters (numsOf flat₁ oracleAt_flat₁ flat_tail seats_scope roundsL₁ told_shared first_tells_six told_bp
  oraclesOf_of_map parF nums_k14 chains_of msgW_some)
open Johnson.RunOne.Law.BookAt15 (toldK1 toldK1_shape toldK1_length)
open Johnson.RunOne.KeySendGood (parIdx)
open Johnson.RunOne.Law.KeyToldFirst (par_facts oracleAt_idx)
open Johnson.RunOne.Law.AtFreeCfg (ReadOf)
open Johnson.RunOne.Law.KeyInScope (key_in_scope five_in_scope)
open Johnson.RunOne.KeyRows23 (atSix numSix seatAt)
open VerifiableInference.Desc.Key.Fill (six)
open Johnson.G (writtenKFull)

/-- A shape fits what is told, read by its numbers. -/
theorem shapeIs_of_nums {T : TreeShape} {o : VerifiableInference.Desc.Oracle} {L W : ℕ} {l : List (ℕ × ℕ)} (ho : numsOf o = (L, W, l))
    (h1 : T.logN = L) (h2 : T.mainSymbols.toList = l.map (·.1)) (h3 : T.maskSymbols.toList = l.map (·.2)) :
    ShapeIs T o := by
  simp only [numsOf, Prod.mk.injEq] at ho
  obtain ⟨rfl, -, rfl⟩ := ho
  exact ⟨by rw [h2, List.map_map]; rfl, by rw [h3, List.map_map]; rfl, h1⟩

theorem give {XI : Type} {G : FileDescription XI} {B : TreeBook} {z j : ℕ} {T : TreeShape} {o : VerifiableInference.Desc.Oracle}
    (h : treeShape B z = some T) (ho : G.oracleAt j = some o) (hS : ShapeIs T o) :
    ∃ T' o', B.trees[z]? = some T' ∧ G.oracleAt j = some o' ∧ ShapeIs T'.shape o' := by
  obtain ⟨t, ht, rfl⟩ := Option.map_eq_some_iff.1 h
  exact ⟨t, o, ht, ho, hS⟩

/-- By the kernel: W's sending at the written key sends a message. -/
theorem msgW_pos : 0 < ((linMessageW keyFull.once.shape).getD #[]).size := by decide +kernel

variable {X : Source} {N : H2U.PlaceNums} {P : LaterPlaces}

/-- **From the file's tree 5 on the IOP as written in Lean tells what W's sending tells.** -/
theorem told_w (hp : (descriptionFromSource X N P).planOk = true) (hD : (descriptionFromSource X N P).data "key file" = .ok writtenKFull)
    (hL : (descriptionFromSource X N P).first.blocksInOrder.map (·.rounds.length) = roundsL₁) (msg : Array OracleNotice)
    (hm : linMessageW X.Y.k.oneTime.lin = some msg) :
    ∃ Q : K1.Par, Q.codes = X.Y.k.oneTime.codes ∧ Q.sent = msg ∧
      ∀ τ, τ < (toldK1 Q).length → (descriptionFromSource X N P).oracleAt (5 + τ) = (toldK1 Q)[τ]? := by
  obtain ⟨A, g, bw, e, hA, hbw⟩ := flat_tail X N P msg hm
  have hlen : (flat₁ X N P).length = 19 := by
    have := congrArg List.length (show (flat₁ X N P).map (·.rounds.length) = roundsL₁ from hL)
    rw [List.length_map] at this
    exact this
  have hA17 : A.length = 17 := by
    rw [hA, List.length_append] at hlen
    simpa using hlen
  have h5 : (oraclesOf A).length = 5 := by
    have := (show (oraclesOf ((flat₁ X N P).take 17)).length = 5 from (seats_scope X N P hp hD hL).2.2)
    rwa [hA, List.take_left' hA17] at this
  refine ⟨parW' X.Y.k.oneTime pieces g msg, rfl, sent_par _ _ _ _ _, fun τ hτ => ?_⟩
  have hτ' : τ < ((K1.oracles (parW' X.Y.k.oneTime pieces g msg)).flatMap id).length := hτ
  have hs : oraclesOf (A ++ [bw, e]) = oraclesOf A ++ (bw.oracles.flatMap id ++ e.oracles.flatMap id) := by
    simp [oraclesOf, List.flatMap_append]
  rw [oracleAt_flat₁, hA, hs, hbw]
  simp only [List.append_assoc]
  rw [List.getElem?_append_right (by rw [h5]; exact Nat.le_add_right _ _), h5, Nat.add_sub_cancel_left]
  exact List.getElem?_append_left hτ'

/-- **What is told of the file's tree 7, by its numbers.** -/
theorem nums_seven (hk : X.chains.made.sized.key = keyFull) (hp : (descriptionFromSource X N P).planOk = true)
    (hD : (descriptionFromSource X N P).data "key file" = .ok writtenKFull)
    (hL : (descriptionFromSource X N P).first.blocksInOrder.map (·.rounds.length) = roundsL₁) :
    ((descriptionFromSource X N P).oracleAt 7).map numsOf = some (22, 36, [(36, 0)]) := by
  obtain ⟨R, hR⟩ := told_shared X N P
  have h6 := first_tells_six X N P hp hD hL
  have hpar : sharedPar X.chains (beforeSharedPoint P) = { parF with beforePoint := beforeSharedPoint P } := by
    unfold sharedPar parF
    rw [hk]
  have hT : (oraclesOf (_root_.Desc.K14.blocksOr (sharedPar X.chains (beforeSharedPoint P)))).map numsOf =
      [(24, 324, [(321, 0), (0, 3)]), (22, 36, [(36, 0)]), (13, 3, [(0, 3)])] := by
    rw [hpar, oraclesOf_of_map _ _ (told_bp parF (beforeSharedPoint P))]
    exact nums_k14
  show ((descriptionFromSource X N P).oracleAt (6 + 1)).map numsOf = _
  unfold FileDescription.oracleAt
  rw [← List.getElem?_map, hR]
  simp only [List.map_append, List.append_assoc, hT]
  rw [List.getElem?_append_right (by rw [List.length_map, h6]; omega), List.length_map, h6, Nat.add_sub_cancel_left]
  rfl

/-! ## 6 The tops -/

variable {Zp : VerifierAndGoals.PublicFiles} {Z : OnBytes.Model.Verify.Public} {cfg : ByteArray} {m : Johnson.G.OfPlan.Made}

/-- **At the first chain's end**: six roots are received; the book's trees 0 and 5 have the shapes that are told of the file's trees 0
and 5. -/
theorem first_end (hZ : VerifierAndGoals.InScope Zp = true) (hP : ReadOf Zp.pol Z) (hm : madeAt Z Zp.lay cfg = .ok m)
    (hX : sourceOf m = .ok X) (hp : (Fk X N P).planOk = true) (hw : (Fk X N P).wantedOk = true)
    (hD : (Fk X N P).data "key file" = .ok writtenKFull) (hft : N.nums.firstTree = 0) (D : WholeD)
    (a : Xi × FirstState) (h : Hist₁ (Fk X N P) D 19 a) :
    a.2.d.roots = 6 ∧
      (∃ T o, treeShape a.2.d.book 0 = some T ∧ (Fk X N P).oracleAt 0 = some o ∧ ShapeIs T o) ∧
      (∃ T o, treeShape a.2.d.book 5 = some T ∧ (Fk X N P).oracleAt 5 = some o ∧ ShapeIs T o) := by
  obtain ⟨x₀, x₁, hl⟩ := LPFD.hl_in_scope hZ hP hm hX hp
  obtain ⟨bw, hbw⟩ := LPFD.hw_in_scope hZ hP hm hX hp pieces (LPFD.sent17 X) (LPFD.g17 X)
  obtain ⟨c₁, k₁, q₁⟩ : ∃ c₁ k₁, (Fk X N P).first.blocksInOrder = c₁ :: k₁ := ⟨_, _, rfl⟩
  have h5s := five_in_scope hZ hP hm hX hp
  have hL := (Johnson.RunOne.Sound.rounds_in_scope hZ hP hm hX hp hw).1
  have h18 := seal_19 hl hbw D a h
  obtain ⟨a17, msg, num, src, h17, hmsg, hlay, hS⟩ := w_18 hl hbw D a h18
  obtain ⟨a1, h1, k117⟩ := keeps_1_17 hp hl D a17 h17
  obtain ⟨layI, hlI, hI⟩ := idx_one D a1 h1
  have A17 := LPFD.aSide_at_all X N P c₁ k₁ D q₁ hZ hP hm hX hp hft 17 a17 (by decide) h17
  have A19 := LPFD.aSide_at_all X N P c₁ k₁ D q₁ hZ hP hm hX hp hft 19 a (by decide) h
  have hst : (oneAt X).ranges.stages.length = 4 := by rw [h5s.2.1]; exact Johnson.RunOne.KeyLetters.stages_full
  have t17 : (show FirstState from a17.2).d.book.trees.size = 5 := by
    rw [(Johnson.RunOne.KeyRows1.front17 (oneAt X) a17.2 A17.1).2.2.1, hst]
  refine ⟨by rw [LPFD.roots_of_aSide19 (oneAt X) atSix a.2 A19, hst], ?_, ?_⟩
  · have e1 : layI.shapes.size = 1 := Johnson.RunOne.Law.BookPlace.single_tree _ _ _ hlI
    have s0 : treeShape a.2.d.book 0 = some (layI.shapes.getD 0 {}) :=
      treeShape_keeps (keeps_of_seated hS) (treeShape_keeps k117 (hI 0 (by rw [e1]; decide)))
    have hmI : Own.treesMade (parIdx X).codes (parIdx X).sent = some layI := by
      rw [Own.treesMade_eq, (par_facts X).1, (par_facts X).2.1]
      exact hlI
    obtain ⟨o0, ho0, hS0⟩ := toldK1_shape (parIdx X) layI hmI 0 _ (getD_some _ 0 {} (by rw [e1]; decide))
    have hlen0 : 0 < (toldK1 (parIdx X)).length := by rw [toldK1_length _ _ hmI, e1]; decide
    exact ⟨_, o0, s0, (oracleAt_idx X N P 0 hlen0).trans ho0, hS0⟩
  · have em : msg = (linMessageW keyFull.once.shape).getD #[] := by
      have hm' := hmsg
      rw [h5s.2.2.1, msgW_some] at hm'
      exact (Option.some.inj hm').symm
    have hpos : 0 < (parW' X.Y.k.oneTime pieces (LPFD.g17 X) msg).sent.size := by
      rw [sent_par, em]
      exact msgW_pos
    have h0 : 0 < (K1.layOf (parW' X.Y.k.oneTime pieces (LPFD.g17 X) msg)).shapes.size :=
      Nat.lt_of_le_of_lt (Nat.zero_le _) (hS.fits 0 hpos).1
    have s5 : treeShape a.2.d.book (5 + 0) = some ((K1.layOf (parW' X.Y.k.oneTime pieces (LPFD.g17 X) msg)).shapes.getD 0 {}) := by
      have := treeShape_made hS h0
      rwa [t17] at this
    obtain ⟨Q, hQc, hQs, hQ⟩ := told_w hp hD hL msg hmsg
    have hmQ : Own.treesMade Q.codes Q.sent = some (K1.layOf (parW' X.Y.k.oneTime pieces (LPFD.g17 X) msg)) := by
      rw [Own.treesMade_eq, hQc, hQs]
      have := hlay
      rw [sent_par] at this
      exact this
    obtain ⟨o5, ho5, hS5⟩ := toldK1_shape Q _ hmQ 0 _ (getD_some _ 0 {} h0)
    exact ⟨_, o5, s5, (hQ 0 (by rw [toldK1_length _ _ hmQ]; exact h0)).trans ho5, hS5⟩

/-- **IN FRONT OF THE KEY FILE's LAST PROXIMITY TEST THE BOOK's TREES 0 · 5 · 6 HAVE THE SHAPES THAT THE IOP AS WRITTEN IN LEAN TELLS OF
THE FILE's TREES 0 · 5 · 7.** -/
theorem book_32_of (hZ : VerifierAndGoals.InScope Zp = true) (hP : ReadOf Zp.pol Z) (hm : madeAt Z Zp.lay cfg = .ok m)
    (hX : sourceOf m = .ok X) (hp : (Fk X N P).planOk = true) (hw : (Fk X N P).wantedOk = true)
    (hD : (Fk X N P).data "key file" = .ok writtenKFull) (hft : N.nums.firstTree = 0) (D : WholeD)
    (a : (Xi × FirstState × St₂) × St₃) (h : Hist₃ (Fk X N P) D 2 a) :
    (∃ T o, a.2.book.trees[0]? = some T ∧ (Fk X N P).oracleAt 0 = some o ∧ ShapeIs T.shape o) ∧
      (∃ T o, a.2.book.trees[5]? = some T ∧ (Fk X N P).oracleAt 5 = some o ∧ ShapeIs T.shape o) ∧
      (∃ T o, a.2.book.trees[6]? = some T ∧ (Fk X N P).oracleAt 7 = some o ∧ ShapeIs T.shape o) := by
  obtain ⟨x₀, x₁, hl⟩ := LPFD.hl_in_scope hZ hP hm hX hp
  obtain ⟨bw, hbw⟩ := LPFD.hw_in_scope hZ hP hm hX hp pieces (LPFD.sent17 X) (LPFD.g17 X)
  have hlen19 : (Fk X N P).first.blocksInOrder.length = 19 :=
    Johnson.RunOne.KeyRows1.flat_length (oneAt X) X.Y.D.1 X.Y.told.1 X.set N x₀ x₁ hl bw hbw
  have hL := (Johnson.RunOne.Sound.rounds_in_scope hZ hP hm hX hp hw).1
  have hk : X.chains.made.sized.key = keyFull :=
    (congrArg (·.made.sized.key) (chains_of hX)).trans (key_in_scope hZ hP hm)
  obtain ⟨f, hfl, -, -, hfd⟩ := Johnson.RunOne.KeyRows23.second_flat X N P
  obtain ⟨a₁, b₁, rs₁, cols₁, hr₁, hb₁, hd₁, -⟩ := Reached.last h
  obtain ⟨a₀, b₀, rs₀, cols₀, hr₀, hb₀, hd₀, -⟩ := Reached.last hr₁
  have hfl' : (Fk X N P).second.blocksInOrder = [f, Johnson.RunOne.KeyRows23.seat (Third.takenSources (ownTest P)),
               Johnson.RunOne.KeyRows23.seat (Johnson.RunOne.KeyRows23.own₃ P), Johnson.RunOne.KeyRows23.seat (Johnson.RunOne.KeyRows23.end₃At X P)] := hfl
  rw [hfl'] at hb₀ hb₁
  have q₀ : b₀ = (held f : Block ((Xi × FirstState × St₂) × St₃) Claim) := (Option.some.inj hb₀).symm
  have q₁ : b₁ = (held (Johnson.RunOne.KeyRows23.seat (Cl := Claim) (Third.takenSources (ownTest P))) :
      Block ((Xi × FirstState × St₂) × St₃) Claim) := (Option.some.inj hb₁).symm
  rw [q₀] at hd₀
  rw [q₁] at hd₁
  obtain ⟨e₀, d₀⟩ := held_decide f a₀ _ _ a₁ hd₀
  obtain ⟨e₁, d₁⟩ := held_decide (Johnson.RunOne.KeyRows23.seat (Cl := Claim) (Third.takenSources (ownTest P))) a₁ _ _ a hd₁
  obtain ⟨hH, hst⟩ : Hist₂ (Fk X N P) D (Fk X N P).shared.blocksInOrder.length ((a₀.1.1, a₀.1.2.1), a₀.1.2.2) ∧
      ((Fk X N P).start₃ a₀.1.1 a₀.1.2.1 a₀.1.2.2).toOption = some a₀.2 := hr₀
  obtain ⟨o, l, -, -, hs⟩ := Johnson.RunOne.KeyRows23.starts_fkD X N P a₀.1.1 a₀.1.2.1 a₀.1.2.2 a₀.2 (LPFD.ok_of_toOption hst)
  have h19 : Hist₁ (Fk X N P) D 19 (a₀.1.1, a₀.1.2.1) := hlen19 ▸ LPFD.hist₂_handed (Fk X N P) D _ _ hH
  obtain ⟨hr6, ⟨T0, o0, s0, hO0, hS0⟩, ⟨T5, o5, s5, hO5, hS5⟩⟩ := first_end hZ hP hm hX hp hw hD hft D _ h19
  rw [hfd] at d₀
  rw [Johnson.RunOne.KeyRows23.seat_decide] at d₁
  have ea : a.2 = a₁.2 := Third.Law.takenSources_same _ _ _ _ _ d₁
  obtain ⟨eb, -, eft⟩ := Third.Law.start₃E_book _ _ _ _ _ _ _ _ _ _ _ hs
  obtain ⟨-, hsz⟩ := H2K.First.k14Second_first (Cl := Unit) (thirdPar X.chains) a₀.2 a₁.2 _ _ d₀
  have hsix : a₀.2.book.trees.size = 6 := by
    rw [eft] at hsz
    have : a₀.2.book.trees.size = a₀.1.2.1.d.roots := Nat.succ.inj hsz
    rw [this, hr6]
  obtain ⟨-, ft⟩ := Third.Law.book_carried (Cl := Unit) (thirdPar X.chains) _ _ _ _ _ _ _ o a₀.2 a₁.2 _ _ hs d₀
  have hsix' : a₀.1.2.1.d.book.trees.size = 6 := by
    have e : a₀.2.book = a₀.1.2.1.d.book := eb
    rw [← e]
    exact hsix
  have old : ∀ i, i < 6 → treeShape a.2.book i = treeShape a₀.1.2.1.d.book i := fun i hi => by
    unfold treeShape
    rw [ea, ft i (by
      show i < a₀.1.2.1.d.book.trees.size
      rw [hsix']
      exact hi)]
    rfl
  obtain ⟨lay, hlay, sO⟩ := omega_tree (Cl := Unit) (thirdPar X.chains) a₀.2 a₁.2 _ _ d₀
  obtain ⟨fo, hfo, hst3⟩ := Third.Law.start₃E_inv _ _ _ _ _ _ _ _ _ _ _ hs
  obtain ⟨hc, -, e0⟩ := Third.Law.start₃_inv _ _ _ _ hst3
  have hcodes : a₀.2.st.codes = keyFull.codes := by
    rw [e0]
    show fo.st.codes = _
    rw [hc, hk]
  have hlay' : layTrees keyFull.codes
      #[{ shape := keyFull.once.shape.omega, leafClass := keyFull.once.shape.omegaLeafClass }] = some lay := by
    rw [← hcodes, ← hk]
    exact hlay
  have K := omega_alone_full
  rw [hlay'] at K
  simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at K
  obtain ⟨k1, k2, k3⟩ := K
  obtain ⟨o7, hO7, hn7⟩ := Option.map_eq_some_iff.1 (nums_seven hk hp hD hL)
  refine ⟨give ((old 0 (by decide)).trans s0) hO0 hS0, give ((old 5 (by decide)).trans s5) hO5 hS5, ?_⟩
  refine give (T := lay.shapes.getD 0 {}) ?_ hO7 (shapeIs_of_nums hn7 k1 k2 k3)
  rw [ea, ← hsix]
  exact sO

/-- **The same at what a caller holds**: the data by way of DK; the numbers of the ranges' test's place are the maker's. -/
theorem book_32 (hZ : VerifierAndGoals.InScope Zp = true) (hP : ReadOf Zp.pol Z) (hm : madeAt Z Zp.lay cfg = .ok m)
    (hX : sourceOf m = .ok X) (hp : (Fk X N P).planOk = true) (hw : (Fk X N P).wantedOk = true) (DK : WholeD)
    (hD₀ : (Fk X N P).data "key file" = .ok (DK.at OnBytes.Slice.frS.P.T.a)) (hDK : DK.at OnBytes.Slice.frS.P.T.a = writtenKFull)
    (hN : rangesNumbers m = .ok N) (D : WholeD) (a : (Xi × FirstState × St₂) × St₃) (h : Hist₃ (Fk X N P) D 2 a) :
    (∃ T o, a.2.book.trees[0]? = some T ∧ (Fk X N P).oracleAt 0 = some o ∧ ShapeIs T.shape o) ∧
      (∃ T o, a.2.book.trees[5]? = some T ∧ (Fk X N P).oracleAt 5 = some o ∧ ShapeIs T.shape o) ∧
      (∃ T o, a.2.book.trees[6]? = some T ∧ (Fk X N P).oracleAt 7 = some o ∧ ShapeIs T.shape o) :=
  book_32_of hZ hP hm hX hp hw (by rw [hD₀, hDK]) (firstTree_of_rangesNumbers hN) D a h

/-- The three indices are there: off₃N's numbering of the last chain's book's trees sends 0 · 5 · 6 to the seats' trees. -/
theorem there_32 : (atSix 0).1 = LPFD.off₃N 0 ∧ (atSix 2).1 = LPFD.off₃N 5 ∧ (atSix 4).1 = LPFD.off₃N 6 := by decide

/-- **At the seats 0 · 2 · 4 (the index masks · W · Omega): the book's tree whose number through the file is the seat's has the shape that
the IOP as written in Lean tells of that tree.** z: the tree's index in the last chain's book. That the book places a message at z is not
said here. -/
theorem shapeIs_32 (hZ : VerifierAndGoals.InScope Zp = true) (hP : ReadOf Zp.pol Z) (hm : madeAt Z Zp.lay cfg = .ok m)
    (hX : sourceOf m = .ok X) (hp : (Fk X N P).planOk = true) (hw : (Fk X N P).wantedOk = true) (DK : WholeD)
    (hD₀ : (Fk X N P).data "key file" = .ok (DK.at OnBytes.Slice.frS.P.T.a)) (hDK : DK.at OnBytes.Slice.frS.P.T.a = writtenKFull)
    (hN : rangesNumbers m = .ok N) (D : WholeD) (a : (Xi × FirstState × St₂) × St₃) (h : Hist₃ (Fk X N P) D 2 a)
    (k : ℕ) (hk : k ∈ [0, 2, 4]) (z : ℕ) (hz : (atSix k).1 = LPFD.off₃N z) :
    ∀ o, (Fk X N P).oracleAt (atSix k).1 = some o → ∃ T, a.2.book.trees[z]? = some T ∧ ShapeIs T.shape o := by
  obtain ⟨⟨T0, o0, t0, hO0, hS0⟩, ⟨T5, o5, t5, hO5, hS5⟩, ⟨T6, o7, t6, hO7, hS7⟩⟩ :=
    book_32 hZ hP hm hX hp hw DK hD₀ hDK hN D a h
  have hoff : (LPFD.off₃N z = 0 → z = 0) ∧ (LPFD.off₃N z = 5 → z = 5) ∧ (LPFD.off₃N z = 7 → z = 6) := by
    unfold LPFD.off₃N
    refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩ <;> split at h <;> (try split at h) <;> omega
  intro o ho
  have hk' : k = 0 ∨ k = 2 ∨ k = 4 := by simpa using hk
  rcases hk' with rfl | rfl | rfl
  · obtain rfl := hoff.1 hz.symm
    obtain rfl : o0 = o := Option.some.inj (hO0.symm.trans ho)
    exact ⟨T0, t0, hS0⟩
  · obtain rfl := hoff.2.1 hz.symm
    obtain rfl : o5 = o := Option.some.inj (hO5.symm.trans ho)
    exact ⟨T5, t5, hS5⟩
  · obtain rfl := hoff.2.2 hz.symm
    obtain rfl : o7 = o := Option.some.inj (hO7.symm.trans ho)
    exact ⟨T6, t6, hS7⟩

end

end Johnson.RunOne.Law.BookAt32

#print axioms Johnson.RunOne.Law.BookAt32.seat_seated
#print axioms Johnson.RunOne.Law.BookAt32.omega_alone_full
#print axioms Johnson.RunOne.Law.BookAt32.omega_alone_no
#print axioms Johnson.RunOne.Law.BookAt32.idx_sent
#print axioms Johnson.RunOne.Law.BookAt32.own_keeps
#print axioms Johnson.RunOne.Law.BookAt32.rng_keeps
#print axioms Johnson.RunOne.Law.BookAt32.batt_book
#print axioms Johnson.RunOne.Law.BookAt32.w_seated
#print axioms Johnson.RunOne.Law.BookAt32.back_one
#print axioms Johnson.RunOne.Law.BookAt32.idx_one
#print axioms Johnson.RunOne.Law.BookAt32.keeps_1_17
#print axioms Johnson.RunOne.Law.BookAt32.w_18
#print axioms Johnson.RunOne.Law.BookAt32.seal_19
#print axioms Johnson.RunOne.Law.BookAt32.shapeIs_of_nums
#print axioms Johnson.RunOne.Law.BookAt32.msgW_pos
#print axioms Johnson.RunOne.Law.BookAt32.told_w
#print axioms Johnson.RunOne.Law.BookAt32.nums_seven
#print axioms Johnson.RunOne.Law.BookAt32.first_end
#print axioms Johnson.RunOne.Law.BookAt32.book_32_of
#print axioms Johnson.RunOne.Law.BookAt32.book_32
#print axioms Johnson.RunOne.Law.BookAt32.there_32
#print axioms Johnson.RunOne.Law.BookAt32.shapeIs_32
#print axioms Johnson.RunOne.Law.BookAt32.give
