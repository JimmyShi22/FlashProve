-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K13/ExchangeM4Proof.lean: kind K13's share of the debt `Exchange` at
the place "M:4": the proofs of the conditional statements of
Johnson/Desc/ProofFile/Honest/K13/ExchangeM4.lean. Statements with their proofs.

How it goes. The member at "M:4" is the lot's sub-protocol wrapped alone, so its accepted step is an
accepted step of that sub-protocol (`k13_m4_alone`, Johnson/Desc/ProofFile/Honest/Member/Uses.lean;
`alone_gives`, AtLot.lean). `play` keeps the input and adds its challenges to those heard
(`play_mid`, Honest/Law/Along.lean; `play_heard`, Honest/Thread/PaysLaw.lean), so the witness
behind, at a continuation, is the witness in front at a longer one. In front `pileOne` is open: the
row on the table is true under the reader at the state in front. The readers at the two states agree
on the message of index masks (`agree4`, Johnson/Desc/K13/Law/Reader4.lean), and the rows stay
(`atM4_rec`, AtRecord.lean): so `pileOne` holds behind: SO FAR NEITHER `WitnessHasW` NOR
`ReplyRides` IS USED. Within the table the cut reader and the plain one agree (`rowsTrue_cut`,
PileOneJoint.lean); with `WitnessHasW`, at the reply that `ReplyRides` gives, that gives `WRow`
behind (`wRow_at_accept`, Johnson/Desc/K13/Honest/WRowAtAccept.lean).
Main names:
  `owes_at_m4`, `owes_tied`: the forward row at the place "M:4" owes `pinV`, `pileOne`, `pinW`,
    `wrow`, whatever the segments' sorts; so does the thread's row number b under `TiedAtM4`.
  `exchange_iff_m4`, `exchange_of_m4`: `Exchange` there is the share at these four; it follows from
    kind K13's share and the shares at `pinW` and `pinV`.
  `sent_of_accept`: where the decision at the place of W's commitment accepts, W's commitment has
    sent a message.
  `rowsWithin_m4`: the rows' mask entries lie within their tables behind the place, if they do in
    front.
  `m4_behind`: what both items stand on.
  `pileOne_at_m4`: **the statement at `pileOne`**: under `IM.Open`, `TiedAtM4` and `PublicAtM4` from
    the thread.
  `wrow_stand`: the core at `wrow`, at one stand at which `ReplyIs` holds.
  `wrow_at_m4`: **the statement at `wrow`**: under these, `ReplyRides` and `WitnessHasW`.
  `exchange_at_m4`: the two together.

What is not claimed. What ExchangeM4.lean says is not claimed: above all, the debt at `wrow` is not
met here: it is carried back to `WitnessHasW`, `ReplyRides`, `PublicAtM4` from the thread in front,
and `TiedAtM4`. Nothing on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K13.ExchangeM4
import Johnson.Desc.ProofFile.Honest.Member.Uses
import Johnson.Desc.ProofFile.Honest.Thread.PaysLaw
import Johnson.Desc.K13.Honest.WRowAtAccept
import Johnson.Desc.K13.Law.PileOneJoint
import Johnson.Desc.K13.Law.WithinM4

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K13
open OnBytes OnBytes.Slice
open VerifiableInference.Desc (Block Chain FileDescription OpenedColumn)
open VerifiableInference.Desc.First (S Item)
open VerifiableInference.Desc.Sound (MsgT wordsFirst)
open VerifiableInference.Desc.K13 (Where whereOf wBlock atM4 pileMasksC rowsWithinC)
open VerifiableInference.Desc.K13.Law
open VerifiableInference.Desc.K13.Honest (wRow_at_accept)
open ProofFile.Honest.AtPlace (k13_m4_alone k13_at_m4 alone_gives)

/-- The forward row at the place "M:4" owes four items, whatever the segments' sorts. -/
theorem owes_at_m4 (links : List VerifiableInference.Desc.First.ModelPart) :
    (FirstRows.rowAt links ⟨1, none, 4, .K1⟩).owes =
      [Item.pinV, Item.pileOne, Item.pinW, Item.wrow] := rfl

/-- Under `TiedAtM4` the thread's row number b owes these four. -/
theorem owes_tied {Bk : ProverCoinCounts} {W₀ Rc Xi Tr X P Cells Tok : Type} {nR : ℕ}
    {L : FirstThread.Letters Bk Cl W₀ Rc Xi Tr X P Cells Tok MsgT} {b : Nat} {Z : Pub}
    {c : Chain S Cl} {arr : ℕ → ℕ → ℕ}
    {mat : Cells → Fin nR → (Fin (whereOf Z).lin.kCol → Bool) → GE}
    (Ti : TiedAtM4 L b Z c arr mat) :
    (L.thread.row b).owes = [Item.pinV, Item.pileOne, Item.pinW, Item.wrow] := by
  show (FirstRows.rows L.links L.ps b).owes = _
  unfold FirstRows.rows
  rw [Ti.row]
  exact owes_at_m4 L.links

/-- `Exchange` at "M:4" is the share at the four items that the forward row owes. -/
theorem exchange_iff_m4 {Bk : ProverCoinCounts} {W₀ Rc Xi Tr X P Cells Tok : Type} {nR : ℕ}
    {L : FirstThread.Letters Bk Cl W₀ Rc Xi Tr X P Cells Tok MsgT} {b : Nat} {Z : Pub}
    {c : Chain S Cl} {arr : ℕ → ℕ → ℕ}
    {mat : Cells → Fin nR → (Fin (whereOf Z).lin.kCol → Bool) → GE}
    (Ti : TiedAtM4 L b Z c arr mat) :
    Exchange L.thread b ↔
      ExchangeOf L.thread b [Item.pinV, Item.pileOne, Item.pinW, Item.wrow] := by
  rw [exchangeOf_all, owes_tied Ti]
  exact Iff.rfl

/-- So it follows from kind K13's share and the shares at `pinV` and `pinW`. -/
theorem exchange_of_m4 {Bk : ProverCoinCounts} {W₀ Rc Xi Tr X P Cells Tok : Type} {nR : ℕ}
    {L : FirstThread.Letters Bk Cl W₀ Rc Xi Tr X P Cells Tok MsgT} {b : Nat} {Z : Pub}
    {c : Chain S Cl} {arr : ℕ → ℕ → ℕ}
    {mat : Cells → Fin nR → (Fin (whereOf Z).lin.kCol → Bool) → GE}
    (Ti : TiedAtM4 L b Z c arr mat) (h1 : ExchangeOf L.thread b [Item.wrow, Item.pileOne])
    (h2 : ExchangeOf L.thread b [Item.pinW]) (h3 : ExchangeOf L.thread b [Item.pinV]) :
    Exchange L.thread b := by
  refine (exchange_iff_m4 Ti).2 ((exchangeOf_mem L.thread b _).2 fun i hi => ?_)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl
  · exact h3
  · exact (exchangeOf_mem L.thread b _).1 h1 _ (by simp)
  · exact h2
  · exact (exchangeOf_mem L.thread b _).1 h1 _ (by simp)

/-- Where the decision at the place of W's commitment accepts, W's commitment has sent a message:
the text behind it takes the first of the numbers handed on. -/
theorem sent_of_accept {Cl' : Type} {Pw : Where} {P' : VerifiableInference.Desc.K1.Par} {s s' : S}
    {r₁ r₂ : Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (h : (atM4 (Cl := Cl') Pw (VerifiableInference.Desc.K1.sendAtS P')).decide s [r₁, r₂] gs =
      .ok s') : 0 < P'.sent.size := by
  obtain ⟨s₁, g₁, rs₂, g₂, h1, h2⟩ := atM4_mid h
  obtain ⟨a, _, ha', _⟩ := sendAtS_full P' s s₁ r₁ r₂ g₁ h1
  obtain ⟨m₀, l, o, _, hs, _, hrows, _⟩ := rowsB_at h2
  rw [ha'] at hs
  obtain rfl := VerifiableInference.Desc.First.Here.mem.inj hs
  obtain ⟨_, _, _, _, hw, _⟩ := rows_ok hrows
  by_contra hc
  have e : P'.sent.size = 0 := by omega
  have hw' : ((Array.range P'.sent.size).map (· + s.st.oracles.size))[0]? = some o.1.w := hw
  rw [e] at hw'
  simp at hw'

/-- The rows' mask entries lie within their tables behind the place, if they do in front. The
library has these lines inside the proof of `withinM4` (Johnson/Desc/K13/Law/WithinM4.lean), for a
test that asks more. -/
theorem rowsWithin_m4 {Cl' : Type} {Pw : Where} {P' : VerifiableInference.Desc.K1.Par} {s s' : S}
    {r₁ r₂ : Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (h : (atM4 (Cl := Cl') Pw (VerifiableInference.Desc.K1.sendAtS P')).decide s [r₁, r₂] gs =
      .ok s') (hr : rowsWithinC s = true) : rowsWithinC s' = true := by
  have hg := atM4_rel VerifiableInference.Desc.Ground.groundKeeps_grows Pw P' s s' _ gs h
  have hrows : s'.rows = s.rows := (atM4_rec h).2.2.2.2
  unfold rowsWithinC at hr ⊢
  rw [hrows]
  simp only [List.all_eq_true, decide_eq_true_eq] at hr ⊢
  intro r hrm t ht
  exact tableSizeC_grows hg _ _ _ (hr r hrm t ht)

/-- **What both items stand on**: under `IM.Open`, `TiedAtM4` and `PublicAtM4` at the state in
front: behind the member's accepted step: the decision of the lot's sub-protocol has accepted, on
two rounds; the input stays; and the row on the table is true at the state behind, of the witness
behind, at the continuation ds'. -/
theorem m4_behind {Bk : ProverCoinCounts} {W₀ Rc Xi Tr X P Cells Tok : Type} {nR : ℕ}
    {L : FirstThread.Letters Bk Cl W₀ Rc Xi Tr X P Cells Tok MsgT} {b : Nat}
    {o : SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription Inst} {Z : Pub} {Bs : PureBase}
    {base : List (Block S Cl)} {c : Chain S Cl} {A : SharedSeat} {B : SecondSeat}
    {arr : ℕ → ℕ → ℕ} {mat : Cells → Fin nR → (Fin (whereOf Z).lin.kCol → Bool) → GE}
    (O : IM.Open o pol lay KL F Z Bs base c A B) (Ti : TiedAtM4 L b Z c arr mat)
    {blk : Block S Cl} (hblk : L.thread.bs[b]? = some blk) {k : Coins Bk} {s s' : S}
    {m : Mid (Local W₀ Rc Xi Tr) X} {En : Env} {ds : List Fmt.Drawn}
    {y : List Played × Mid (Local W₀ Rc Xi Tr) X} {cols : List OpenedColumn}
    (hT : Thr L.thread b k s m En) (hP : PublicAtM4 (whereOf Z) s)
    (hS : L.thread.Stepped blk k s m En ds y cols s') (ds' : List Fmt.Drawn) :
    ∃ (P' : VerifiableInference.Desc.K1.Par) (r₁ r₂ : Fmt.RoundView)
      (gs : List (List (Nat × List UInt64))),
      (atM4 (Cl := Unit) (whereOf Z) (VerifiableInference.Desc.K1.sendAtS P')).decide s [r₁, r₂]
        gs = .ok s' ∧ y.2.st.input = m.st.input ∧
      RowsTrue (rwBook arr mat (L.pubOf m.st.input.x, s')) s'
        (L.Q.wit k y.2.st.input (y.2.st.heard ++ ds')) := by
  obtain ⟨⟨⟨l, _, hplay⟩, _⟩, hstep⟩ := hS
  obtain ⟨hin, _, _⟩ := play_mid l ds [] m y hplay
  have hheard := play_heard l ds [] m y hplay
  have hblk' : L.bs[b]? = some blk := hblk
  have hmem : blk ∈ c.blocksInOrder := by
    rw [← Ti.flat]
    exact List.mem_of_getElem? hblk'
  have hpl := Ti.place blk hblk'
  -- W's commitment, as the lot takes it
  obtain ⟨P', hw, _⟩ := k13_at_m4 o pol lay KL F Z Bs base c A B O
  -- the member's step is the lot's sub-protocol's
  obtain ⟨x, hF, hA⟩ := k13_m4_alone O hw hmem hpl
  have hb := ((alone_gives sameReply x blk _ _ _ hF hA).2.2.2.2.2.2 _ s s' _ _ cols).1 hstep
  have hst : (atM4 (Cl := Unit) (whereOf Z)
      (VerifiableInference.Desc.K1.sendAtS P')).step L.thread.ft s (roundsOf y.1) cols =
      .ok (s', cols.length) := hb.1
  have hM4 : StepM4 Unit (whereOf Z) P' (L.pubOf m.st.input.x, s)
      (L.pubOf m.st.input.x, s') := ⟨rfl, _, _, _, _, hst⟩
  obtain ⟨r₁, r₂, gs, hdec⟩ := hM4.decide
  have hrows' : s'.rows = s.rows := (atM4_rec hdec).2.2.2.2
  -- the witness behind, at ds', is the witness in front at ds ++ ds'
  have hv : L.Q.wit k y.2.st.input (y.2.st.heard ++ ds') =
      L.Q.wit k m.st.input (m.st.heard ++ (ds ++ ds')) := by
    rw [hin, hheard, List.append_assoc]
  -- pileOne in front
  have h1 : (L.Mg m.st.input).pileOne (L.pubOf m.st.input.x, s) (L.thread.strs En)
      (L.Q.wit k m.st.input (m.st.heard ++ (ds ++ ds'))) :=
    hT.2.2.2.1 (ds ++ ds') Item.pileOne Ti.opened
  rw [Ti.pileOne, ← hv] at h1
  -- pileOne behind
  refine ⟨P', r₁, r₂, gs, hdec, hin, fun r hr => ?_⟩
  rw [hrows'] at hr
  exact (holds_congr ρg ((pileMasksC_iff s).1 hP.masks r hr)
    (agree4 arr mat (whereOf Z) P' (L.pubOf m.st.input.x, s)
      (L.pubOf m.st.input.x, s') _ hM4 hP.there hP.book hP.tree)).2 (h1 r hr)

/-- **`PileOneAtM4`**: behind the accepted step of the member at "M:4" the item `pileOne` holds:
under `IM.Open`, `TiedAtM4` and `PublicAtM4` from the thread in front, and no more. -/
theorem pileOne_at_m4 : PileOneAtM4 := by
  intro Bk W₀ Rc Xi Tr X P Cells Tok nR L b o pol lay KL F Z Bs base c A B arr mat O Ti hpub
    blk hblk k s m En ds y cols s' hT hd hS ds' i hi
  obtain rfl : i = Item.pileOne := List.mem_singleton.1 hi
  obtain ⟨_, _, _, _, _, hin, h2⟩ := m4_behind O Ti hblk hT (hpub k s m En hT) hS ds'
  show (L.Mg y.2.st.input).pileOne (L.pubOf y.2.st.input.x, s') _
    (L.Q.wit k y.2.st.input (y.2.st.heard ++ ds'))
  rw [Ti.pileOne]
  have e : L.pubOf y.2.st.input.x = L.pubOf m.st.input.x := by rw [hin]
  show RowsTrue (rwBook arr mat (L.pubOf y.2.st.input.x, s')) s' _
  rw [e]
  exact h2

/-- **The core at `wrow`, at one stand**: under `IM.Open`, `TiedAtM4` and `WitnessHasW`: at a stand
at which the thread holds in front, `PublicAtM4` holds AND THE REPLY THAT THE STATE HOLDS IS THE ONE
ASKED: behind the member's accepted step the item `wrow` holds, at every continuation. -/
theorem wrow_stand {Bk : ProverCoinCounts} {W₀ Rc Xi Tr X P Cells Tok : Type} {nR : ℕ}
    {L : FirstThread.Letters Bk Cl W₀ Rc Xi Tr X P Cells Tok MsgT} {b : Nat}
    {o : SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription Inst} {Z : Pub} {Bs : PureBase}
    {base : List (Block S Cl)} {c : Chain S Cl} {A : SharedSeat} {B : SecondSeat}
    {arr : ℕ → ℕ → ℕ} {mat : Cells → Fin nR → (Fin (whereOf Z).lin.kCol → Bool) → GE}
    {asked : Xi → E} (O : IM.Open o pol lay KL F Z Bs base c A B) (Ti : TiedAtM4 L b Z c arr mat)
    (hWs : WitnessHasW L b Z arr mat asked) {blk : Block S Cl}
    (hblk : L.thread.bs[b]? = some blk) {k : Coins Bk} {s s' : S}
    {m : Mid (Local W₀ Rc Xi Tr) X} {En : Env} {ds : List Fmt.Drawn}
    {y : List Played × Mid (Local W₀ Rc Xi Tr) X} {cols : List OpenedColumn}
    (hT : Thr L.thread b k s m En) (hP : PublicAtM4 (whereOf Z) s)
    (hY : ReplyIs asked m.st.input.x s) (hd : drawsFit blk.rounds ds = true)
    (hS : L.thread.Stepped blk k s m En ds y cols s') :
    L.thread.Items [Item.wrow] k s' y.2 (En.add y.1) := by
  intro ds' i hi
  obtain rfl : i = Item.wrow := List.mem_singleton.1 hi
  have hWIs := hWs blk hblk k s m En ds y cols s' hT hY hd hS ds'
  obtain ⟨P', r₁, r₂, gs, hdec, hin, h2⟩ := m4_behind O Ti hblk hT hP hS ds'
  obtain ⟨msg₀, ids, row, hs⟩ := hP.claim
  have hrows : s.rows = [row] := by simp only [S.rows, hs, rowOfClaim_member]
  have hrows' : s'.rows = s.rows := (atM4_rec hdec).2.2.2.2
  show (L.Mg y.2.st.input).wrow (L.pubOf y.2.st.input.x, s') _
    (L.Q.wit k y.2.st.input (y.2.st.heard ++ ds'))
  rw [Ti.wrow]
  have h3 := (rowsTrue_cut arr mat (L.pubOf m.st.input.x, s') _ (rowsWithin_m4 hdec hP.within)).1
    h2 row (by rw [hrows', hrows]; exact List.mem_singleton.2 rfl)
  exact wRow_at_accept hdec hs (sent_of_accept hdec) hP.room _ _ (hWIs row hrows) h3

/-- **`WRowAtM4`**: behind that step the item `wrow` holds: under the same three premises,
`ReplyRides` and `WitnessHasW`. -/
theorem wrow_at_m4 : WRowAtM4 := by
  intro Bk W₀ Rc Xi Tr X P Cells Tok nR L b o pol lay KL F Z Bs base c A B arr mat asked O Ti hpub
    hY hWs blk hblk k s m En ds y cols s' hT hd hS
  exact wrow_stand O Ti hWs hblk hT (hpub k s m En hT) (hY k s m En hT) hd hS

/-- **`ExchangeAtM4`**: the two items together, from the two statements. -/
theorem exchange_at_m4 : ExchangeAtM4 := by
  intro Bk W₀ Rc Xi Tr X P Cells Tok nR L b o pol lay KL F Z Bs base c A B arr mat asked O Ti hpub
    hY hWs
  exact (exchangeOf_append L.thread b [Item.wrow] [Item.pileOne]).2
    ⟨wrow_at_m4 L b o pol lay KL F Z Bs base c A B arr mat asked O Ti hpub hY hWs,
      pileOne_at_m4 L b o pol lay KL F Z Bs base c A B arr mat O Ti hpub⟩

end ProofFile.Honest.K13

#print axioms ProofFile.Honest.K13.owes_at_m4
#print axioms ProofFile.Honest.K13.owes_tied
#print axioms ProofFile.Honest.K13.exchange_iff_m4
#print axioms ProofFile.Honest.K13.exchange_of_m4
#print axioms ProofFile.Honest.K13.sent_of_accept
#print axioms ProofFile.Honest.K13.rowsWithin_m4
#print axioms ProofFile.Honest.K13.m4_behind
#print axioms ProofFile.Honest.K13.pileOne_at_m4
#print axioms ProofFile.Honest.K13.wrow_stand
#print axioms ProofFile.Honest.K13.wrow_at_m4
#print axioms ProofFile.Honest.K13.exchange_at_m4
