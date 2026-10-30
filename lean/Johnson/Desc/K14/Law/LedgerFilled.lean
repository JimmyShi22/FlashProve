-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K14/Law/LedgerFilled.lean: THE ONE TERM (share_row,
Johnson/Desc/K14/Law/LedgerRow.lean) WITH FEWER LETTERS: smp₂ := smpSt cs oNo stSh (another file's
filling: K1's reading smpAt at the member's number in the chain's statement:
Johnson/Desc/Sound/SmpShared.lean) · X := ANY TEST BESIDE shapeK THAT THE KIND's OWN BLOCKS HAND ON
· in promSigS's idle slot for the book: shiftBook N.lo (Johnson/Desc/Sound/HeldShift.lean), as
Johnson/Desc/Sound/NineAt.lean and TenAt.lean lay it at blocks 9 and 10.

  HandsOn, HandsOn.and   what is owed of X at the kind's eight clauses, IN THE BLOCKS' OWN
                  DECIDE-FORM (step · zeta · last); two such tests laid together are one.
  sharedX_zeta, handsOn_sharedX   sharedX (Johnson/Desc/Sound/SharedX.lean) is
                  such a test: from its sharedX_k14 | sharedX_end, under the plan's hlU, hlO (the
                  two sendings' layouts), hS, hm (the masks ahead; by run: true).
  hands_piece     a piece that holds, in the wrap, a block which decides as the i-th of the kind's
                  eight hands such a test on from i + 1 to i + 2.
  HandsAt, HandsOn.at   THE SAME, ASKED LESS: at the pieces, inside the promise: what share_filled
                  itself spends. The decide-form gives it. A test whose carriage wants the
                  book-keeping, or the rounds' own test that a piece's yes holds and a bare decision
                  does not ("the statement is in order" over a sending), is paid in this form.
  share_filled    **the one term at these fillings.** PAID AGAINST share_row: hsm · hX2 … hX11 ·
                  hkeep5.
  once_filled     **the call** at it.
NEW PREMISES: hX (HandsAt: whoever lays X; beside it X is owed at the chain's first record, at the
front, at "LIN point" and inside h9 | h10: LedgerRow.lean's head) · h2r … h8r (the block that a
piece holds has the kind's block's ROUNDS too: handed to hX's step; at b.retype: by rfl) · hoU (the
plan's: a member that sits at o_u's seat bears o_u's number).
WHAT STAYS WITH WEIGHT: hD2 | hD5 (paid in Johnson/Desc/K14/Law/LedgerSeamRow.lean) · h9 | h10; the
letters decT₂ · Mg₀ (the sample rows; dot) · Pm₀.shape 10 | 11 | 12 · oNo · the numbers and the
rounds' data: as in LedgerRow.lean's head.
What is not claimed. NO MEMBER IS SHOWN. By run (three rides: made-up
weights small; another build's example small and full): shapeK && layX && sharedX && codY &&
omY say yes at borders 2 … 9 of the real walk, each of the tests at all thirteen borders, 49
controls no. No soundness.

-/
import Johnson.Desc.K14.Law.LedgerPays
import Johnson.Desc.Sound.SharedX

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice Cb Johnson.Pack Desc.Plain
open Iop Run OnBytes.Maker OnBytes.Flat
open OnBytes.Means (Words)
open VerifiableInference.Desc (Block Strs Wit FileDescription Grows)
open VerifiableInference.Desc.ChainEnd (untestedL Exact)
open VerifiableInference.Desc.K1 (sendPiece seedMaps)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Shared
open Desc.K14.Law.Fence (sharedX sharedX_parts sharedX_k14 sharedX_end seatX_same membX)

/-- Over all records: what stands beside shapeK does not read z_fd. -/
theorem sharedX_zeta (Q : P14) (sentU : Array OracleNotice) (layU layO : TreeLay) (s : St)
    (z : List E) (h : sharedX Q sentU layU layO 7 s = true) :
    sharedX Q sentU layU layO 8 { s with loc := { s.loc with zFd := z } } = true := by
  obtain ⟨h1, h2, h3, h4⟩ := (sharedX_parts Q sentU layU layO 7 s).1 h
  refine (sharedX_parts Q sentU layU layO 8 _).2 ⟨bookX_zeta _ s z h1,
    seatX_same Q sentU layU layO 7 s _ rfl (Or.inr (Or.inr (by omega))) h2, ?_, h4⟩
  exact h3

/-- **A test beside shapeK that K14's own blocks hand on**, IN THE BLOCKS' OWN DECIDE-FORM: what
    whoever
lays X beside shapeK owes at our eight clauses: step: the i-th of the kind's eight (1 ≤ i: "LIN
    point"
is not ours) hands it on from i + 1 to i + 2 · zeta: it does not read z_fd · last: the end, which
leaves the record, hands it on. -/
structure HandsOn (bs : List (Block St Unit)) (X : ℕ → St → Bool) : Prop where
  step : ∀ i b, 1 ≤ i → bs[i]? = some b → ∀ d d' rs gs, b.decide d rs gs = .ok d' →
    X (i + 1) d = true → X (i + 2) d' = true
  zeta : ∀ (s : St) (z : List E), X 7 s = true →
    X 8 { s with loc := { s.loc with zFd := z } } = true
  last : ∀ s, X 11 s = true → X 12 s = true

/-- Two such tests, laid together. -/
theorem HandsOn.and {bs : List (Block St Unit)} {X Y : ℕ → St → Bool} (hX : HandsOn bs X)
    (hY : HandsOn bs Y) : HandsOn bs fun k s => X k s && Y k s :=
  ⟨fun i b hi hb d d' rs gs h hxy => by
      obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.1 hxy
      exact Bool.and_eq_true_iff.2 ⟨hX.step i b hi hb d d' rs gs h h1, hY.step i b hi hb d d' rs gs
          h h2⟩,
    fun s z hxy => by
      obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.1 hxy
      exact Bool.and_eq_true_iff.2 ⟨hX.zeta s z h1, hY.zeta s z h2⟩,
    fun s hxy => by
      obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.1 hxy
      exact Bool.and_eq_true_iff.2 ⟨hX.last s h1, hY.last s h2⟩⟩

/-- **sharedX is such a test.** -/
theorem handsOn_sharedX (Q : P14) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hbl : blocks Q = some [b1, b2, b3, b4, b5, b6, b7, b8]) (sentU : Array OracleNotice)
    (hU : withU Q.S = some sentU) (layU layO : TreeLay)
    (hlU : layTrees Q.codes sentU = some layU)
    (hlO : layTrees Q.codes (withOmega Q.S) = some layO)
    (hS : Q.S.sharedSplitNeeded = true) (hm : Q.par.S.masksAhead = true) :
    HandsOn [b1, b2, b3, b4, b5, b6, b7, b8] (sharedX Q sentU layU layO) :=
  ⟨fun i b _ hb d d' rs gs h hx =>
      sharedX_k14 Q b1 b2 b3 b4 b5 b6 b7 b8 hbl sentU hU layU layO hlU hlO hS hm i b hb d d' rs gs h
          hx,
    sharedX_zeta Q sentU layU layO, sharedX_end Q sentU layU layO⟩

variable {P₁ Cl Xi Cells Tok : Type} {Fr : Frame}

/-- **Such a test is handed on** by a piece that holds, in the wrap, a block which decides as the
    i-th
of the kind's eight. -/
theorem hands_piece (bs : List (Block St Unit)) (X : ℕ → St → Bool) (hX : HandsOn bs X) (i : ℕ)
    (hi : 1 ≤ i) (b : Block St Unit) (hb : bs[i]? = some b) (c : Block St Cl) (hc : DecidesAs c b)
    (x : Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT)) (hx : x.b = heldW c)
    (a : (P₁ × St) × Fr.E.Str) (τ : Iop.Tr (uLT (ckP .two) x.ds)) (y : (P₁ × St) × Fr.E.Str)
    (hout : x.ior.red.out a τ = some y) (h : X (i + 1) a.1.2 = true) : X (i + 2) y.1.2 = true := by
  obtain ⟨rs, gs, hd⟩ := held_yes x c hx a τ y hout
  rw [hc] at hd
  exact hX.step i b hi hb _ _ rs gs hd h

/-- **The same, asked less**: AT THE PIECES, INSIDE THE PROMISE: what share_filled itself spends. A
    test
whose carriage wants the book-keeping, or the rounds' own test that a piece's yes holds and a bare
decision does not (a statement in order over a sending), is paid here. -/
structure HandsAt (on : ℕ → (P₁ × St) × Fr.E.Str → Prop) (bs : List (Block St Unit))
    (X : ℕ → St → Bool) : Prop where
  step : ∀ i b, 1 ≤ i → bs[i]? = some b → ∀ c : Block St Cl, DecidesAs c b → c.rounds = b.rounds →
    ∀ x : Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT), x.b = heldW c → ∀ a τ y, on (i + 1)
        a →
      x.ior.red.out a τ = some y → X (i + 2) y.1.2 = true
  zeta : ∀ (s : St) (z : List E), X 7 s = true →
    X 8 { s with loc := { s.loc with zFd := z } } = true
  last : ∀ s, X 11 s = true → X 12 s = true

/-- The decide-form gives it, where the promise holds the test. -/
theorem HandsOn.at {bs : List (Block St Unit)} {X : ℕ → St → Bool} (hX : HandsOn bs X)
    (on : ℕ → (P₁ × St) × Fr.E.Str → Prop) (hon : ∀ k a, on k a → X k a.1.2 = true) :
    HandsAt (Cl := Cl) (Cells := Cells) (Tok := Tok) on bs X :=
  ⟨fun i b hi hb c hc _ x hx a τ y ha hout =>
      hands_piece bs X hX i hi b hb c hc x hx a τ y hout (hon _ a ha), hX.zeta, hX.last⟩

variable (cs : OnBytes.Codes) (G : FileDescription Xi) (arr : ℕ → ℕ → ℕ) (oNo : Mem → ℕ)
  (ms : List Mem) (decT₂ : (ℕ → Option (ℕ × List UInt64)) → St → Option Cells) (c₀ : Cells)
  (N : NumbersS) (Mg₀ : MeaningS St P₁ (Wit Cells Tok MsgT)) (Pm₀ : PromMeaning St)
  (Oc : P₁ → Strs → Prop)
  (mem : ℕ → Option Mem) (rd : (x : Mem) → ((sigOf cs x.1.l).om x.2).Msg → Part → ℕ → GE)
  (e' n nU nO : ℕ) (num : Msg2 → ℕ) (Q : P14) (sentU : Array OracleNotice) (X : ℕ → St → Bool)
  (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit) (c2 c3 c4 c5 c6 c7 c8 c11 : Block St Cl)
  (f pt x3 x6 x8 x9 x10 x11 : Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT))
  (base2 : ℕ) (d21 d22 : RDT)
  (ex2 : (P₁ × St) × Fr.E.Str → Iop.Tr (uLT (ckP .two) [d21, d22]) → Wit Cells Tok MsgT → Wit Cells
      Tok MsgT)
  (er2 : Err (uLT (ckP .two) [d21, d22]))
  (base4 : ℕ) (d4 : RDT) (ex4 : (P₁ × St) × Fr.E.Str → Iop.Tr (uLT (ckP .two) [d4]) → Wit Cells Tok
      MsgT → Wit Cells Tok MsgT)
  (er4 : Err (uLT (ckP .two) [d4]))
  (base5 : ℕ) (d51 d52 : RDT)
  (ex5 : (P₁ × St) × Fr.E.Str → Iop.Tr (uLT (ckP .two) [d51, d52]) → Wit Cells Tok MsgT → Wit Cells
      Tok MsgT)
  (er5 : Err (uLT (ckP .two) [d51, d52]))
  (base7 : ℕ) (d7 : RDT) (ex7 : (P₁ × St) × Fr.E.Str → Iop.Tr (uLT (ckP .two) [d7]) → Wit Cells Tok
      MsgT → Wit Cells Tok MsgT)
  (er7 : Err (uLT (ckP .two) [d7]))
  (ht : Tiled (pc2 c2 base2 d21 d22 ex2 er2) [x3, (pc1 c4 base4 d4 ex4 er4), (pc2 c5 base5 d51 d52
      ex5 er5), x6, (pc1 c7 base7 d7 ex7 er7), x8, x9, x10, x11])
  (hlo : ∀ m, N.lo ≤ (N.tenant m).1) (tU : (N.tenant .oU).1 < x3.base)
  (tO : (N.tenant .oOmega).1 < x6.base) (tS : (N.tenant .oSp).1 < x6.base)
  (hbl : blocks Q = some [b1, b2, b3, b4, b5, b6, b7, b8])
  (hS : Q.S.sharedSplitNeeded = true)
  (hdk : ∀ c (s s' : St), s'.loc.key = s.loc.key → decT₂ c s' = decT₂ c s)
  (hsr : SampleRides Mg₀ num) (hnum : num .oU = nU)
  (h2c : DecidesAs c2 b2) (h3c : DecidesAs c3 b3) (h4c : DecidesAs c4 b4) (h5c : DecidesAs c5 b5)
  (h6c : DecidesAs c6 b6) (h7c : DecidesAs c7 b7) (h8c : DecidesAs c8 b8) (h2r : c2.rounds =
      b2.rounds) (h3r : c3.rounds = b3.rounds) (h4r : c4.rounds = b4.rounds) (h5r : c5.rounds =
      b5.rounds) (h6r : c6.rounds = b6.rounds) (h8r : c8.rounds = b8.rounds)
  (hx3 : x3.b = heldW c3) (hx6 : x6.b = heldW c6) (hx8 : x8.b = heldW c8)
  (hx11 : x11.b = heldW c11) (he11 : Exact (fun d : St => untestedL d.st) c11)
  (xU xO : Mem) (hU : mem nU = some xU) (hO : mem nO = some xO) (mU : xU ∈ ms) (mO : xO ∈ ms)
  (sU : SitsAt xU (N.tenant .oU).1 (N.tenant .oU).2)
  (sO : SitsAt xO (N.tenant .oOmega).1 (N.tenant .oOmega).2)
  (hUw : withU Q.S = some sentU) (hn0 : nU = 0) (hnO : nO = nU + sentU.size)
  -- whoever lays X; the plan's letter oNo
  (hX : HandsAt (Cl := Cl) (Cells := Cells) (Tok := Tok) (onQ₂ N (pmK cs G (smpSt cs oNo stSh) ms
      decT₂ (shiftBook N.lo) Pm₀ n nU nO Q X) Oc true f (pt :: [(pc2 c2 base2 d21 d22 ex2 er2), x3,
      (pc1 c4 base4 d4 ex4 er4), (pc2 c5 base5 d51 d52 ex5 er5), x6, (pc1 c7 base7 d7 ex7 er7), x8,
      x9, x10, x11])) [b1, b2, b3, b4, b5, b6, b7, b8] X)
  (hoU : ∀ z ∈ ms, SitsAt z (N.tenant .oU).1 (N.tenant .oU).2 → oNo z = nU)
  -- "send o_u": but for ε2, at a yes the new message has its promise behind
  (ε2 : Err (uLT (ckP .two) [d21, d22]))
  (hD2 : ∀ a, onQ₂ N (pmK cs G (smpSt cs oNo stSh) ms decT₂ (shiftBook N.lo) Pm₀ n nU nO Q X) Oc
      true f (pt :: [(pc2 c2 base2 d21 d22 ex2 er2), x3, (pc1 c4 base4 d4 ex4
      er4), (pc2 c5 base5 d51 d52 ex5 er5), x6, (pc1 c7 base7 d7 ex7 er7), x8, x9, x10, x11]) 2 a →
      Doomed (uLT (ckP .two) [d21, d22]) ε2 fun τ =>
    ∀ y, (pc2 c2 base2 d21 d22 ex2 er2).ior.red.out a τ = some y →
      (PromS.noColl .oU).holds N (pm0 cs G (smpSt cs oNo stSh) ms decT₂ (shiftBook N.lo) Pm₀ n nU nO
          Q) y.1.2 (strsOfAct Fr ((actQ N f (pt :: [(pc2 c2 base2 d21 d22 ex2 er2), x3, (pc1 c4
          base4 d4 ex4 er4), (pc2 c5 base5 d51 d52 ex5 er5), x6, (pc1 c7 base7 d7 ex7 er7), x8, x9,
          x10, x11]) 3).2 y)))
  -- "LOC"
  {ns4 : ℕ} (hd4 : SendsDraws (toRD d4) ns4 0 n Q.par.S.fold.index.code.logN)
  (ho4 : d4.opens = []) (e4 : ℕ) (he4 : (2 ^ Q.par.S.fold.index.code.logN - e' - 1) ^ n ≤ e4)
  -- "send o_omega": the like for o_omega and o_sp
  (ε5 : Err (uLT (ckP .two) [d51, d52]))
  (hD5 : ∀ a, onQ₂ N (pmK cs G (smpSt cs oNo stSh) ms decT₂ (shiftBook N.lo) Pm₀ n nU nO Q X) Oc
      true f (pt :: [(pc2 c2 base2 d21 d22 ex2 er2), x3, (pc1 c4 base4 d4 ex4
      er4), (pc2 c5 base5 d51 d52 ex5 er5), x6, (pc1 c7 base7 d7 ex7 er7), x8, x9, x10, x11]) 5 a →
      Doomed (uLT (ckP .two) [d51, d52]) ε5 fun τ =>
    ∀ y, (pc2 c5 base5 d51 d52 ex5 er5).ior.red.out a τ = some y → ∀ m, m = Msg2.oOmega ∨ m = .oSp →
      (PromS.noColl m).holds N (pm0 cs G (smpSt cs oNo stSh) ms decT₂ (shiftBook N.lo) Pm₀ n nU nO
          Q) y.1.2 (strsOfAct Fr ((actQ N f (pt :: [(pc2 c2 base2 d21 d22 ex2 er2), x3, (pc1 c4
          base4 d4 ex4 er4), (pc2 c5 base5 d51 d52 ex5 er5), x6, (pc1 c7 base7 d7 ex7 er7), x8, x9,
          x10, x11]) 6).2 y)))
  -- "LIN zeta"
  {ns7 a7 : ℕ} (hd7 : SendsDraws (toRD d7) ns7 Q.par.S.kRow 0 a7) (e7 : ℕ)
  (he7 : Q.par.S.kRow * Fintype.card GE ^ (Q.par.S.kRow - 1) ≤ e7)
  (hS12 : ∀ s, Pm₀.shape 11 s = true → Pm₀.shape 12 s = true)
  (own : OwnErrs (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT))
  (ho2' : own 2 (pc2 c2 base2 d21 d22 ex2 er2) = ε2)
  (ho4' : own 4 (pc1 c4 base4 d4 ex4 er4) = (posMaps d4 Q.par.S.fold.index.code.logN n).err ((e4,
      ()) : ℕ × Unit))
  (ho5' : own 5 (pc2 c5 base5 d51 d52 ex5 er5) = ε5)
  (ho7' : own 7 (pc1 c7 base7 d7 ex7 er7) = (vecMaps d7 Q.par.S.kRow).err ((e7, ()) : ℕ × Unit))
  (h9 : ClauseAt N (mgK cs G arr (smpSt cs oNo stSh) ms decT₂ Mg₀ mem rd e' n nO Q) (pmK cs G (smpSt
      cs oNo stSh) ms decT₂ (shiftBook N.lo) Pm₀ n nU nO Q X) Oc true f
      (pt :: [(pc2 c2 base2 d21 d22 ex2 er2), x3, (pc1 c4 base4 d4 ex4 er4), (pc2 c5 base5 d51 d52
      ex5 er5), x6, (pc1 c7 base7 d7 ex7 er7), x8, x9, x10, x11]) (exK cs G arr (smpSt cs oNo stSh)
      ms decT₂ c₀ N Fr) 9 x9 (own 9 x9))
  (h10 : ClauseAt N (mgK cs G arr (smpSt cs oNo stSh) ms decT₂ Mg₀ mem rd e' n nO Q) (pmK cs G
      (smpSt cs oNo stSh) ms decT₂ (shiftBook N.lo) Pm₀ n nU nO Q X) Oc
      true f (pt :: [(pc2 c2 base2 d21 d22 ex2 er2), x3, (pc1 c4 base4 d4 ex4 er4), (pc2 c5 base5
      d51 d52 ex5 er5), x6, (pc1 c7 base7 d7 ex7 er7), x8, x9, x10, x11]) (exK cs G arr (smpSt cs
      oNo stSh) ms decT₂ c₀ N Fr) 10 x10 (own 10 x10))
include ht hlo tU tO tS hbl hS hdk hsr hnum h2c h3c h4c h5c h6c h7c h8c h2r h3r h4r h5r h6r h8r hx3
    hx6 hx8 hx11 he11 hU hO
    mU
  mO sU sO hUw hn0 hnO hX hoU hD2 hd4 ho4 he4 hD5 hd7 he7 hS12 ho2' ho4' ho5' ho7' h9 h10

/-- **THE ONE TERM, at smpSt and at ANY test X beside shapeK that the kind's blocks hand on.** -/
theorem share_filled : EachPlainShOwn N (mgK cs G arr (smpSt cs oNo stSh) ms decT₂ Mg₀ mem rd e' n
    nO Q) (pmK cs G (smpSt cs oNo stSh) ms decT₂ (shiftBook N.lo) Pm₀ n nU nO Q X) Oc true f (pt ::
        [(pc2 c2 base2 d21 d22 ex2 er2), x3, (pc1 c4 base4 d4 ex4 er4),
    (pc2 c5 base5 d51 d52 ex5 er5), x6, (pc1 c7 base7 d7 ex7 er7), x8, x9, x10, x11]) (exK cs G arr
    (smpSt cs oNo stSh) ms decT₂ c₀ N Fr) own 2 [(pc2 c2 base2 d21 d22 ex2 er2), x3, (pc1 c4 base4
    d4 ex4 er4), (pc2 c5 base5 d51 d52 ex5 er5), x6, (pc1 c7 base7 d7 ex7 er7), x8, x9, x10, x11] :=
    by
  have xs : ∀ (k : ℕ) a, onQ₂ N (pmK cs G (smpSt cs oNo stSh) ms decT₂ (shiftBook N.lo) Pm₀ n nU nO
      Q X) Oc true f (pt :: [(pc2 c2 base2 d21 d22 ex2 er2), x3, (pc1 c4
      base4 d4 ex4 er4), (pc2 c5 base5 d51 d52 ex5 er5), x6, (pc1 c7 base7 d7 ex7 er7), x8, x9, x10,
      x11]) k a → X k a.1.2 = true := fun k a ha =>
    (Bool.and_eq_true_iff.1 (x_of_on cs G (smpSt cs oNo stSh) ms decT₂ (shiftBook N.lo) N Pm₀ Oc n
        nU nO f (pt :: [(pc2 c2 base2 d21 d22 ex2 er2), x3, (pc1 c4 base4 d4 ex4 er4), (pc2 c5 base5
        d51 d52 ex5 er5), x6, (pc1 c7 base7 d7 ex7 er7), x8, x9, x10, x11]) Q (besX Q X) k a ha)).2
  exact share_row cs G arr (smpSt cs oNo stSh) ms decT₂ c₀ (shiftBook N.lo) N Mg₀ Pm₀ Oc mem rd e' n
      nU nO num Q X b1 b2 b3 b4 b5 b6 b7 b8 c2 c3 c4 c5 c6 c7 c8 c11 f pt
      x3 x6 x8 x9 x10 x11 base2 d21 d22 ex2 er2 base4 d4 ex4 er4 base5 d51 d52 ex5 er5 base7 d7 ex7
      er7 ht hlo tU tO tS hbl hS (smpReads_smpSt cs oNo) hdk hsr hnum h2c h3c h4c h5c h6c h7c h8c
          hx3 hx6 hx8 hx11 he11 xU xO hU hO mU mO sU sO sentU hUw hn0 hnO
    (fun a τ y ha hout => hX.step 1 _ (by omega) rfl c2 h2c h2r (pc2 c2 base2 d21 d22 ex2
        er2) rfl a τ y ha hout)
    (fun a τ y ha hout => hX.step 2 _ (by omega) rfl c3 h3c h3r x3 hx3 a τ y ha hout)
    (fun a τ y ha hout => hX.step 3 _ (by omega) rfl c4 h4c h4r (pc1 c4 base4 d4 ex4 er4) rfl
        a τ y ha hout)
    (fun a τ y ha hout => hX.step 4 _ (by omega) rfl c5 h5c h5r (pc2 c5 base5 d51 d52 ex5
        er5) rfl a τ y ha hout)
    (fun a τ y ha hout => hX.step 5 _ (by omega) rfl c6 h6c h6r x6 hx6 a τ y ha hout)
    hX.zeta
    (fun a τ y ha hout => hX.step 7 _ (by omega) rfl c8 h8c h8r x8 hx8 a τ y ha hout)
    hX.last
    ε2 hD2 hd4 ho4 e4 he4 ε5 hD5 (keep5_paid cs G ms decT₂ (shiftBook N.lo) N Pm₀ Oc n nU nO f (pt
        :: [(pc2 c2 base2
        d21 d22 ex2 er2), x3, (pc1 c4
        base4 d4 ex4 er4), (pc2 c5 base5 d51 d52 ex5 er5), x6, (pc1 c7 base7 d7 ex7 er7), x8, x9,
        x10, x11]) Q (besX Q X) b1 b2 b3 b4 b5 b6 b7 b8 hbl oNo hoU c5 h5c
            base5 d51 d52 ex5 er5) hd7 e7 he7 hS12 own ho2' ho4' ho5' ho7' h9 h10

/-- **THE CALL, at these fillings: charged once.** -/
theorem once_filled (slots : ℕ) (hh : EachHands (actQ N f (pt :: [(pc2 c2 base2 d21 d22 ex2 er2),
    x3, (pc1 c4 base4 d4 ex4 er4), (pc2 c5 base5 d51 d52 ex5 er5), x6, (pc1 c7 base7 d7 ex7 er7),
    x8, x9, x10, x11])) 2 [(pc2 c2 base2 d21 d22 ex2 er2), x3, (pc1 c4 base4 d4 ex4 er4), (pc2 c5
    base5 d51 d52 ex5 er5), x6, (pc1 c7 base7 d7 ex7 er7), x8, x9, x10, x11])
    (hr : EachRides N (mgK cs G arr (smpSt cs oNo stSh) ms decT₂ Mg₀ mem rd e' n nO Q) (pmK cs G
        (smpSt cs oNo stSh) ms decT₂ (shiftBook N.lo) Pm₀ n nU nO Q X) Oc
        true f (pt :: [(pc2 c2 base2 d21 d22 ex2 er2), x3, (pc1 c4 base4 d4 ex4 er4), (pc2 c5 base5
        d51 d52 ex5 er5), x6, (pc1 c7 base7 d7 ex7 er7), x8, x9, x10, x11]) (exK cs G arr (smpSt cs
        oNo stSh) ms decT₂ c₀ N Fr) 2 [(pc2 c2 base2 d21 d22 ex2 er2), x3, (pc1 c4 base4 d4 ex4
        er4), (pc2 c5 base5 d51 d52 ex5 er5), x6, (pc1 c7 base7 d7 ex7 er7), x8, x9, x10, x11]) :
    EachLawsBNOwn (keyE N f (pt :: [(pc2 c2 base2 d21 d22 ex2 er2), x3, (pc1 c4 base4 d4 ex4 er4),
        (pc2 c5 base5 d51 d52 ex5 er5), x6, (pc1 c7 base7 d7 ex7 er7), x8, x9, x10, x11])) (onQ₂ N
        (pmK cs G (smpSt cs oNo stSh) ms decT₂ (shiftBook N.lo) Pm₀ n nU nO Q X) Oc true f (pt ::
            [(pc2 c2 base2 d21 d22 ex2 er2), x3, (pc1 c4 base4 d4 ex4 er4), (pc2
        c5 base5 d51 d52 ex5 er5), x6, (pc1 c7 base7 d7 ex7 er7), x8, x9, x10, x11]))
      (stepE N (mgK cs G arr (smpSt cs oNo stSh) ms decT₂ Mg₀ mem rd e' n nO Q) (pmK cs G (smpSt cs
          oNo stSh) ms decT₂ (shiftBook N.lo) Pm₀ n nU nO Q X) Oc true f
          (pt :: [(pc2 c2 base2 d21 d22 ex2 er2), x3, (pc1 c4 base4 d4 ex4 er4), (pc2 c5 base5 d51
          d52 ex5 er5), x6, (pc1 c7 base7 d7 ex7 er7), x8, x9, x10, x11]) fun k a _ w => (exK cs G
          arr (smpSt cs oNo stSh) ms decT₂ c₀ N Fr) k ((actQ N f (pt :: [(pc2 c2 base2 d21 d22 ex2
          er2), x3, (pc1 c4 base4 d4 ex4 er4), (pc2 c5 base5 d51 d52 ex5 er5), x6, (pc1 c7 base7 d7
          ex7 er7), x8, x9, x10, x11]) k).2 a) w) slots own 2 [(pc2 c2 base2 d21 d22 ex2 er2), x3,
          (pc1 c4 base4 d4 ex4 er4), (pc2 c5 base5 d51 d52 ex5 er5), x6, (pc1 c7 base7 d7 ex7 er7),
          x8, x9, x10, x11] :=
  eachLawsBNOwn_plain N (mgK cs G arr (smpSt cs oNo stSh) ms decT₂ Mg₀ mem rd e' n nO Q) (pmK cs G
      (smpSt cs oNo stSh) ms decT₂ (shiftBook N.lo) Pm₀ n nU nO Q X) Oc
      true f (pt :: [(pc2 c2 base2 d21 d22 ex2 er2), x3, (pc1 c4 base4 d4 ex4 er4), (pc2 c5 base5
      d51 d52 ex5 er5), x6, (pc1 c7 base7 d7 ex7 er7), x8, x9, x10, x11]) (exK cs G arr (smpSt cs
      oNo stSh) ms decT₂ c₀ N Fr) slots own [(pc2 c2 base2 d21 d22 ex2 er2), x3, (pc1 c4 base4 d4
      ex4 er4), (pc2 c5 base5 d51 d52 ex5 er5), x6, (pc1 c7 base7 d7 ex7 er7), x8, x9, x10, x11] 2
      (Nat.le_refl 2) hh
    (share_filled cs G arr oNo ms decT₂ c₀ N Mg₀ Pm₀ Oc mem rd e' n nU nO num Q sentU X b1 b2 b3 b4
        b5 b6 b7 b8 c2 c3 c4 c5 c6 c7 c8 c11 f pt x3 x6 x8 x9 x10 x11 base2 d21 d22 ex2 er2
        base4 d4 ex4 er4 base5 d51 d52 ex5 er5 base7 d7 ex7 er7 ht hlo tU tO tS hbl hS hdk hsr hnum
        h2c h3c h4c h5c h6c h7c h8c h2r h3r h4r h5r h6r h8r hx3 hx6 hx8 hx11 he11 xU xO hU hO mU mO
            sU sO hUw hn0 hnO hX hoU
            ε2 hD2 hd4 ho4 e4 he4 ε5 hD5 hd7 e7 he7 hS12 own ho2' ho4' ho5' ho7' h9
        h10) hr

end Desc.K14.Law

#print axioms Desc.K14.Law.sharedX_zeta
#print axioms Desc.K14.Law.HandsOn.and
#print axioms Desc.K14.Law.handsOn_sharedX
#print axioms Desc.K14.Law.hands_piece
#print axioms Desc.K14.Law.HandsOn.at
#print axioms Desc.K14.Law.share_filled
#print axioms Desc.K14.Law.once_filled
