-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Second/K08/BlocksInOfLayout.lean: THE APPROXIMATE RANGE PROOF (KIND K8): EVERY BLOCK OF AN
    ARRAY OF A LAWFUL LAYOUT LIES INSIDE THE ORACLE MESSAGE THAT FIRST HELD THE ARRAY: the three
    fields of BlockInMsg (Johnson/Desc/First/K8/LawBlockIn.lean: ok · rows ·
    places), WRITTEN OUT, as a law from the programs' own test on a layout (reqLayoutOk,
    OnBytes/Iop/ReqRows.lean). The field «rows» (b.firstRow + 2 ^
    b.rowBits ≤ s.mainRows) had no payer and no evaluated test. Statements and proofs. Nothing is
    evaluated here.


WHAT IS CALLED, NOT TYPED HERE: matrixOk_of_layoutOk (Johnson/Desc/First/Att/K05LayoutOk.lean: kind
    K5's files: it draws the clause «no block is in rows that are not sent» out of
    reqMessageLayoutOk) · pub_start (Johnson/IMR/RecRun.lean) and pub_layoutOk
    (Johnson/IMR/LayoutOkPub.lean):
    where the plain road's public part is
    made, the layout has passed that test.
  aligned_fits            a % 2 ^ k = 0 · a < 2 ^ P · k ≤ P ⊢ a + 2 ^ k ≤ 2 ^ P.
  ell_of_lengthsOk        under Codes.lengthsOk a code's message length is 2 ^ its logEll.
  blocksIn_of_layoutOk  codes.lengthsOk · reqLayoutOk codes s layout · reqArray layout born name =
      some a ⊢ link born of the shape has the message number a.message; it has main rows; and at
      every block of a: laidBlockOk at that message's two numbers of bits · its rows end at or below
      the message's main rows · its places end at or below the main code's length.
  blocksIn_at_statement the same at a statement S, its o-th oracle message x and the statement's
      own numbers of bits (S.rowBits o .main · S.placeBits o .main: the letters in which CellsIn
      asks BlockInMsg), WHERE x HAS THE SHAPE OF THE MESSAGE THAT FIRST HELD THE ARRAY (the premise
      hsh).
  pub_lengthsOk           where the plain road's public part is made: Codes.lengthsOk at its codes
      (the first clause of S.startOk).
  blocksIn_at_pub       so, where the plain road's public part Z is made, at every function in the
      second hash function's place: blocksIn_of_layoutOk's end at Z.first.codes, Z.first.shape,
      Z.first.layout, with no other premise than «the layout has the array».
Limits. TOOLS: no reached state of a verifier stands in any statement here. hsh is a premise: that a
    reached state's statement has, under the number that the open link's context gives
    (Named.msgNow), a message of the first holder's shape is shown nowhere here; for an array born
    at an earlier link that message is the copy sent anew at the last switch. That the statement has
    a message under that number at all (hx), that its codes and the open link's layout are
    Z.first's, and that a member's shape is that message's, is not shown here: so K8's files'
    clause on CellsIn stays open. BlockInMsg itself is not imported:
    a term of it is ⟨ok, rows, places⟩ from
    the three conjuncts. Whether pub returns at any files is an evaluation's to show
    (ScopeMembers.lean · BlocksInAt.lean: not in this library). No soundness is claimed.

-/
import Johnson.Desc.First.Att.K05LayoutOk
import Johnson.IMR.LayoutOkPub
import Johnson.Pack.Port

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Second.K08
open OnBytes OnBytes.Model OnBytes.Params
open Johnson.Pack (pMain)
open VerifiableInference.Desc.First.Att.P (matrixOk_of_layoutOk)

theorem aligned_fits {a k P : ℕ} (h0 : a % 2 ^ k = 0) (hlt : a < 2 ^ P) (hk : k ≤ P) :
    a + 2 ^ k ≤ 2 ^ P := by
  obtain ⟨q, rfl⟩ := Nat.dvd_of_mod_eq_zero h0
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [pow_add] at hlt ⊢
  have hq : q < 2 ^ d := Nat.lt_of_mul_lt_mul_left hlt
  calc 2 ^ k * q + 2 ^ k = 2 ^ k * (q + 1) := by ring
    _ ≤ 2 ^ k * 2 ^ d := Nat.mul_le_mul_left _ hq

theorem ell_of_lengthsOk {codes : Codes} (hlen : codes.lengthsOk = true) {c : Code}
    (hc : c ∈ codes.base) : c.ell = 2 ^ c.logEll := by
  show c.ell = 2 ^ ceilLog2 c.ell
  unfold Codes.lengthsOk at hlen
  obtain ⟨hb1, _⟩ := Eq.mp (Bool.and_eq_true _ _) hlen
  have hp2 := Array.all_eq_true_iff_forall_mem.1 hb1 c hc
  unfold powerOfTwo at hp2
  obtain ⟨_, hp3⟩ := Eq.mp (Bool.and_eq_true _ _) hp2
  exact (by simpa using hp3 : 2 ^ ceilLog2 c.ell = c.ell).symm

/-- What laidBlockOk says of a block's places. -/
theorem places_of_blockOk {b : LaidBlock} {R P : ℕ} (h : laidBlockOk b R P = true) :
    b.firstPlace + 2 ^ b.placeBits ≤ 2 ^ P := by
  unfold laidBlockOk laidAligned at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨_, _⟩, hP⟩, _⟩, _⟩, _⟩, ⟨_, h0⟩⟩, _⟩, hlt⟩ := h
  exact aligned_fits h0 hlt hP


theorem blocksIn_of_layoutOk (codes : Codes) (s : ReqShape) (layout : ReqLayout)
    (hlen : codes.lengthsOk = true) (h : reqLayoutOk codes s layout = true) (born : ℕ)
    (name : String) (a : ReqArray) (ha : OnBytes.reqArray layout born name = some a) :
    ∃ (L : ReqLink) (msg : ReqMessage), s.link[born]? = some L ∧
      L.messages[a.message]? = some msg ∧ msg.shape.mainRows ≠ 0 ∧
      ∀ b ∈ a.blocks,
        laidBlockOk b (ceilLog2 msg.shape.mainRows) (pMain codes msg.shape).logEll = true ∧
          b.firstRow + 2 ^ b.rowBits ≤ msg.shape.mainRows ∧
          b.firstPlace + 2 ^ b.placeBits ≤ (pMain codes msg.shape).ell := by
  obtain ⟨L, msg, c, hL, hm, hc, h0, hmx, hrow⟩ :=
    matrixOk_of_layoutOk codes s layout h born name a ha
  have hp : pMain codes msg.shape = c := by
    unfold pMain
    rw [Array.getD_eq_getD_getElem?, hc]
    rfl
  refine ⟨L, msg, hL, hm, h0, fun b hb => ?_⟩
  rw [hp]
  have hok : laidBlockOk b (ceilLog2 msg.shape.mainRows) c.logEll = true := by
    unfold laidMatrixOk at hmx
    obtain ⟨h12, _⟩ := Eq.mp (Bool.and_eq_true _ _) hmx
    obtain ⟨hall, _⟩ := Eq.mp (Bool.and_eq_true _ _) h12
    have g1 := List.all_eq_true.1 hall b hb
    obtain ⟨g2, _⟩ := Eq.mp (Bool.and_eq_true _ _) g1
    obtain ⟨g3, _⟩ := Eq.mp (Bool.and_eq_true _ _) g2
    exact g3
  refine ⟨hok, hrow b hb, ?_⟩
  rw [ell_of_lengthsOk hlen (Array.mem_of_getElem? hc)]
  exact places_of_blockOk hok


theorem blocksIn_at_statement (St : Statement) (s : ReqShape) (layout : ReqLayout)
    (hlen : St.codes.lengthsOk = true) (h : reqLayoutOk St.codes s layout = true) (born : ℕ)
    (name : String) (a : ReqArray) (ha : OnBytes.reqArray layout born name = some a) (o : ℕ)
    (x : Oracle) (hx : St.oracles[o]? = some x)
    (hsh : ∀ (L : ReqLink) (msg : ReqMessage), s.link[born]? = some L →
      L.messages[a.message]? = some msg → x.shape = msg.shape) :
    ∀ b ∈ a.blocks,
      laidBlockOk b (St.rowBits o .main) (St.placeBits o .main) = true ∧
        b.firstRow + 2 ^ b.rowBits ≤ x.shape.mainRows ∧
        b.firstPlace + 2 ^ b.placeBits ≤ (pMain St.codes x.shape).ell := by
  obtain ⟨L, msg, hL, hm, h0, hall⟩ :=
    blocksIn_of_layoutOk St.codes s layout hlen h born name a ha
  have e := hsh L msg hL hm
  have hR : St.rowBits o .main = ceilLog2 msg.shape.mainRows := by
    unfold Statement.rowBits
    rw [hx]
    show ceilLog2 (x.shape.rows .main) = ceilLog2 msg.shape.mainRows
    rw [e]
    rfl
  have hP : St.placeBits o .main = (pMain St.codes msg.shape).logEll := by
    have hne : ¬ ((msg.shape.rows .main == 0) = true) := by
      show ¬ ((msg.shape.mainRows == 0) = true)
      simpa using h0
    unfold Statement.placeBits
    rw [hx]
    show (if (x.shape.rows .main == 0) = true then 0
      else (St.codes.base.getD x.shape.code default).logEll) = (pMain St.codes msg.shape).logEll
    rw [e, if_neg hne]
    rfl
  intro b hb
  rw [hR, hP, e]
  exact hall b hb

theorem pub_lengthsOk {o : ProofFile.SecondHashFunctionArgument} {pol ly KL : ByteArray} {Z : ProofFile.Pub}
    (h : ProofFile.pureRoad.pub o pol ly KL = .ok Z) : Z.first.codes.lengthsOk = true := by
  have hs := Meaning.K2.pub_start h
  unfold VerifiableInference.Desc.First.S.startP at hs
  split at hs
  · rename_i hk
    unfold VerifiableInference.Desc.First.S.startOk at hk
    simp only [Bool.and_eq_true] at hk
    exact hk.1
  · cases hs


theorem blocksIn_at_pub {o : ProofFile.SecondHashFunctionArgument} {pol ly KL : ByteArray} {Z : ProofFile.Pub}
    (h : ProofFile.pureRoad.pub o pol ly KL = .ok Z) (born : ℕ) (name : String) (a : ReqArray)
    (ha : OnBytes.reqArray Z.first.layout born name = some a) :
    ∃ (L : ReqLink) (msg : ReqMessage), Z.first.shape.link[born]? = some L ∧
      L.messages[a.message]? = some msg ∧ msg.shape.mainRows ≠ 0 ∧
      ∀ b ∈ a.blocks,
        laidBlockOk b (ceilLog2 msg.shape.mainRows) (pMain Z.first.codes msg.shape).logEll = true ∧
          b.firstRow + 2 ^ b.rowBits ≤ msg.shape.mainRows ∧
          b.firstPlace + 2 ^ b.placeBits ≤ (pMain Z.first.codes msg.shape).ell :=
  blocksIn_of_layoutOk _ _ _ (pub_lengthsOk h) (Meaning.K2.pub_layoutOk h) born name a ha

end Second.K08

#print axioms Second.K08.blocksIn_of_layoutOk
#print axioms Second.K08.blocksIn_at_statement
#print axioms Second.K08.pub_lengthsOk
#print axioms Second.K08.blocksIn_at_pub
