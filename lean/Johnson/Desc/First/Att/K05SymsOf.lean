-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/K05SymsOf.lean: kind K5: SymsOK (Johnson/Desc/First/Att/K05AddrTieOf.lean:
what the tie spends of the guards of the caller's reading) FROM TESTS WITH CODE ON PUBLIC DATA THAT
ARE CHEAP AT EVERY SIZE: none of them walks over the symbols.

Why. "Every symbol address inside the sizes has a seat that lies in its table" runs over every
symbol of every matrix: at the full size no run can try them one by one. The programs' own test on a
layout (reqLayoutOk, OnBytes/Iop/ReqRows.lean) says that each array's blocks tile it and lie in rows
that are sent: so one test an ARRAY is enough.

IS IT EMPTY HERE? NO MEMBER IS SHOWN: no test is evaluated here.

Main names:
  `symArrayB D i tl μ`: a Bool, at matrix number μ of the list: link i's list of arrays names its
    symbol array; the layout has it; it has at least the matrix's rows of symbols and its columns;
    the member that holds it (msgOfArray, Johnson/Desc/First/Att/K05ReadMsgs.lean) is in the
    caller's list.
  `symArraysB D x tl`: that at every matrix of the list.
  `seatCalls_of`: seatCalls' answer, from its four parts.
  `symsOK_of_layout`: **SymsOK x tl D rad**, from: Codes.lengthsOk D.codes · reqLayoutOk D.codes
    D.shape D.layout · symArraysB D x tl: THREE BOOLS. Spent: kept_same
    (Johnson/Desc/First/Att/K05KeptSame.lean: the field keptSame is a law of the programs'
    reqGroupAt: no test); laid_no_hole, laidIn_row_in, laidIn_place_lt
    (Johnson/Desc/First/Att/K05NoHole.lean); matrixOk_of_layoutOk and seat_shape's argument
    (Johnson/Desc/First/Att/K05LayoutOk.lean).
Limits. The first two Bools are tested where the chain starts (Johnson/Desc/First/State.lean), at
its own letters; that these are D's is not joined.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.K05LayoutOk
import Johnson.Desc.First.Att.K05NoHole
import Johnson.Desc.First.Att.K05ReadMsgs
import Johnson.Desc.First.Att.K05KeptSame

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.Att.P
open OnBytes OnBytes.Model OnBytes.Params
open OnBytes.Road.Rows (Addr)
open VerifiableInference.Desc.K9L (blockFacts)
open VerifiableInference.Desc.First.Look (Sent sigListCalls seatCalls keptAt bornAt messagesAt szOf
  laidPlace)

/-- One test an array. -/
def symArrayB (D : Sent) (i : ℕ) (tl : HTailF2) (μ : ℕ) : Bool :=
  match (D.arrayOf.getD i #[])[tl.gtTree.getD μ 0]? with
  | none => false
  | some bn =>
    match OnBytes.reqArray D.layout bn.1 bn.2 with
    | none => false
    | some a =>
      Decidable.decide (_root_.Alg.symRows (tl.mats.getD μ {}).m ≤ a.sizeI) &&
        Decidable.decide ((tl.mats.getD μ {}).k ≤ a.sizeC) &&
        (msgOfArray D i (tl.gtTree.getD μ 0)).any fun k =>
          Decidable.decide (k < (shapesCalls D i).length)

/-- That at every matrix of the list. -/
def symArraysB (D : Sent) (x : VerifiableInference.Desc.First.Look.Place) (tl : HTailF2) : Bool :=
  (List.range tl.NM).all fun μ => symArrayB D x.link tl μ

/-- seatCalls' answer, from its four parts. -/
theorem seatCalls_of {D : Sent} {i t r c k : ℕ} {bn : ℕ × String} {a : ReqArray} {rp : ℕ × ℕ}
    (hbn : (D.arrayOf.getD i #[])[t]? = some bn)
    (ha : OnBytes.reqArray D.layout bn.1 bn.2 = some a) (hp : laidPlace a.blocks r c = some rp)
    (hm : msgOfArray D i t = some k) :
    seatCalls D i (.cell t r c) = some ⟨k, false, rp.1, rp.2⟩ := by
  unfold msgOfArray at hm
  rw [hbn] at hm
  have hm2 : ((OnBytes.reqArray D.layout bn.1 bn.2).bind fun a =>
      if bn.1 == i then some ((keptAt D i).length + a.message)
      else (bornAt D i).idxOf? (bn.1, a.message)) = some k := hm
  rw [ha] at hm2
  have hm3 : (if bn.1 == i then some ((keptAt D i).length + a.message)
      else (bornAt D i).idxOf? (bn.1, a.message)) = some k := hm2
  show ((D.arrayOf.getD i #[])[t]?.bind fun bn =>
      (OnBytes.reqArray D.layout bn.1 bn.2).bind fun a =>
        (laidPlace a.blocks r c).bind fun rp =>
          if bn.1 == i then
            some (⟨(keptAt D i).length + a.message, false, rp.1, rp.2⟩ :
              VerifiableInference.Desc.First.Look.Seat)
          else ((bornAt D i).idxOf? (bn.1, a.message)).map fun k => ⟨k, false, rp.1, rp.2⟩) = _
  rw [hbn]
  show ((OnBytes.reqArray D.layout bn.1 bn.2).bind fun a =>
        (laidPlace a.blocks r c).bind fun rp =>
          if bn.1 == i then
            some (⟨(keptAt D i).length + a.message, false, rp.1, rp.2⟩ :
              VerifiableInference.Desc.First.Look.Seat)
          else ((bornAt D i).idxOf? (bn.1, a.message)).map fun k => ⟨k, false, rp.1, rp.2⟩) = _
  rw [ha]
  show ((laidPlace a.blocks r c).bind fun rp =>
          if bn.1 == i then
            some (⟨(keptAt D i).length + a.message, false, rp.1, rp.2⟩ :
              VerifiableInference.Desc.First.Look.Seat)
          else ((bornAt D i).idxOf? (bn.1, a.message)).map fun k => ⟨k, false, rp.1, rp.2⟩) = _
  rw [hp]
  show (if bn.1 == i then
            some (⟨(keptAt D i).length + a.message, false, rp.1, rp.2⟩ :
              VerifiableInference.Desc.First.Look.Seat)
          else ((bornAt D i).idxOf? (bn.1, a.message)).map fun k => ⟨k, false, rp.1, rp.2⟩) = _
  by_cases hb : (bn.1 == i) = true
  · rw [if_pos hb] at hm3 ⊢
    obtain rfl := Option.some.inj hm3
    rfl
  · rw [if_neg hb] at hm3 ⊢
    rw [hm3]
    rfl

/-- **SymsOK from four Bools, none of which walks over the symbols.** -/
theorem symsOK_of_layout {x : VerifiableInference.Desc.First.Look.Place} {tl : HTailF2} {D : Sent}
    {rad : OracleShape → Nat} (hlen : D.codes.lengthsOk = true)
    (hlo : reqLayoutOk D.codes D.shape D.layout = true) (hsa : symArraysB D x tl = true) :
    SymsOK x tl D rad := by
  refine ⟨kept_same D x.link, fun μ i' c => ?_⟩
  have h1 := List.all_eq_true.1 hsa μ.val (List.mem_range.2 μ.2)
  unfold symArrayB at h1
  cases hbn : (D.arrayOf.getD x.link #[])[tl.gtTree.getD μ.val 0]? with
  | none =>
    rw [hbn] at h1
    cases h1
  | some bn =>
    rw [hbn] at h1
    simp only at h1
    cases ha : OnBytes.reqArray D.layout bn.1 bn.2 with
    | none =>
      rw [ha] at h1
      cases h1
    | some a =>
      rw [ha] at h1
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h1
      obtain ⟨⟨hI, hC⟩, hmm⟩ := h1
      cases hm : msgOfArray D x.link (tl.gtTree.getD μ.val 0) with
      | none =>
        rw [hm] at hmm
        cases hmm
      | some k =>
        rw [hm] at hmm
        have hk : k < (sigListCalls D rad x.link).length := by
          have h2 : k < (shapesCalls D x.link).length := by simpa using hmm
          rw [← shapes_any D rad x.link, List.length_map] at h2
          exact h2
        obtain ⟨Lk, msg, c0, hlk, hmsg, hcode, _, hmx, hrow⟩ :=
          matrixOk_of_layoutOk D.codes D.shape D.layout hlo bn.1 bn.2 a ha
        obtain ⟨rp, hp⟩ := laid_no_hole a _ _ hmx (Nat.lt_of_lt_of_le i'.2 hI)
          (Nat.lt_of_lt_of_le c.2 hC)
        have hz := seatCalls_of hbn ha hp hm
        refine ⟨_, hz, hk, ?_⟩
        obtain ⟨b, hb, hh, rfl⟩ := laidPlace_block hp
        have hF : VerifiableInference.Desc.K9L.BlockFacts b (ceilLog2 msg.shape.mainRows) c0.logEll := by
          unfold laidMatrixOk at hmx
          obtain ⟨h12, _⟩ := Eq.mp (Bool.and_eq_true _ _) hmx
          obtain ⟨hall, _⟩ := Eq.mp (Bool.and_eq_true _ _) h12
          have g1 := List.all_eq_true.1 hall b hb
          obtain ⟨g2, _⟩ := Eq.mp (Bool.and_eq_true _ _) g1
          obtain ⟨g3, _⟩ := Eq.mp (Bool.and_eq_true _ _) g2
          exact blockFacts b _ _ g3
        -- the member's shape is the first holder's
        obtain ⟨bn1, a1, msg1, hbn1, ha1, hmsg1, hsh⟩ :=
          seat_shape_of (kept_same D x.link) (rad := rad) hz hk
        obtain rfl : bn1 = bn := Option.some.inj (hbn1.symm.trans hbn)
        obtain rfl : a1 = a := Option.some.inj (ha1.symm.trans ha)
        rw [messagesAt_of hlk] at hmsg1
        obtain rfl : msg1 = msg := Option.some.inj (hmsg1.symm.trans hmsg)
        rw [if_neg (by simp)]
        show (VerifiableInference.Desc.First.Look.laidIn b i'.val c.val).1 <
            ((sigListCalls D rad x.link).get ⟨k, hk⟩).1.mainRows ∧
          (VerifiableInference.Desc.First.Look.laidIn b i'.val c.val).2 <
            (Johnson.Pack.pMain D.codes ((sigListCalls D rad x.link).get ⟨k, hk⟩).1).ell
        have hsh' : ((sigListCalls D rad x.link).get ⟨k, hk⟩).1 = msg1.shape := hsh
        rw [hsh']
        refine ⟨Nat.lt_of_lt_of_le (laidIn_row_in b _ _ hF _ _ hh) (hrow b hb), ?_⟩
        have hell : (Johnson.Pack.pMain D.codes msg1.shape).ell = 2 ^ c0.logEll := by
          unfold Johnson.Pack.pMain
          rw [Array.getD_eq_getD_getElem?, hcode]
          show c0.ell = 2 ^ ceilLog2 c0.ell
          unfold Codes.lengthsOk at hlen
          obtain ⟨hb1, _⟩ := Eq.mp (Bool.and_eq_true _ _) hlen
          have hmem : c0 ∈ D.codes.base := Array.mem_of_getElem? hcode
          have hp2 := Array.all_eq_true_iff_forall_mem.1 hb1 c0 hmem
          unfold powerOfTwo at hp2
          obtain ⟨_, hp3⟩ := Eq.mp (Bool.and_eq_true _ _) hp2
          exact (by simpa using hp3 : 2 ^ ceilLog2 c0.ell = c0.ell).symm
        rw [hell]
        exact laidIn_place_lt b _ _ hF _ _

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.seatCalls_of
#print axioms VerifiableInference.Desc.First.Att.P.symsOK_of_layout
