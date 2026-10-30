-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K13/CoinsTieOfK1.lean: kind K13, the members' batching:
`coinsTie_of_facts` (CoinsTieOfFacts.lean of this folder) WHERE THE SENDER OF THE INDEX MASKS'
MESSAGE IS A SENDING OF KIND K1's (Honest/K1/Coins.lean): UNDER THE SAME FACTS ON THE STATE, THE
PUBLIC TEST `sendFits`, AND WHERE THE SENDER's TEXT AT ROW ν % R, PLACE ν / R (R: the shape's number
of mask rows) ANSWERS THE PART's OWN VALUE NUMBER maskStart + ν (the premises are not shown; no
example is known at which all hold and the thread stands somewhere): THE KIND's TIE `CoinsTie`. Of
that lemma's eight named premises two fall: `SenderLaysOwn` holds by unfolding at the row laid here,
and "inside the count" is K1's `mask_in`. Two statements with their proofs; no definition.

Main names: `val_coinsE_getD`: a part's value by number, as the program's element, reads as the
value (`ce`); beyond the count both are 0. `coinsTie_of_k1`: **the tie.**

THE PREMISES OF `coinsTie_of_k1`. As in `coinsTie_of_facts`, at d := dueR P ride and base :=
maskStart P ride kk: hrd, hsh, hq, hSt, hO, hV, ho, hS, hfree. New, all public: hkk (the sending has
a message number kk), hfit (THE PUBLIC TEST `sendFits P ride`, Honest/K1/Coins.lean, BY NAME:
without it a value number could overrun the part's count, where `ce` gives 0), hshape (its shape is
sh), ha (it has an answer), hfreeP (free is at most the shape's count of free entries at the
sending's codes). hTxt, THE SENDER's, in its own terms: at an input that Vd admits, at least N
challenges and each ν below free: the text answers ce (own k) (maskStart P ride kk + ν). At K1's own
text it is paid by a call: CoinsTieOfMsgTxt.lean of this folder.

How. From hfit: the message's table does not ride (`fits_noRide`, Honest/K1/PadLaw.lean); a number
below the free count is below rows times length (`free_lt`, Honest/K1/Fence.lean); so the value
numbers lie inside the part's count (`mask_in`, Honest/K1/MaskLaw.lean). Then `coinsTie_of_facts` at
rowOf cs ν := (coinsE cs).getD (maskStart P ride kk + ν) zeroE. `val_coinsE_getD` is the library's
`gl_section` (Johnson/Desc/K13/Law/Pin.lean) at the list `coinsE`.

Related. `ProofFile.Honest.K14.val_coinsE` (Honest/K14/SendingsViaRows.lean) says what `val_coinsE_getD`
says, at the list's array and the reading rdE: it is not called: that file stands over kind K14's
sendings.

Limits. NOT IN FRONT OF A LAW OVER COINS: the ground: the Limits of CoinsTieOfFacts.lean of this
folder. CONDITIONAL ON ALL OF THESE: none is shown here of any thread, Script, sending or book. WHAT
IT DOES NOT SAY: that no value is laid at two places: within this one message the map from ν to the
value number is injective by its form; across messages, and against tails, pads and main rows,
nothing is said. THE TIES OF COUNTS THAT CoinsTieOfFacts.lean's head names stand here too; of its
third: hshape and hfreeP are premises: that the sending's codes are the state's is not said at these
letters. "Coin" is the frame's word for a value that the book hands out: nothing is said to be fresh
or masked, and nothing on what an entry is for. This file's imports reach Johnson/Goal/, by
ExchangeAtM3.lean: as CoinsTieOfFacts.lean's head tells.

What is not claimed. That any premise holds. It is none of the library's goals. Nothing on
soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K13.CoinsTieOfFacts
import Johnson.Desc.ProofFile.Honest.K1.Fence
import Johnson.Desc.K13.Law.Pin

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K13
open OnBytes
open OnBytes.Slice (GE)
open VerifiableInference.Desc (K1.Par)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K12.Door (msgShapesB bookInOrderB seatsCarriedB placesBelowB)
open VerifiableInference.Desc.K13 (Where)
open VerifiableInference.Desc.K13.Law (Wit ρg rwBook LedgerAt gl_section)
open VerifiableInference.Desc.Sound (MsgT)
open Johnson.Prover.Send (shapeAt)
open ProofFile.Honest.FirstThread (Letters OwnMsgs)
open ProofFile.Honest.K1 (Ride dueR ce sendFits mask_in fits_noRide free_lt)

/-- A part's coin by number, as the program's element, reads as the coin; beyond the count: 0. -/
theorem val_coinsE_getD {d : Due} (cs : Cs d) (i : ℕ) :
    ρg.val ((coinsE cs).getD i zeroE) = ce cs i := by
  unfold coinsE ce
  by_cases h : i < d.e
  · rw [dif_pos h, List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos h]
    exact gl_section _
  · rw [dif_neg h, List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_neg h]
    exact ρg.zero

variable {Bk : ProverCoinCounts} {Cl W₀ Rc Xi Tr X Pp Cells Tok : Type}

/-- **`CoinsTie` WHERE THE SENDER IS A SENDING OF KIND K1's.** CONDITIONAL: on every premise named;
which they are: the head. -/
theorem coinsTie_of_k1 (L : Letters Bk Cl W₀ Rc Xi Tr X Pp Cells Tok MsgT) (b : Nat)
    (weights : W₀ → Weights) (pile : PileOf Xi) (P₁₃ : Where)
    (rd : Pp × S → VerifiableInference.Desc.Wit Cells Tok MsgT →
      Wit GE P₁₃.lin.matrixRows P₁₃.lin.kCol)
    {nR kC : ℕ} (arr : ℕ → ℕ → ℕ) (mat : Cells → Fin nR → (Fin kC → Bool) → GE)
    (hrd : ∀ a v, (rd a v).mask = (rwBook arr mat a v).mask)
    (M : List OracleShape) (Ld : VerifiableInference.Desc.K12.Door.Laid) (im k₀ free : ℕ)
    (sh : OracleShape) (q : ℕ × ℕ)
    (hsh : M[im]? = some sh) (hq : Ld.places[im]? = some q)
    (hSt : ∀ k s m En, Thr L.thread b k s m En →
      s.out.indexMasks = im ∧ msgShapesB M s.st = true ∧
        bookInOrderB 0 s.book s.roots = true ∧ seatsCarriedB Ld s.book = true ∧
        s.book.place.size = s.st.oracles.size ∧
        placesBelowB Ld s.book.place.size s.book.trees.size = true ∧ LedgerAt s.st im k₀ ∧
        free = Send.freeMaskEntries sh.maskRows (s.st.codes.mask.getD sh.maskCode default).ell
          sh.answers)
    {Vd : Local W₀ Rc Xi Tr → Prop} {N fx : ℕ}
    {txt : Coins Bk → Local W₀ Rc Xi Tr → List Fmt.Drawn → Bool → ℕ → ℕ → Option GE}
    (hO : OwnMsgs L.Q Vd N (arr q.1 q.2) fx txt)
    (hV : ∀ k s m En, Thr L.thread b k s m En → Vd m.st.input ∧ N ≤ m.st.heard.length)
    (P : K1.Par) (ride : Nat → Option Ride) (kk : ℕ) (hkk : kk < P.sent.size)
    (hfit : sendFits P ride = true) (hshape : shapeAt P kk = sh) (ha : sh.answers ≠ 0)
    (hfreeP : free ≤ Send.freeMaskEntries sh.maskRows
      (P.codes.mask.getD sh.maskCode default).ell sh.answers)
    {o : Addr} {own : Coins Bk → Cs (dueR P ride)}
    (ho : OwnIs Bk L.thread.chain o (dueR P ride) own)
    (hTxt : ∀ k w (hd : List Fmt.Drawn) ν, Vd w → N ≤ hd.length → ν < free →
      txt k w (hd.take fx) true (ν % sh.maskRows) (ν / sh.maskRows) =
        some (ce (own k) (K1.maskStart P ride kk + ν)))
    (hS : ∀ blk, L.thread.bs[b]? = some blk →
      oneStretch (rowEntries Bk blk.place 2 0) =
        some (o, K1.maskStart P ride kk + k₀, 2 * P₁₃.lin.kCol + 1))
    (hfree : k₀ + (2 * P₁₃.lin.kCol + 1) ≤ free) :
    CoinsTie L b weights pile P₁₃ rd := by
  subst hshape
  have hr : ride kk = none := fits_noRide P ride kk hfit hkk ha
  have hell : ∀ ν, ν < free → ν < (shapeAt P kk).maskRows *
      (P.codes.mask.getD (shapeAt P kk).maskCode default).ell := fun ν hν =>
    free_lt _ _ _ ν (Nat.pos_of_ne_zero ha) (Nat.lt_of_lt_of_le hν hfreeP)
  refine coinsTie_of_facts L b weights pile P₁₃ rd arr mat hrd M Ld im k₀ free (shapeAt P kk) q hsh
    hq hSt hO hV
    (rowOf := fun cs ν => (coinsE cs).getD (K1.maskStart P ride kk + ν) zeroE) (own := own)
    (base := K1.maskStart P ride kk) ?_ (fun _ _ _ => rfl) ho ?_ hS hfree
  · intro k w hd ν hv hN hν
    rw [hTxt k w hd ν hv hN hν, val_coinsE_getD]
  · intro ν hν
    exact mask_in P ride kk ν hkk hr (hell ν hν)

end ProofFile.Honest.K13

#print axioms ProofFile.Honest.K13.val_coinsE_getD
#print axioms ProofFile.Honest.K13.coinsTie_of_k1
