-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoAttLists2.lean.
Which claims the check of the attention sub-proof adds, as written lists: claims 5 to 8.

The routines of OnBytes/Model/AttentionClaimsB.lean, walked as those of claims 3 and 4 are in
OnBytes/Tie/Pv/Lookup/Ends/FoAttLists1.lean, by the rules of OnBytes/Tie/Pv/Lookup/Ends/FoRd.lean.

Main names:
 * `rd_readDenominator`, `rd_readIndexBit`: two more readers' values.
 * `endValuesET`, `ad_endValuesE`; `claim5T`, with the value `claim5V`; `adV_claim5`: claim 5.
 * `valueProductT`, `ad_valueProduct`; `claim6T`; `ad_claim6`. `claim7T`; `ad_claim7`. `bitsSumF`,
   `claim8T`; `ad_claim8`.

What is lost against the routines: the values and the lists here are total. They do not say where a
routine refuses: `xlT` (OnBytes/Tie/Pv/Lookup/Ends/FoAttLists1.lean), of which `readHeadT` and
`readGroupT` are made, is the empty form where `xl` refuses. Off a run that returns, a list means
nothing. Nothing says that a routine returns. The lists are tied to a run by `Adds`
(OnBytes/Tie/Pv/Led/LedAdds.lean): the forms are added one after the other, in the list's order;
`Added` (OnBytes/Tie/Pv/Lookup/Ends/FoAdded.lean) is not concluded here.

Not claimed: anything on soundness, completeness or hiding.
Nor is it claimed what the forms are worth.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoAttLists1

set_option autoImplicit false

namespace Fo
open OnBytes OnBytes.Model OnBytes.PscRun OnBytes.Attention

variable {K : ℕ}

/-- `readDenominator`, if it returns, leaves the state and returns `readDenominatorF`. -/
theorem rd_readDenominator (h : Attention.Heard) (t : ℕ) (zg : Array E) (lam a : ℕ) :
    Rd h.iU3 K (readDenominator h t zg lam a) (readDenominatorF h K t zg lam a) :=
  rd_weighted _ _ _ _ fun _ => rd_shV h t _ _ _ _ _

/-- `readIndexBit`, if it returns, leaves the state and returns `readIndexBitF`. -/
theorem rd_readIndexBit (h : Attention.Heard) (t : ℕ) (zg : Array E) (lam a b : ℕ) :
    Rd h.iU3 K (readIndexBit h t zg lam a b) (readIndexBitF h K t zg lam a b) :=
  rd_weighted _ _ _ _ fun _ => rd_shV h t _ _ _ _ _

/-! ### claim 5 -/

/-- The two claims of `endValuesE`. -/
def endValuesET (h : Attention.Heard) (K b : ℕ) (w : PW) : List Aff :=
  [sc3A h.d.scE b - readDenominatorF h K h.t.hE h.d.scE.r w.lam w.a] ++
    [sc3B h.d.scE b - readHeadT h K h.t.qO h.S.atO h.d.scE.r h.d.zcW w.lam w.a]

/-- `endValuesE`, if it returns, has added them. -/
theorem ad_endValuesE (h : Attention.Heard) (b : ℕ) (w : PW) :
    Ad h.iU3 K (endValuesE h b w) (endValuesET h K b w) :=
  Ad.after (rd_readDenominator h _ _ _ _) (Ad.seq (Ad.lin _)
    (Ad.after (rd_readHead h _ _ _ _ _ _) (Ad.lin _)))

/-- The joins that claim 5 returns. -/
def claim5V (h : Attention.Heard) (j : Joins) : Joins :=
  (joinR16 h.S h.d j).set h.d.qWH (keyWH h.d)

/-- The claims of claim 5, in the order in which they are added. -/
def claim5T (h : Attention.Heard) (K : ℕ) : List Aff :=
  [lessF (Aff.slot h.d.sZC) h.d.pwW fun w => readDenominatorF h K h.t.hW h.d.zgW w.lam w.a] ++
  ([lessF (Aff.slot h.d.sRH) h.d.pwW fun w =>
      readHeadT h K h.t.tO (atRh h.S) h.d.zgW h.d.zcW w.lam w.a] ++
  ([lessF (Aff.slot h.d.sRHP) h.d.pwW fun w =>
      readHeadT h K h.t.tO (atRhp h.S) h.d.zgW h.d.zcW w.lam w.a] ++
  (((List.range h.S.cf.lt).flatMap fun k =>
      [lessF (Aff.slot (h.d.sIB + k)) h.d.pwX fun w =>
        readIndexBitF h K h.t.hX h.d.zgX w.lam w.a k]) ++
  ([lessF (Aff.slot h.d.s5h) h.d.pwH fun w =>
      readHeadT h K h.t.tO (atRh h.S) h.d.zgH h.d.zcH w.lam w.a] ++
  ([lessF (Aff.slot (h.d.s5h + 1)) h.d.pwH fun w =>
      readHeadT h K h.t.tO (atRhp h.S) h.d.zgH h.d.zcH w.lam w.a] ++
  ([h.d.scE.rowU] ++
  (((List.range h.S.NP).flatMap fun b => endValuesET h K b (h.d.pwW.getD b default)) ++ [])))))))

/-- **Claim 5, if it returns, returns the written joins and has added the written list.** -/
theorem adV_claim5 (h : Attention.Heard) (j : Joins) :
    AdV h.iU3 K (claim5 h j) (claim5V h j) (claim5T h K) := by
  unfold claim5 claim5V claim5T
  refine AdV.after (rd_lessPieces _ _ _
    (fun w => readDenominatorF h K h.t.hW h.d.zgW w.lam w.a)
    fun w => rd_readDenominator h _ _ _ _) ?_
  refine AdV.after (rd_lessPieces _ _ _
    (fun w => readHeadT h K h.t.tO (atRh h.S) h.d.zgW h.d.zcW w.lam w.a)
    fun w => rd_readHead h _ _ _ _ _ _) ?_
  refine AdV.after (rd_lessPieces _ _ _
    (fun w => readHeadT h K h.t.tO (atRhp h.S) h.d.zgW h.d.zcW w.lam w.a)
    fun w => rd_readHead h _ _ _ _ _ _) ?_
  refine AdV.after (rd_lessPieces _ _ _
    (fun w => readHeadT h K h.t.tO (atRh h.S) h.d.zgH h.d.zcH w.lam w.a)
    fun w => rd_readHead h _ _ _ _ _ _) ?_
  refine AdV.after (rd_lessPieces _ _ _
    (fun w => readHeadT h K h.t.tO (atRhp h.S) h.d.zgH h.d.zcH w.lam w.a)
    fun w => rd_readHead h _ _ _ _ _ _) ?_
  refine AdV.seq (Ad.lin _) (AdV.seq (Ad.lin _) (AdV.seq (Ad.lin _) ?_))
  refine AdV.seq (Ad.forInList _ _ ?_ _) ?_
  · intro k
    exact AdV.after (rd_lessPieces _ _ _
      (fun w => readIndexBitF h K h.t.hX h.d.zgX w.lam w.a k)
      fun w => rd_readIndexBit h _ _ _ _ _) (AdV.seq (l₂ := []) (Ad.lin _) (AdV.pure _))
  refine AdV.seq (Ad.lin _) (AdV.seq (Ad.lin _) (AdV.seq (Ad.lin _) ?_))
  refine AdV.seq (Ad.forInList _ _ ?_ _) (AdV.pure _)
  intro b
  exact AdV.seq (l₂ := []) (ad_endValuesE h b _) (AdV.pure _)

/-! ### claim 6 -/

/-- The claims of `valueProduct`: the sumcheck's row, then two for each pair. -/
def valueProductT (h : Attention.Heard) (K : ℕ) (sc : Sc3) (tS : ℕ) (pt : Array E) (isD : Bool)
    (tV : ℕ) : List Aff :=
  [sc.rowU] ++ (List.range h.S.NP).flatMap fun b =>
    [sc3A sc b - (planeF h K tS 3 (h.d.pwW.getD b default).lam (h.d.pwW.getD b default).a pt isD +
      Aff.ofConst (ofNat 128) +
      Aff.scale (planeF h K tS 4 (h.d.pwW.getD b default).lam (h.d.pwW.getD b default).a pt isD)
        (ofNat 256))] ++
    [sc3B sc b - (Aff.ofConst h.d.gam +
      readGroupT h K tV h.S.atV sc.r h.d.zcW (h.d.pwW.getD b default).lam)]

/-- `valueProduct`, if it returns, has added them. -/
theorem ad_valueProduct (h : Attention.Heard) (sc : Sc3) (tS : ℕ) (pt : Array E) (isD : Bool)
    (tV : ℕ) : Ad h.iU3 K (valueProduct h sc tS pt isD tV) (valueProductT h K sc tS pt isD tV) := by
  unfold valueProduct valueProductT
  refine Ad.seq (Ad.lin _) (Ad.then0 (Ad.forInList _ _ ?_ _) Ad.pure)
  intro b
  refine AdV.after (rd_plane h _ _ _ _ _ _) (AdV.after (rd_plane h _ _ _ _ _ _) ?_)
  refine AdV.seq (Ad.lin _) (AdV.after (rd_readGroup h _ _ _ _ _) ?_)
  exact AdV.seq (l₂ := []) (Ad.lin _) (AdV.pure _)

/-- The claims of claim 6. -/
def claim6T (h : Attention.Heard) (K : ℕ) : List Aff :=
  [Aff.slot h.d.sCl + Aff.slot (h.d.sCl + 1) - Aff.slot h.d.sACC -
    Aff.scale (Aff.slot h.d.sZC) h.d.gam] ++
  (valueProductT h K h.d.vpm h.t.tVM h.t.ptM false h.t.qVM ++
    valueProductT h K h.d.vpd h.t.tVD h.t.ptD true h.t.qVD)

/-- **Claim 6, if it returns, has added the written list.** -/
theorem ad_claim6 (h : Attention.Heard) : Ad h.iU3 K (claim6 h) (claim6T h K) :=
  Ad.seq (Ad.lin _) (Ad.seq (ad_valueProduct h _ _ _ _ _) (ad_valueProduct h _ _ _ _ _))

/-! ### claim 7 -/

/-- The claims of claim 7. -/
def claim7T (h : Attention.Heard) (K : ℕ) : List Aff :=
  ((List.range h.S.NP).flatMap fun b =>
    [Aff.slot (h.x.sM6 + b) - readMaximumF h K h.t.hT h.x.tg (b / h.S.HA) (b % h.S.HA)]) ++
  ([h.x.scF.rowU] ++
  (((List.range h.S.NP).flatMap fun b =>
    [sc3A h.x.scF b -
      readHeadT h K h.t.qF h.S.atQ (h.x.rg h.S) (h.x.rc h.S) (b / h.S.HA) (b % h.S.HA)]) ++
  ([h.x.scd.rowU] ++
  (((List.range h.S.Lam).flatMap fun lam =>
    [Aff.slot (h.x.sKC + lam) - readGroupT h K h.t.qKx h.S.atK (h.x.pg h.S) (h.x.rc h.S) lam]) ++
  ((List.range h.S.NP).flatMap fun b => (List.range h.S.cf.lt).flatMap fun k =>
    [Aff.slot (h.x.sIb h.S b k) -
      readIndexBitF h K h.t.hPi (h.x.pg h.S) (b / h.S.HA) (b % h.S.HA) k])))))

/-- **Claim 7, if it returns, has added the written list.** -/
theorem ad_claim7 (h : Attention.Heard) : Ad h.iU3 K (claim7 h) (claim7T h K) := by
  unfold claim7 claim7T
  refine Ad.seq (Ad.forInList _ _ ?_ _) (Ad.seq (Ad.lin _) (Ad.seq (Ad.forInList _ _ ?_ _)
    (Ad.seq (Ad.lin _) (Ad.seq (Ad.forInList _ _ ?_ _)
      (Ad.then0 (Ad.forInList _ _ ?_ _) Ad.pure)))))
  · intro b
    exact AdV.after (rd_readMaximum h _ _ _ _) (AdV.seq (l₂ := []) (Ad.lin _) (AdV.pure _))
  · intro b
    exact AdV.after (rd_readHead h _ _ _ _ _ _) (AdV.seq (l₂ := []) (Ad.lin _) (AdV.pure _))
  · intro lam
    exact AdV.after (rd_readGroup h _ _ _ _ _) (AdV.seq (l₂ := []) (Ad.lin _) (AdV.pure _))
  · intro b
    refine AdV.seq0 (Ad.forInList _ _ ?_ _) (AdV.seq (l₂ := []) Ad.pure (AdV.pure _))
    intro k
    exact AdV.after (rd_readIndexBit h _ _ _ _ _) (AdV.seq (l₂ := []) (Ad.lin _) (AdV.pure _))

/-! ### claim 8 -/

/-- The first end value of pair b less the weighted bits of its index. -/
def bitsSumF (h : Attention.Heard) (K b : ℕ) : Aff :=
  (List.range h.S.cf.lt).foldl (fun s k =>
    Aff.addMul s (readIndexBitF h K h.t.hR2 (h.x.rg2 h.S) (b / h.S.HA) (b % h.S.HA) k)
      (mulE minusOne ((eqTab (h.x.rk h.S)).getD k zeroE))) (sc3A h.x.scH b)

/-- The claims of claim 8. -/
def claim8T (h : Attention.Heard) (K : ℕ) : List Aff :=
  [h.x.scH.rowU] ++ (List.range h.S.NP).flatMap fun b =>
    [sc3B h.x.scH b - sc3A h.x.scH b + Aff.ofConst oneE] ++ [bitsSumF h K b]

/-- **Claim 8, if it returns, has added the written list.** -/
theorem ad_claim8 (h : Attention.Heard) : Ad h.iU3 K (claim8 h) (claim8T h K) := by
  unfold claim8 claim8T bitsSumF
  refine Ad.seq (Ad.lin _) (Ad.then0 (Ad.forInList _ _ ?_ _) Ad.pure)
  intro b
  refine AdV.seq (Ad.lin _) (AdV.after (Rd.foldlM
    (fun s k => do
      let bit ← readIndexBit h h.t.hR2 (h.x.rg2 h.S) (b / h.S.HA) (b % h.S.HA) k
      pure (Aff.addMul s bit (mulE minusOne ((eqTab (h.x.rk h.S)).getD k zeroE))))
    (fun s k => Aff.addMul s
      (readIndexBitF h K h.t.hR2 (h.x.rg2 h.S) (b / h.S.HA) (b % h.S.HA) k)
      (mulE minusOne ((eqTab (h.x.rk h.S)).getD k zeroE)))
    (fun _ k => Rd.bind (rd_readIndexBit h _ _ _ _ _) (Rd.pure _)) _ _) ?_)
  exact AdV.seq (l₂ := []) (Ad.lin _) (AdV.pure _)

end Fo
