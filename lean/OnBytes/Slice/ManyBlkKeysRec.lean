-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/ManyBlkKeysRec.lean: a yes of the written link, at a decision whose yes gives the yes
of the program's link at two keys, gives the yes in the field AT THE PAIR OF RECORDS THAT IS READ
OFF THE TWO KEYS.

`yes_in_field_manyR` (OnBytes/Slice/ManyBlkWrittenRec.lean) is stated at a pair of records r which
the two keys hold. This file names that pair as a function of the keys: each seed's point, each
seed's factor and each answer, read in the field (`recAtR`: the text of `recOfKey`,
OnBytes/Slice/BlkKeyRec.lean, with the shape's three numbers as letters). A key holds what is read
off it if its sizes fit the shape, no seed's factor is the program's 0, and each factor's words are
below the prime. The program tests the first two, so a yes gives them. The third stays a hypothesis
on the keys here; OnBytes/Slice/KeyTableRec.lean shows it of the keys that `tableKey` returns.

Main definitions: `recAtR`, `recsAtR`.
Main theorems: `recAtR_eq`, `keyHasR_recAtR`, `yes_in_field_keysR`.

Not claimed. All that the head of OnBytes/Slice/ManyBlkWrittenRec.lean does not claim, but for what
is said above of the keys. That a factor's words are below the prime (`hok0`, `hok1`). That the keys
name the items 0 and 1 (`hi0`, `hi1`). Where a key's record and seeds come from. A factor that reads
as 0 is read as 1 by `recAtR`; after a yes there is none among factors with words below the prime.
Nothing on soundness.

-/
import OnBytes.Slice.ManyBlkWrittenRec

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Prob Cb Cb.Ood _root_.Run
open Params (LinkShape IoppStage)

/-- The record that stands in a key, read in the field: n seeds with points of lg coordinates, and n
answers for each of 2 ^ v rows. Entry r * n + i of the key's array is the answer of row r under seed
i. -/
noncomputable def recAtR (v lg n : ℕ) (key : TableKey) : RecP NZ v lg n :=
  (fun i => (fun t => readE ((key.seeds.getD i.val default).z.getD t.val zeroE),
      asFactor (readE (key.seeds.getD i.val default).beta)),
    fun q => readE (key.record.getD (Sz.rowNo q.1 * n + q.2.val) zeroE))

/-- At a shape's three numbers it is `recOfKey`. -/
theorem recAtR_eq (sh : Params.IndexShape) (key : TableKey) :
    recAtR sh.v sh.cubeBits sh.answers key = recOfKey sh key := rfl

/-- A key holds the record that is read off it, if its sizes fit the shape, no seed's factor is the
program's 0, and the factors have words below the prime. -/
theorem keyHasR_recAtR (v lg n : ℕ) (sh : Params.IndexShape) (key : TableKey) (hv : sh.v = v)
    (hlg : sh.cubeBits = lg) (hn : sh.answers = n) (hf : key.fits sh = true)
    (hz : (key.seeds.all fun x => !isZeroE x.beta) = true)
    (hok : ∀ x ∈ key.seeds, okE x.beta = true) : KeyHasR v lg n sh key (recAtR v lg n key) := by
  subst hv hlg hn
  exact keyHasR_recOfKey sh key hf hz hok

/-- The pair of records that is read off the two keys, as the library's link takes it. -/
noncomputable def recsAtR (S : Sz) (lg n : ℕ) (first further : TableKey) :
    (S.lkR (recZ S.P.T.l lg n)).X0 :=
  (recAtR S.P.v lg n first, recAtR S.P.v lg n further)

/-- Whenever the written link accepts a transcript, the chain's yes in the field holds, at the pair
of records that is read off the two keys. The letters and hypotheses are those of
`yes_in_field_manyR`; in the place of `hK0` and `hK1`: lg and n are the shape's numbers, and each
seed's factor has words below the prime. -/
theorem yes_in_field_keysR (S : Sz) (t₀ lg n : ℕ) (Λ : LinkShape) (first further : TableKey)
    (st1 : IoppStage) (rest : List IoppStage) (htest : Λ.test = st1 :: rest)
    (h2 : 2 ≤ rest.length) (hride : Λ.choice.masksRide = true) (s0 : Start) (K : Codes)
    (d1 d2 d3 d4 d5 dA : PQ.RD) (c : Chain (S.sg t₀)) (xs : List PQ.XO) (dec : PQ.View → Bool)
    (hdec : ∀ V, dec V = true → (linkVerify Λ first further).decides s0 V = true)
    (hs0 : (S.sg t₀).h = 0) (hP : c.Pub K st1 rest) (hh : HeadTrees d1 d2 d3 d4 d5 dA)
    (hc : c.Trees) (hl : 1 + c.len ≤ 2 ^ 16) (sh fr : OracleShape)
    (hW : PQ.colW d2.tree = Fmt.M2.widthOf S.P.mems 1)
    (mem : Fmt.M2.Mem) (hmems : S.P.mems = [mem, mem]) (hE : mem.overE = true)
    (hm0 : mem.masks = 0) (f1 : ℕ) (hst : (Fmt.M2.starts [mem, mem]).1 = [some 0, some f1])
    (hf1 : mem.rows ≤ f1) (hk : f1 + mem.rows ≤ 2 ^ Fmt.M2.kOf [mem, mem])
    (hR : sh.mainRows = mem.rows) (h3 : sh.mainDeg = 3) (hz : sh.maskRows = 0)
    (hfm : fr.mainRows = 0) (hfz : 0 < fr.maskRows)
    (hs : s0.samples = 1) (hi0 : first.item = 0) (hi1 : further.item = 1)
    (hpads : 3 * n ≤ S.P.T.l) (hlg : Λ.table.cubeBits = lg) (hn : Λ.table.answers = n)
    (hok0 : ∀ x ∈ first.seeds, okE x.beta = true) (hok1 : ∀ x ∈ further.seeds, okE x.beta = true)
    (hS : LinkSizes S Λ s0.st.codes) (hF : LinkFit S Λ (Λ.side false 1) (Λ.side true 1))
    (hd : BatDraws S d1 d2 d3 d4 d5 dA)
    (hn0 : (Λ.side false 1).columns = Λ.columnsFirst)
    (hn1 : (Λ.side true 1).columns = Λ.columnsFurther)
    (hkeep : ∀ V, HeadKeepsR Λ first further (startCtx s0 V) V K S.P.Z.l
      (GroupTie (S.sg t₀) 0 [sh, sh, fr] #[some 0, some f1] #[none, none]))
    (g1 : (wRound d2).Orc → (S.sg t₀).cIn.Word)
    (y : (S.lkR (recZ S.P.T.l lg n)).E0.Str) m0 c0 m1 c1 m2 c2 m3 c3 m4 c4 m5 c5 mA cA (b : c.Bl)
    (hacc : (written S d1 d2 d3 d4 d5 (dA :: c.rds) xs dec).accept () y
      (m0, c0, m1, c1, m2, c2, m3, c3, m4, c4, m5, c5, mA, cA, c.trL b) = true) :
    c.Acc (sumStmR (RowNo.port S (recZ S.P.T.l lg n) n fun σ => Equiv.refl (Fin n) σ) t₀
        (rowsXR S (recZ S.P.T.l lg n) n (Equiv.refl (Fin n)) t₀
          (st4R S (recZ S.P.T.l lg n) (recsAtR S lg n first further) d1 d2 d3 d4 d5 y c1 m2 c2 m3 c4
            c5).1).1
        (rowsXR S (recZ S.P.T.l lg n) n (Equiv.refl (Fin n)) t₀
          (st4R S (recZ S.P.T.l lg n) (recsAtR S lg n first further) d1 d2 d3 d4 d5 y c1 m2 c2 m3 c4
            c5).1).2 (drawnE dA cA))
      (wordIn (S.sg t₀) (col1 S d2 m2.1)) (wordFr (S.sg t₀) (col1 S d2 m2.1)) (g1 m2.1) b :=
  yes_in_field_manyR S t₀ lg n Λ first further st1 rest htest h2 hride s0 K d1 d2 d3 d4 d5 dA c xs
    dec hdec hs0 hP hh hc hl sh fr hW mem hmems hE hm0 f1 hst hf1 hk hR h3 hz hfm hfz hs hi0 hi1
    hpads (recsAtR S lg n first further)
    (fun hf hnz => keyHasR_recAtR S.P.v lg n _ first hS.v hlg hn hf hnz hok0)
    (fun hf hnz => keyHasR_recAtR S.P.v lg n _ further hS.v hlg hn hf hnz hok1)
    hS hF hd hn0 hn1 hkeep g1 y m0 c0 m1 c1 m2 c2 m3 c3 m4 c4 m5 c5 mA cA b hacc

end OnBytes.Slice

#print axioms OnBytes.Slice.recAtR_eq
#print axioms OnBytes.Slice.keyHasR_recAtR
#print axioms OnBytes.Slice.yes_in_field_keysR
