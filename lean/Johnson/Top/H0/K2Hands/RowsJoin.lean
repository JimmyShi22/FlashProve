-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Hands/RowsJoin.lean: the code switch: THE LAST JOIN, ROW BY ROW: WHAT THE
SWITCH HANDS ON: every row of the typed caller switchSel behind the positions (LdLocD.rowsOf at
closeSel) stands in the list of rows that the program lays, with the same target and the same
vector, read in the field.

It gathers, for the three sorts of rows:
  the carried claim  rows_claim (RowsAt.lean), switchCarried_iff (RowsOrder.lean), claim_reads
                 (ClaimJoin.lean), sel_claim (Johnson/Top/H/SwitchRowsKept.lean)
  an old sample row  rows_sample, sample_reads (here, from keptForm_reads), sel_sample
  a generator row  gen_join (DrawJoin.lean), sel_gen_new, sel_gen_old (AtSel.lean), sel_target
Main names:
  pushTo_comp    coefficients carried along two maps, one after the other
  sample_reads   an old sample row of a kept member, as the program carries it over
  sel_claim_new, sel_claim_old, sel_sample_new, sel_sample_old  the typed rows at an entry of the
                 new sending, and at an entry of a message that stayed open
  TieX           what is asked of the typed statement x: its claim is (old.target read, vecOf); each
                 held sample's answer and matrix are a stored sample row's target and form; its
                 positions are the draws; its long symbols are the symbols read (coordOf)
  rows_join      THE JOIN
THE CLAUSE «sample» OF TieX HOLDS A NAMED PREMISE THAT NO LEMMA OF THIS FOLDER PAYS: that the typed
sample's matrix at the seed, carried along the held member's slots (hd.sJ), is slotVec of formOn of
the stored sample row. form_portZ_F (Johnson/Pack/FormPortZF.lean) reads a sample's matrix for one
case of shapes alone, and says nothing on the target; form_portZ
(Johnson/Desc/K12/Law/FormPortZE.lean) has both cases, and K2Hears/SeedBehind.lean spends it for the
NEW messages' rows.
LIMITS. All of FrameOK, Names, NamesK, Slots, ClaimOK and TieX are PREMISES; nothing here shows that
a run of the programs meets them, so the theorem is not shown to be non-empty. (Brought further, not
paid: Paid.lean, AtYes.lean, TiePaid.lean.) rows_join says that each typed row stands in the
program's list. It does NOT say that the places of two typed rows differ, nor that every row of the
list is a typed row: the numbering both ways is Numbering.lean's, joined in HandsOn.lean. The text's
rows are read at the entries of the new sending alone. No soundness is claimed.
-/
import Johnson.Top.H0.K2Hands.AtSel
import Johnson.Top.H0.K2Hands.ClaimJoin

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Hands
open OnBytes.Slice Cb Iop IOR Johnson.Pack Johnson.Top.H

theorem pushTo_comp {I M Ent : Type} [Fintype I] [Fintype M] (q : I → M) (p : M → Ent)
    (c : I → GE) (n : Ent) : pushTo (fun i => p (q i)) c n = pushTo p (pushTo q c) n := by
  classical
  symm
  unfold pushTo
  calc (∑ m, if p m = n then ∑ i, (if q i = m then c i else 0) else 0)
      = ∑ m, ∑ i, if p m = n then (if q i = m then c i else 0) else 0 := by
        refine Finset.sum_congr rfl fun m _ => ?_
        by_cases h : p m = n
        · simp [h]
        · simp [h]
    _ = ∑ i, ∑ m, if p m = n then (if q i = m then c i else 0) else 0 := Finset.sum_comm
    _ = ∑ i, if p (q i) = n then c i else 0 := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_eq_single (q i)]
        · simp
        · intro m _ hm
          have h : ¬ q i = m := fun k => hm k.symm
          simp [h]
        · intro h
          exact absurd (Finset.mem_univ _) h

section Text
variable {s : Sg} {K : Type} [Fintype K] [DecidableEq K] {cs : OnBytes.Codes}
  {l : List (OnBytes.OracleShape × ℕ)}
  {iJ : (s.cKept K).J → (sigOf cs l).Ent} {iQ : (s.cKept K).Q → (sigOf cs l).Ent}
  {W : OnBytes.SwitchFrame} {ids : ℕ → ℕ} {aMain aM0 aT0 aM1 aT1 : ℕ} {mem row : K → ℕ}
  {pl : K → OnBytes.KeptPlace} {aKept : K → ℕ}

/-- **An old sample row of a kept member, carried over.** -/
theorem sample_reads (D : Names s K cs l iJ iQ W ids aMain aM0 aT0 aM1 aT1)
    (DK : NamesK s K cs l iJ iQ W ids mem row pl aKept)
    (member : ∀ κ, W.kept[mem κ]? = some (pl κ)) (a : ℕ) (k : OnBytes.KeptPlace)
    (hk : W.kept[a]? = some k) (Sl : Slots s K cs l W ids mem row a k) (sample : OnBytes.Row) :
    ReadsAs cs l ids (sampleRow W k sample)
      (pushTo iJ (slotVec s K mem row a k.rowBits (formOn sample))) := fun n =>
  keptForm_reads D DK member a k hk Sl (formOn sample) n

end Text

variable {S : Sig GE} (R : RowsK S) [Nonempty R.G.P] {kp : S.O → Prop} [DecidablePred kp]
  (Hd : GHeld R.Sh kp) {B Kc St₀ Wp : Type} [Fintype B] (Sb : B → Type)
  (sl : ∀ b, Slf GE (Sb b) R.G.C.J) (Z : Evader GE (R.G.Row B)) {E₀ : ExtSpec}
  (A₀ : Rels Kc St₀ E₀ ((S.sub kp).Msg × Wp))
  (cs : OnBytes.Codes) (l : List (OnBytes.OracleShape × ℕ))
  (iJ : R.Sh.Cf.J → (sigOf cs l).Ent) (iQ : R.Sh.Cf.Q → (sigOf cs l).Ent)
  (t : ℕ) (w₀ : (Hd.foldD Sb sl Z A₀).tgt.W)

set_option quotPrecheck false in
local notation "LocK" => (closeSel Hd Sb sl Z A₀ cs l iJ iQ t w₀).loc
set_option quotPrecheck false in
local notation "pJK" => fun j : R.Sh.Cf.J =>
  ((⟨Sum.inr (iJ j).1, (iJ j).2⟩ : (closeSel Hd Sb sl Z A₀ cs l iJ iQ t w₀).loc.S.Ent))
set_option quotPrecheck false in
local notation "pQK" => fun q : R.Sh.Cf.Q =>
  ((⟨Sum.inr (iQ q).1, (iQ q).2⟩ : (closeSel Hd Sb sl Z A₀ cs l iJ iQ t w₀).loc.S.Ent))
set_option quotPrecheck false in
local notation "OldO" => (vecD (Hd.foldD Sb sl Z A₀)).S₂.O

theorem sel_claim_new (x : ((LocK).Xc × (LocK).hd.Smp) × (LocK).Lc) (n : (sigOf cs l).Ent) :
    ((LocK).rowsOf pJK pQK Slf.idf id x).2 (.inl ()) ⟨Sum.inr n.1, n.2⟩ = pushTo iJ x.1.1.2 n :=
  pushTo_inr (A := OldO) (B := (sigOf cs l).O) (F := fun a => ((LocK).S.om a).C.J) iJ x.1.1.2 n

theorem sel_claim_old (x : ((LocK).Xc × (LocK).hd.Smp) × (LocK).Lc) (a : OldO)
    (e : ((LocK).S.om (Sum.inl a)).C.J) :
    ((LocK).rowsOf pJK pQK Slf.idf id x).2 (.inl ()) ⟨Sum.inl a, e⟩ = 0 :=
  pushTo_inl (A := OldO) (B := (sigOf cs l).O) (F := fun a => ((LocK).S.om a).C.J) iJ x.1.1.2 a e

theorem sel_sample_new (x : ((LocK).Xc × (LocK).hd.Smp) × (LocK).Lc)
    (ks : Σ k, ((LocK).hd.o k).Z.S) (n : (sigOf cs l).Ent) :
    ((LocK).rowsOf pJK pQK Slf.idf id x).2 (.inr (.inl ks)) ⟨Sum.inr n.1, n.2⟩ =
      pushTo iJ (pushTo ((LocK).hd.sJ ks.1) (((LocK).hd.o ks.1).Z.mat (x.1.2 ks.1).1 ks.2)) n :=
  (pushTo_inr (A := OldO) (B := (sigOf cs l).O) (F := fun a => ((LocK).S.om a).C.J)
    (fun j => iJ ((LocK).hd.sJ ks.1 j)) (((LocK).hd.o ks.1).Z.mat (x.1.2 ks.1).1 ks.2) n).trans
    (pushTo_comp ((LocK).hd.sJ ks.1) iJ _ n)

theorem sel_sample_old (x : ((LocK).Xc × (LocK).hd.Smp) × (LocK).Lc)
    (ks : Σ k, ((LocK).hd.o k).Z.S) (a : OldO) (e : ((LocK).S.om (Sum.inl a)).C.J) :
    ((LocK).rowsOf pJK pQK Slf.idf id x).2 (.inr (.inl ks)) ⟨Sum.inl a, e⟩ = 0 :=
  pushTo_inl (A := OldO) (B := (sigOf cs l).O) (F := fun a => ((LocK).S.om a).C.J)
    (fun j => iJ ((LocK).hd.sJ ks.1 j)) (((LocK).hd.o ks.1).Z.mat (x.1.2 ks.1).1 ks.2) a e

/-- What is asked of the typed statement x behind the positions. -/
structure TieX (x : ((LocK).Xc × (LocK).hd.Smp) × (LocK).Lc) (St : OnBytes.Statement)
    (W : OnBytes.SwitchFrame) (ids : ℕ → ℕ) (old : OnBytes.SingleRows) (pos : OnBytes.Positions)
    (y : Array OnBytes.E) (mem row : R.Kp → ℕ) (pl : R.Kp → OnBytes.KeptPlace) : Prop where
  target : x.1.1.1 = readE old.target
  vector : x.1.1.2 = vecOf R.s R.Kp old row pl
  sample : ∀ ks : Σ k, ((LocK).hd.o k).Z.S, ∃ (a i : ℕ) (k : OnBytes.KeptPlace) (smp : OnBytes.Row),
    W.kept[a]? = some k ∧ (samplesOf St k)[i]? = some smp ∧
      Slots R.s R.Kp cs l W ids mem row a k ∧ (x.1.2 ks.1).2 ks.2 = readE smp.target ∧
      pushTo ((LocK).hd.sJ ks.1) (((LocK).hd.o ks.1).Z.mat (x.1.2 ks.1).1 ks.2) =
        slotVec R.s R.Kp mem row a k.rowBits (formOn smp)
  draw : ∀ i : Fin (LocK).t, pos.draws.toList[i.val]? = some (x.2.1 i).val
  symbol : ∀ (i : Fin (LocK).t) (α : (LocK).C.Aa), x.2.2 i α =
    readE (symAtB old pos y (x.2.1 i).val (coordOf R.s R.Kp W old mem row α))

/-- **The last join, row by row.** -/
theorem rows_join {St : OnBytes.Statement} {old : OnBytes.SingleRows} {T : OnBytes.SwitchTarget}
    {g : ℕ} {anew : Array ℕ} {pos : OnBytes.Positions} {y : Array OnBytes.E}
    {rows : List OnBytes.Row} {W : OnBytes.SwitchFrame} {carried : OnBytes.Row} {ids : ℕ → ℕ}
    {aMain aM0 aT0 aM1 aT1 : ℕ} {mem row : R.Kp → ℕ} {pl : R.Kp → OnBytes.KeptPlace}
    {aKept : R.Kp → ℕ} (L : Laid St old T g anew pos y rows W carried)
    (F : FrameOK W aMain aM0 aT0 aM1 aT1)
    (D : Names R.s R.Kp cs l iJ iQ W ids aMain aM0 aT0 aM1 aT1)
    (DK : NamesK R.s R.Kp cs l iJ iQ W ids mem row pl aKept)
    (member : ∀ κ, W.kept[mem κ]? = some (pl κ)) (rowIn : ∀ κ, row κ < (pl κ).rows)
    (hm : old.masks = 2) (h0 : aM0 = W.parts.maskAt.getD 0 0) (h1 : aM1 = W.parts.maskAt.getD 1 0)
    (Q : ∀ ks, old.kept.toList.mapM (placeOf W) = some ks →
      ClaimOK R.s R.Kp cs l W ids mem row pl old ks)
    (x : ((LocK).Xc × (LocK).hd.Smp) × (LocK).Lc)
    (X : TieX R Hd Sb sl Z A₀ cs l iJ iQ t w₀ x St W ids old pos y mem row pl)
    (b : (LocK).RowN) :
    ∃ (place : ℕ) (r : OnBytes.Row), rows[place]? = some r ∧
      readE r.target = ((LocK).rowsOf pJK pQK Slf.idf id x).1 b ∧
      (∀ n : (sigOf cs l).Ent,
        coefAt r (ids (entAt cs l n).1) (entAt cs l n).2.1 (entAt cs l n).2.2 =
          ((LocK).rowsOf pJK pQK Slf.idf id x).2 b ⟨Sum.inr n.1, n.2⟩) ∧
      ∀ (a : OldO) (e : ((LocK).S.om (Sum.inl a)).C.J),
        ((LocK).rowsOf pJK pQK Slf.idf id x).2 b ⟨Sum.inl a, e⟩ = 0 := by
  rcases b with ⟨⟩ | ks | ⟨i, α⟩
  · obtain ⟨ks, hks, rfl⟩ := (switchCarried_iff W old carried).1 L.claim
    refine ⟨0, _, rows_claim L, X.target.symm, fun n => ?_,
      sel_claim_old R Hd Sb sl Z A₀ cs l iJ iQ t w₀ x⟩
    rw [sel_claim_new, X.vector]
    exact claim_reads F D DK member old ks hm h0 h1 (Q ks hks) n
  · obtain ⟨a, i, k, smp, hk, hs, Sl, ht, hv⟩ := X.sample ks
    refine ⟨_, _, rows_sample L a i k smp hk hs, ht.symm, fun n => ?_,
      sel_sample_old R Hd Sb sl Z A₀ cs l iJ iQ t w₀ x ks⟩
    rw [sel_sample_new, hv]
    exact sample_reads D DK member a k hk Sl smp n
  · have ha : R.s.C.a = W.code.logN := by rw [D.codeC]; rfl
    have hx : (x.2.1 i).val < 2 ^ W.code.logN :=
      lt_of_lt_of_eq (x.2.1 i).isLt (congrArg (fun e => 2 ^ e) ha)
    obtain ⟨r, hr, ht, hv⟩ := gen_join L F D DK member rowIn hm i.val (x.2.1 i).val (X.draw i) hx α
    refine ⟨_, r, hr, ?_, fun n => ?_, sel_gen_old R Hd Sb sl Z A₀ cs l iJ iQ t w₀ x (i, α)⟩
    · rw [ht]
      exact (X.symbol i α).symm
    · rw [sel_gen_new]
      exact hv n

end VerifiableInference.Desc.First.K2Hands

#print axioms VerifiableInference.Desc.First.K2Hands.sample_reads
#print axioms VerifiableInference.Desc.First.K2Hands.rows_join
