-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Hands/HandsOn.lean: the code switch: THE LAST JOIN: WHAT THE SWITCH HANDS
ON: every row of the typed caller switchSel behind the positions stands AT ITS NUMBERED PLACE in the
list of rows that the program lays, with the same target and the same vector, AND THE TEXT's ROW HAS
NO COEFFICIENT ELSEWHERE; the numbering is one to one and onto the list's places.

RowsJoin.lean's rows_join gave "for each typed row a place". Two things are added here: the
numbering as one function with a name (Numbering.lean's rowNo), and that a row of the text has no
coefficient outside the entries of the new sending (Support.lean, SupportClaim.lean).
  Inside      the three numbers of which the last clause speaks: InBits and InClaim together
  gen_join2   gen_join with that clause
  TieN        RowsJoin.lean's TieX with the held samples' numbers as two functions aOf and iOf
  hands_on_rows  THE JOIN, at rows[rowNo … b]?
  hands_on_count  rows.length is 1 + (all sample rows) + (positions) * (1 + kept rows + 2): with
              rowNo_inj and rowNo_onto (Numbering.lean) the numbering is a one-to-one map onto the
              list's places
UNPAID HERE: FrameOK, Names, NamesK, Slots, ClaimOK, TieN, and for the numbering SlotsAll and Held.
So nothing here is shown to be non-empty. (Brought further, not paid: Paid.lean makes FrameOK, Names
and NamesK from one record AtSwitch, and ClaimOK from it and four plain clauses; AtYes.lean's
atSwitch_of makes eight of its clauses at a yes; TieSym.lean's tieN_of makes TieN's clauses «draw»
and «symbol», the second from the premise ShowsAt; TiePaid.lean's hands_of_plan brings all of them
to the three records CallerAt, FrontAt, YesAt, which are premises.) TieN's clause «sample» holds the
named premise on the typed sample's matrix that no lemma pays (see RowsJoin.lean's head).
WHAT THE LAST CLAUSE LEAVES UNSAID: indices from 2 ^ (a table's index bits) on (a table has none);
and, in a kept member's new main table, indices that name no row of the member or no place of a row
(see SupportClaim.lean's head). No soundness is claimed.
-/
import Johnson.Top.H0.K2Hands.RowsJoin
import Johnson.Top.H0.K2Hands.SupportClaim
import Johnson.Top.H0.K2Hands.Numbering

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Hands
open OnBytes.Slice Cb Iop IOR Johnson.Pack Johnson.Top.H

/-- The three numbers of which the clause "no coefficient elsewhere" speaks. -/
def Inside {K : Type} (s : Sg) (W : OnBytes.SwitchFrame) (pl : K → OnBytes.KeptPlace) (o : ℕ)
    (part : OnBytes.Part) (J : ℕ) : Prop := InBits W pl o part J ∧ InClaim s W o part J

section Text
variable {s : Sg} {K : Type} [Fintype K] [DecidableEq K] {cs : OnBytes.Codes}
  {l : List (OnBytes.OracleShape × ℕ)}
  {iJ : (s.cKept K).J → (sigOf cs l).Ent} {iQ : (s.cKept K).Q → (sigOf cs l).Ent}
  {W : OnBytes.SwitchFrame} {ids : ℕ → ℕ} {aMain aM0 aT0 aM1 aT1 : ℕ} {mem row : K → ℕ}
  {pl : K → OnBytes.KeptPlace} {aKept : K → ℕ}
  {S : OnBytes.Statement} {old : OnBytes.SingleRows} {T : OnBytes.SwitchTarget} {g : ℕ}
  {anew : Array ℕ} {pos : OnBytes.Positions} {y : Array OnBytes.E} {rows : List OnBytes.Row}
  {carried : OnBytes.Row}

/-- All generator rows, row by row, with "no coefficient elsewhere". -/
theorem gen_join2 (L : Laid S old T g anew pos y rows W carried)
    (F : FrameOK W aMain aM0 aT0 aM1 aT1) (D : Names s K cs l iJ iQ W ids aMain aM0 aT0 aM1 aT1)
    (DK : NamesK s K cs l iJ iQ W ids mem row pl aKept)
    (member : ∀ κ, W.kept[mem κ]? = some (pl κ)) (rowIn : ∀ κ, row κ < (pl κ).rows)
    (hm : old.masks = 2) (i x : ℕ) (hi : pos.draws.toList[i]? = some x)
    (hx : x < 2 ^ W.code.logN) (α : (s.cKept K).Aa) :
    ∃ r, rows[1 + (allSamples S W + (i * (1 + keptRows W + 2) + rowPlace s K W mem row α))]? =
        some r ∧
      r.target = symAtB old pos y x (coordOf s K W old mem row α) ∧
      ReadsAs cs l ids r (genVec s K iJ iQ x α) ∧ OnlyAt cs l ids (InBits W pl) r := by
  have hR : ∀ x ∈ pos.draws.toList, (OnBytes.switchGenerators W old x (symAtB old pos y x)).length =
      1 + keptRows W + 2 := fun x _ => by rw [gens_length, hm]
  have lay : ∀ c r, (OnBytes.switchGenerators W old x (symAtB old pos y x))[c]? = some r →
      rows[1 + (allSamples S W + (i * (1 + keptRows W + 2) + c))]? = some r := by
    intro c r h
    have hc : c < 1 + keptRows W + 2 := by
      have h' := (List.getElem?_eq_some_iff.1 h).1
      rwa [gens_length, hm] at h'
    rw [rows_gen L _ hR i c x hi hc]
    exact h
  rcases α with ⟨_ | κ, ⟨⟩⟩ | ⟨⟩ | ⟨⟩
  · exact ⟨_, lay _ _ (gens_main W old x _), rfl, main_reads F D x hx _, main_only F D x hx _⟩
  · exact ⟨_, lay _ _ (gens_kept W old x _ (mem κ) (row κ) (pl κ) (member κ) (rowIn κ)), rfl,
      kept_reads F D DK κ x hx _, kept_only F D DK κ x hx _⟩
  · exact ⟨_, lay _ _ (gens_mask W old x _ 0 (by omega)), rfl, mask0_reads F D x _,
      mask_only D 0 aM0 aT0 F.mask0 _ _ D.mask0Msg D.mask0Tail x _⟩
  · exact ⟨_, lay _ _ (gens_mask W old x _ 1 (by omega)), rfl, mask1_reads F D x _,
      mask_only D 1 aM1 aT1 F.mask1 _ _ D.mask1Msg D.mask1Tail x _⟩

/-- The number of rows that a switch lays, at t draws. -/
theorem hands_on_count (L : Laid S old T g anew pos y rows W carried) (hm : old.masks = 2) {t : ℕ}
    (ht : pos.draws.toList.length = t) :
    rows.length = 1 + allSamples S W + t * (1 + keptRows W + 2) := by
  rw [rows_length L, hm, ht]

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

/-- What is asked of the typed statement x behind the positions; aOf, iOf: the numbers of the held
messages and of their samples' answers. -/
structure TieN (x : ((LocK).Xc × (LocK).hd.Smp) × (LocK).Lc) (St : OnBytes.Statement)
    (W : OnBytes.SwitchFrame) (ids : ℕ → ℕ) (old : OnBytes.SingleRows) (pos : OnBytes.Positions)
    (y : Array OnBytes.E) (mem row : R.Kp → ℕ) (pl : R.Kp → OnBytes.KeptPlace)
    (aOf : (LocK).hd.K → ℕ) (iOf : ∀ k, ((LocK).hd.o k).Z.S → ℕ) : Prop where
  target : x.1.1.1 = readE old.target
  vector : x.1.1.2 = vecOf R.s R.Kp old row pl
  sample : ∀ ks : Σ k, ((LocK).hd.o k).Z.S, ∃ (k : OnBytes.KeptPlace) (smp : OnBytes.Row),
    W.kept[aOf ks.1]? = some k ∧ (samplesOf St k)[iOf ks.1 ks.2]? = some smp ∧
      Slots R.s R.Kp cs l W ids mem row (aOf ks.1) k ∧ (x.1.2 ks.1).2 ks.2 = readE smp.target ∧
      pushTo ((LocK).hd.sJ ks.1) (((LocK).hd.o ks.1).Z.mat (x.1.2 ks.1).1 ks.2) =
        slotVec R.s R.Kp mem row (aOf ks.1) k.rowBits (formOn smp)
  draw : ∀ i : Fin (LocK).t, pos.draws.toList[i.val]? = some (x.2.1 i).val
  symbol : ∀ (i : Fin (LocK).t) (α : (LocK).C.Aa), x.2.2 i α =
    readE (symAtB old pos y (x.2.1 i).val (coordOf R.s R.Kp W old mem row α))

/-- **The last join, row by row, at the numbered places.** -/
theorem hands_on_rows {St : OnBytes.Statement} {old : OnBytes.SingleRows}
    {T : OnBytes.SwitchTarget} {g : ℕ} {anew : Array ℕ} {pos : OnBytes.Positions}
    {y : Array OnBytes.E} {rows : List OnBytes.Row} {W : OnBytes.SwitchFrame}
    {carried : OnBytes.Row} {ids : ℕ → ℕ} {aMain aM0 aT0 aM1 aT1 : ℕ} {mem row : R.Kp → ℕ}
    {pl : R.Kp → OnBytes.KeptPlace} {aKept : R.Kp → ℕ} {aOf : (LocK).hd.K → ℕ}
    {iOf : ∀ k, ((LocK).hd.o k).Z.S → ℕ} (L : Laid St old T g anew pos y rows W carried)
    (F : FrameOK W aMain aM0 aT0 aM1 aT1)
    (D : Names R.s R.Kp cs l iJ iQ W ids aMain aM0 aT0 aM1 aT1)
    (DK : NamesK R.s R.Kp cs l iJ iQ W ids mem row pl aKept)
    (member : ∀ κ, W.kept[mem κ]? = some (pl κ)) (rowIn : ∀ κ, row κ < (pl κ).rows)
    (hm : old.masks = 2) (h0 : aM0 = W.parts.maskAt.getD 0 0) (h1 : aM1 = W.parts.maskAt.getD 1 0)
    (Q : ∀ ks, old.kept.toList.mapM (placeOf W) = some ks →
      ClaimOK R.s R.Kp cs l W ids mem row pl old ks)
    (x : ((LocK).Xc × (LocK).hd.Smp) × (LocK).Lc)
    (X : TieN R Hd Sb sl Z A₀ cs l iJ iQ t w₀ x St W ids old pos y mem row pl aOf iOf)
    (b : (LocK).RowN) :
    ∃ r : OnBytes.Row, rows[rowNo R.s R.Kp St W mem row aOf iOf b]? = some r ∧
      readE r.target = ((LocK).rowsOf pJK pQK Slf.idf id x).1 b ∧
      (∀ n : (sigOf cs l).Ent,
        coefAt r (ids (entAt cs l n).1) (entAt cs l n).2.1 (entAt cs l n).2.2 =
          ((LocK).rowsOf pJK pQK Slf.idf id x).2 b ⟨Sum.inr n.1, n.2⟩) ∧
      (∀ (a : OldO) (e : ((LocK).S.om (Sum.inl a)).C.J),
        ((LocK).rowsOf pJK pQK Slf.idf id x).2 b ⟨Sum.inl a, e⟩ = 0) ∧
      OnlyAt cs l ids (Inside R.s W pl) r := by
  rcases b with ⟨⟩ | ks | ⟨i, α⟩
  · obtain ⟨ks, hks, rfl⟩ := (switchCarried_iff W old carried).1 L.claim
    refine ⟨_, rows_claim L, X.target.symm, fun n => ?_,
      sel_claim_old R Hd Sb sl Z A₀ cs l iJ iQ t w₀ x, fun o part J hin =>
        claim_only F D DK member old ks hm h0 h1 (Q ks hks) o part J hin.2⟩
    rw [sel_claim_new, X.vector]
    exact claim_reads F D DK member old ks hm h0 h1 (Q ks hks) n
  · obtain ⟨k, smp, hk, hs, Sl, ht, hv⟩ := X.sample ks
    refine ⟨_, rows_sample L (aOf ks.1) (iOf ks.1 ks.2) k smp hk hs, ht.symm, fun n => ?_,
      sel_sample_old R Hd Sb sl Z A₀ cs l iJ iQ t w₀ x ks, fun o part J hin =>
        sample_only D DK member (aOf ks.1) k hk Sl smp o part J
          (hin.2.2 k (List.mem_of_getElem? hk))⟩
    rw [sel_sample_new, hv]
    exact sample_reads D DK member (aOf ks.1) k hk Sl smp n
  · have ha : R.s.C.a = W.code.logN := by rw [D.codeC]; rfl
    have hx : (x.2.1 i).val < 2 ^ W.code.logN :=
      lt_of_lt_of_eq (x.2.1 i).isLt (congrArg (fun e => 2 ^ e) ha)
    obtain ⟨r, hr, ht, hv, ho⟩ :=
      gen_join2 L F D DK member rowIn hm i.val (x.2.1 i).val (X.draw i) hx α
    refine ⟨r, hr, ?_, fun n => ?_, sel_gen_old R Hd Sb sl Z A₀ cs l iJ iQ t w₀ x (i, α),
      fun o part J hin => ho o part J hin.1⟩
    · rw [ht]
      exact (X.symbol i α).symm
    · rw [sel_gen_new]
      exact hv n

end VerifiableInference.Desc.First.K2Hands

#print axioms VerifiableInference.Desc.First.K2Hands.gen_join2
#print axioms VerifiableInference.Desc.First.K2Hands.hands_on_count
#print axioms VerifiableInference.Desc.First.K2Hands.hands_on_rows
